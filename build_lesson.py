#!/usr/bin/env python3
"""Autonomous Guyton physiology lesson builder (GitHub Actions "studio").

One run = one printed page of Guyton and Hall, *Textbook of Medical
Physiology*, 13th edition:
  1. render the book page image (200 dpi),
  2. extract the page's exact English text,
  3. ask Google Gemini for the Persian translation, a detailed Persian
     explanation (شرح) and a 4-question quiz (JSON mode, fail-closed),
  4. build a CINEMATIC CONTENT-ANIMATION teaching film (Jupiter's rule:
     from the first second to the last, the main visual is an animated
     depiction of the lesson's subject matter itself — the physiological
     processes shown moving, like a film of the lesson; the lesson text
     and شرح accompany it in an alongside panel, never as full-screen
     text slides; tables/categorisations are built row by row inside
     the animation) with English narration (edge-tts) and dual EN+FA
     burned-in subtitles,
  5. send everything to Telegram in the fixed order
     page image -> English text -> translation -> شرح -> film -> quiz,
  6. only then advance state.json by one page.

FAIL-CLOSED: any error anywhere exits non-zero and nothing is sent.

Secrets come from the environment only (GitHub Secrets at runtime):
  TELEGRAM_BOT_TOKEN, GEMINI_API_KEY, CHAT_ID.
Optional env: GEMINI_MODEL (default gemini-3.8-flash), EDGE_TTS_PROXY,
VAZIRMATN_DIR (folder containing Vazirmatn-Bold.ttf / -Regular.ttf).

--dry-run: build everything into out/ (page.png, lesson.md, film.mp4),
send nothing, do not advance state.json. In dry-run mode ONLY, when no
GEMINI_API_KEY is available, the builder falls back to a test fixture:
the already-approved sample lesson for printed page 3 stored at
~/workspace/your_files/guyton-sample-text.md. That fixture path exists
purely so the pipeline can be verified offline; real runs use Gemini.
"""
import argparse
import asyncio
import hashlib
import io
import json
import math
import os
import random
import re
import subprocess
import sys
import time
import zipfile

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
STATE_PATH = os.path.join(HERE, "state.json")
OUT = os.path.join(HERE, "out")
WORK = os.path.join(HERE, "work")
FRAMES = os.path.join(WORK, "frames")
IA_ITEM = "guyton-hall-textbook-of-medical-physiology-13-e-2016-bacteri.-blogsky"
LOCAL_PDF_CANDIDATES = [
    os.path.join(HERE, "guyton13.pdf"),
    os.path.expanduser("~/workspace/guyton-sample/guyton13.pdf"),
]
FIXTURE_MD = os.path.expanduser("~/workspace/your_files/guyton-sample-text.md")
VAZIRMATN_URL = ("https://github.com/rastikerdar/vazirmatn/releases/"
                 "download/v33.003/vazirmatn-v33.003.zip")
BOOK = "Guyton and Hall, Textbook of Medical Physiology, 13th edition"

W, H = 1280, 720
FPS = 10
BG = (16, 24, 48)
GOLD = (212, 164, 55)
WHITE = (245, 245, 240)
LIGHT = (200, 210, 230)
CARD = (26, 38, 70)
SUB_EN = (255, 235, 170)


class Fail(Exception):
    """Any failure: abort the whole run, send nothing."""


def log(msg):
    print(f"[guyton-agent] {msg}", flush=True)


def run(cmd, tag):
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise Fail(f"command failed ({tag}): {r.stderr[-800:]}")
    return r


def ffprobe_duration(path):
    r = run(["ffprobe", "-v", "error", "-show_entries", "format=duration",
             "-of", "json", path], "ffprobe")
    return float(json.loads(r.stdout)["format"]["duration"])


# ---------------------------------------------------------------- state
def load_state():
    with open(STATE_PATH, encoding="utf-8") as f:
        st = json.load(f)
    if not isinstance(st.get("printed_page"), int) or not isinstance(st.get("pdf_page"), int):
        raise Fail("state.json must hold integer printed_page and pdf_page")
    return st


def save_state(st):
    tmp = STATE_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(st, f, ensure_ascii=False, indent=1)
    os.replace(tmp, STATE_PATH)


# ------------------------------------------------------------------ PDF
def obtain_pdf():
    """Local copy if present, else download from the Internet Archive."""
    for cand in LOCAL_PDF_CANDIDATES:
        if os.path.exists(cand) and os.path.getsize(cand) > 1_000_000:
            log(f"using local PDF: {cand}")
            return cand
    log("resolving PDF on archive.org ...")
    meta_url = f"https://archive.org/metadata/{IA_ITEM}"
    r = requests.get(meta_url, timeout=120)
    if r.status_code != 200:
        raise Fail(f"archive.org metadata HTTP {r.status_code}")
    files = r.json().get("files", [])
    pdfs = [f for f in files if f.get("name", "").lower().endswith(".pdf")]
    if not pdfs:
        raise Fail("no PDF file listed in the archive.org item")
    pdfs.sort(key=lambda f: int(f.get("size", 0)), reverse=True)
    name = pdfs[0]["name"]
    url = f"https://archive.org/download/{IA_ITEM}/{name}"
    dest = os.path.join(HERE, "guyton13.pdf")
    log(f"downloading {url} ...")
    with requests.get(url, timeout=900, stream=True) as resp:
        if resp.status_code != 200:
            raise Fail(f"PDF download HTTP {resp.status_code}")
        with open(dest, "wb") as f:
            for chunk in resp.iter_content(chunk_size=1 << 20):
                f.write(chunk)
    if os.path.getsize(dest) < 1_000_000:
        raise Fail("downloaded PDF is suspiciously small")
    return dest


def render_page(pdf_path, pdf_page, out_png):
    import pymupdf
    doc = pymupdf.open(pdf_path)
    if pdf_page < 1 or pdf_page > doc.page_count:
        raise Fail(f"pdf_page {pdf_page} out of range (book has {doc.page_count})")
    page = doc[pdf_page - 1]  # state stores 1-based PDF page numbers
    pix = page.get_pixmap(dpi=200)
    pix.save(out_png)
    log(f"page image rendered: {out_png} ({pix.width}x{pix.height})")


_SPACED_CAPS = re.compile(r"^([A-Z0-9] )+[A-Z0-9]$")
_ALLCAPS_HEAD = re.compile(r"^[A-Z][A-Z0-9 ,&'’\-—–:;()]{6,}$")


def clean_page_text(raw, printed_page):
    """Conservative cleanup of PyMuPDF text: drop page furniture (folio,
    spaced-letter unit/chapter running heads), undo soft-hyphen splits and
    line wraps. The wording itself is never altered."""
    t = raw.replace("\xad", "")            # soft hyphen used for word splits
    t = t.replace("­", "")
    t = t.replace(" ", " ").replace(" ", " ")
    kept = []  # (stripped_text, raw_line_ended_with_space)
    for ln in t.split("\n"):
        s = ln.strip()
        if not s:
            continue
        if s == str(printed_page):          # folio number
            continue
        if _SPACED_CAPS.match(s):           # "U N I T I", "C H A P T E R 1"
            continue
        kept.append((s, ln.endswith(" ")))
    # join wrapped lines into paragraphs; ALL-CAPS section heads stand alone
    paragraphs, cur = [], ""

    def flush():
        nonlocal cur
        if cur.strip():
            paragraphs.append(re.sub(r"\s+", " ", cur).strip())
        cur = ""

    prev_space = True
    for s, ended_space in kept:
        if _ALLCAPS_HEAD.match(s) and len(s) < 90:
            flush()
            paragraphs.append(s.title().replace("—The", " — The"))
            prev_space = True
            continue
        if not cur:
            cur = s
        elif prev_space:
            cur = cur + " " + s              # normal word-boundary wrap
        else:
            cur = cur + s                    # word split across the line break
        prev_space = ended_space
        if s.endswith((".", "!", "?", ":", "”")) and len(cur) > 400:
            flush()
            prev_space = True
    flush()
    return "\n\n".join(p for p in paragraphs if p)


def extract_page_text(pdf_path, pdf_page, printed_page):
    import pymupdf
    doc = pymupdf.open(pdf_path)
    raw = doc[pdf_page - 1].get_text()
    text = clean_page_text(raw, printed_page)
    if len(text) < 200:
        raise Fail("extracted page text is too short — refusing to build on it")
    return text


# ---------------------------------------------------------------- fonts
def ensure_fonts():
    """Return (vazir_bold, vazir_regular, deja_bold, deja_regular) paths.
    Vazirmatn: $VAZIRMATN_DIR, ./fonts, system dirs, else download the
    official release zip. Falls back to DejaVu when unavailable."""
    from PIL import ImageFont  # noqa: F401  (Pillow must exist)
    cands = []
    if os.environ.get("VAZIRMATN_DIR"):
        cands.append(os.environ["VAZIRMATN_DIR"])
    cands += [os.path.join(HERE, "fonts"),
              os.path.expanduser("~/.fonts"),
              "/usr/share/fonts/truetype/vazirmatn"]
    vb = vr = None
    for d in cands:
        b = os.path.join(d, "Vazirmatn-Bold.ttf")
        r = os.path.join(d, "Vazirmatn-Regular.ttf")
        if os.path.exists(b) and os.path.exists(r):
            vb, vr = b, r
            break
    if not vb:
        try:
            log("downloading Vazirmatn font ...")
            resp = requests.get(VAZIRMATN_URL, timeout=300)
            if resp.status_code == 200:
                z = zipfile.ZipFile(io.BytesIO(resp.content))
                dest = os.path.join(HERE, "fonts")
                os.makedirs(dest, exist_ok=True)
                for name, out_name in (("fonts/ttf/Vazirmatn-Bold.ttf", "Vazirmatn-Bold.ttf"),
                                       ("fonts/ttf/Vazirmatn-Regular.ttf", "Vazirmatn-Regular.ttf")):
                    with z.open(name) as src, open(os.path.join(dest, out_name), "wb") as f:
                        f.write(src.read())
                vb = os.path.join(dest, "Vazirmatn-Bold.ttf")
                vr = os.path.join(dest, "Vazirmatn-Regular.ttf")
        except Exception as e:
            log(f"Vazirmatn download failed ({e}); falling back to DejaVu")
    deja_dir = "/usr/share/fonts/truetype/dejavu"
    db = os.path.join(deja_dir, "DejaVuSans-Bold.ttf")
    dr = os.path.join(deja_dir, "DejaVuSans.ttf")
    if not os.path.exists(db):
        db = dr = None
    if not vb:
        vb, vr = db, dr
    if not vb:
        raise Fail("no usable font found (need Vazirmatn or DejaVu)")
    log(f"fonts: FA={'Vazirmatn' if 'Vazirmatn' in vb else 'DejaVu'}")
    return vb, vr, db, dr


# ------------------------------------------------------- Persian shaping
from PIL import features as _pil_features
USE_RAQM = _pil_features.check("raqm")


def shape_fa(text):
    """With libraqm, Pillow shapes raw Persian itself (direction='rtl').
    Without it, pre-shape with arabic-reshaper + python-bidi."""
    if USE_RAQM:
        return text
    import arabic_reshaper
    from bidi.algorithm import get_display
    return get_display(arabic_reshaper.reshape(text))


def fa_kwargs():
    return {"direction": "rtl", "language": "fa"} if USE_RAQM else {}


# ---------------------------------------------------------------- brain
GEMINI_PROMPT = """You are the teaching brain of an autonomous physiology course based on Guyton and Hall, Textbook of Medical Physiology, 13th edition. Below is the EXACT English text of one printed page of the book (page {page}).

Return ONLY a JSON object (no markdown, no extra text) with EXACTLY these keys:
- "translation_fa": the COMPLETE Persian translation of the page text, faithful and fluent, paragraphs separated by \\n\\n. Keep section headings as their own paragraphs.
- "explanation_fa": a detailed Persian explanation (شرح) that teaches this page step by step, section by section, following the page's own order. Use ### headings for sub-sections. Every technical term is explained at its first use, with the English term in parentheses, e.g. سلول (Cell). Write for a medical student; be thorough but clear. THE SHARH METHOD (mandatory — see SHARH_METHOD.md and SOURCES.md in this repository): write this شرح the way the world's best physiology teachers teach, in the combined tradition of the 100 collected university and lecture sources (Guyton-based university handouts, TeachMePhysiology, OpenStax, LibreTexts, Ninja Nerd, Dr Najeeb, Armando Hasudungan, Medical Gateway and the rest of SOURCES.md). Rules: (1) ONE COHERENT LESSON — the شرح is a single connected, flowing lesson, never disconnected notes: each section links back to the previous section and points forward to the next, so the whole page reads as one story with a beginning and an end. (2) PARAGRAPH BY PARAGRAPH — EVERY paragraph of the page gets its OWN ### section, in the page's exact order; never merge two paragraphs into one section, never skip a paragraph, and if the page continues a paragraph from the previous page, say so and complete its idea. (3) COMPLETE AND PRECISE — every fact, number, thickness, percentage and name in the paragraph is explained, not merely repeated: state what each number means, compare it with something familiar, and say why it matters physiologically; every mechanism is broken into its small steps in order. (4) A FLUENT EXAMPLE FOR EVERY PARAGRAPH — each section contains at least one concrete, vivid example from everyday life or the clinic, introduced with «مثال:», in the manner of the great lecture teachers: first the analogy or the living picture, then the exact mechanism it stands for. (5) MECHANISM BEFORE MEMORY — always explain HOW and WHY a process happens before naming anything to be memorised, and end each section with one short line beginning «جمع‌بندی:» that states the single idea the student must carry away from that paragraph. (6) HUMAN, WARM AND FLUENT — natural flowing Persian, as a kind teacher speaking to one student; short clear sentences; a guiding question to the reader now and then («حالا فکر کن...»); no dry list-of-facts style. Stay faithful to the page and to standard physiology: never invent numbers, names or mechanisms the page does not support.
- "explanation_summaries_en": a list of short English summaries (1-2 simple sentences each), ONE per ### section of explanation_fa, in the same order. These are spoken aloud in the lesson film.
- "categories": if the page contains a clear categorisation or list (for example the branches of a science, types of something), an object {{"title_en": "...", "title_fa": "...", "items": [{{"en": "...", "fa": "..."}}]}} with 3-10 items; otherwise null.
- "visuals": the animation plan for the lesson film: {{"paragraphs": [...], "points": [...]}}. "paragraphs" holds EXACTLY {n_paras} items — one for each paragraph of the page text below, in the same order. "points" holds EXACTLY one item per "explanation_summaries_en" entry, in the same order. Each item is {{"kind": ..., "en": "...", "fa": "..."}}. "kind" is the animation that best matches what that paragraph/point describes, chosen ONLY from: "flow" (something moving along a path or vessel), "exchange" (two spaces swapping molecules across a membrane), "carrier" (a carrier ferrying molecules across a membrane), "levels" (amounts or levels rising and falling), "assemble" (small units joining into a larger structure), "cycle" (a process going round and round in a loop), "cell" (activity inside a living cell), "compare" (two sides with different amounts or activity). "en" is a very short English label (at most 8 words) naming what moves, e.g. "oxygen molecules leave the blood". "fa" is the same short label in Persian. THE LAW OF THIS COURSE: every concept taught in this lesson — in every paragraph of the page and in every explanation point — MUST be explained by its own process animation whose motion shows that very concept happening, and the label must name the actual moving elements of that concept. Never assign a generic, decorative or unrelated animation to a concept; if a concept describes a process, its animation must depict that process itself.
- "quiz": EXACTLY 4 questions based ONLY on this page: [{{"q_fa": "question in Persian", "a_fa": "full answer in Persian", "q_en": "the same question in English", "a_en": "the same answer in English"}}].

PAGE TEXT:
\"\"\"
{text}
\"\"\"
"""


def call_gemini(page_text, printed_page):
    api_key = os.environ.get("GEMINI_API_KEY", "")
    if not api_key:
        raise Fail("GEMINI_API_KEY is not set")
    model = os.environ.get("GEMINI_MODEL", "gemini-3.8-flash")
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/"
           f"{model}:generateContent")
    n_paras = len([p for p in page_text.split("\n\n") if p.strip()])
    body = {
        "contents": [{"parts": [{"text": GEMINI_PROMPT.format(
            page=printed_page, text=page_text, n_paras=n_paras)}]}],
        "generationConfig": {"responseMimeType": "application/json",
                             "temperature": 0.4},
    }
    try:
        r = requests.post(url, data=json.dumps(body),
                          headers={"Content-Type": "application/json",
                                   "x-goog-api-key": api_key}, timeout=600)
    except Exception as e:
        raise Fail(f"Gemini API call failed: {e}")
    if r.status_code != 200:
        raise Fail(f"Gemini API HTTP {r.status_code}: {r.text[:300]}")
    try:
        resp = r.json()
        text = resp["candidates"][0]["content"]["parts"][0]["text"]
        data = json.loads(text)
    except Exception as e:
        raise Fail(f"Gemini reply is not valid JSON: {e}")
    return validate_content(data, n_paragraphs=n_paras)


# Animation kinds the film renderer actually implements. Gemini must pick
# every scene's visual from this controlled vocabulary (fail-closed).
VISUAL_KINDS = {"flow", "exchange", "carrier", "levels", "assemble",
                "cycle", "cell", "compare"}


def _validate_visual(spec, where):
    if not isinstance(spec, dict):
        raise Fail(f"visual spec for {where} is not an object")
    if spec.get("kind") not in VISUAL_KINDS:
        raise Fail(f"visual spec for {where} has invalid kind: {spec.get('kind')!r}")
    for k in ("en", "fa"):
        v = spec.get(k)
        if not isinstance(v, str) or not v.strip() or len(v) > 120:
            raise Fail(f"visual spec for {where} lacks a short {k} label")


def validate_content(data, n_paragraphs=None):
    if not isinstance(data, dict):
        raise Fail("lesson content is not a JSON object")
    for key in ("translation_fa", "explanation_fa", "explanation_summaries_en", "quiz"):
        if key not in data:
            raise Fail(f"lesson content is missing key: {key}")
    if not str(data["translation_fa"]).strip() or not str(data["explanation_fa"]).strip():
        raise Fail("translation/explanation is empty")
    quiz = data["quiz"]
    if not isinstance(quiz, list) or len(quiz) != 4:
        raise Fail("quiz must contain exactly 4 questions")
    for q in quiz:
        for k in ("q_fa", "a_fa", "q_en", "a_en"):
            if not str(q.get(k, "")).strip():
                raise Fail(f"quiz item is missing {k}")
    if not isinstance(data["explanation_summaries_en"], list) or not data["explanation_summaries_en"]:
        raise Fail("explanation_summaries_en must be a non-empty list")
    cat = data.get("categories")
    if cat is not None:
        if not isinstance(cat, dict) or not isinstance(cat.get("items"), list) or not cat["items"]:
            raise Fail("categories is malformed")
    # CINEMATIC CONTENT ANIMATION: every content unit (each exact-text
    # paragraph, each explanation point) must carry a valid visual spec.
    vis = data.get("visuals")
    if not isinstance(vis, dict):
        raise Fail("lesson content is missing the visuals animation plan")
    paras_v, points_v = vis.get("paragraphs"), vis.get("points")
    if not isinstance(paras_v, list) or not paras_v:
        raise Fail("visuals.paragraphs must be a non-empty list")
    if n_paragraphs is not None and len(paras_v) != n_paragraphs:
        raise Fail(f"visuals.paragraphs has {len(paras_v)} items, "
                   f"expected exactly {n_paragraphs} (one per page paragraph)")
    if not isinstance(points_v, list) or \
            len(points_v) != len(data["explanation_summaries_en"]):
        raise Fail("visuals.points must match explanation_summaries_en one to one")
    for i, s in enumerate(paras_v):
        _validate_visual(s, f"paragraph {i + 1}")
    for i, s in enumerate(points_v):
        _validate_visual(s, f"explanation point {i + 1}")
    return data


# ------------------------------------------- dry-run test fixture (p. 3)
# Used ONLY in --dry-run when GEMINI_API_KEY is absent: parses the
# already-approved sample lesson (printed page 3) so the whole pipeline
# can be verified offline. Real runs always use Gemini.
FIXTURE_SUMMARIES_EN = [
    "Physiology is the science of mechanisms: it explains the physical and chemical steps behind life. It has many branches, from viral physiology to human physiology, and human physiology is the subject of this book.",
    "We stay alive because of complex control systems. Hunger makes us seek food, fear makes us seek refuge, and cold makes us look for warmth. These automatic responses let us live in widely varying conditions.",
    "The cell is the basic living unit of the body. Each organ is an aggregate of many different cells, held together by intercellular supporting structures, like bricks held by mortar.",
]
FIXTURE_QUIZ_EN = [
    ("According to the book, what is physiology, and exactly what does it explain?",
     "Physiology is the science that explains the physical and chemical mechanisms responsible for the origin, development, and progression of life."),
    ("According to the book, why do we stay alive? Give two of the book's own examples.",
     "We stay alive because of complex control systems. For example, hunger makes us seek food, and fear makes us seek refuge; cold makes us look for warmth."),
    ("What is the basic living unit of the body? What is an organ made of, and how are its cells held together?",
     "The basic living unit is the cell. Each organ is an aggregate of many different cells, held together by intercellular supporting structures."),
    ("Name three subdivisions of physiology mentioned in the first paragraph.",
     "For example: cellular physiology, plant physiology, and human physiology. The text also names viral, bacterial, invertebrate, vertebrate, and mammalian physiology."),
]
FIXTURE_CATEGORIES = {
    "title_en": "The branches of physiology",
    "title_fa": "زیرشاخه‌های فیزیولوژی",
    "items": [
        {"en": "Viral physiology", "fa": "فیزیولوژی ویروسی"},
        {"en": "Bacterial physiology", "fa": "فیزیولوژی باکتریایی"},
        {"en": "Cellular physiology", "fa": "فیزیولوژی سلولی"},
        {"en": "Plant physiology", "fa": "فیزیولوژی گیاهی"},
        {"en": "Invertebrate physiology", "fa": "فیزیولوژی بی‌مهرگان"},
        {"en": "Vertebrate physiology", "fa": "فیزیولوژی مهره‌داران"},
        {"en": "Mammalian physiology", "fa": "فیزیولوژی پستانداران"},
        {"en": "Human physiology", "fa": "فیزیولوژی انسان"},
    ],
}
# Animation plan for the page-3 fixture: one visual per English paragraph
# (same order as the sample text) and one per explanation point (same
# order as FIXTURE_SUMMARIES_EN). Kinds are from VISUAL_KINDS.
FIXTURE_VISUALS = {
    "paragraphs": [
        {"kind": "levels", "en": "life at every scale, virus to human",
         "fa": "حیات در همهٔ مقیاس‌ها، از ویروس تا انسان"},
        {"kind": "cycle", "en": "control systems sense and respond",
         "fa": "دستگاه‌های کنترلی حس می‌کنند و پاسخ می‌دهند"},
        {"kind": "assemble", "en": "cells join together, forming an organ",
         "fa": "سلول‌ها کنار هم اندام را می‌سازند"},
    ],
    "points": [
        {"kind": "flow", "en": "physical and chemical steps at work",
         "fa": "مراحل فیزیکی و شیمیایی در کار"},
        {"kind": "cycle", "en": "a need is sensed, the body responds",
         "fa": "نیاز حس می‌شود و بدن پاسخ می‌دهد"},
        {"kind": "cell", "en": "inside the living cell",
         "fa": "درون سلول زنده"},
    ],
}


def _strip_md(text):
    text = re.sub(r"\*\*(.+?)\*\*", r"\1", text)
    text = re.sub(r"\*(.+?)\*", r"\1", text)
    return text.strip()


def load_fixture(printed_page):
    if printed_page != 3:
        raise Fail("the offline test fixture only covers printed page 3; "
                   "set GEMINI_API_KEY for other pages")
    if not os.path.exists(FIXTURE_MD):
        raise Fail(f"test fixture not found: {FIXTURE_MD}")
    with open(FIXTURE_MD, encoding="utf-8") as f:
        md = f.read()
    sections = re.split(r"\n## ", md)

    def section(idx_marker):
        for s in sections:
            if s.startswith(idx_marker):
                return s
        raise Fail(f"fixture section {idx_marker} not found")

    en_sec = section("۱)")
    en_paras = []
    for ln in en_sec.split("\n"):
        ln = ln.strip()
        if ln.startswith(">"):
            en_paras.append(_strip_md(ln.lstrip("> ").strip()))
    if len(en_paras) < 3:
        raise Fail("fixture: could not parse the English paragraphs")

    fa_sec = section("۲)")
    fa_body = fa_sec.split("\n", 1)[1]
    translation = "\n\n".join(
        _strip_md(p) for p in fa_body.strip().split("\n\n")
        if p.strip() and set(p.strip()) != {"-"})

    ex_sec = section("۳)")
    explanation = ex_sec.split("\n", 1)[1].strip()
    explanation = re.sub(r"\n---\s*$", "", explanation)

    q_sec = section("۴)")
    questions = re.findall(r"\*\*سؤال \d+\.\*\*\s*(.+)", q_sec)
    answers = re.findall(r"\*\*پاسخ \d+\.\*\*\s*(.+)", q_sec)
    if len(questions) != 4 or len(answers) != 4:
        raise Fail("fixture: could not parse 4 quiz questions/answers")
    quiz = [{"q_fa": _strip_md(q), "a_fa": _strip_md(a),
             "q_en": FIXTURE_QUIZ_EN[i][0], "a_en": FIXTURE_QUIZ_EN[i][1]}
            for i, (q, a) in enumerate(zip(questions, answers))]
    data = {
        "translation_fa": translation,
        "explanation_fa": explanation,
        "explanation_summaries_en": FIXTURE_SUMMARIES_EN,
        "categories": FIXTURE_CATEGORIES,
        "visuals": FIXTURE_VISUALS,
        "quiz": quiz,
        "_fixture_english_paragraphs": en_paras,
    }
    validate_content(data, n_paragraphs=len(en_paras))
    return data


def split_explanation_points(explanation_fa):
    """Split شرح into (title, body) points at ### headings."""
    parts = re.split(r"\n### ", "\n" + explanation_fa)
    points = []
    for p in parts:
        p = p.strip()
        if not p:
            continue
        if "\n" in p:
            title, body = p.split("\n", 1)
        else:
            title, body = p, ""
        points.append((_strip_md(title), _strip_md(body)))
    return points


# ------------------------------------------------------------ film: draw
from PIL import Image, ImageDraw, ImageFont

FONTS = {}  # filled by init_fonts()


def F(kind, size):
    key = (kind, size)
    if key not in FONTS:
        FONTS[key] = ImageFont.truetype(FONTS["paths"][kind], size)
    return FONTS[key]


def init_fonts():
    vb, vr, db, dr = ensure_fonts()
    FONTS["paths"] = {"fa_b": vb, "fa_r": vr,
                      "en_b": db or vb, "en_r": dr or vr}
    # subtitle fonts are fixed-size, preloaded under their own keys
    FONTS[("sub_en", 25)] = ImageFont.truetype(FONTS["paths"]["en_b"], 25)
    FONTS[("sub_fa", 26)] = ImageFont.truetype(FONTS["paths"]["fa_b"], 26)


_tmp = Image.new("RGB", (10, 10))
_d = ImageDraw.Draw(_tmp)


def _len(text, font, fa=False):
    if fa:
        return _d.textlength(shape_fa(text), font=font, **fa_kwargs())
    return _d.textlength(text, font=font)


def wrap_ltr(text, font, maxw):
    words, lines, cur = text.split(), [], ""
    for w_ in words:
        t = (cur + " " + w_).strip()
        if _d.textlength(t, font=font) <= maxw:
            cur = t
        else:
            if cur:
                lines.append(cur)
            cur = w_
    if cur:
        lines.append(cur)
    return lines


def wrap_fa(text, font, maxw):
    words, lines, cur = text.split(), [], ""
    for w_ in words:
        t = (cur + " " + w_).strip()
        if _len(t, font, fa=True) <= maxw:
            cur = t
        else:
            if cur:
                lines.append(cur)
            cur = w_
    if cur:
        lines.append(cur)
    return lines


def draw_fa(draw, xy, text, font, fill, anchor="ra"):
    draw.text(xy, shape_fa(text), font=font, fill=fill, anchor=anchor, **fa_kwargs())


def center_text(draw, y, text, font, fill, maxw=1160, lh=None):
    lh = lh or int(font.size * 1.25)
    for ln in wrap_ltr(text, font, maxw):
        w_ = draw.textlength(ln, font=font)
        draw.text(((W - w_) / 2, y), ln, font=font, fill=fill)
        y += lh
    return y


def center_fa(draw, y, text, font, fill, maxw=1100, lh=None, right=None):
    lh = lh or int(font.size * 1.35)
    rx = right if right is not None else W - 60
    for ln in wrap_fa(text, font, maxw):
        draw_fa(draw, (rx, y), ln, font, fill, anchor="ra")
        y += lh
    return y


def slide_base():
    img = Image.new("RGB", (W, H), BG)
    return img, ImageDraw.Draw(img, "RGBA")


def header(d, step_label, title, fa_sub=None):
    d.text((60, 40), step_label, font=F("en_b", 29), fill=GOLD)
    d.line([(60, 88), (1220, 88)], fill=GOLD, width=3)
    y = center_text(d, 112, title, F("en_b", 42), WHITE)
    if fa_sub:
        y = center_fa(d, y + 4, fa_sub, F("fa_r", 27), LIGHT)
    return y + 22


# ------------------------------------------------------- subtitle band
SUB_EN_F = ("sub_en", 25)
SUB_FA_F = ("sub_fa", 26)
EN_LH, FA_LH = 32, 37


def cue_lines(en, fa):
    return (wrap_ltr(en, F(*SUB_EN_F), 1180),
            wrap_fa(fa, F(*SUB_FA_F), 1180))


def band_height(cues):
    h = 90
    for en, fa in cues:
        el, fl = cue_lines(en, fa)
        h = max(h, 14 + len(el) * EN_LH + 8 + len(fl) * FA_LH + 12)
    return h


def with_band(base_img, en, fa, bh):
    out = base_img.convert("RGB")
    ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(ov)
    top = H - bh
    d.rectangle([0, top, W, H], fill=(5, 8, 18, 208))
    d.line([(0, top), (W, top)], fill=GOLD + (255,), width=2)
    el, fl = cue_lines(en, fa)
    y = top + 14
    for ln in el:
        w_ = d.textlength(ln, font=F(*SUB_EN_F))
        d.text(((W - w_) / 2, y), ln, font=F(*SUB_EN_F), fill=SUB_EN + (255,))
        y += EN_LH
    y += 8
    for ln in fl:
        draw_fa(d, (W - 50, y), ln, F(*SUB_FA_F), WHITE + (255,), anchor="ra")
        y += FA_LH
    out.paste(ov, (0, 0), ov)
    return out


# ------------------------------------------------------------------ TTS
async def _edge_synth(text, out_path):
    import edge_tts
    kwargs = {"voice": "en-US-ChristopherNeural", "rate": "-10%"}
    proxy = os.environ.get("EDGE_TTS_PROXY")
    if proxy:
        kwargs["proxy"] = proxy
    comm = edge_tts.Communicate(text, **kwargs)
    await comm.save(out_path)


def synth(text):
    """edge-tts narration for one cue, cached by text hash in work/."""
    key = hashlib.md5(text.encode("utf-8")).hexdigest()[:16]
    out = os.path.join(WORK, f"narr-{key}.mp3")
    if os.path.exists(out) and os.path.getsize(out) > 1000:
        return out, ffprobe_duration(out)
    last_err = None
    for _attempt in range(2):
        try:
            asyncio.run(_edge_synth(text, out))
            if os.path.exists(out) and os.path.getsize(out) > 1000:
                return out, ffprobe_duration(out)
            last_err = "empty audio"
        except Exception as e:
            last_err = str(e)
    raise Fail(f"edge-tts failed for cue {text[:50]!r}: {last_err}")


def split_sentences(text):
    parts = re.split(r"(?<=[.!?])\s+", text.strip())
    return [p for p in parts if p]


# ------------------------------------------------------------- painters
def _fade(col, bg, a):
    a = max(0.0, min(1.0, a))
    return tuple(int(bg[i] + (col[i] - bg[i]) * a) for i in range(3))


def paint_title(p, bottom, printed_page, t=0.0):
    img, d = slide_base()
    draw_ambient(d, t, bottom)
    mid = bottom // 2
    lw = int(1160 * min(1.0, p * 2.2))
    d.rectangle([(W - lw) // 2, mid - 218, (W + lw) // 2, mid - 214], fill=GOLD)
    steps = [
        (0.05, "GUYTON AND HALL", ("en_b", 34), GOLD, mid - 190),
        (0.18, "Textbook of Medical Physiology", ("en_b", 47), WHITE, mid - 132),
        (0.32, "13th Edition", ("en_r", 30), LIGHT, mid - 68),
        (0.46, f"Printed page {printed_page}", ("en_b", 40), GOLD, mid + 2),
        (0.62, "One page at a time: the page, its exact words, translation, "
               "explanation, film and quiz", ("en_r", 25), LIGHT, mid + 66),
    ]
    for start, text, fk, col, y in steps:
        a = (p - start) / 0.16
        if a <= 0:
            continue
        center_text(d, y, text, F(*fk), _fade(col, BG, a), maxw=1080)
    if p > 0.78:
        center_fa(d, mid + 150, "درس امروز: یک صفحه از کتاب فیزیولوژی گایتون",
                  F("fa_r", 27), _fade(LIGHT, BG, (p - 0.78) / 0.2))
    return img


def paint_page(p, bottom, page_png):
    img, d = slide_base()
    y = header(d, "STEP 1 — THE BOOK PAGE", "First, look at the real page",
               "گام یکم: خود صفحهٔ کتاب")
    page = Image.open(page_png)
    ph = min(bottom - y - 14, 430)
    pw = int(page.width * ph / page.height)
    px, py = 90, y + 4
    img.paste(page.resize((pw, ph)), (px, py))
    d.rectangle([px, py, px + pw, py + ph], outline=GOLD, width=3)
    # moving highlight travelling down the page
    hy = py + int(ph * min(1.0, p * 1.06))
    ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    od = ImageDraw.Draw(ov)
    od.rectangle([px + 3, max(py + 3, hy - 26), px + pw - 3, min(py + ph - 3, hy + 26)],
                 fill=(212, 164, 55, 70), outline=(212, 164, 55, 220))
    img.paste(Image.alpha_composite(img.convert("RGBA"), ov).convert("RGB"), (0, 0))
    d = ImageDraw.Draw(img, "RGBA")
    bx = px + pw + 56
    items = ["This is the real page of the book",
             "Step 2: its exact English words",
             "Step 3: the Persian translation",
             "Step 4: the explanation, with animations",
             "Step 5: a quiz with answers"]
    yy = y + 22
    for i, it in enumerate(items):
        if p < 0.12 + i * 0.17:
            continue
        d.text((bx, yy), "•", font=F("en_r", 27), fill=GOLD)
        for ln in wrap_ltr(it, F("en_r", 27), W - bx - 90):
            d.text((bx + 38, yy), ln, font=F("en_r", 27), fill=WHITE)
            yy += 35
        yy += 20
    return img


def paint_text_para(p, bottom, idx, head, body):
    img, d = slide_base()
    y = header(d, "STEP 2 — THE BOOK'S EXACT WORDS", f"Paragraph {idx + 1}")
    card_bot = bottom - 8
    d.rounded_rectangle([60, y, 1220, card_bot], radius=18, fill=CARD, outline=GOLD, width=2)
    yy = y + 20
    if head:
        w_ = d.textlength(head, font=F("en_b", 27))
        d.text(((W - w_) / 2, yy), head, font=F("en_b", 27), fill=GOLD)
        yy += 44
    lines = wrap_ltr(body, F("en_r", 23), 1060)
    words_total = sum(len(ln.split()) for ln in lines)
    reveal = int(words_total * min(1.0, p * 1.12))
    # index of the last (possibly partial) revealed line
    seen, last_idx = 0, -1
    for li, ln in enumerate(lines):
        if seen >= reveal:
            break
        last_idx = li
        seen += len(ln.split())
    if last_idx < 0:
        return img
    max_lines = max(1, (card_bot - yy - 12) // 30)
    start = max(0, last_idx - max_lines + 1)  # slide the window when full
    seen = sum(len(ln.split()) for ln in lines[:start])
    for li in range(start, last_idx + 1):
        ln = lines[li]
        lw = len(ln.split())
        txt = ln if seen + lw <= reveal else " ".join(ln.split()[: reveal - seen])
        w_ = d.textlength(txt, font=F("en_r", 23))
        d.text(((W - w_) / 2, yy), txt, font=F("en_r", 23), fill=WHITE)
        seen += lw
        yy += 30
    return img


def paint_translation(p, bottom, idx, fa_text):
    img, d = slide_base()
    y = header(d, "STEP 3 — PERSIAN TRANSLATION", f"Translation — paragraph {idx + 1}",
               "گام سوم: ترجمهٔ فارسی")
    card_bot = bottom - 8
    d.rounded_rectangle([60, y, 1220, card_bot], radius=18, fill=CARD, outline=GOLD, width=2)
    lines = wrap_fa(fa_text, F("fa_r", 26), 1020)
    n_show = max(1, int(len(lines) * min(1.0, p * 1.15)))
    max_lines = max(1, (card_bot - y - 40) // 37)
    start = max(0, n_show - max_lines)  # slide the window when full
    yy = y + 26
    for ln in lines[start:n_show]:
        draw_fa(d, (W - 100, yy), ln, F("fa_r", 26), WHITE, anchor="ra")
        yy += 37
    return img


def paint_explain(p, bottom, title_fa, body_fa):
    img, d = slide_base()
    y = header(d, "STEP 4 — EXPLANATION", "Explanation", "شرح درس")
    card_bot = bottom - 8
    d.rounded_rectangle([60, y, 1220, card_bot], radius=18, fill=CARD, outline=GOLD, width=2)
    yy = y + 18
    yy = center_fa(d, yy, title_fa, F("fa_b", 27), GOLD, maxw=1040, right=W - 100)
    yy += 6
    raw_lines = []
    for ln in body_fa.split("\n"):
        ln = ln.strip().lstrip("-• ").strip()
        if ln:
            raw_lines.extend(wrap_fa(ln, F("fa_r", 23), 1040))
    max_lines = max(1, (card_bot - yy - 14) // 30)
    # progressive reveal; once the card is full, the window slides so the
    # newest line is always visible (the full شرح is also sent as text)
    n_show = max(1, int(len(raw_lines) * min(1.0, p * 1.12)))
    start = max(0, n_show - max_lines)
    for ln in raw_lines[start:n_show]:
        draw_fa(d, (W - 100, yy), ln, F("fa_r", 23), WHITE, anchor="ra")
        yy += 30
    return img


# ------------------------- cinematic content-animation scenes (Jupiter)
# CINEMATIC CONTENT ANIMATION rule: the main visual of every content
# scene is an animated depiction of the lesson's subject matter itself
# (a "visual" spec from the controlled vocabulary in VISUAL_KINDS),
# drawn in a stage on the left ~60% of the frame; the scene's text sits
# in a panel on the right and appears progressively with the narration.
# Every primitive's elements move with absolute time t, so no frame is
# ever a static text slide.
ANIM_X0, ANIM_X1 = 44, 796
PANEL_X0, PANEL_X1 = 820, 1236
DEFAULT_VISUAL = {"kind": "flow", "en": "the body at work",
                  "fa": "بدن در حال کار"}


def _spec_seed(spec):
    return int(hashlib.md5(spec.get("en", "").encode("utf-8")).hexdigest()[:8], 16)


def _ease(u):
    u = max(0.0, min(1.0, u))
    return u * u * (3 - 2 * u)


def _prim_flow(d, rect, p, t, seed):
    """Particles streaming through a vessel, walls gently waving."""
    x0, y0, x1, y1 = rect
    w = x1 - x0
    cy = (y0 + y1) / 2
    hh = (y1 - y0) * 0.24
    for sgn in (-1, 1):
        pts = [(x, cy + sgn * hh + 7 * math.sin(x / 55.0 + t * 0.9
                                                + (0 if sgn < 0 else 1.4)))
               for x in range(x0, x1 + 1, 12)]
        d.line(pts, fill=(236, 158, 158), width=5)
    for k in range(3):  # chevrons riding the stream
        cxp = x0 + ((k * w / 3 + t * 46) % w)
        d.line([(cxp, cy - 13), (cxp + 15, cy), (cxp, cy + 13)], fill=GOLD, width=4)
    cols = [(140, 228, 255), (255, 214, 120), (255, 170, 170), (170, 240, 190)]
    rnd = random.Random(seed)
    for i in range(26):
        sp = rnd.uniform(34, 78)
        lane = rnd.uniform(-hh + 16, hh - 16)
        r = rnd.uniform(4, 7.5)
        x = x0 - 16 + ((rnd.uniform(0, w + 32) + t * sp) % (w + 32))
        yy = cy + lane + 6 * math.sin(x / 48.0 + i * 1.7)
        d.ellipse([x - r, yy - r, x + r, yy + r], fill=cols[i % 4] + (235,),
                  outline=WHITE + (160,), width=1)


def _prim_exchange(d, rect, p, t, seed):
    """Two compartments swapping molecules across a porous membrane."""
    x0, y0, x1, y1 = rect
    w, h = x1 - x0, y1 - y0
    cx = (x0 + x1) / 2
    d.rectangle([x0 + 6, y0 + 8, cx - 8, y1 - 8], fill=(70, 120, 200, 40))
    d.rectangle([cx + 8, y0 + 8, x1 - 6, y1 - 8], fill=(90, 200, 130, 36))
    seg = (y1 - y0 - 40) / 6
    for i in range(6):
        yy0 = y0 + 20 + i * seg
        if i % 2 == 1:  # a pore, glowing gold
            d.line([(cx, yy0 + seg * 0.3), (cx, yy0 + seg * 0.7)], fill=GOLD, width=6)
        else:
            d.line([(cx, yy0 + 3), (cx, yy0 + seg - 3)], fill=(200, 210, 240), width=5)
    rnd = random.Random(seed)
    for i in range(30):
        left = i % 2 == 0
        col = (140, 228, 255) if left else (255, 180, 90)
        bx = rnd.uniform(x0 + 30, cx - 30) if left else rnd.uniform(cx + 30, x1 - 30)
        by = rnd.uniform(y0 + 30, y1 - 30)
        ph1, ph2 = rnd.uniform(0, 6.28), rnd.uniform(0, 6.28)
        if i % 5 == 0:  # a crosser, swinging through a pore
            bx = cx + math.sin(t * 0.45 + ph1) * w * 0.17
            by = y0 + h * (0.3 + 0.2 * ((i // 5) % 3))
        px = bx + 9 * math.sin(t * 1.25 + ph1)
        py = by + 8 * math.cos(t * 1.6 + ph2)
        d.ellipse([px - 6, py - 6, px + 6, py + 6], fill=col + (235,),
                  outline=WHITE + (150,), width=1)


def _prim_carrier(d, rect, p, t, seed):
    """Carrier proteins ferrying molecules across a membrane, in cycle."""
    x0, y0, x1, y1 = rect
    w = x1 - x0
    cy = (y0 + y1) / 2
    d.rectangle([x0 + 14, cy - 15, x1 - 14, cy + 15], fill=(70, 90, 150, 160))
    d.line([(x0 + 14, cy - 15), (x1 - 14, cy - 15)], fill=(236, 158, 158), width=3)
    d.line([(x0 + 14, cy + 15), (x1 - 14, cy + 15)], fill=(236, 158, 158), width=3)
    rnd = random.Random(seed)
    for i in range(16):  # free molecules jiggling on both sides
        top = i % 2 == 0
        bx = rnd.uniform(x0 + 30, x1 - 30)
        by = rnd.uniform(y0 + 24, cy - 46) if top else rnd.uniform(cy + 46, y1 - 24)
        ph = rnd.uniform(0, 6.28)
        px = bx + 8 * math.sin(t * 1.4 + ph)
        py = by + 6 * math.cos(t * 1.1 + ph * 2)
        d.ellipse([px - 5, py - 5, px + 5, py + 5], fill=(170, 240, 190, 220))
    for ci in range(3):  # three carriers, staggered cycles
        cxp = x0 + w * (0.25 + 0.25 * ci)
        u = (t * 0.22 + ci * 0.37) % 1.0
        d.rounded_rectangle([cxp - 27, cy - 24, cxp + 27, cy + 24], radius=10,
                            fill=(96, 64, 148, 255), outline=WHITE, width=2)
        my = None
        if u < 0.45:  # open upward; a molecule descends into the carrier
            d.polygon([(cxp - 11, cy - 24), (cxp + 11, cy - 24), (cxp, cy - 6)],
                      fill=BG + (255,))
            my = cy - 64 + 40 * _ease(u / 0.45)
        elif u < 0.6:  # bound inside while the carrier flips
            d.ellipse([cxp - 7, cy - 7, cxp + 7, cy + 7], fill=GOLD + (255,))
        elif u < 0.9:  # open downward; the molecule is released below
            d.polygon([(cxp - 11, cy + 24), (cxp + 11, cy + 24), (cxp, cy + 6)],
                      fill=BG + (255,))
            my = cy + 24 + 36 * _ease((u - 0.6) / 0.3)
        if my is not None:
            d.ellipse([cxp - 7, my - 7, cxp + 7, my + 7],
                      fill=(140, 228, 255, 255), outline=WHITE, width=1)


def _prim_levels(d, rect, p, t, seed):
    """Three tanks whose levels rise and fall, out of phase."""
    x0, y0, x1, y1 = rect
    w = x1 - x0
    base = y1 - 26
    top = y0 + 34
    cols = [(140, 228, 255), (255, 180, 90), (170, 240, 190)]
    tw = min(120.0, w / 4.2)
    for i in range(3):
        tx0 = x0 + w * (0.16 + 0.27 * i)
        tx1 = tx0 + tw
        d.rounded_rectangle([tx0, top, tx1, base], radius=8,
                            outline=(200, 215, 245), width=3)
        frac = 0.45 + 0.28 * math.sin(t * 0.55 + i * 2.1) \
            + 0.12 * math.sin(p * 6.28 + i)
        frac = max(0.1, min(0.9, frac))
        ly = base - (base - top) * frac
        d.rectangle([tx0 + 4, ly, tx1 - 4, base - 4], fill=cols[i] + (150,))
        wave = [(x, ly + 3 * math.sin(x / 16.0 + t * 2.2 + i))
                for x in range(int(tx0) + 4, int(tx1) - 3, 8)]
        d.line(wave, fill=cols[i] + (255,), width=3)
        axp = (tx0 + tx1) / 2
        if math.cos(t * 0.55 + i * 2.1) > 0:  # currently rising
            d.polygon([(axp, top - 20), (axp - 8, top - 6), (axp + 8, top - 6)],
                      fill=GOLD)
        else:  # currently falling
            d.polygon([(axp, top - 6), (axp - 8, top - 20), (axp + 8, top - 20)],
                      fill=GOLD)
    d.line([(x0 + 10, base), (x1 - 10, base)], fill=(200, 215, 245), width=2)


def _prim_assemble(d, rect, p, t, seed):
    """Scattered units drift together and link into a larger structure."""
    x0, y0, x1, y1 = rect
    w, h = x1 - x0, y1 - y0
    cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
    rnd = random.Random(seed)
    n = 18
    units = []
    for i in range(n):
        ang = rnd.uniform(0, 6.283)
        rad = math.sqrt(rnd.uniform(0.05, 1.0))
        txp = cx + math.cos(ang) * rad * w * 0.30
        typ = cy + math.sin(ang) * rad * h * 0.30
        sxp = x0 + rnd.uniform(20, w - 20)
        syp = y0 + rnd.uniform(16, h - 16)
        units.append((sxp, syp, txp, typ, rnd.uniform(11, 17),
                      rnd.choice([(70, 120, 190), (80, 150, 120),
                                  (110, 130, 200), (90, 160, 170)]),
                      rnd.uniform(0, 6.28)))
    u = _ease(min(1.0, p * 1.5))
    pos = []
    for (sxp, syp, txp, typ, r, col, ph) in units:
        px = sxp + (txp - sxp) * u + 2.0 * math.sin(t * 1.3 + ph)
        py = syp + (typ - syp) * u + 2.0 * math.cos(t * 1.1 + ph)
        pos.append((px, py, r, col))
    if p > 0.55:  # the mortar: links between neighbours fade in
        a = int(200 * min(1.0, (p - 0.55) / 0.3))
        for i in range(n):
            for j in range(i + 1, n):
                if math.hypot(pos[i][0] - pos[j][0], pos[i][1] - pos[j][1]) < 86:
                    d.line([pos[i][:2], pos[j][:2]], fill=GOLD + (a,), width=2)
    for (px, py, r, col) in pos:
        d.ellipse([px - r, py - r, px + r, py + r], fill=col + (255,),
                  outline=(200, 215, 245), width=1)
        d.ellipse([px - 3.5, py - 3.5, px + 3.5, py + 3.5], fill=(40, 34, 84, 255))
    if p > 0.85:  # the finished structure is outlined in gold
        d.ellipse([cx - w * 0.36, cy - h * 0.36, cx + w * 0.36, cy + h * 0.36],
                  outline=GOLD, width=3)


def _prim_cycle(d, rect, p, t, seed):
    """A bright marker travelling around a loop; nodes light as it passes."""
    x0, y0, x1, y1 = rect
    w, h = x1 - x0, y1 - y0
    cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
    R = min(w, h) * 0.34
    ring = [(cx + R * math.cos(a), cy + R * math.sin(a))
            for a in [i * 0.05 for i in range(126)]]
    d.line(ring + [ring[0]], fill=(150, 180, 230), width=3)
    theta = -t * 0.55  # clockwise
    for k in range(4):
        a = -math.pi / 2 + k * math.pi / 2
        nx, ny = cx + R * math.cos(a), cy + R * math.sin(a)
        diff = abs((theta - a + math.pi) % (2 * math.pi) - math.pi)
        lit = diff < 0.55
        d.ellipse([nx - 17, ny - 17, nx + 17, ny + 17],
                  fill=GOLD if lit else CARD, outline=WHITE, width=2)
        s = str(k + 1)
        tw_ = d.textlength(s, font=F("en_b", 19))
        d.text((nx - tw_ / 2, ny - 12), s, font=F("en_b", 19),
               fill=BG if lit else WHITE)
    for back in range(5):  # the marker and its fading trail
        a = theta + back * 0.16
        mx, my = cx + R * math.cos(a), cy + R * math.sin(a)
        r = 10 - back * 1.5
        d.ellipse([mx - r, my - r, mx + r, my + r],
                  fill=(255, 214, 120, 255 - back * 45))
    for k in range(2):  # small orbiters near the centre
        a = t * (0.8 + 0.4 * k) + k * 3.1
        mx = cx + (R * 0.38) * math.cos(a)
        my = cy + (R * 0.38) * math.sin(a)
        d.ellipse([mx - 6, my - 6, mx + 6, my + 6], fill=(140, 228, 255, 230))


def _prim_cell(d, rect, p, t, seed):
    """A living cell: pulsing nucleus, drifting particles, membrane traffic."""
    x0, y0, x1, y1 = rect
    w, h = x1 - x0, y1 - y0
    cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
    rx, ry = w * 0.40, h * 0.38
    d.ellipse([cx - rx, cy - ry, cx + rx, cy + ry], fill=(33, 56, 104, 255),
              outline=(240, 200, 90), width=4)
    d.ellipse([cx - rx + 10, cy - ry + 10, cx + rx - 10, cy + ry - 10],
              outline=(150, 180, 230), width=2)
    nr = rx * 0.30 * (1 + 0.05 * math.sin(t * 2.0))  # pulsing nucleus
    nx, ny = cx - rx * 0.25, cy
    d.ellipse([nx - nr, ny - nr * 0.8, nx + nr, ny + nr * 0.8],
              fill=(96, 64, 148, 255), outline=WHITE, width=2)
    for (fx, fy) in [(-0.45, -0.45), (0.35, 0.5), (0.55, -0.35)]:  # mitochondria
        mx = cx + fx * rx
        my = cy + fy * ry + 4 * math.sin(t * 1.6 + fx * 9)
        d.ellipse([mx - 26, my - 12, mx + 26, my + 12], fill=(206, 122, 54, 255),
                  outline=(250, 200, 140), width=2)
        d.line([(mx - 16, my), (mx - 5, my - 5), (mx + 5, my + 5), (mx + 16, my)],
               fill=(250, 220, 170), width=2)
    rnd = random.Random(seed)
    for i in range(22):  # cytoplasm particles drifting inside the cell
        ph1, ph2 = rnd.uniform(0, 6.28), rnd.uniform(0, 6.28)
        sp1, sp2 = rnd.uniform(0.25, 0.6), rnd.uniform(0.2, 0.5)
        px = cx + rx * 0.62 * math.sin(ph1 + t * sp1)
        py = cy + ry * 0.62 * math.sin(ph2 + t * sp2)
        d.ellipse([px - 3.5, py - 3.5, px + 3.5, py + 3.5],
                  fill=(250, 230, 150, 235))
    for i in range(5):  # molecules crossing the membrane, in and out
        a = i * 1.256 + 0.4
        dist = 0.55 + 0.75 * (0.5 + 0.5 * math.sin(t * 0.6 + i * 1.7))
        px = cx + math.cos(a) * rx * dist
        py = cy + math.sin(a) * ry * dist
        d.ellipse([px - 5, py - 5, px + 5, py + 5], fill=(140, 228, 255, 240),
                  outline=WHITE, width=1)
    labels = [("membrane", cx + rx * 0.30, cy - ry + 10),
              ("nucleus", nx, ny - rx * 0.30 * 0.8 - 24),
              ("mitochondria", cx + rx * 0.35, cy + ry * 0.5 + 20)]
    for i, (txt, lx, ly) in enumerate(labels):
        if p < 0.25 + i * 0.25:
            continue
        tw_ = d.textlength(txt, font=F("en_r", 16))
        d.text((lx - tw_ / 2, ly), txt, font=F("en_r", 16), fill=(200, 220, 255))


def _prim_compare(d, rect, p, t, seed):
    """Two sides with clearly different amounts/activity, split by a divider."""
    x0, y0, x1, y1 = rect
    w, h = x1 - x0, y1 - y0
    cx = (x0 + x1) / 2
    more_right = seed % 2 == 0
    midy = (y0 + y1) / 2
    d.line([(cx, y0 + 12), (cx, y1 - 40)], fill=GOLD, width=3)
    d.ellipse([cx - 17, midy - 17, cx + 17, midy + 17], fill=CARD,
              outline=GOLD, width=2)
    tw_ = d.textlength("vs", font=F("en_b", 16))
    d.text((cx - tw_ / 2, midy - 11), "vs", font=F("en_b", 16), fill=GOLD)
    rnd = random.Random(seed)
    for side in (0, 1):
        sx0 = x0 + 10 if side == 0 else cx + 12
        sx1 = cx - 12 if side == 0 else x1 - 10
        busy = (side == 1) == more_right
        n = 20 if busy else 7
        sp_mul = 2.2 if busy else 0.7
        col = (255, 214, 120) if busy else (140, 170, 220)
        for i in range(n):
            bx = rnd.uniform(sx0 + 14, sx1 - 14)
            by = rnd.uniform(y0 + 20, y1 - 66)
            ph = rnd.uniform(0, 6.28)
            px = bx + 12 * math.sin(t * sp_mul * 0.8 + ph)
            py = by + 9 * math.cos(t * sp_mul * 0.6 + ph * 1.3)
            px = max(sx0 + 6, min(sx1 - 6, px))
            d.ellipse([px - 5, py - 5, px + 5, py + 5], fill=col + (235,))
        lvl = (0.78 if busy else 0.3) + 0.05 * math.sin(t * 1.3 + side * 2.0)
        d.rectangle([sx0, y1 - 34, sx0 + (sx1 - sx0) * lvl, y1 - 18],
                    fill=col + (170,))
        d.rectangle([sx0, y1 - 34, sx1, y1 - 18], outline=(200, 215, 245), width=1)


_PRIMS = {"flow": _prim_flow, "exchange": _prim_exchange,
          "carrier": _prim_carrier, "levels": _prim_levels,
          "assemble": _prim_assemble, "cycle": _prim_cycle,
          "cell": _prim_cell, "compare": _prim_compare}


def draw_visual(d, rect, spec, p, t):
    _PRIMS.get(spec.get("kind"), _prim_flow)(d, rect, p, t, _spec_seed(spec))


def draw_panel_en(d, rect, head, body, p):
    """The alongside panel for English text: progressive word reveal."""
    x0, y0, x1, y1 = rect
    d.rounded_rectangle([x0, y0, x1, y1], radius=16, fill=CARD,
                        outline=GOLD, width=2)
    yy = y0 + 14
    if head:
        hsize = 20
        while hsize > 13 and d.textlength(head, font=F("en_b", hsize)) > (x1 - x0) - 24:
            hsize -= 2  # shrink a long heading until it fits the panel
        hw = d.textlength(head, font=F("en_b", hsize))
        d.text(((x0 + x1 - hw) / 2, yy), head, font=F("en_b", hsize), fill=GOLD)
        yy += 32
    lines = wrap_ltr(body, F("en_r", 20), (x1 - x0) - 30)
    words_total = sum(len(ln.split()) for ln in lines)
    reveal = int(words_total * min(1.0, p * 1.12))
    seen, last_idx = 0, -1
    for li, ln in enumerate(lines):
        if seen >= reveal:
            break
        last_idx = li
        seen += len(ln.split())
    if last_idx < 0:
        return
    max_lines = max(1, (y1 - yy - 10) // 26)
    start = max(0, last_idx - max_lines + 1)  # slide the window when full
    seen = sum(len(ln.split()) for ln in lines[:start])
    for li in range(start, last_idx + 1):
        ln = lines[li]
        lw = len(ln.split())
        txt = ln if seen + lw <= reveal else " ".join(ln.split()[: reveal - seen])
        d.text((x0 + 15, yy), txt, font=F("en_r", 20), fill=WHITE)
        seen += lw
        yy += 26


def draw_panel_fa(d, rect, title, body, p):
    """The alongside panel for Persian text: progressive line reveal."""
    x0, y0, x1, y1 = rect
    d.rounded_rectangle([x0, y0, x1, y1], radius=16, fill=CARD,
                        outline=GOLD, width=2)
    yy = y0 + 12
    if title:
        yy = center_fa(d, yy, title, F("fa_b", 21), GOLD,
                       maxw=(x1 - x0) - 30, right=x1 - 15)
        yy += 4
    raw = []
    for ln in body.split("\n"):
        ln = ln.strip().lstrip("-• ").strip()
        if ln:
            raw.extend(wrap_fa(ln, F("fa_r", 21), (x1 - x0) - 30))
    if not raw:
        return
    max_lines = max(1, (y1 - yy - 10) // 30)
    n_show = max(1, int(len(raw) * min(1.0, p * 1.12)))
    start = max(0, n_show - max_lines)  # slide the window when full
    for ln in raw[start:n_show]:
        draw_fa(d, (x1 - 15, yy), ln, F("fa_r", 21), WHITE, anchor="ra")
        yy += 30


def _center_fa_line(d, cxm, y, text, font, fill):
    w_ = _len(text, font, fa=True)
    draw_fa(d, (cxm - w_ / 2, y), text, font, fill, anchor="la")


def paint_visual(p, t, dur, bottom, step_label, title_en, title_fa,
                 spec, panel_kind, panel_head, panel_body):
    """One cinematic content scene: animated subject matter on the left,
    the accompanying text in a panel on the right, caption under the
    stage naming what is moving (EN + FA)."""
    img, d = slide_base()
    y = header(d, step_label, title_en, title_fa)
    top = y + 2
    bot = bottom - 6
    panel_rect = (PANEL_X0, top, PANEL_X1, bot)
    if panel_kind == "en":
        draw_panel_en(d, panel_rect, panel_head, panel_body, p)
    else:
        draw_panel_fa(d, panel_rect, panel_head, panel_body, p)
    cap_y = bot - 52
    anim_rect = (ANIM_X0, top, ANIM_X1, cap_y - 6)
    d.rounded_rectangle([anim_rect[0] - 6, anim_rect[1] - 4,
                         anim_rect[2] + 6, anim_rect[3] + 4],
                        radius=14, outline=(90, 110, 170), width=2)
    draw_visual(d, anim_rect, spec, p, t)
    if p > 0.03:  # caption naming the moving elements, fading in
        a = min(1.0, (p - 0.03) / 0.15)
        cxm = (ANIM_X0 + ANIM_X1) / 2
        en = spec.get("en", "")
        tw_ = d.textlength(en, font=F("en_b", 20))
        d.text((cxm - tw_ / 2, cap_y), en, font=F("en_b", 20),
               fill=_fade(GOLD, BG, a))
        _center_fa_line(d, cxm, cap_y + 27, spec.get("fa", ""),
                        F("fa_r", 19), _fade(LIGHT, BG, a))
    return img


def draw_ambient(d, t, bottom, seed=99, n=42):
    """Slowly drifting particles behind the title/closing cards, so even
    those frames are alive (first second to last)."""
    rnd = random.Random(seed)
    for i in range(n):
        bx = rnd.uniform(0, W)
        by = rnd.uniform(0, max(1, bottom))
        sp = rnd.uniform(6, 20)
        r = rnd.uniform(1.6, 3.6)
        x = (bx + t * sp) % W
        yy = (by - t * sp * 0.4) % max(1, bottom)
        d.ellipse([x - r, yy - r, x + r, yy + r], fill=(150, 190, 255, 90))


# ------------------------------------------- matplotlib step diagrams
def _mpl_canvas():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    return plt


def make_categories_steps(categories):
    """One PNG per build step: root first, then items appear one by one."""
    os.makedirs(WORK, exist_ok=True)
    plt = _mpl_canvas()
    from matplotlib.patches import FancyBboxPatch
    BGHEX, GOLDH, CARDH, TXTH = "#101830", "#d4a437", "#1a2650", "#f5f5f0"
    items = categories["items"]
    n = len(items)
    paths = []
    for step in range(n + 1):
        fig, ax = plt.subplots(figsize=(12.4, 3.6), dpi=100)
        fig.patch.set_facecolor(BGHEX)
        ax.set_facecolor(BGHEX)
        ax.set_xlim(0, 124)
        ax.set_ylim(0, 36)
        ax.axis("off")

        def box(x, y, w, h, text, fc=CARDH, ec=GOLDH, tc=TXTH, fs=12, bold=False):
            ax.add_patch(FancyBboxPatch((x, y), w, h,
                                        boxstyle="round,pad=0.4,rounding_size=1.2",
                                        fc=fc, ec=ec, lw=1.6))
            ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", color=tc,
                    fontsize=fs, fontweight="bold" if bold else "normal", linespacing=1.35)

        box(37, 29.0, 50, 6.4, categories["title_en"].upper(), fc="#24355f", fs=13.5, bold=True)
        if step >= 1:
            ax.plot([62, 62], [29.0, 26.6], color=GOLDH, lw=1.8)
            span = 116.0
            x0 = 62 - span / 2 + span / (2 * n)
            ax.plot([62 - span / 2 + span / (2 * n), 62 + span / 2 - span / (2 * n)],
                    [26.6, 26.6], color=GOLDH, lw=1.8)
            bw = min(15.0, span / n - 1.5)
            for i in range(min(step, n)):
                cx = x0 + i * (span / n)
                ax.plot([cx, cx], [26.6, 24.8], color=GOLDH, lw=1.8)
                hot = i == step - 1
                box(cx - bw / 2, 14.6, bw, 10.2, items[i]["en"].replace(" physiology", "\nphysiology"),
                    fc="#6b5518" if hot else CARDH, ec=GOLDH if hot else "#7d8fc4",
                    fs=11, bold=hot)
        pth = os.path.join(WORK, f"cat-step-{step}.png")
        fig.savefig(pth, facecolor=BGHEX)
        plt.close(fig)
        paths.append(pth)
    return paths


def make_loop_steps():
    """Feedback-loop diagram in 5 build steps."""
    os.makedirs(WORK, exist_ok=True)
    plt = _mpl_canvas()
    from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
    BGHEX, GOLDH, CARDH, TXTH = "#101830", "#d4a437", "#1a2650", "#f5f5f0"
    boxes = [(4, 31.0, "1 · A NEED arises\nthe body lacks something"),
             (86, 31.0, "2 · The body SENSES it\nhunger · fear · cold"),
             (86, 16.4, "3 · RESPONSE\nwe act to fix it"),
             (4, 16.4, "4 · BALANCE restored\nthe need is met")]
    arrows = [((39.5, 35.3), (84.5, 35.3)), ((103, 30.2), (103, 25.8)),
              ((84.5, 20.7), (39.5, 20.7)), ((21, 25.8), (21, 30.2))]
    paths = []
    for step in range(1, 6):
        fig, ax = plt.subplots(figsize=(12.4, 4.15), dpi=100)
        fig.patch.set_facecolor(BGHEX)
        ax.set_facecolor(BGHEX)
        ax.set_xlim(0, 124)
        ax.set_ylim(0, 41.5)
        ax.axis("off")
        for i, (x, y, text) in enumerate(boxes):
            if step >= i + 1:
                ax.add_patch(FancyBboxPatch((x, y), 34, 8.6,
                                            boxstyle="round,pad=0.4,rounding_size=1.2",
                                            fc=CARDH, ec=GOLDH, lw=1.7))
                ax.text(x + 17, y + 4.3, text, ha="center", va="center", color=TXTH,
                        fontsize=12, linespacing=1.4)
            if step >= i + 2 or (step == 5 and i == 3):
                (x1, y1), (x2, y2) = arrows[i]
                ax.add_patch(FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-|>",
                                             mutation_scale=22, color=GOLDH, lw=2.2))
        if step >= 5:
            ax.text(62, 27.2, "complex control\nsystems", ha="center", va="center",
                    color=GOLDH, fontsize=13.5, fontweight="bold", linespacing=1.4)
            chips = [("Hunger", "seek food"), ("Fear", "seek refuge"), ("Cold", "seek warmth")]
            for i, (a, b) in enumerate(chips):
                x = 6 + i * 39
                ax.add_patch(FancyBboxPatch((x, 1.6), 35, 9.4,
                                            boxstyle="round,pad=0.4,rounding_size=1.2",
                                            fc="#24355f", ec="#7d8fc4", lw=1.4))
                ax.text(x + 17.5, 6.3, f"{a}  →  {b}", ha="center", va="center",
                        color=TXTH, fontsize=12.5)
        pth = os.path.join(WORK, f"loop-step-{step}.png")
        fig.savefig(pth, facecolor=BGHEX)
        plt.close(fig)
        paths.append(pth)
    return paths


def paint_diagram_steps(p, bottom, step_paths, title, fa_sub, note=None):
    img, d = slide_base()
    y = header(d, "STEP 4 — EXPLANATION", title, fa_sub)
    step = min(len(step_paths) - 1, int(p * len(step_paths)))
    diag = Image.open(step_paths[step])
    avail_h = bottom - y - (44 if note else 8)
    scale = min(1160 / diag.width, avail_h / diag.height)
    dw, dh = int(diag.width * scale), int(diag.height * scale)
    img.paste(diag.resize((dw, dh)), ((W - dw) // 2, y + 2))
    if note and p > 0.85:
        center_text(d, y + dh + 12, note, F("en_b", 25), GOLD)
    return img


def paint_cell(p, bottom):
    img, d = slide_base()
    y = header(d, "STEP 4 — EXPLANATION", "The cell — the living unit of the body",
               "شرح: سلول، واحد زندهٔ بدن")
    top = y + 6
    bot = bottom - 6
    cx, cy = 400, (top + bot) // 2
    rx, ry = 300, min(185, (bot - top) // 2 - 6)
    if p > 0.03:  # membrane + inner ring fade in first
        d.ellipse([cx - rx, cy - ry, cx + rx, cy + ry], fill=(33, 56, 104),
                  outline=(240, 200, 90), width=5)
        d.ellipse([cx - rx + 12, cy - ry + 12, cx + rx - 12, cy + ry - 12],
                  outline=(150, 180, 230), width=2)
    if p > 0.18:  # nucleus
        d.ellipse([cx - 120, cy - 68, cx + 10, cy + 62], fill=(96, 64, 148),
                  outline=WHITE, width=2)
        d.ellipse([cx - 88, cy - 36, cx - 38, cy + 14], fill=(64, 40, 104))
    if p > 0.32:  # mitochondria
        for (mx, my, ang) in [(cx + 120, cy - 80, 25), (cx + 60, cy + 78, -20),
                              (cx - 190, cy + 60, 40)]:
            lay = Image.new("RGBA", (130, 70), (0, 0, 0, 0))
            ld = ImageDraw.Draw(lay)
            ld.ellipse([5, 12, 125, 58], fill=(206, 122, 54), outline=(250, 200, 140), width=2)
            ld.line([25, 35, 45, 24, 65, 44, 85, 24, 105, 35], fill=(250, 220, 170), width=3)
            lay = lay.rotate(ang, expand=True, resample=Image.BICUBIC)
            img.paste(lay, (mx - lay.width // 2, my - lay.height // 2), lay)
        d = ImageDraw.Draw(img, "RGBA")
    if p > 0.44:  # ribosome dots appear in two waves
        rnd = random.Random(7)
        dots = []
        for _ in range(46):
            px = cx + rnd.randint(-rx + 30, rx - 30)
            py = cy + rnd.randint(-ry + 26, ry - 26)
            if ((px - cx) / rx) ** 2 + ((py - cy) / ry) ** 2 < 0.92 and \
                    not (cx - 130 < px < cx + 20 and cy - 78 < py < cy + 72):
                dots.append((px, py))
        n_show = len(dots) if p > 0.56 else len(dots) // 2
        for (px, py) in dots[:n_show]:
            d.ellipse([px - 3, py - 3, px + 3, py + 3], fill=(250, 230, 150))
    labels = [
        ("Cell membrane", "the outer wrap", (cx + 150, cy - ry + 16)),
        ("Mitochondrion", "releases energy", (cx + 120, cy - 80)),
        ("Cytoplasm", "the jelly-like inside", (cx + 205, cy - 40)),
        ("Nucleus", "the control center", (cx - 55, cy)),
        ("Ribosomes", "tiny builder dots", (cx - 200, cy + 95)),
    ]
    lx = 786
    ly = top + 10
    for i, (name, desc, (px, py)) in enumerate(labels):
        if p < 0.58 + i * 0.084:
            ly += 54
            continue
        d.line([(px, py), (lx - 14, ly + 11)], fill=(170, 190, 230), width=2)
        d.ellipse([px - 4, py - 4, px + 4, py + 4], fill=GOLD)
        d.text((lx, ly), name, font=F("en_b", 23), fill=GOLD)
        nw = d.textlength(name, font=F("en_b", 23))
        d.text((lx + nw + 8, ly + 2), "— " + desc, font=F("en_r", 20), fill=WHITE)
        ly += 54
    return img


# --------------------------------------------- body-process animations
def heart_points(cx, cy, scale):
    pts = []
    for i in range(201):
        t = 2 * math.pi * i / 200
        x = 16 * math.sin(t) ** 3
        yy = 13 * math.cos(t) - 5 * math.cos(2 * t) - 2 * math.cos(3 * t) - math.cos(4 * t)
        pts.append((cx + x * scale, cy - yy * scale))
    return pts


def build_buildup_scene(bottom):
    from matplotlib.path import Path as MplPath
    cx, cy, scale = 640, (120 + bottom) // 2 + 6, 12.6
    poly = heart_points(cx, cy, scale)
    path = MplPath(poly)
    rnd = random.Random(42)
    cells = []
    tries = 0
    while len(cells) < 110 and tries < 6000:
        tries += 1
        px = cx + rnd.uniform(-165, 165)
        py = cy + rnd.uniform(-160, 160)
        if path.contains_point((px, py)):
            cells.append((px, py, rnd.uniform(11, 16),
                          rnd.choice([(70, 120, 190), (80, 150, 120),
                                      (110, 130, 200), (90, 160, 170)])))
    cells.sort(key=lambda c: math.hypot(c[0] - cx, c[1] - cy))
    pairs = []
    for i in range(len(cells)):
        for j in range(i + 1, len(cells)):
            if math.hypot(cells[i][0] - cells[j][0], cells[i][1] - cells[j][1]) < 47:
                pairs.append((i, j))
    return {"cx": cx, "cy": cy, "poly": poly, "cells": cells, "pairs": pairs,
            "bottom": bottom}


def draw_buildup(st, p, t):
    img, d = slide_base()
    cx, cy = st["cx"], st["cy"]
    d.text((60, 40), "STEP 4 — EXPLANATION · ANIMATION", font=F("en_b", 29), fill=GOLD)
    d.line([(60, 88), (1220, 88)], fill=GOLD, width=3)
    cells = st["cells"]
    if p < 0.20:
        stage = "1 — The cell: the basic living unit of the body"
        r = 46 + 5 * math.sin(t * 3.2)
        d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=(70, 120, 190),
                  outline=(240, 200, 90), width=4)
        nr = r * 0.42
        d.ellipse([cx - nr, cy - nr, cx + nr, cy + nr], fill=(96, 64, 148),
                  outline=WHITE, width=2)
    else:
        if p < 0.52:
            stage = "2 — Cells multiply and gather together"
            frac = (p - 0.20) / 0.32
        elif p < 0.78:
            stage = "3 — Intercellular structures hold them together"
            frac = 1.0
        else:
            stage = "4 — Together, the cells form an ORGAN"
            frac = 1.0
        n_show = int(len(cells) * min(1.0, frac * 1.15))
        if p >= 0.52:
            sa = int(255 * min(1.0, (p - 0.52) / 0.2)) if p < 0.78 else 255
            ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            od = ImageDraw.Draw(ov)
            for i, j in st["pairs"]:
                if i < n_show and j < n_show:
                    od.line([cells[i][:2], cells[j][:2]], fill=(212, 164, 55, sa), width=2)
            img.paste(Image.alpha_composite(img.convert("RGBA"), ov).convert("RGB"), (0, 0))
            d = ImageDraw.Draw(img, "RGBA")
        for idx in range(n_show):
            px, py, r, col = cells[idx]
            d.ellipse([px - r, py - r, px + r, py + r], fill=col,
                      outline=(200, 215, 245), width=1)
            d.ellipse([px - 3.5, py - 3.5, px + 3.5, py + 3.5], fill=(40, 34, 84))
        if p >= 0.78:
            glow = (p - 0.78) / 0.22
            wd = 3 + int(3 * glow)
            d.line(st["poly"] + [st["poly"][0]], fill=GOLD, width=wd, joint="curve")
    center_text(d, 100, stage, F("en_b", 30), GOLD)
    return img


def build_rbc_scene(bottom):
    legend_y = bottom - 38
    scene_bot = legend_y - 14
    cap_cy = (150 + scene_bot) // 2
    return {"bottom": bottom, "cap_cy": cap_cy, "cap_hh": 48,
            "legend_y": legend_y, "scene_bot": scene_bot}


def draw_rbc(st, p, t, dur):
    img, d = slide_base()
    cy, hh = st["cap_cy"], st["cap_hh"]
    legend_y, scene_bot = st["legend_y"], st["scene_bot"]
    d.text((60, 40), "STEP 4 — EXPLANATION · ANIMATION", font=F("en_b", 29), fill=GOLD)
    d.line([(60, 88), (1220, 88)], fill=GOLD, width=3)
    center_text(d, 94, "What cells DO — red blood cells carry oxygen to the tissues",
                F("en_b", 27), GOLD)
    wall_top = cy - hh
    wall_bot = cy + hh
    tissue = []
    for i in range(4):
        x0 = 110 + i * 280
        tissue.append((x0, 148, x0 + 240, wall_top - 26, i, 0))
        tissue.append((x0, wall_bot + 26, x0 + 240, scene_bot - 26, i, 1))
    flash = {}
    parts = []
    spawn_dt = 0.42
    travel = 1.5
    for k in range(int(dur / spawn_dt) + 2):
        tb = k * spawn_dt + 0.4
        age = t - tb
        if age < 0:
            continue
        r2 = random.Random(1000 + k)
        slot = r2.randrange(6)
        direc = -1 if k % 2 == 0 else 1
        ox0 = 100 + ((slot * 185 + tb * 62) % 1090)
        oy0 = cy + r2.uniform(-14, 14)
        if age < travel:
            xx = ox0 + age * 20 + math.sin(age * 5 + k) * 7
            yy = oy0 + direc * (hh + 58) * (age / travel)
            parts.append((xx, yy))
        elif age < travel + 0.55:
            col = min(3, max(0, int((ox0 - 110) // 280)))
            flash[(col, 0 if direc < 0 else 1)] = 1.0 - (age - travel) / 0.55
    for (x0, y0, x1, y1, col, row) in tissue:
        fl = flash.get((col, row), 0.0)
        base, target = (32, 54, 96), (96, 150, 205)
        fill = tuple(int(base[c] + (target[c] - base[c]) * fl) for c in range(3))
        d.rounded_rectangle([x0, y0, x1, y1], radius=26, fill=fill,
                            outline=(96, 128, 190), width=2)
        ncx, ncy = (x0 + x1) // 2, (y0 + y1) // 2
        d.ellipse([ncx - 17, ncy - 17, ncx + 17, ncy + 17], fill=(58, 44, 110),
                  outline=(140, 150, 200), width=1)
    d.text((84, wall_top - 24), "◀ from the lungs", font=F("en_r", 19), fill=LIGHT)
    tw = d.textlength("to the tissues ▶", font=F("en_r", 19))
    d.text((1210 - tw, wall_top - 24), "to the tissues ▶", font=F("en_r", 19), fill=LIGHT)
    d.rectangle([70, wall_top, 1210, wall_bot], fill=(48, 26, 38))
    for sgn in (-1, 1):
        pts = [(x, cy + sgn * hh + 5 * math.sin(x / 95.0 + (0 if sgn < 0 else 1.3)))
               for x in range(70, 1211, 14)]
        d.line(pts, fill=(236, 158, 158), width=5)
    for s in range(6):
        x = 100 + ((s * 185 + t * 62) % 1090)
        yy = cy + 15 * math.sin(x / 130.0 + s * 1.7)
        d.ellipse([x - 31, yy - 20, x + 31, yy + 20], fill=(203, 52, 40),
                  outline=(255, 150, 130), width=2)
        d.ellipse([x - 15, yy - 9, x + 15, yy + 9], fill=(233, 138, 118))
    for (xx, yy) in parts:
        d.ellipse([xx - 6, yy - 6, xx + 6, yy + 6], fill=(140, 228, 255),
                  outline=WHITE, width=1)
        d.ellipse([xx - 2, yy - 2, xx + 2, yy + 2], fill=WHITE)
    # legend
    ly = legend_y
    d.ellipse([84, ly + 2, 116, ly + 24], fill=(203, 52, 40), outline=(255, 150, 130), width=2)
    d.text((126, ly), "red blood cell", font=F("en_r", 20), fill=WHITE)
    d.ellipse([330, ly + 4, 354, ly + 28], fill=(140, 228, 255), outline=WHITE, width=1)
    d.text((364, ly), "oxygen (O2)", font=F("en_r", 20), fill=WHITE)
    d.rounded_rectangle([560, ly + 2, 596, ly + 28], radius=8, fill=(32, 54, 96),
                        outline=(96, 128, 190), width=2)
    d.text((606, ly), "tissue cell (flashes when it receives oxygen)",
           font=F("en_r", 20), fill=WHITE)
    return img


def paint_quiz(p, bottom, n, q_fa, a_fa, answer_start):
    img, d = slide_base()
    y = header(d, "STEP 5 — QUIZ", f"Question {n} of 4", "آزمون")
    q_bot = y + 140
    d.rounded_rectangle([60, y, 1220, q_bot], radius=18, fill=CARD, outline=GOLD, width=2)
    qp = min(1.0, p / max(0.05, answer_start - 0.10))
    q_size = 28
    for cand in (28, 25, 22):
        q_size = cand
        if len(wrap_fa(q_fa, F("fa_r", cand), 1000)) * (cand + 12) <= q_bot - y - 30:
            break
    q_lines = wrap_fa(q_fa, F("fa_r", q_size), 1000)
    words_total = sum(len(ln.split()) for ln in q_lines)
    reveal = int(words_total * qp)
    yy = y + 22
    seen = 0
    for ln in q_lines:
        lw = len(ln.split())
        if seen >= reveal:
            break
        txt = ln if seen + lw <= reveal else " ".join(ln.split()[: reveal - seen])
        draw_fa(d, (W - 105, yy), txt, F("fa_r", q_size), WHITE, anchor="ra")
        seen += lw
        yy += q_size + 12
    if answer_start - 0.10 < p < answer_start:
        center_text(d, q_bot + 12, "think…", F("en_r", 24), LIGHT)
    if p >= answer_start:
        a_top = q_bot + 46
        a_bot = bottom - 8
        d.rounded_rectangle([60, a_top, 1220, a_bot], radius=18, fill=(30, 52, 34),
                            outline=GOLD, width=2)
        ap = min(1.0, (p - answer_start) / max(0.05, 1.0 - answer_start) * 1.15)
        center_fa(d, a_top + 8, "پاسخ", F("fa_b", 24), GOLD, right=W - 105)
        # shrink the answer font until every wrapped line fits the card,
        # so no line can ever slide under the subtitle band
        a_size, a_lines = 17, wrap_fa(a_fa, F("fa_r", 17), 1060)
        for cand in (23, 21, 19, 17):
            cand_lines = wrap_fa(a_fa, F("fa_r", cand), 1060)
            if a_top + 44 + len(cand_lines) * (cand + 10) <= a_bot - 4:
                a_size, a_lines = cand, cand_lines
                break
        words_total = sum(len(ln.split()) for ln in a_lines)
        reveal = int(words_total * ap)
        yy = a_top + 44
        seen = 0
        for ln in a_lines:
            lw = len(ln.split())
            if seen >= reveal:
                break
            txt = ln if seen + lw <= reveal else " ".join(ln.split()[: reveal - seen])
            draw_fa(d, (W - 105, yy), txt, F("fa_r", a_size), WHITE, anchor="ra")
            seen += lw
            yy += a_size + 10
    return img


def paint_closing(p, bottom, printed_page, t=0.0):
    img, d = slide_base()
    draw_ambient(d, t, bottom, seed=7)
    mid = bottom // 2
    if p > 0.05:
        center_text(d, mid - 120, "END OF THE LESSON", F("en_b", 38),
                    _fade(GOLD, BG, (p - 0.05) / 0.2))
    if p > 0.3:
        center_text(d, mid - 48, f"Printed page {printed_page} is complete.",
                    F("en_r", 29), _fade(WHITE, BG, (p - 0.3) / 0.2))
    if p > 0.55:
        center_text(d, mid - 6, f"Next lesson: printed page {printed_page + 1}.",
                    F("en_r", 29), _fade(WHITE, BG, (p - 0.55) / 0.2))
    if p > 0.75:
        center_fa(d, mid + 52, "پایان درس؛ درس بعدی: صفحهٔ بعد کتاب.",
                  F("fa_r", 28), _fade(LIGHT, BG, (p - 0.75) / 0.2))
    return img


# --------------------------------------------------------- film assembly
def split_fa_sentences(text):
    parts = re.split(r"(?<=[.؛!؟])\s+", text.strip())
    return [p for p in parts if p]


def detect_head(paragraph):
    """A short opening sentence like 'Human Physiology.' is a heading."""
    m = re.match(r"^(.+?\.)\s+(.*)$", paragraph, re.S)
    if m and len(m.group(1).split()) <= 9 and "," not in m.group(1):
        return m.group(1), m.group(2)
    return None, paragraph


def build_scenes(content, english_paras, translation_paras, page_png,
                 printed_page, keyword_text=""):
    # diagram/animation scenes are chosen by what the WHOLE page talks
    # about (e.g. page 3 discusses red blood cells and oxygen further
    # down), not only by the paragraphs quoted in the text scenes
    full_lower = keyword_text or " ".join(english_paras).lower()
    scenes = []

    def S(cues, paint, min_dur=0.0, pause_after_first=0.0):
        scenes.append({"cues": cues, "paint": paint, "min_dur": min_dur,
                       "pause": pause_after_first})

    S([("Guyton and Hall, Textbook of Medical Physiology, thirteenth edition.",
        "فیزیولوژی گایتون و هال — ویرایش سیزدهم"),
       (f"Today's lesson is printed page {printed_page}. We go step by step: "
        "the page, its exact words, the translation, the explanation, and a quiz.",
        f"درس امروز: صفحهٔ چاپی {printed_page} — گام‌به‌گام")],
      lambda p, t, dur, bottom, fr: paint_title(p, bottom, printed_page, t),
      min_dur=6.0)

    S([("First, look at the real page of the book. The highlight travels "
        "over the page we are studying today.", "گام یکم: خود صفحهٔ کتاب")],
      lambda p, t, dur, bottom, fr: paint_page(p, bottom, page_png),
      min_dur=7.0)

    # CINEMATIC CONTENT ANIMATION — THE LAW OF THIS COURSE: every concept
    # taught (each paragraph, each explanation point) MUST be explained by
    # its own process animation depicting that concept itself. There is no
    # fallback animation: a missing spec fails the build (fail-closed), so
    # no concept can ever be presented as text alone or with a generic
    # animation. The text accompanies the animation in the alongside panel.
    visuals = content.get("visuals") or {}
    para_visuals = visuals.get("paragraphs") or []
    point_visuals = visuals.get("points") or []

    def para_spec(i):
        if i >= len(para_visuals):
            raise Fail(f"paragraph {i + 1} has no process-animation spec")
        return para_visuals[i]

    def point_spec(j):
        if j >= len(point_visuals):
            raise Fail(f"explanation point {j + 1} has no process-animation spec")
        return point_visuals[j]

    for i, para in enumerate(english_paras):
        head, body = detect_head(para)
        fa_sents = split_fa_sentences(translation_paras[i]) if i < len(translation_paras) else []
        cues = []
        for j, sent in enumerate(split_sentences(body)):
            fa = fa_sents[min(j, len(fa_sents) - 1)] if fa_sents else f"متن کتاب — پاراگراف {i + 1}"
            cues.append((sent, fa))
        if not cues:
            continue
        spec = para_spec(i)
        S(cues, lambda p, t, dur, bottom, fr, i=i, head=head, body=body,
          spec=spec:
          paint_visual(p, t, dur, bottom, "STEP 2 — THE BOOK'S EXACT WORDS",
                       f"Paragraph {i + 1}", None, spec, "en", head, body),
          min_dur=3.0)

    for i, fa_para in enumerate(translation_paras):
        n_lines = max(1, len(wrap_fa(fa_para, F("fa_r", 21),
                                     PANEL_X1 - PANEL_X0 - 30)))
        spec = para_spec(i)
        S([(f"Now, the Persian translation of paragraph {i + 1}.",
            f"ترجمهٔ فارسی — پاراگراف {i + 1}")],
          lambda p, t, dur, bottom, fr, i=i, fa_para=fa_para, spec=spec:
          paint_visual(p, t, dur, bottom, "STEP 3 — PERSIAN TRANSLATION",
                       f"Translation — paragraph {i + 1}", "ترجمهٔ فارسی",
                       spec, "fa", None, fa_para),
          min_dur=2.0 + 0.8 * n_lines)

    points = split_explanation_points(content["explanation_fa"])
    summaries = content["explanation_summaries_en"]
    cat = content.get("categories")
    cat_steps = make_categories_steps(cat) if cat else None
    loop_steps = make_loop_steps() if "control system" in full_lower else None
    buildup = build_buildup_scene(560) if "organ" in full_lower else None
    rbc = build_rbc_scene(560) if ("red blood cell" in full_lower or "oxygen" in full_lower) else None

    def diagram_after(idx):
        if idx == 0 and cat_steps:
            S([("Watch this categorisation build up, one item at a time.",
                cat["title_fa"])],
              lambda p, t, dur, bottom, fr: paint_diagram_steps(
                  p, bottom, cat_steps, cat["title_en"], cat["title_fa"]),
              min_dur=2.5 + 1.1 * len(cat["items"]))
        if idx == 1 and loop_steps:
            S([("This is the loop of a control system: a need arises, the body "
                "senses it, the body responds, and balance is restored.",
                "چرخهٔ دستگاه کنترلی بدن")],
              lambda p, t, dur, bottom, fr: paint_diagram_steps(
                  p, bottom, loop_steps, "How a control system works", "دستگاه کنترلی چگونه کار می‌کند"),
              min_dur=10.0)
        if idx == 2:
            if "cell" in full_lower:
                S([("Let us look at a cell, the living unit of the body. "
                    "Its parts appear one by one.", "سلول، واحد زندهٔ بدن")],
                  lambda p, t, dur, bottom, fr: paint_cell(p, bottom), min_dur=9.0)
            if buildup:
                S([("One cell alone is not an organ. Cells multiply, gather, and "
                    "are held together by intercellular structures — and together "
                    "they form an organ.", "از سلول تا اندام")],
                  lambda p, t, dur, bottom, fr: draw_buildup(buildup, p, t),
                  min_dur=13.0)
            if rbc:
                S([("Red blood cells do a vital job: they carry oxygen from the "
                    "lungs to every tissue. Watch the oxygen leave the red cells "
                    "and enter the tissue cells.", "گلبول قرمز و رساندن اکسیژن به بافت‌ها")],
                  lambda p, t, dur, bottom, fr: draw_rbc(rbc, p, t, dur),
                  min_dur=14.0)

    for j, (title_fa, body_fa) in enumerate(points):
        summary = summaries[j] if j < len(summaries) else f"Explanation, part {j + 1}."
        cues = [(s, title_fa) for s in split_sentences(summary)] or [(summary, title_fa)]
        spec = point_spec(j)
        n_panel = max(1, len(wrap_fa(body_fa, F("fa_r", 21),
                                     PANEL_X1 - PANEL_X0 - 30)))
        S(cues, lambda p, t, dur, bottom, fr, title_fa=title_fa,
          body_fa=body_fa, spec=spec:
          paint_visual(p, t, dur, bottom, "STEP 4 — EXPLANATION",
                       "Explanation", "شرح درس", spec, "fa", title_fa, body_fa),
          min_dur=max(4.0, min(26.0, 0.5 * n_panel)))
        diagram_after(j)
    if not points:
        diagram_after(0)
    if len(points) < 3:
        diagram_after(2)

    for i, q in enumerate(content["quiz"]):
        # subtitles carry the question and the answer's first sentence;
        # the FULL answer is revealed inside the scene's answer card
        a_sub = split_fa_sentences(q["a_fa"])
        S([(q["q_en"], q["q_fa"]), (q["a_en"], a_sub[0] if a_sub else q["a_fa"])],
          lambda p, t, dur, bottom, fr, i=i, q=q:
          paint_quiz(p, bottom, i + 1, q["q_fa"], q["a_fa"], fr[1][0]),
          min_dur=6.0, pause_after_first=2.2)

    S([(f"That was printed page {printed_page}. In the next lesson, we continue "
        f"with printed page {printed_page + 1}.", "پایان درس")],
      lambda p, t, dur, bottom, fr: paint_closing(p, bottom, printed_page, t),
      min_dur=5.0)
    return scenes


def _make_silence(path, seconds):
    if not os.path.exists(path):
        run(["ffmpeg", "-y", "-f", "lavfi", "-i", "anullsrc=r=44100:cl=stereo",
             "-t", str(seconds), path], "silence")


def _normalize_audio(src, tag):
    """Normalize any narration clip to 44.1 kHz stereo WAV so the concat
    step is robust across TTS sources. Keyed by the source file's name
    (a hash of the cue text), so it can never go stale between lessons."""
    base = os.path.splitext(os.path.basename(src))[0]
    out = os.path.join(WORK, f"norm-{base}.wav")
    if not (os.path.exists(out) and os.path.getsize(out) > 1000):
        run(["ffmpeg", "-y", "-i", src, "-ar", "44100", "-ac", "2", out],
            f"norm-{tag}")
    return out


def render_film(scenes, out_path):
    import shutil
    shutil.rmtree(FRAMES, ignore_errors=True)
    os.makedirs(FRAMES, exist_ok=True)
    silence = os.path.join(WORK, "silence-2.2.wav")
    _make_silence(silence, 2.2)
    seg_paths = []
    total = 0.0
    for si, scene in enumerate(scenes):
        cue_files, cue_durs = [], []
        for en, _fa in scene["cues"]:
            path, dur = synth(en)
            cue_files.append(path)
            cue_durs.append(dur)
        starts, tcur = [], 0.0
        for ci, cd in enumerate(cue_durs):
            starts.append(tcur)
            tcur += cd
            if ci == 0 and scene["pause"] > 0:
                tcur += scene["pause"]
        dur = max(tcur, scene["min_dur"])
        total += dur
        fracs = [(starts[i] / dur, (starts[i] + cue_durs[i]) / dur)
                 for i in range(len(cue_durs))]
        bh = band_height(scene["cues"])
        bottom = H - bh
        sdir = os.path.join(FRAMES, f"scene-{si:02d}")
        os.makedirs(sdir, exist_ok=True)
        n_frames = max(1, math.ceil(dur * FPS))
        for fi in range(n_frames):
            t = fi / FPS
            p = min(1.0, t / dur)
            active = scene["cues"][0]
            for ci in range(len(scene["cues"])):
                if starts[ci] <= t:
                    active = scene["cues"][ci]
            img = scene["paint"](p, t, dur, bottom, fracs)
            img = with_band(img, active[0], active[1], bh)
            img.save(os.path.join(sdir, f"{fi:05d}.jpg"), quality=90)
        # scene audio: cues (+pause) padded with silence to the scene length
        norm_files = [_normalize_audio(cf, f"{si:02d}-{ci}")
                      for ci, cf in enumerate(cue_files)]
        list_path = os.path.join(WORK, f"audio-list-{si:02d}.txt")
        with open(list_path, "w") as f:
            for ci, cf in enumerate(norm_files):
                f.write(f"file '{cf}'\n")
                if ci == 0 and scene["pause"] > 0:
                    f.write(f"file '{silence}'\n")
        audio = os.path.join(WORK, f"scene-{si:02d}.mp3")
        run(["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", list_path,
             "-af", "apad", "-t", f"{dur:.3f}", "-c:a", "libmp3lame", audio],
            f"audio-{si}")
        seg = os.path.join(WORK, f"seg-{si:02d}.mp4")
        run(["ffmpeg", "-y", "-framerate", str(FPS), "-i",
             os.path.join(sdir, "%05d.jpg"), "-i", audio,
             "-c:v", "libx264", "-preset", "veryfast", "-crf", "23",
             "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "128k",
             "-t", f"{dur:.3f}", seg], f"seg-{si}")
        seg_paths.append(seg)
        log(f"scene {si + 1}/{len(scenes)} done ({dur:.1f}s)")
    concat_list = os.path.join(WORK, "concat.txt")
    with open(concat_list, "w") as f:
        for s in seg_paths:
            f.write(f"file '{s}'\n")
    run(["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", concat_list,
         "-c", "copy", out_path], "final-concat")
    real = ffprobe_duration(out_path)
    log(f"film rendered: {out_path} — {real:.1f}s (planned {total:.1f}s)")
    if abs(real - total) > 3.0:
        raise Fail(f"film duration mismatch: {real:.1f}s vs planned {total:.1f}s")
    return real


# ------------------------------------------------------------- lesson.md
def build_lesson_md(printed_page, english_paras, content):
    lines = [f"# Guyton Physiology — Lesson: printed page {printed_page}",
             "",
             f"**Book:** {BOOK}",
             f"**Printed page:** {printed_page}",
             "",
             "## 1) The book's exact English text",
             ""]
    for p in english_paras:
        lines += [p, ""]
    lines += ["## 2) Persian translation (ترجمهٔ فارسی)", "",
              content["translation_fa"], "",
              "## 3) Explanation (شرح)", "",
              content["explanation_fa"], "",
              "## 4) Quiz (آزمون)", ""]
    for i, q in enumerate(content["quiz"]):
        lines += [f"**Question {i + 1}.** {q['q_fa']}", ""]
    lines += ["### Answers (پاسخ‌ها)", ""]
    for i, q in enumerate(content["quiz"]):
        lines += [f"**Answer {i + 1}.** {q['a_fa']}", ""]
    return "\n".join(lines)


# -------------------------------------------------------------- Telegram
def tg_call(method, token, data=None, files=None):
    url = f"https://api.telegram.org/bot{token}/{method}"
    r = requests.post(url, data=data or {}, files=files, timeout=600)
    if r.status_code != 200:
        raise Fail(f"Telegram {method} HTTP {r.status_code}: {r.text[:300]}")
    body = r.json()
    if not body.get("ok"):
        raise Fail(f"Telegram {method} not ok: {body}")
    return body


def split_text(text, limit=3900):
    chunks, cur = [], ""
    for para in text.split("\n\n"):
        if len(para) > limit:  # very long single paragraph: hard-split
            if cur:
                chunks.append(cur)
                cur = ""
            for i in range(0, len(para), limit):
                chunks.append(para[i:i + limit])
            continue
        cand = (cur + "\n\n" + para) if cur else para
        if len(cand) <= limit:
            cur = cand
        else:
            chunks.append(cur)
            cur = para
    if cur:
        chunks.append(cur)
    return [c for c in chunks if c.strip()]


def send_lesson(token, chat_id, printed_page, page_png, english_text,
                content, film_path):
    def msg(text):
        tg_call("sendMessage", token, {"chat_id": chat_id, "text": text})
        time.sleep(1)

    with open(page_png, "rb") as f:
        tg_call("sendPhoto", token,
                {"chat_id": chat_id,
                 "caption": f"📖 Guyton and Hall — printed page {printed_page}"},
                files={"photo": f})
    time.sleep(1)
    for chunk in split_text(f"📄 The book's exact words — printed page {printed_page}\n\n{english_text}"):
        msg(chunk)
    for chunk in split_text("🌐 ترجمهٔ فارسی\n\n" + content["translation_fa"]):
        msg(chunk)
    for chunk in split_text("📚 شرح\n\n" + content["explanation_fa"]):
        msg(chunk)
    with open(film_path, "rb") as f:
        tg_call("sendVideo", token,
                {"chat_id": chat_id,
                 "caption": f"🎬 Teaching film — printed page {printed_page}",
                 "supports_streaming": "true"},
                files={"video": f})
    time.sleep(1)
    quiz_text = "📝 آزمون\n\n" + "\n\n".join(
        f"سؤال {i + 1}: {q['q_fa']}" for i, q in enumerate(content["quiz"]))
    for chunk in split_text(quiz_text):
        msg(chunk)
    ans_text = "✅ پاسخ‌ها\n\n" + "\n\n".join(
        f"پاسخ {i + 1}: {q['a_fa']}" for i, q in enumerate(content["quiz"]))
    for chunk in split_text(ans_text):
        msg(chunk)
    log("lesson sent to Telegram")


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true",
                    help="build into out/ only; send nothing; keep state")
    args = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(WORK, exist_ok=True)
    try:
        if not args.dry_run:
            for var in ("TELEGRAM_BOT_TOKEN", "GEMINI_API_KEY", "CHAT_ID"):
                if not os.environ.get(var):
                    raise Fail(f"{var} is not set (required for a real run)")
        init_fonts()
        state = load_state()
        printed_page, pdf_page = state["printed_page"], state["pdf_page"]
        if pdf_page - 4 != printed_page:
            log(f"warning: pdf_page {pdf_page} - 4 != printed_page {printed_page}; "
                "trusting state.json as-is")
        pdf_path = obtain_pdf()
        page_png = os.path.join(OUT, "page.png")
        render_page(pdf_path, pdf_page, page_png)
        page_text = extract_page_text(pdf_path, pdf_page, printed_page)
        log(f"extracted {len(page_text)} chars of page text")

        if os.environ.get("GEMINI_API_KEY"):
            content = call_gemini(page_text, printed_page)
            english_paras = [p for p in page_text.split("\n\n") if p.strip()]
            log("content generated by Gemini")
        elif args.dry_run:
            content = load_fixture(printed_page)
            english_paras = content.pop("_fixture_english_paragraphs")
            log("DRY-RUN: using the approved page-3 sample as a test fixture")
        else:
            raise Fail("GEMINI_API_KEY is not set")

        translation_paras = [p for p in content["translation_fa"].split("\n\n") if p.strip()]
        lesson_md = build_lesson_md(printed_page, english_paras, content)
        with open(os.path.join(OUT, "lesson.md"), "w", encoding="utf-8") as f:
            f.write(lesson_md)

        scenes = build_scenes(content, english_paras, translation_paras,
                              page_png, printed_page,
                              keyword_text=page_text.lower())
        film_path = os.path.join(OUT, "film.mp4")
        render_film(scenes, film_path)

        if args.dry_run:
            log("DRY-RUN complete: out/page.png, out/lesson.md, out/film.mp4 "
                "(nothing sent, state unchanged)")
            return 0
        send_lesson(os.environ["TELEGRAM_BOT_TOKEN"], os.environ["CHAT_ID"],
                    printed_page, page_png,
                    "\n\n".join(english_paras), content, film_path)
        state["printed_page"] = printed_page + 1
        state["pdf_page"] = pdf_page + 1
        save_state(state)
        log(f"state advanced: next lesson = printed page {printed_page + 1}")
        return 0
    except Fail as e:
        print(f"[guyton-agent] FAILED (fail-closed, nothing sent): {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
