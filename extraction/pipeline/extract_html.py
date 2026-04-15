"""Phase 1b: Extract HTML formatting from PDF for bold/italic detection.

Uses pdftohtml (Poppler) to extract HTML with <b> and <i> tags, then
parses bold declarations (theorem/definition/lemma/corollary headers)
and italic concept introductions.
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

from pipeline.config import (
    PDF_PATH,
    PDFTOHTML,
    RAW_TEXT_DIR,
    CHAPTERS,
)
from pipeline.extract_text import normalize_ligatures


# ── HTML extraction ────────────────────────────────────────────────────

def extract_html() -> str:
    """Run pdftohtml and return the full HTML string."""
    result = subprocess.run(
        [PDFTOHTML, "-stdout", "-i", "-noframes", str(PDF_PATH)],
        capture_output=True,
        text=True,
        check=True,
        timeout=120,
    )
    return result.stdout


# ── Bold declaration extraction ────────────────────────────────────────

# Patterns for bold formal statement headers
BOLD_THEOREM_RE = re.compile(
    r"<b>Theorem\s*(?:&#160;)*\s*(\d{3}[A-Z])\s*(?:&#160;)*\s*</b>"
)
BOLD_DEFINITION_RE = re.compile(
    r"<b>De(?:fi|ﬁ)nition\s*(?:&#160;)*\s*(\d{3}[A-Z])\s*(?:&#160;)*\s*</b>"
)
BOLD_LEMMA_RE = re.compile(
    r"<b>Lemma\s*(?:&#160;)*\s*(\d{3}[A-Z])\s*(?:&#160;)*\s*</b>"
)
BOLD_COROLLARY_RE = re.compile(
    r"<b>Corollary\s*(?:&#160;)*\s*(?:(\d{3}[A-Z]))?\s*(?:&#160;)*\s*</b>"
)
BOLD_PROOF_RE = re.compile(
    r"<b>Proof\.?\s*(?:&#160;)*\s*</b>"
)


def extract_bold_declarations(html: str) -> list[dict]:
    """Extract all bold formal statement declarations from HTML.

    Returns a list of dicts with keys: kind, number, page (approximate).
    """
    declarations = []
    # Track approximate page number via <a name=N> tags
    current_page = 0
    page_re = re.compile(r'<a name=(\d+)>')

    for line in html.split("\n"):
        # Update page tracking
        page_matches = page_re.findall(line)
        if page_matches:
            current_page = int(page_matches[-1])

        # Check for each type of declaration
        for m in BOLD_THEOREM_RE.finditer(line):
            declarations.append({
                "kind": "theorem",
                "number": m.group(1),
                "page": current_page,
            })

        for m in BOLD_DEFINITION_RE.finditer(line):
            declarations.append({
                "kind": "definition",
                "number": m.group(1),
                "page": current_page,
            })

        for m in BOLD_LEMMA_RE.finditer(line):
            declarations.append({
                "kind": "lemma",
                "number": m.group(1),
                "page": current_page,
            })

        for m in BOLD_COROLLARY_RE.finditer(line):
            number = m.group(1) or ""
            declarations.append({
                "kind": "corollary",
                "number": number,
                "page": current_page,
            })

    return declarations


# ── Statement body extraction from italic tags ────────────────────────

def extract_statement_bodies(html: str, declarations: list[dict]) -> list[dict]:
    """For each declaration, extract the italic statement body text and its page range.

    In Butcher's textbook, the statement body (after the bold header)
    is typeset in italics. The body ends when italic formatting stops
    (at the Proof or next statement).

    Returns the declarations list enriched with 'body_text' and 'body_end_page'.
    """
    page_re = re.compile(r'<a name=(\d+)>')

    for decl in declarations:
        kind = decl["kind"]
        number = decl.get("number", "")
        if not number:
            continue

        # Find this declaration in HTML
        # Pattern: <b>Theorem 110C </b><i>...body...</i>
        kind_label = {
            "theorem": "Theorem",
            "definition": "De(?:fi|ﬁ)nition",
            "lemma": "Lemma",
            "corollary": "Corollary",
        }.get(kind, kind.title())

        header_re = re.compile(
            r"<b>" + kind_label + r"\s*(?:&#160;)*\s*" + re.escape(number)
            + r"\s*(?:&#160;)*\s*</b>"
        )
        m = header_re.search(html)
        if not m:
            continue

        # From the end of </b>, find all italic text until <b>Proof or next <b>Theorem/etc
        start_pos = m.end()
        # Find the next bold marker (Proof or next declaration)
        next_bold = re.search(r"<b>", html[start_pos:])
        if next_bold:
            end_pos = start_pos + next_bold.start()
        else:
            end_pos = min(start_pos + 5000, len(html))

        region = html[start_pos:end_pos]

        # Extract all italic text from this region
        italic_parts = re.findall(r"<i>([^<]*)</i>", region)
        body_text = " ".join(italic_parts)
        body_text = body_text.replace("&#160;", " ")
        body_text = re.sub(r"\s+", " ", body_text).strip()

        # Find the page where the body ends
        pages_in_region = page_re.findall(region)
        body_end_page = int(pages_in_region[-1]) if pages_in_region else decl["page"]

        decl["body_text"] = body_text[:500]  # truncate for storage
        decl["body_end_page"] = body_end_page

    return declarations


# ── Italic term extraction ─────────────────────────────────────────────

ITALIC_RE = re.compile(r"<i>([^<]+)</i>")

# Definition-introducing phrases (may appear before <i> tags)
DEFN_INTRO_RE = re.compile(
    r"(?:is\s+(?:called|said\s+to\s+be|termed)|"
    r"(?:we\s+(?:say|define))|"
    r"known\s+as)"
    r"(?:\s+(?:the|a|an))?\s*(?:&#160;)*\s*"
    r"(?:<br/>\s*)?<i>",
    re.IGNORECASE,
)


def extract_italic_terms(html: str) -> list[dict]:
    """Extract italic terms that appear near definition-introducing phrases.

    Returns a list of dicts with keys: term, page, context.
    """
    terms = []
    current_page = 0
    page_re = re.compile(r'<a name=(\d+)>')

    for line in html.split("\n"):
        page_matches = page_re.findall(line)
        if page_matches:
            current_page = int(page_matches[-1])

        # Find definition-introducing phrases followed by italic text
        for m in DEFN_INTRO_RE.finditer(line):
            # Extract the italic term after the phrase
            after = line[m.end():]
            # Remove the <i> tag that was already part of the match
            # Actually, let's find the italic term right at the match point
            rest = line[m.start():]
            italic_match = re.search(r"<i>([^<]+)</i>", rest)
            if italic_match:
                term = italic_match.group(1).replace("&#160;", " ").strip()
                # Clean up the term
                term = normalize_ligatures(term)
                term = re.sub(r"\s+", " ", term).strip(" .,;:'\"")
                if len(term) > 2 and len(term) < 80:
                    terms.append({
                        "term": term,
                        "page": current_page,
                    })

    return terms


# ── Main driver ────────────────────────────────────────────────────────

def main() -> None:
    print("Phase 1b: Extracting HTML formatting ...")

    html = extract_html()

    # Save raw HTML for reference
    html_path = RAW_TEXT_DIR / "html_full.html"
    html_path.write_text(html, encoding="utf-8")
    print(f"  Wrote {html_path} ({len(html)} chars)")

    # Extract bold declarations
    declarations = extract_bold_declarations(html)
    print(f"  Found {len(declarations)} bold declarations:")
    kind_counts = {}
    for d in declarations:
        kind_counts[d["kind"]] = kind_counts.get(d["kind"], 0) + 1
    for k, v in sorted(kind_counts.items()):
        print(f"    {k}: {v}")

    # Extract statement bodies from italic tags
    declarations = extract_statement_bodies(html, declarations)
    with_body = sum(1 for d in declarations if d.get("body_text"))
    print(f"  Statement bodies extracted: {with_body}/{len(declarations)}")

    # Extract italic terms
    italic_terms = extract_italic_terms(html)
    print(f"  Found {len(italic_terms)} italic concept terms")

    # Save formatting data
    formatting_data = {
        "bold_declarations": declarations,
        "italic_terms": italic_terms,
    }
    fmt_path = RAW_TEXT_DIR / "formatting.json"
    fmt_path.write_text(
        json.dumps(formatting_data, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"  Wrote {fmt_path}")


if __name__ == "__main__":
    main()
