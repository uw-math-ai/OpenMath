"""Phase 1a: Extract text from PDF and split into per-chapter files.

Uses pdftotext (Poppler) to extract the full text, then splits it into
per-chapter files (ch01.txt through ch05.txt) by detecting chapter boundaries.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

from pipeline.config import (
    PDF_PATH,
    PDFTOTEXT,
    RAW_TEXT_DIR,
    CHAPTERS,
    RUNNING_HEADERS,
)


# ── Ligature normalization ─────────────────────────────────────────────

def normalize_ligatures(text: str) -> str:
    """Replace PDF ligature characters with their ASCII equivalents."""
    return (
        text
        .replace("\ufb00", "ff")
        .replace("\ufb01", "fi")
        .replace("\ufb02", "fl")
        .replace("\ufb03", "ffi")
        .replace("\ufb04", "ffl")
    )


# ── Running header detection ───────────────────────────────────────────

def is_running_header(line: str) -> bool:
    """Check if a line is a running page header to be filtered."""
    stripped = line.strip()
    if not stripped:
        return False
    # Direct match against known headers
    if stripped in RUNNING_HEADERS:
        return True
    # Page-number + header pattern: "52    NUMERICAL DIFFERENTIAL EQUATION METHODS"
    m = re.match(r"^(\d{1,4})\s{2,}(.+)$", stripped)
    if m:
        header_text = m.group(2).strip()
        if header_text in RUNNING_HEADERS:
            return True
    # Reverse pattern: "DIFFERENTIAL AND DIFFERENCE EQUATIONS        7"
    m = re.match(r"^(.+?)\s{2,}(\d{1,4})$", stripped)
    if m:
        header_text = m.group(1).strip()
        if header_text in RUNNING_HEADERS:
            return True
    return False


# ── Text extraction ────────────────────────────────────────────────────

def extract_full_text() -> str:
    """Run pdftotext and return the full text."""
    result = subprocess.run(
        [PDFTOTEXT, "-layout", str(PDF_PATH), "-"],
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout


def find_chapter_boundaries(lines: list[str]) -> dict[int, int]:
    """Find the starting line index for each chapter (1-5).

    Looks for "Chapter N" on its own line (possibly with leading whitespace),
    where N is 1-5.

    Returns {chapter_number: line_index}.
    """
    boundaries: dict[int, int] = {}
    chapter_re = re.compile(r"^Chapter\s+(\d)\s*$")
    for i, line in enumerate(lines):
        m = chapter_re.match(line.strip())
        if m:
            ch = int(m.group(1))
            if 1 <= ch <= 5 and ch not in boundaries:
                boundaries[ch] = i
    return boundaries


def find_references_start(lines: list[str]) -> int | None:
    """Find the line index where 'References' section begins."""
    # Look for "References" on its own line after chapter 5
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "References":
            return i
    return None


def split_into_chapters(lines: list[str]) -> dict[int, list[str]]:
    """Split the full text into per-chapter line lists.

    Returns {chapter_number: [lines]}.
    """
    boundaries = find_chapter_boundaries(lines)
    refs_start = find_references_start(lines)

    if len(boundaries) < 5:
        print(f"  WARNING: Only found {len(boundaries)} chapter boundaries: {sorted(boundaries.keys())}")

    chapters: dict[int, list[str]] = {}
    sorted_chs = sorted(boundaries.keys())

    for idx, ch in enumerate(sorted_chs):
        start = boundaries[ch]
        if idx + 1 < len(sorted_chs):
            end = boundaries[sorted_chs[idx + 1]]
        elif refs_start is not None:
            end = refs_start
        else:
            end = len(lines)
        chapters[ch] = lines[start:end]

    return chapters


# ── Main driver ────────────────────────────────────────────────────────

def main() -> None:
    print("Phase 1a: Extracting text from PDF ...")

    # Extract full text
    raw_text = extract_full_text()
    text = normalize_ligatures(raw_text)
    lines = text.split("\n")
    print(f"  Total lines: {len(lines)}")

    # Save full text
    RAW_TEXT_DIR.mkdir(parents=True, exist_ok=True)
    full_text_path = RAW_TEXT_DIR / "full_text.txt"
    full_text_path.write_text(text, encoding="utf-8")
    print(f"  Wrote {full_text_path}")

    # Split into chapters
    chapters = split_into_chapters(lines)

    for ch in sorted(chapters.keys()):
        ch_lines = chapters[ch]
        filename = f"ch{ch:02d}.txt"
        filepath = RAW_TEXT_DIR / filename
        filepath.write_text("\n".join(ch_lines), encoding="utf-8")
        print(f"  {filename}: {len(ch_lines)} lines")

    print(f"\nPhase 1a complete: {len(chapters)} chapter files written")


if __name__ == "__main__":
    main()
