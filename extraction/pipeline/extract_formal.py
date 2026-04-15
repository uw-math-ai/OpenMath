"""Phase 2: Extract formal mathematical statements from per-chapter text files.

Reads raw_text/ch01.txt .. ch05.txt produced by Phase 1, and writes
raw_text/formal_statements.json containing every Theorem, Definition,
Lemma, Corollary, and Proof found in the textbook.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, asdict, field
from pathlib import Path

from pipeline.config import (
    RAW_TEXT_DIR,
    CHAPTERS,
    THEOREM_DECL_RE,
    DEFINITION_DECL_RE,
    LEMMA_DECL_RE,
    COROLLARY_DECL_RE,
    PROOF_DECL_RE,
    SECTION_HEADER_RE,
    SUBSECTION_HEADER_RE,
    SUBSECTION_BARE_RE,
    EXERCISES_RE,
    chapter_from_subsection,
)

# ── Running header detection ───────────────────────────────────────────
# Running headers have the form:
#   "164   NUMERICAL METHODS FOR ORDINARY DIFFERENTIAL EQUATIONS"
#   "DIFFERENTIAL AND DIFFERENCE EQUATIONS    49"
# These must be filtered so they don't break proof extraction.

_HEADER_KEYWORDS = [
    "NUMERICAL METHODS FOR ORDINARY DIFFERENTIAL EQUATIONS",
    "DIFFERENTIAL AND DIFFERENCE EQUATIONS",
    "NUMERICAL DIFFERENTIAL EQUATION METHODS",
    "GENERAL LINEAR METHODS",
    "LINEAR MULTISTEP METHODS",
    # Runge-Kutta with various dash types (en-dash, hyphen, em-dash)
    "RUNGE\u2013KUTTA METHODS",   # en-dash
    "RUNGE-KUTTA METHODS",         # hyphen
    "RUNGE\u2014KUTTA METHODS",   # em-dash
]

# Build valid subsection numbers from chapter metadata
_VALID_SUBSECTIONS: set[str] = set()
for _ch, _info in CHAPTERS.items():
    for _sec in _info["sections"]:
        # Each section NN has subsections NN0-NN9 (approximately)
        for _sub_digit in range(10):
            _VALID_SUBSECTIONS.add(str(_sec * 10 + _sub_digit))


_RUNNING_HEADER_RE = re.compile(
    r"^(\d{1,3})\s{3,}(.+)$"  # "164   CHAPTER TITLE"
    r"|"
    r"^(.+?)\s{3,}(\d{1,3})$"  # "CHAPTER TITLE    164"
)

def _is_running_header(line: str) -> bool:
    """Detect running page headers that appear in pdftotext output.

    Running headers have the form:
      "164   NUMERICAL METHODS FOR ORDINARY DIFFERENTIAL EQUATIONS"
      "DIFFERENTIAL AND DIFFERENCE EQUATIONS                   49"
    They are distinguished from content by having a page number on one end
    and a known chapter title (or close match) as the main content.
    """
    stripped = line.strip()
    if not stripped:
        return False
    m = _RUNNING_HEADER_RE.match(stripped)
    if not m:
        return False
    # Extract the title part (whichever group matched)
    if m.group(1):  # "NNN   TITLE" pattern
        title_part = m.group(2).strip()
    else:           # "TITLE   NNN" pattern
        title_part = m.group(3).strip()
    # Check if the title part matches a known header keyword
    title_upper = title_part.upper()
    for keyword in _HEADER_KEYWORDS:
        if keyword.upper() in title_upper or title_upper in keyword.upper():
            return True
    return False


# ── Data model ─────────────────────────────────────────────────────────

@dataclass
class FormalStatement:
    kind: str           # "theorem", "definition", "lemma", "corollary", "proof"
    number: str         # "101A", "212A", "" for unnumbered
    chapter: int        # 1-5
    section: str        # "10", "21", etc. (2-digit section)
    subsection: str     # "100", "213", etc. (3-digit subsection)
    text: str           # Full statement text
    line_start: int     # Line number in chapter file (1-based)
    line_end: int       # Line number in chapter file (1-based)
    proof_text: str = ""  # Full proof text (merged from associated proof)
    page: int = 0       # Approximate page number from HTML
    introduces: list = field(default_factory=list)  # Concept names introduced


def _extract_introduced_concepts(text: str) -> list[str]:
    """Extract concept names introduced in a statement.

    Butcher introduces concepts in single quotes: 'Lipschitz condition',
    'A-stable', 'elementary differential', etc.
    """
    concepts = []
    # Match both straight quotes and Unicode curly quotes
    for m in re.finditer(r"['\u2018]([^'\u2019\n]+)['\u2019]", text):
        term = m.group(1).strip()
        term = re.sub(r"\s+", " ", term)  # clean line-break artifacts
        if 2 < len(term) < 60:
            concepts.append(term)
    return concepts


# ── Helpers ────────────────────────────────────────────────────────────

def is_formal_header(line: str) -> bool:
    """Check if a line starts a new formal statement."""
    stripped = line.strip()
    if THEOREM_DECL_RE.match(stripped):
        return True
    if DEFINITION_DECL_RE.match(stripped):
        return True
    if LEMMA_DECL_RE.match(stripped):
        return True
    if COROLLARY_DECL_RE.match(stripped):
        return True
    if PROOF_DECL_RE.match(stripped):
        return True
    return False


def is_structural_boundary(line: str, chapter: int = 0) -> bool:
    """Check if a line is a structural boundary (section/subsection header, exercises).

    Validates that matched numbers are plausible for the given chapter,
    to avoid false positives from running headers (e.g., page numbers).
    """
    stripped = line.strip()
    if not stripped:
        return False
    # Skip running headers — they look like subsection headers but aren't
    if _is_running_header(stripped):
        return False
    # Section header: "NN   Title"
    m = SECTION_HEADER_RE.match(stripped)
    if m:
        sec_num = int(m.group(1))
        # Validate: section numbers are 10-55 and match current chapter
        if chapter > 0:
            if sec_num // 10 == chapter:
                return True
        elif 10 <= sec_num <= 55:
            return True
    # Subsection header: "NNN   Title"
    m = SUBSECTION_HEADER_RE.match(stripped)
    if m:
        subsec_num = m.group(1)
        if subsec_num in _VALID_SUBSECTIONS:
            if chapter == 0 or chapter_from_subsection(int(subsec_num)) == chapter:
                return True
    # Bare subsection number: "NNN" on its own line
    m = SUBSECTION_BARE_RE.match(stripped)
    if m:
        subsec_num = m.group(1)
        if subsec_num in _VALID_SUBSECTIONS:
            if chapter == 0 or chapter_from_subsection(int(subsec_num)) == chapter:
                return True
    # Exercises marker
    if EXERCISES_RE.match(stripped):
        return True
    return False


def _is_terminator(line: str, chapter: int = 0) -> bool:
    """Return True if *line* should terminate a statement or proof block."""
    stripped = line.strip()
    if not stripped:
        return False
    if _is_running_header(stripped):
        return False
    if is_formal_header(stripped):
        return True
    if is_structural_boundary(stripped, chapter):
        return True
    return False


# QED box character — pdftotext renders □ as \x01 (ASCII SOH)
QED_CHAR = "\x01"


def _has_qed(line: str) -> bool:
    """Check if a line contains a QED box marker."""
    return QED_CHAR in line


def _strip_qed(line: str) -> str:
    """Remove QED box marker from a line."""
    return line.replace(QED_CHAR, "").rstrip()


def _clean_collected(lines: list[str]) -> str:
    """Join collected lines, remove running headers and QED markers."""
    cleaned = []
    for line in lines:
        if _is_running_header(line.strip()):
            continue
        cleaned.append(_strip_qed(line))
    return "\n".join(cleaned).strip()


def _load_bold_declarations() -> set[tuple[str, str]]:
    """Load bold declaration set from formatting.json.

    Returns a set of (kind, number) tuples, e.g. {("theorem", "101A"), ("lemma", "310B")}.
    """
    fmt_path = RAW_TEXT_DIR / "formatting.json"
    if not fmt_path.exists():
        return set()
    with open(fmt_path, encoding="utf-8") as f:
        data = json.load(f)
    return {
        (d["kind"], d["number"])
        for d in data.get("bold_declarations", [])
        if d.get("number")  # skip unnumbered corollaries
    }


def _load_page_map() -> dict[tuple[str, str], int]:
    """Load page numbers for declarations from formatting.json.

    Returns {(kind, number): page}.
    """
    fmt_path = RAW_TEXT_DIR / "formatting.json"
    if not fmt_path.exists():
        return {}
    with open(fmt_path, encoding="utf-8") as f:
        data = json.load(f)
    return {
        (d["kind"], d["number"]): d.get("page", 0)
        for d in data.get("bold_declarations", [])
        if d.get("number")
    }


# ── Per-chapter extraction ─────────────────────────────────────────────

def _extract_from_chapter(
    chapter: int,
    lines: list[str],
    bold_decls: set[tuple[str, str]],
    page_map: dict[tuple[str, str], int],
) -> list[FormalStatement]:
    """Scan *lines* from one chapter and return all formal statements found."""
    statements: list[FormalStatement] = []
    current_section: str = ""
    current_subsection: str = ""

    i = 0
    n = len(lines)

    while i < n:
        line = lines[i]
        stripped = line.strip()

        # ── Skip running headers ────────────────────────────────
        if _is_running_header(stripped):
            i += 1
            continue

        # ── Track current section/subsection ─────────────────────
        m_sec = SECTION_HEADER_RE.match(stripped)
        if m_sec and not _is_running_header(stripped):
            sec_num = m_sec.group(1)
            sec_int = int(sec_num)
            if sec_int // 10 == chapter:
                current_section = sec_num

        m_subsec = SUBSECTION_HEADER_RE.match(stripped)
        if not m_subsec:
            m_subsec = SUBSECTION_BARE_RE.match(stripped)
        if m_subsec and not _is_running_header(stripped):
            subsec_num = m_subsec.group(1)
            if subsec_num in _VALID_SUBSECTIONS and chapter_from_subsection(int(subsec_num)) == chapter:
                current_subsection = subsec_num

        # ── Try each formal statement type ───────────────────────

        # Theorem
        m_thm = THEOREM_DECL_RE.match(stripped)
        if m_thm:
            thm_number = m_thm.group(1)
            if ("theorem", thm_number) in bold_decls:
                bold_decls.discard(("theorem", thm_number))
                line_start = i + 1
                collected = [stripped]
                j = i + 1
                while j < n and not _is_terminator(lines[j], chapter):
                    collected.append(lines[j].rstrip())
                    j += 1
                statements.append(FormalStatement(
                    kind="theorem",
                    number=thm_number,
                    chapter=chapter,
                    section=current_section,
                    subsection=current_subsection,
                    text=_clean_collected(collected),
                    line_start=line_start,
                    line_end=j,
                    page=page_map.get(("theorem", thm_number), 0),
                ))
                i = j
                continue
            else:
                i += 1
                continue

        # Definition
        m_def = DEFINITION_DECL_RE.match(stripped)
        if m_def:
            def_number = m_def.group(1)
            if ("definition", def_number) in bold_decls:
                bold_decls.discard(("definition", def_number))
                line_start = i + 1
                collected = [stripped]
                j = i + 1
                while j < n and not _is_terminator(lines[j], chapter):
                    collected.append(lines[j].rstrip())
                    j += 1
                statements.append(FormalStatement(
                    kind="definition",
                    number=def_number,
                    chapter=chapter,
                    section=current_section,
                    subsection=current_subsection,
                    text=_clean_collected(collected),
                    line_start=line_start,
                    line_end=j,
                    page=page_map.get(("definition", def_number), 0),
                ))
                i = j
                continue
            else:
                i += 1
                continue

        # Lemma
        m_lem = LEMMA_DECL_RE.match(stripped)
        if m_lem:
            lem_number = m_lem.group(1)
            if ("lemma", lem_number) in bold_decls:
                bold_decls.discard(("lemma", lem_number))
                line_start = i + 1
                collected = [stripped]
                j = i + 1
                while j < n and not _is_terminator(lines[j], chapter):
                    collected.append(lines[j].rstrip())
                    j += 1
                statements.append(FormalStatement(
                    kind="lemma",
                    number=lem_number,
                    chapter=chapter,
                    section=current_section,
                    subsection=current_subsection,
                    text=_clean_collected(collected),
                    line_start=line_start,
                    line_end=j,
                    page=page_map.get(("lemma", lem_number), 0),
                ))
                i = j
                continue
            else:
                i += 1
                continue

        # Corollary
        m_cor = COROLLARY_DECL_RE.match(stripped)
        if m_cor:
            cor_number = m_cor.group(1) or ""
            # For unnumbered corollaries, assign ID based on preceding statement
            if not cor_number:
                for prev_stmt in reversed(statements):
                    if prev_stmt.kind in ("theorem", "lemma"):
                        cor_number = f"cor_after_{prev_stmt.number}"
                        break
            line_start = i + 1
            collected = [stripped]
            j = i + 1
            while j < n and not _is_terminator(lines[j], chapter):
                collected.append(lines[j].rstrip())
                j += 1
            statements.append(FormalStatement(
                kind="corollary",
                number=cor_number,
                chapter=chapter,
                section=current_section,
                subsection=current_subsection,
                text=_clean_collected(collected),
                line_start=line_start,
                line_end=j,
                page=page_map.get(("corollary", cor_number), 0),
            ))
            i = j
            continue

        # Proof
        m_prf = PROOF_DECL_RE.match(stripped)
        if m_prf:
            line_start = i + 1
            collected = [stripped]
            j = i + 1
            while j < n and not _is_terminator(lines[j], chapter):
                collected.append(lines[j].rstrip())
                # QED marker ends the proof
                if _has_qed(lines[j]):
                    j += 1
                    break
                j += 1
            # Determine proof number from preceding statement
            proof_number = ""
            for prev_stmt in reversed(statements):
                if prev_stmt.kind in ("theorem", "lemma", "corollary", "definition"):
                    proof_number = prev_stmt.number
                    break
            statements.append(FormalStatement(
                kind="proof",
                number=proof_number,
                chapter=chapter,
                section=current_section,
                subsection=current_subsection,
                text=_clean_collected(collected),
                line_start=line_start,
                line_end=j,
            ))
            i = j
            continue

        i += 1

    return statements


# ── Proof association ──────────────────────────────────────────────────

def _associate_proofs(statements: list[FormalStatement]) -> list[FormalStatement]:
    """Link each Proof to its preceding statement, merge text, remove proof entries."""
    for idx, stmt in enumerate(statements):
        if stmt.kind == "proof":
            for prev_idx in range(idx - 1, -1, -1):
                prev = statements[prev_idx]
                if prev.kind in ("theorem", "lemma", "corollary", "definition"):
                    prev.proof_text = stmt.text
                    break
    return [s for s in statements if s.kind != "proof"]


def _extract_all_concepts(statements: list[FormalStatement]) -> None:
    """Populate the 'introduces' field for all statements."""
    total = 0
    for stmt in statements:
        concepts = _extract_introduced_concepts(stmt.text)
        if concepts:
            stmt.introduces = concepts
            total += len(concepts)
    print(f"  Concept names extracted: {total} across {sum(1 for s in statements if s.introduces)} statements")


# ── Main driver ────────────────────────────────────────────────────────

def extract_all() -> list[FormalStatement]:
    """Extract formal statements from every chapter file."""
    all_statements: list[FormalStatement] = []
    bold_decls = _load_bold_declarations()
    page_map = _load_page_map()
    print(f"  Loaded {len(bold_decls)} bold declarations from formatting.json")

    for ch in range(1, 6):
        filename = f"ch{ch:02d}.txt"
        filepath = RAW_TEXT_DIR / filename
        if not filepath.exists():
            print(f"  [skip] {filepath} not found")
            continue
        text = filepath.read_text(encoding="utf-8")
        lines = text.split("\n")
        chapter_stmts = _extract_from_chapter(ch, lines, bold_decls, page_map)
        print(f"  ch{ch:02d}: {len(chapter_stmts)} statements")
        all_statements.extend(chapter_stmts)

    all_statements = _associate_proofs(all_statements)
    _extract_all_concepts(all_statements)
    return all_statements


def main() -> None:
    print("Phase 2: Extracting formal statements ...")
    statements = extract_all()

    out_path = RAW_TEXT_DIR / "formal_statements.json"
    payload = [asdict(s) for s in statements]
    out_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    # Summary
    kinds: dict[str, int] = {}
    chapters: dict[int, int] = {}
    for s in statements:
        kinds[s.kind] = kinds.get(s.kind, 0) + 1
        chapters[s.chapter] = chapters.get(s.chapter, 0) + 1

    print(f"\nWrote {len(statements)} statements to {out_path}")
    print("By kind:")
    for k, v in sorted(kinds.items()):
        print(f"  {k}: {v}")
    print("By chapter:")
    for ch, v in sorted(chapters.items()):
        print(f"  ch{ch}: {v}")

    # Count statements with proofs
    with_proof = sum(1 for s in statements if s.proof_text)
    print(f"\nStatements with proofs: {with_proof}")


if __name__ == "__main__":
    main()
