"""
Generate theorem_mapping.json: maps each formalized entity to its natural-language
textbook statement and verbatim Lean declaration.
"""

import json
import re
from pathlib import Path

ROOT = Path(__file__).parent.parent
FORMALIZATION_DATA = ROOT / "extraction" / "formalization_data"
OUTPUT = ROOT / "extraction" / "theorem_mapping.json"

COMPLETED_STATUSES = {"formalized", "partial"}

# Separators that end the statement and start the proof/body.
# For non-structure declarations only — structures/classes use the
# `where` keyword as the start of their FIELDS, which are part of the
# statement, not the proof. See `extract_lean_statement`.
PROOF_SEP = re.compile(r":=\s*by\b|:=(?!\s*by)|\bwhere\s*$")

# Lines that start a new top-level declaration. Used to find the end
# of a structure / class / inductive body.
TOP_LEVEL_RE = re.compile(
    r"^(noncomputable\s+|protected\s+|private\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class|instance|inductive|"
    r"namespace|end\b|section\b|opaque|axiom|example)\b"
)

# Declaration kinds whose body IS part of the statement.
STRUCTURE_LIKE = {"structure", "class", "inductive"}


def _build_pattern(qualified_name: str) -> re.Pattern:
    """
    Build a regex that matches the start of a Lean declaration whose
    spelled-out name (after the keyword) ends with `qualified_name`.

    Examples of names that appear in files:
      - "IsConvergent"  (short)
      - "LinearMultistepMethod.IsConvergent"  (dotted)
    """
    escaped = re.escape(qualified_name)
    return re.compile(
        r"^[ \t]*(noncomputable\s+)?"
        r"(def|theorem|lemma|abbrev|structure|class|instance|nonrec def)\s+"
        + escaped
        + r"\b"
    )


def extract_lean_statement(lean_file: Path, lean_symbol: str) -> str | None:
    """
    Return the declaration header (keyword through proof separator, exclusive).

    Tries progressively longer suffixes of lean_symbol so that both
    'ShortName' and 'Ns.ShortName' spellings in the file are matched.
    """
    try:
        source = lean_file.read_text(encoding="utf-8")
    except FileNotFoundError:
        return None

    lines = source.splitlines()

    # Build candidate names to try: shortest suffix first, then longer ones.
    # lean_symbol = "OpenMath.Chapter4.Section404.LinearMultistepMethod.IsConvergent"
    # segments stripped of the fixed module prefix "OpenMath.ChapterN.SectionNNN."
    parts = lean_symbol.split(".")
    # Drop the first three fixed segments (OpenMath, ChapterN, SectionNNN)
    meaningful = parts[3:] if len(parts) > 3 else parts
    # Try from shortest to longest: ["IsConvergent", "LinearMultistepMethod.IsConvergent", ...]
    candidates = [".".join(meaningful[i:]) for i in range(len(meaningful) - 1, -1, -1)]

    start = None
    for candidate in candidates:
        pattern = _build_pattern(candidate)
        for i, line in enumerate(lines):
            if pattern.match(line):
                start = i
                break
        if start is not None:
            break

    if start is None:
        return None

    # Detect the declaration kind so we know whether `where` ends the
    # statement (def/theorem/etc.) or begins the body that we want to keep
    # (structure/class/inductive).
    kind_m = re.match(
        r"^[ \t]*(?:noncomputable\s+|protected\s+|private\s+)*(\w+)\s+",
        lines[start],
    )
    kind = kind_m.group(1) if kind_m else ""

    collected: list[str] = []
    if kind in STRUCTURE_LIKE:
        # Keep header AND body. Stop only at the next top-level declaration.
        collected.append(lines[start])
        for line in lines[start + 1:]:
            if TOP_LEVEL_RE.match(line):
                break
            collected.append(line)
    else:
        for line in lines[start:]:
            m = PROOF_SEP.search(line)
            if m:
                collected.append(line[: m.start()].rstrip())
                break
            collected.append(line)

    return "\n".join(collected).rstrip()


def extract_statements_for_entry(
    lean_file_rel: str | None, lean_symbol: str | None
) -> str | None:
    """
    Handle potentially comma-separated lean_symbols (partial entries split
    across multiple declarations). Returns all statements joined by a blank line.
    """
    if not lean_symbol or not lean_file_rel:
        return None

    lean_file = ROOT / lean_file_rel

    # Some "partial" entries store multiple symbols separated by ", "
    symbols = [s.strip() for s in lean_symbol.split(",")]
    results: list[str] = []
    for sym in symbols:
        stmt = extract_lean_statement(lean_file, sym)
        if stmt:
            results.append(stmt)

    return "\n\n".join(results) if results else None


def main() -> None:
    status_data: dict = json.loads(
        (FORMALIZATION_DATA / "lean_status.json").read_text()
    )

    mapping: dict = {}
    missing_lean: list[str] = []
    missing_entity: list[str] = []

    for entity_id, entry in status_data.items():
        if entry["status"] not in COMPLETED_STATUSES:
            continue

        lean_symbol: str | None = entry.get("lean_symbol")
        lean_file_rel: str | None = entry.get("lean_file")

        # Load entity JSON for natural-language content
        entity_path = (
            FORMALIZATION_DATA / "entities" / f"{entity_id.replace(':', '_')}.json"
        )
        if not entity_path.exists():
            missing_entity.append(entity_id)
            continue
        entity: dict = json.loads(entity_path.read_text())

        # Extract verbatim Lean statement(s)
        lean_statement = extract_statements_for_entry(lean_file_rel, lean_symbol)
        if lean_symbol and lean_file_rel and lean_statement is None:
            missing_lean.append(entity_id)

        mapping[entity_id] = {
            # Identity
            "lean_symbol":     lean_symbol,
            "lean_file":       lean_file_rel,
            "status":          entry["status"],
            "kind":            entity.get("kind"),
            "number":          entity.get("number"),
            "name":            entity.get("name"),
            # Location in textbook
            "chapter":         entity.get("chapter"),
            "section":         entity.get("section"),
            "subsection":      entity.get("subsection"),
            "subsection_title": entity.get("subsection_title"),
            "page":            entity.get("page"),
            # Textbook content
            "preamble":        entity.get("preamble"),
            "introduces":      entity.get("introduces"),
            "variables":       entity.get("variables"),
            "statement_text":  entity.get("statement_text"),
            "statement_latex": entity.get("statement_latex"),
            "proof_latex":     entity.get("proof_latex"),
            "context_latex":   entity.get("context_latex"),
            # Dependency graph
            "dependencies":    entity.get("dependencies"),
            "dependents":      entity.get("dependents"),
            # Lean
            "lean_statement":  lean_statement,
        }

    OUTPUT.write_text(json.dumps(mapping, indent=2, ensure_ascii=False) + "\n")

    print(f"Written {len(mapping)} entries to {OUTPUT.relative_to(ROOT)}")
    if missing_entity:
        print(f"  Missing entity JSONs ({len(missing_entity)}): {missing_entity}")
    if missing_lean:
        print(
            f"  Could not extract Lean statement ({len(missing_lean)}): {missing_lean}"
        )


if __name__ == "__main__":
    main()
