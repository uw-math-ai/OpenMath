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


def find_proof_separator(lines: list[str], start: int) -> tuple[int, int] | None:
    """Find where the proof body begins for a proof-bearing declaration.

    Walks characters starting at lines[start], tracking bracket depth so
    that Lean 4 named-argument syntax (e.g. `R := ℝ` inside parens) and
    default-value syntax (e.g. `(x : Nat := 5)`) are NOT mistaken for the
    proof separator. Skips content inside `--` line comments and `/- … -/`
    block comments.

    Returns (line_idx, col_idx) of the matched separator, or None if not
    found. The separator is one of:
      - `:= by`  (top-level proof start)
      - `:=`     (top-level term-level body — for `def`s this is the body,
                  but for theorems/lemmas/corollaries it's the proof)
      - `where`  (trailing word-bounded `where` at depth 0)
    """
    paren = bracket = brace = 0
    block_comment_depth = 0

    for line_idx in range(start, len(lines)):
        line = lines[line_idx]
        i = 0
        n = len(line)
        while i < n:
            # Inside block comment — only look for `-/`
            if block_comment_depth > 0:
                if i + 1 < n and line[i] == '-' and line[i + 1] == '/':
                    block_comment_depth -= 1
                    i += 2
                    continue
                # Block comments can nest in Lean 4
                if i + 1 < n and line[i] == '/' and line[i + 1] == '-':
                    block_comment_depth += 1
                    i += 2
                    continue
                i += 1
                continue

            # Line comment — skip rest of line
            if i + 1 < n and line[i] == '-' and line[i + 1] == '-':
                break
            # Block comment open
            if i + 1 < n and line[i] == '/' and line[i + 1] == '-':
                block_comment_depth += 1
                i += 2
                continue

            ch = line[i]
            if ch == '(':
                paren += 1
            elif ch == ')':
                paren = max(0, paren - 1)
            elif ch == '[':
                bracket += 1
            elif ch == ']':
                bracket = max(0, bracket - 1)
            elif ch == '{':
                brace += 1
            elif ch == '}':
                brace = max(0, brace - 1)
            elif ch == ':' and i + 1 < n and line[i + 1] == '=':
                if paren == 0 and bracket == 0 and brace == 0:
                    return (line_idx, i)
                i += 2
                continue
            elif (
                ch == 'w'
                and line[i:i + 5] == 'where'
                and (i == 0 or not (line[i - 1].isalnum() or line[i - 1] == '_'))
                and (i + 5 == n or not (line[i + 5].isalnum() or line[i + 5] == '_'))
                and paren == 0 and bracket == 0 and brace == 0
                and line[i + 5:].strip() == ''
            ):
                return (line_idx, i)
            i += 1
    return None

# Lines that start a new top-level declaration. Used to find the end
# of a structure / class / inductive body.
TOP_LEVEL_RE = re.compile(
    r"^(noncomputable\s+|protected\s+|private\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class|instance|inductive|"
    r"namespace|end\b|section\b|opaque|axiom|example)\b"
)

# Declaration kinds whose body IS the proof — truncate at `:=` / `where`.
# Everything else has CONTENT in the body (predicate definitions, structure
# fields, inductive constructors, instance witnesses) — keep the body and
# stop only at the next top-level declaration.
PROOF_BEARING_KINDS = {"theorem", "lemma", "corollary"}


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
    if kind in PROOF_BEARING_KINDS:
        # theorem/lemma/corollary: body is the proof, drop it.
        sep = find_proof_separator(lines, start)
        if sep is None:
            # No proof separator found — include everything from `start`
            # to the next top-level declaration. Safer than dropping the
            # extraction entirely.
            collected.append(lines[start])
            for line in lines[start + 1:]:
                if TOP_LEVEL_RE.match(line):
                    break
                collected.append(line)
        else:
            sep_line, sep_col = sep
            for idx in range(start, sep_line):
                collected.append(lines[idx])
            collected.append(lines[sep_line][:sep_col].rstrip())
    else:
        # def / abbrev / structure / class / instance / inductive:
        # body IS the content. Keep until the next top-level declaration.
        collected.append(lines[start])
        for line in lines[start + 1:]:
            if TOP_LEVEL_RE.match(line):
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
