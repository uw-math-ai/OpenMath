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


def _extract_from_start(lines: list[str], start: int) -> str | None:
    """Given a list of source lines and the index of the declaration's first
    line, return the extracted statement. Proof-bearing kinds truncate at
    the proof separator; everything else keeps the body until the next
    top-level declaration."""
    if not (0 <= start < len(lines)):
        return None

    kind_m = re.match(
        r"^[ \t]*(?:noncomputable\s+|protected\s+|private\s+)*(\w+)\s+",
        lines[start],
    )
    kind = kind_m.group(1) if kind_m else ""

    collected: list[str] = []
    if kind in PROOF_BEARING_KINDS:
        sep = find_proof_separator(lines, start)
        if sep is None:
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
        collected.append(lines[start])
        for line in lines[start + 1:]:
            if TOP_LEVEL_RE.match(line):
                break
            collected.append(line)

    return "\n".join(collected).rstrip()


def extract_lean_statement(lean_file: Path, lean_symbol: str) -> str | None:
    """Return the declaration header (keyword through proof separator,
    exclusive). Tries progressively longer suffixes of lean_symbol so that
    both 'ShortName' and 'Ns.ShortName' spellings in the file are matched."""
    try:
        source = lean_file.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError, UnicodeDecodeError):
        return None

    lines = source.splitlines()

    parts = lean_symbol.split(".")
    meaningful = parts[3:] if len(parts) > 3 else parts
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
    return _extract_from_start(lines, start)


_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$")
_END_RE       = re.compile(r"^\s*end(?:\s+([\w.]+))?\s*$")
_DECL_RE      = re.compile(
    r"^[ \t]*(?:noncomputable\s+|protected\s+|private\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|instance|inductive)\s+"
    r"([\w.]+)\b"
)


def _index_declarations(lines: list[str]) -> dict[str, list[int]]:
    """Build {fully_qualified_name: [line_indices]} by walking the file
    and tracking `namespace ... end` blocks. A declaration `def X.Y` inside
    `namespace A.B` indexes as `A.B.X.Y`. Also indexes the bare short name
    as a fallback key."""
    out: dict[str, list[int]] = {}
    stack: list[str] = []
    for i, line in enumerate(lines):
        m = _NAMESPACE_RE.match(line)
        if m:
            for part in m.group(1).split("."):
                stack.append(part)
            continue
        m = _END_RE.match(line)
        if m:
            if m.group(1):
                for part in reversed(m.group(1).split(".")):
                    if stack and stack[-1] == part:
                        stack.pop()
            elif stack:
                stack.pop()
            continue
        m = _DECL_RE.match(line)
        if m:
            decl = m.group(1)
            decl_parts = decl.split(".")
            full = ".".join(stack + decl_parts)
            out.setdefault(full, []).append(i)
            # Also key by every shorter suffix so partial qualifiers match.
            for j in range(1, len(decl_parts) + 1 + len(stack)):
                suffix = ".".join((stack + decl_parts)[-j:])
                if suffix != full:
                    out.setdefault(suffix, []).append(i)
    return out


_KIND_WORDS = {
    "thm": ["Theorem", "Thm"],
    "def": ["Definition", "Def"],
    "lem": ["Lemma", "Lem"],
    "cor": ["Corollary", "Cor"],
}

# Which Lean keywords are acceptable when looking for an entity of a given
# kind. Note that Lean 4 has no `corollary` keyword — corollaries are
# normally written as `theorem` in Mathlib-style code.
_KIND_ACCEPT = {
    "thm": {"theorem", "lemma"},
    "def": {"def", "structure", "class", "abbrev", "instance", "inductive"},
    "lem": {"lemma", "theorem"},
    "cor": {"theorem", "lemma"},
}

_KIND_DECL_RE = re.compile(
    r"^[ \t]*(?:noncomputable\s+|protected\s+|private\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class|instance|inductive)\s+"
)


def _line_kind(line: str) -> str | None:
    m = _KIND_DECL_RE.match(line)
    return m.group(1) if m else None


def find_by_textbook_reference(
    lean_root: Path, entity_id: str
) -> tuple[Path, int] | None:
    """Locate the declaration that formalizes a textbook entity, using
    docstring/comment references like 'Theorem 355B' or '§355B'.

    Strategy:
      1. Collect candidates from every *.lean file: for each reference,
         look ahead up to 40 lines for the FIRST declaration.
      2. Prefer candidates whose Lean keyword matches the entity's kind
         (a `theorem`/`lemma` for `thm:XXX`; a `def`/`structure`/... for
         `def:XXX`). This avoids picking an auxiliary `def` that happens
         to follow a docstring about Theorem 355B.
      3. Among the preferred set, return the one with the smallest
         reference-to-declaration distance (tightest binding).
      4. Only if no kind-matching candidate exists, fall back to the
         closest any-kind candidate.
    """
    if ":" not in entity_id:
        return None
    kind, num = entity_id.split(":", 1)
    if not re.fullmatch(r"\d{3}[A-Z]", num):
        return None
    words = _KIND_WORDS.get(kind, [])
    alternation = "|".join(re.escape(w) for w in (words + ["§"])) or "§"
    ref_re = re.compile(
        rf"(?:{alternation})\s*{re.escape(num)}(?![0-9A-Za-z])",
        re.IGNORECASE,
    )

    accept_kinds = _KIND_ACCEPT.get(kind, set())
    kind_hits: list[tuple[int, Path, int]] = []
    any_hits:  list[tuple[int, Path, int]] = []

    for f in sorted(lean_root.rglob("*.lean")):
        try:
            lines = f.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError):
            continue
        for i, line in enumerate(lines):
            if not ref_re.search(line):
                continue
            for j in range(i, min(i + 40, len(lines))):
                decl_kind = _line_kind(lines[j])
                if not decl_kind:
                    continue
                distance = j - i
                if decl_kind in accept_kinds:
                    kind_hits.append((distance, f, j))
                else:
                    any_hits.append((distance, f, j))
                break  # only the first declaration following each reference

    pool = kind_hits if kind_hits else any_hits
    if not pool:
        return None
    pool.sort(key=lambda c: (c[0], str(c[1]), c[2]))
    _, f, j = pool[0]
    return (f, j)


def _camelcase(s: str) -> str:
    """Convert a phrase like 'Lipschitz condition in its second variable'
    into 'LipschitzConditionInItsSecondVariable'. Drops parenthesized
    qualifiers and punctuation."""
    s = re.sub(r"\([^)]*\)", "", s or "")
    s = re.sub(r"\[[^\]]*\]", "", s)
    parts = re.findall(r"[A-Za-z0-9]+", s)
    out: list[str] = []
    for p in parts:
        out.append(p if p[0].isupper() else p.capitalize())
    return "".join(out)


def _derive_candidates(
    entity_id: str, entity: dict, lean_symbol: str | None
) -> list[str]:
    """Return search names to try, in priority order: explicit lean_symbol
    first; then textbook-id-derived (`thm_110C`, `Thm110C`); then camelcased
    forms of `introduces` and `name`."""
    seen: set[str] = set()
    out: list[str] = []

    def add(c: str) -> None:
        if c and c not in seen:
            seen.add(c)
            out.append(c)

    if lean_symbol:
        for sym in lean_symbol.split(","):
            sym = sym.strip()
            if sym:
                add(sym)

    # Id-derived variants. Useful for projects that name decls after the
    # textbook section (e.g. `theorem thm_110C`).
    if ":" in entity_id:
        kind, num = entity_id.split(":", 1)
        add(f"{kind}_{num}")
        add(f"{kind.capitalize()}{num}")
        add(f"{kind.capitalize()}_{num}")
        add(f"{kind}{num}")

    # Camelcased introduces entries.
    for item in entity.get("introduces") or []:
        c = _camelcase(item)
        if c and len(c) >= 5:
            add(c)

    # Camelcased name as a last resort.
    c = _camelcase(entity.get("name") or "")
    if c and len(c) >= 5:
        add(c)

    return out


def find_in_tree(
    lean_root: Path, search_names: list[str]
) -> tuple[Path, str] | None:
    """Search all *.lean files under lean_root for a declaration matching
    any of `search_names` (or any of their suffixes). Pre-indexes every
    file once using namespace-aware tracking, then tries each candidate
    longest-first.

    Returns (actual_file_path, extracted_statement) on success, else None.
    """
    # Expand each search name into suffixes (longest first), de-duplicated
    # while preserving priority order.
    seen: set[str] = set()
    candidates: list[str] = []
    for name in search_names:
        parts = name.split(".")
        meaningful = parts[3:] if (len(parts) > 3 and parts[0] == "OpenMath") else parts
        if not meaningful:
            continue
        for i in range(len(meaningful)):
            cand = ".".join(meaningful[i:])
            if cand and cand not in seen:
                seen.add(cand)
                candidates.append(cand)

    # Pre-index every file under lean_root.
    file_data: list[tuple[Path, list[str], dict[str, list[int]]]] = []
    for f in sorted(lean_root.rglob("*.lean")):
        try:
            lines = f.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError):
            continue
        file_data.append((f, lines, _index_declarations(lines)))

    for candidate in candidates:
        for f, lines, idx in file_data:
            line_idxs = idx.get(candidate)
            if not line_idxs:
                continue
            stmt = _extract_from_start(lines, line_idxs[0])
            if stmt:
                return (f, stmt)
    return None


def extract_statements_for_entry(
    entity_id: str,
    entity: dict,
    lean_file_rel: str | None,
    lean_symbol: str | None,
    lean_root: Path | None = None,
) -> tuple[str | None, str | None, list[str]]:
    """Extract Lean statement(s) for an entity.

    Steps, in order:
      1. If lean_status.json has both `lean_file` and `lean_symbol`, try
         the explicit file first.
      2. Otherwise (or if (1) fails), derive a list of candidate names
         from the entity content — explicit lean_symbol, textbook-id
         forms (`thm_110C`, `Thm110C`), and camelcased introduces/name —
         and search the whole `lean_root` tree.

    Returns (joined_statement, actual_file_rel, notes). Notes describe
    any remapping or discovery for human review.
    """
    notes: list[str] = []
    results: list[str] = []
    actual_files: list[Path] = []

    symbols = (
        [s.strip() for s in lean_symbol.split(",")] if lean_symbol else [None]
    )

    for sym in symbols:
        stmt: str | None = None
        actual: Path | None = None

        # 1. Try the explicit file from lean_status.json.
        if sym and lean_file_rel:
            lean_file = ROOT / lean_file_rel
            if lean_file.exists():
                stmt = extract_lean_statement(lean_file, sym)
                if stmt:
                    actual = lean_file

        # 2. Textbook-reference search — look for a docstring like
        #    'Theorem 110C' / '§110C' pointing to a declaration.
        if stmt is None and lean_root is not None and lean_root.exists():
            ref_hit = find_by_textbook_reference(lean_root, entity_id)
            if ref_hit is not None:
                f, line_idx = ref_hit
                try:
                    f_lines = f.read_text(encoding="utf-8").splitlines()
                    s = _extract_from_start(f_lines, line_idx)
                    if s:
                        stmt, actual = s, f
                        rel = actual.relative_to(ROOT).as_posix()
                        if lean_file_rel and lean_file_rel != rel:
                            notes.append(
                                f"remapped via textbook-ref: expected {lean_file_rel}, found in {rel}"
                            )
                        elif not lean_file_rel:
                            notes.append(f"discovered via textbook-ref in {rel}")
                except (OSError, UnicodeDecodeError):
                    pass

        # 3. Tree-wide search with derived candidates.
        if stmt is None and lean_root is not None and lean_root.exists():
            candidates = _derive_candidates(entity_id, entity, sym)
            if candidates:
                found = find_in_tree(lean_root, candidates)
                if found is not None:
                    actual, stmt = found
                    rel = actual.relative_to(ROOT).as_posix()
                    if lean_file_rel and lean_file_rel != rel:
                        notes.append(
                            f"remapped: expected {lean_file_rel}, found in {rel}"
                        )
                    elif not lean_file_rel:
                        notes.append(f"discovered in {rel}")

        if stmt and stmt not in results:
            results.append(stmt)
            if actual is not None:
                actual_files.append(actual)

    joined = "\n\n".join(results) if results else None

    actual_rel: str | None = None
    if actual_files:
        first = actual_files[0].relative_to(ROOT).as_posix()
        actual_rel = first
        if any(p != actual_files[0] for p in actual_files[1:]):
            notes.append(f"multiple files used; reporting first: {first}")

    return joined, actual_rel, notes


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(
        description="Build theorem_mapping.json from formalization_data + Lean source"
    )
    parser.add_argument(
        "--lean-root", type=Path, default=ROOT / "OpenMath",
        help="Tree to search when lean_file from lean_status.json doesn't "
             "resolve (default: ./OpenMath)"
    )
    parser.add_argument(
        "--no-fallback", action="store_true",
        help="Disable tree-search fallback; only use lean_file from lean_status.json"
    )
    args = parser.parse_args()

    lean_root: Path | None = None if args.no_fallback else args.lean_root

    status_data: dict = json.loads(
        (FORMALIZATION_DATA / "lean_status.json").read_text()
    )

    mapping: dict = {}
    no_lean_found: list[str] = []
    missing_entity: list[str] = []
    remapped: list[tuple[str, list[str]]] = []
    discovered: list[tuple[str, list[str]]] = []

    # Iterate EVERY textbook entity, regardless of butcher's lean_status
    # value — on a different repo the status field is meaningless and we
    # want to give every entity a chance to be located.
    entity_dir = FORMALIZATION_DATA / "entities"
    entity_ids = sorted(
        p.stem.replace("_", ":", 1)
        for p in entity_dir.glob("*.json")
    )

    for entity_id in entity_ids:
        entry = status_data.get(entity_id, {})
        lean_symbol: str | None = entry.get("lean_symbol")
        lean_file_rel: str | None = entry.get("lean_file")

        entity_path = (
            FORMALIZATION_DATA / "entities" / f"{entity_id.replace(':', '_')}.json"
        )
        if not entity_path.exists():
            missing_entity.append(entity_id)
            continue
        entity: dict = json.loads(entity_path.read_text())

        # Extract verbatim Lean statement(s); record the file actually used.
        lean_statement, actual_file_rel, notes = extract_statements_for_entry(
            entity_id, entity, lean_file_rel, lean_symbol, lean_root=lean_root,
        )
        if lean_statement is None:
            no_lean_found.append(entity_id)
        if notes:
            if any(n.startswith("remapped") for n in notes):
                remapped.append((entity_id, notes))
            else:
                discovered.append((entity_id, notes))

        mapping[entity_id] = {
            # Identity
            "lean_symbol":     lean_symbol,
            "lean_file":       actual_file_rel or lean_file_rel,
            "lean_file_original": lean_file_rel if actual_file_rel and actual_file_rel != lean_file_rel else None,
            "status":          entry.get("status"),
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
    print(f"  Lean root searched as fallback: {lean_root}")
    if missing_entity:
        print(f"  Missing entity JSONs ({len(missing_entity)}): {missing_entity}")
    if no_lean_found:
        print(
            f"  No Lean statement found ({len(no_lean_found)}): {no_lean_found}"
        )
    if remapped:
        print(f"  Remapped via tree search ({len(remapped)}):")
        for eid, ns in remapped:
            for n in ns:
                print(f"    {eid}: {n}")
    if discovered:
        print(f"  Discovered (no original lean_file) ({len(discovered)}):")
        for eid, ns in discovered:
            for n in ns:
                print(f"    {eid}: {n}")


if __name__ == "__main__":
    main()
