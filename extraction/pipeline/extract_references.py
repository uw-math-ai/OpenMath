"""Phase 4a: Extract cross-references between formal statements.

For each formal statement (theorem, definition, lemma, corollary),
finds all references to other formal statements, equations, sections,
and concept names within its text and proof text.

Three methods:
1. Regex matching for explicit "Theorem NNN[A-Z]" etc. references
2. Concept name matching from definition-introduced terms
3. Equation-to-statement linking via subsection proximity
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from pipeline.config import (
    RAW_TEXT_DIR,
    FORMAL_REF_RE,
    SECTION_REF_RE,
    EQUATION_REF_RE,
    section_from_subsection,
)
from pipeline.extract_text import normalize_ligatures


def _normalize_kind(kind_str: str) -> str:
    """Normalize kind string from regex match to standard form."""
    k = kind_str.lower()
    if "theorem" in k:
        return "theorem"
    if "defi" in k or "deﬁ" in k:
        return "definition"
    if "lemma" in k:
        return "lemma"
    if "corollary" in k:
        return "corollary"
    return k


def _make_id(kind: str, number: str) -> str:
    """Create a unique ID for a formal statement."""
    prefix = {
        "theorem": "thm",
        "definition": "def",
        "lemma": "lem",
        "corollary": "cor",
    }.get(kind, kind[:3])
    return f"{prefix}:{number}"


# ── Concept name extraction from definitions ───────────────────────────

# Plural forms for common nouns
_PLURAL_MAP = {
    "method": "methods",
    "condition": "conditions",
    "differential": "differentials",
    "weight": "weights",
    "constant": "constants",
    "tree": "trees",
    "equation": "equations",
}


def _generate_aliases(term: str) -> list[tuple[str, bool]]:
    """Generate variants for a concept name.

    Returns a list of (variant, is_full_name) tuples.
    is_full_name=True marks the original term (exact match);
    False marks derived aliases (substring/plural/dash-variant).

    Handles:
    - Dash normalization (en-dash, em-dash, `--`, hyphen)
    - pdftotext hyphen-space artifacts (P -reducible ↔ P-reducible)
    - Trailing qualifier strip (in its second variable, etc.)
    - Plural forms (method → methods)
    """
    aliases: list[tuple[str, bool]] = [(term, True)]

    def add(variant: str) -> None:
        variant = variant.strip()
        if variant and variant != term and (variant, False) not in aliases and (variant, True) not in aliases:
            aliases.append((variant, False))

    # A. Dash normalization
    for src in ["\u2013", "\u2014", "--", "-"]:
        if src in term:
            for dst in ["\u2013", "\u2014", "--", "-"]:
                if src != dst:
                    add(term.replace(src, dst))

    # B. pdftotext hyphen-space artifact for single-letter prefix
    # "P-reducible" ↔ "P -reducible"
    m = re.match(r"^([A-Z])-(.+)$", term)
    if m:
        add(f"{m.group(1)} -{m.group(2)}")
    m = re.match(r"^([A-Z])\s+-(.+)$", term)
    if m:
        add(f"{m.group(1)}-{m.group(2)}")

    # C. Trailing qualifier strip
    qualifiers = [
        r"\s+in\s+its\s+\w+\s+variable\b.*$",
        r"\s+with\s+respect\s+to\b.*$",
        r"\s+of\s+\w+\s+type\b.*$",
        r"\s+in\s+the\s+sense\s+of\b.*$",
        r"\s+at\s+\w+\b.*$",
        r"\s+principle$",
        r"\s+relative\s+to\b.*$",
    ]
    for pat in qualifiers:
        stripped = re.sub(pat, "", term, flags=re.IGNORECASE).strip()
        if stripped != term and len(stripped) > 3:
            add(stripped)

    # D. Plurals
    term_lower = term.lower()
    for sing, plur in _PLURAL_MAP.items():
        if term_lower.endswith(sing):
            idx = len(term) - len(sing)
            add(term[:idx] + plur)

    return aliases


def _extract_concept_names(statements: list[dict]) -> dict[str, list[tuple[str, int, bool]]]:
    """Extract concept names from the 'introduces' field of statements.

    Returns {concept_name_lower: [(defining_statement_id, chapter, is_full_name)]}.
    is_full_name=True means the term matches the exact `introduces` entry;
    False means it was generated as an alias.
    """
    # Minimal blocklist: only truly generic words that are NEVER introduced
    GENERIC_TERMS = {
        "the", "that", "this", "a", "an",
        "method", "methods", "problem", "condition",
        "function", "equation", "system", "variable",
        # def:530C introduces "order" but it's too polysemic
        "order",
    }

    concept_map: dict[str, list[tuple[str, int, bool]]] = {}

    for s in statements:
        sid = _make_id(s["kind"], s["number"])
        chapter = s["chapter"]

        # Primary: use the 'introduces' field
        introduces = s.get("introduces", [])
        if not introduces and s["kind"] == "definition":
            # Fallback: extract from text
            for m in re.finditer(r"['\u2018]([^'\u2019\n]+)['\u2019]", s["text"]):
                term = m.group(1).strip()
                term = re.sub(r"\s+", " ", term)
                if 2 < len(term) < 60:
                    introduces.append(term)

        for term in introduces:
            for alias, is_full in _generate_aliases(term):
                alias_lower = alias.lower().strip()
                if alias_lower in GENERIC_TERMS:
                    continue
                if len(alias_lower) < 4:
                    continue
                concept_map.setdefault(alias_lower, []).append((sid, chapter, is_full))

    # Deduplicate entries
    for term in concept_map:
        seen = set()
        deduped = []
        for entry in concept_map[term]:
            key = (entry[0], entry[1])
            if key not in seen:
                seen.add(key)
                deduped.append(entry)
        concept_map[term] = deduped

    return concept_map


def _pick_best_target(
    entries: list[tuple[str, int, bool]],
    src_chapter: int,
    source_id: str,
) -> str | None:
    """Pick the best target from candidate definitions by chapter proximity.

    Full-name matches take priority over alias matches.
    """
    # Filter out self
    candidates = [(sid, ch, is_full) for sid, ch, is_full in entries if sid != source_id]
    if not candidates:
        return None

    # Split full vs alias
    full_matches = [(sid, ch) for sid, ch, is_full in candidates if is_full]
    alias_matches = [(sid, ch) for sid, ch, is_full in candidates if not is_full]

    # Prefer full-name matches
    pool = full_matches if full_matches else alias_matches
    if not pool:
        return None

    # Chapter-proximity scoring
    best_id = None
    best_score = float("inf")
    for def_id, def_chapter in pool:
        if def_chapter == src_chapter:
            score = 0
        elif def_chapter < src_chapter:
            score = src_chapter - def_chapter
        else:
            score = (def_chapter - src_chapter) + 10  # penalty for forward ref
        if score < best_score:
            best_score = score
            best_id = def_id
    return best_id


def _find_concept_references(
    statement: dict,
    source_id: str,
    concept_map: dict[str, list[tuple[str, int, bool]]],
) -> list[dict]:
    """Find concept name references using longest-match-wins.

    Algorithm:
    1. Find all potential matches (every alias against combined text)
    2. Sort by length descending so specific forms win over generic
    3. Consume text positions — shorter matches can't overlap with already-consumed ranges
    4. For each accepted match, pick the best target (full-name first, then chapter-proximity)
    """
    combined = statement["text"]
    if statement.get("proof_text"):
        combined += "\n" + statement["proof_text"]
    combined_lower = combined.lower()
    src_chapter = statement["chapter"]

    # 1. Find all potential matches
    all_matches: list[tuple[int, int, str, list[tuple[str, int, bool]]]] = []
    for term, entries in concept_map.items():
        # Hyphen-aware word boundary: don't match inside "A-stable" for "stable"
        pattern = r"(?<![\w\-])" + re.escape(term) + r"(?![\w\-])"
        for m in re.finditer(pattern, combined_lower):
            all_matches.append((m.start(), m.end(), term, entries))

    # 2. Sort by length (longer first), then by start position
    all_matches.sort(key=lambda x: (-(x[1] - x[0]), x[0]))

    # 3. Consume positions — shorter matches can't overlap
    consumed: list[tuple[int, int]] = []
    accepted: list[tuple[int, int, str, list[tuple[str, int, bool]]]] = []
    for start, end, term, entries in all_matches:
        overlap = any(not (end <= cs or start >= ce) for cs, ce in consumed)
        if not overlap:
            accepted.append((start, end, term, entries))
            consumed.append((start, end))

    # 4. Build edges — dedupe targets per source
    edges = []
    seen_targets: set[str] = set()
    for _, _, term, entries in accepted:
        best_id = _pick_best_target(entries, src_chapter, source_id)
        if best_id and best_id not in seen_targets:
            edges.append({
                "source": source_id,
                "target": best_id,
                "edge_type": "uses_concept",
                "context": term,
            })
            seen_targets.add(best_id)

    return edges


# ── Equation-to-statement linking ──────────────────────────────────────

def _build_equation_owner_map(statements: list[dict]) -> dict[str, str]:
    """Map equation tags to their 'owning' statement.

    An equation (NNNx) is owned by the definition or theorem in the same
    subsection (NNN) that first introduces it. Definitions take priority
    over theorems since equations in definitions are typically definitional.

    Returns {eq_tag: statement_id}.
    """
    eq_owners: dict[str, str] = {}

    # First pass: definitions (higher priority)
    for s in statements:
        if s["kind"] != "definition":
            continue
        sid = _make_id(s["kind"], s["number"])
        subsec = s["number"][:3]  # e.g., "110" from "110A"
        text = s["text"]
        for m in EQUATION_REF_RE.finditer(text):
            tag = m.group(1)
            if tag[:3] == subsec and tag not in eq_owners:
                eq_owners[tag] = sid

    # Second pass: theorems and lemmas
    for s in statements:
        if s["kind"] not in ("theorem", "lemma"):
            continue
        sid = _make_id(s["kind"], s["number"])
        subsec = s["number"][:3]
        text = s["text"]
        for m in EQUATION_REF_RE.finditer(text):
            tag = m.group(1)
            if tag[:3] == subsec and tag not in eq_owners:
                eq_owners[tag] = sid

    return eq_owners


def _find_equation_links(
    statement: dict,
    source_id: str,
    eq_owners: dict[str, str],
) -> list[dict]:
    """Find references to equations owned by other statements.

    When a statement references equation (NNNx) and that equation is
    'owned' by another statement, create a dependency edge.
    """
    edges = []
    combined = statement["text"]
    if statement.get("proof_text"):
        combined += "\n" + statement["proof_text"]

    for m in EQUATION_REF_RE.finditer(combined):
        tag = m.group(1)
        owner_id = eq_owners.get(tag)
        if owner_id and owner_id != source_id:
            edges.append({
                "source": source_id,
                "target": owner_id,
                "edge_type": "uses_equation_from",
                "context": f"({tag}) owned by {owner_id}",
            })

    return edges


# ── Main extraction ────────────────────────────────────────────────────

def extract_references() -> list[dict]:
    """Extract cross-references from all formal statements.

    Returns a list of edge dicts: {source, target, edge_type, context}.
    """
    stmts_path = RAW_TEXT_DIR / "formal_statements.json"
    with open(stmts_path, encoding="utf-8") as f:
        statements = json.load(f)

    # Build indices
    known_ids = {_make_id(s["kind"], s["number"]) for s in statements}
    concept_map = _extract_concept_names(statements)
    eq_owners = _build_equation_owner_map(statements)

    print(f"  Concept names extracted: {len(concept_map)}")
    print(f"  Equations linked to statements: {len(eq_owners)}")

    edges: list[dict] = []

    for stmt in statements:
        source_id = _make_id(stmt["kind"], stmt["number"])
        search_text = stmt["text"]
        if stmt.get("proof_text"):
            search_text += "\n" + stmt["proof_text"]
        search_text = normalize_ligatures(search_text)

        # 1. Explicit formal statement references (regex)
        for m in FORMAL_REF_RE.finditer(search_text):
            ref_kind = _normalize_kind(m.group(1))
            ref_number = m.group(2)
            target_id = _make_id(ref_kind, ref_number)
            if target_id != source_id and target_id in known_ids:
                edges.append({
                    "source": source_id,
                    "target": target_id,
                    "edge_type": f"uses_{ref_kind}",
                    "context": m.group(0),
                })

        # 2. Concept name references
        concept_edges = _find_concept_references(stmt, source_id, concept_map)
        edges.extend(concept_edges)

        # 3. Equation-to-statement links
        eq_edges = _find_equation_links(stmt, source_id, eq_owners)
        edges.extend(eq_edges)

        # 4. Section references (kept for completeness)
        for m in SECTION_REF_RE.finditer(search_text):
            sec_num = m.group(1)
            edges.append({
                "source": source_id,
                "target": f"sec:{sec_num}",
                "edge_type": "uses_section",
                "context": m.group(0),
            })

    # Deduplicate edges
    seen = set()
    unique_edges = []
    for e in edges:
        key = (e["source"], e["target"], e["edge_type"])
        if key not in seen:
            seen.add(key)
            unique_edges.append(e)

    return unique_edges


def main() -> None:
    print("Phase 4a: Extracting cross-references ...")
    edges = extract_references()

    out_path = RAW_TEXT_DIR / "references.json"
    out_path.write_text(
        json.dumps(edges, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    # Summary by edge type
    type_counts: dict[str, int] = {}
    for e in edges:
        type_counts[e["edge_type"]] = type_counts.get(e["edge_type"], 0) + 1

    # Count formal-to-formal (non-section, non-raw-equation)
    formal_edges = [e for e in edges
                    if not e["target"].startswith("sec:")]
    print(f"  Total edges: {len(edges)}")
    print(f"  Formal-to-formal edges: {len(formal_edges)}")
    for t, c in sorted(type_counts.items()):
        print(f"    {t}: {c}")
    print(f"  Wrote {out_path}")


if __name__ == "__main__":
    main()
