"""Phase 8: Build formalization-ready data layout.

Joins all extraction outputs (statements, LaTeX, context, names, references)
into a single per-entity view designed for downstream Lean formalization
consumers. Output goes to extraction/formalization_data/.

Also merges hand-curated content from extraction/extensions/:
  - missing_statements.json: textbook entities the auto-extractor missed
  - helper_entities.json:    Lean-side helpers (aux: prefix), NOT in Butcher
  - extra_references.json:   manually-curated dependency edges

See extraction/EXTENSIBILITY.md for the agent-facing recipe.

Layout produced:
    formalization_data/
        index.json
        topo_order.json
        entities/<prefix>_<number>.json   (one file per statement)
        by_chapter/ch0N.json              (chapter-grouped index; helpers excluded)
        lean_status.json                  (editable; placeholders preserved)
"""
from __future__ import annotations

import json
import re
from collections import defaultdict
from pathlib import Path

from pipeline.config import CHAPTERS, RAW_TEXT_DIR, SUBSECTION_TITLES
from pipeline.break_cycles import break_cycles


OUT_DIR = RAW_TEXT_DIR.parent / "formalization_data"
ENTITIES_DIR = OUT_DIR / "entities"
BY_CHAPTER_DIR = OUT_DIR / "by_chapter"
EXTENSIONS_DIR = RAW_TEXT_DIR.parent / "extensions"

KIND_PREFIX = {
    "theorem": "thm",
    "definition": "def",
    "lemma": "lem",
    "corollary": "cor",
}
ALLOWED_KINDS = set(KIND_PREFIX.keys())
AUX_PREFIX = "aux"

SLUG_RE = re.compile(r"^[a-z0-9_]{3,50}$")
BUTCHER_NUM_RE = re.compile(r"^\d{3}[A-Z]$")


def _make_id(kind: str, number: str) -> str:
    return f"{KIND_PREFIX.get(kind, kind[:3])}:{number}"


def _statement_id(stmt: dict) -> str:
    """Compute an entity ID, accounting for the aux: prefix on helpers."""
    if stmt.get("_is_helper"):
        return f"{AUX_PREFIX}:{stmt['number']}"
    return _make_id(stmt["kind"], stmt["number"])


def _short_id_from_long(long_key: str) -> str:
    """Convert 'theorem:101A' → 'thm:101A'. Pass-through if already short."""
    if ":" not in long_key:
        return long_key
    kind, num = long_key.split(":", 1)
    if kind in KIND_PREFIX:
        return f"{KIND_PREFIX[kind]}:{num}"
    return long_key


def _id_to_filename(short_id: str) -> str:
    """'thm:110C' → 'thm_110C.json'."""
    return short_id.replace(":", "_") + ".json"


# ── Loading auto-extracted data ────────────────────────────────────────


def _load_auto() -> dict:
    """Load all auto-extracted sources keyed for fast lookup."""
    with open(RAW_TEXT_DIR / "formal_statements.json", encoding="utf-8") as f:
        statements = json.load(f)

    latex_map: dict[str, dict] = {}
    with open(RAW_TEXT_DIR / "formal_statements_latex.json", encoding="utf-8") as f:
        for s in json.load(f):
            sid = _make_id(s["kind"], s["number"])
            latex_map[sid] = s

    context_map: dict[str, dict] = {}
    with open(RAW_TEXT_DIR / "statement_context.json", encoding="utf-8") as f:
        for s in json.load(f):
            sid = _make_id(s["kind"], s["number"])
            context_map[sid] = s

    context_latex_map: dict[str, str] = {}
    ctx_path = RAW_TEXT_DIR / "context_latex.json"
    if ctx_path.exists():
        with open(ctx_path, encoding="utf-8") as f:
            for k, v in json.load(f).items():
                context_latex_map[_short_id_from_long(k)] = v

    names_map: dict[str, str] = {}
    names_path = RAW_TEXT_DIR / "statement_names.json"
    if names_path.exists():
        with open(names_path, encoding="utf-8") as f:
            for k, v in json.load(f).items():
                names_map[_short_id_from_long(k)] = v

    with open(RAW_TEXT_DIR / "references_merged.json", encoding="utf-8") as f:
        edges = json.load(f)

    return {
        "statements": statements,
        "latex": latex_map,
        "context": context_map,
        "context_latex": context_latex_map,
        "names": names_map,
        "edges": edges,
    }


# ── Loading + validating extensions ────────────────────────────────────


def _read_extension(name: str, default):
    """Read an extensions/*.json file; return default if absent."""
    p = EXTENSIONS_DIR / name
    if not p.exists():
        return default
    with open(p, encoding="utf-8") as f:
        return json.load(f)


def _validate_missing(stmt: dict, auto_ids: set[str], idx: int) -> str:
    required = ("kind", "number", "chapter", "section", "subsection", "text")
    for f in required:
        if f not in stmt:
            raise ValueError(
                f"missing_statements[{idx}]: missing required field '{f}'"
            )
    if stmt["kind"] not in ALLOWED_KINDS:
        raise ValueError(
            f"missing_statements[{idx}]: kind must be one of {sorted(ALLOWED_KINDS)}, "
            f"got {stmt['kind']!r}"
        )
    if not BUTCHER_NUM_RE.match(stmt["number"]):
        raise ValueError(
            f"missing_statements[{idx}]: number {stmt['number']!r} does not match "
            "Butcher format (3 digits + uppercase letter, e.g. '235B')"
        )
    sid = _make_id(stmt["kind"], stmt["number"])
    if sid in auto_ids:
        raise ValueError(
            f"missing_statements[{idx}]: ID {sid} already exists in auto-extracted "
            "data — re-extraction now covers it; delete the manual entry"
        )
    return sid


def _validate_helper(helper: dict, all_helper_slugs: set[str], auto_ids: set[str], idx: int) -> str:
    required = ("kind", "number", "name", "motivation", "statement_latex")
    for f in required:
        if f not in helper or helper[f] in (None, ""):
            raise ValueError(
                f"helper_entities[{idx}]: missing required field '{f}'"
            )
    if helper["kind"] not in ALLOWED_KINDS:
        raise ValueError(
            f"helper_entities[{idx}]: kind must be one of {sorted(ALLOWED_KINDS)}, "
            f"got {helper['kind']!r}"
        )
    slug = helper["number"]
    if not SLUG_RE.match(slug):
        raise ValueError(
            f"helper_entities[{idx}]: number {slug!r} is not a valid slug "
            "(snake_case, [a-z0-9_], length 3-50)"
        )
    if slug in all_helper_slugs:
        raise ValueError(
            f"helper_entities[{idx}]: duplicate slug {slug!r}"
        )
    sid = f"{AUX_PREFIX}:{slug}"
    if sid in auto_ids:
        raise ValueError(
            f"helper_entities[{idx}]: ID {sid} collides with an auto-extracted ID"
        )
    return sid


def _validate_removed(raw: list, auto_ids: set[str]) -> tuple[list[dict], set[tuple[str, str]]]:
    """Validate a removed_references.json list.

    Returns (cleaned_rows, pair_set). Each row must have string 'source' and
    'target'. 'reason' is optional but WARNED if missing. Unknown IDs WARN
    but are retained (user may pre-deny an edge the extractor hasn't
    produced yet — LLM runs are nondeterministic). Duplicates silently
    deduplicated.
    """
    if not isinstance(raw, list):
        raise ValueError("removed_references.json must contain a JSON array")

    pair_set: set[tuple[str, str]] = set()
    cleaned: list[dict] = []
    for i, row in enumerate(raw):
        if not isinstance(row, dict):
            raise ValueError(f"removed_references[{i}]: entry must be an object")
        for f in ("source", "target"):
            if f not in row or not isinstance(row[f], str) or not row[f]:
                raise ValueError(f"removed_references[{i}]: missing/invalid '{f}' (must be non-empty string)")
        s, t = row["source"], row["target"]
        if (s, t) in pair_set:
            continue  # silent dedupe
        if "reason" not in row or not row["reason"]:
            print(f"  WARNING: removed_references[{i}] ({s} → {t}) has no 'reason' — add one so the denial doesn't rot")
        for label, sid in (("source", s), ("target", t)):
            if sid not in auto_ids:
                print(f"  WARNING: removed_references[{i}]: {label} {sid!r} is not a known auto-extracted ID (kept anyway)")
        pair_set.add((s, t))
        cleaned.append(row)

    return cleaned, pair_set


def _load_extensions(auto_ids: set[str]) -> dict:
    """Load and validate hand-curated extensions. Raises on invalid input."""
    missing_raw = _read_extension("missing_statements.json", [])
    helper_raw = _read_extension("helper_entities.json", [])
    extra_edges = _read_extension("extra_references.json", [])
    removed_raw = _read_extension("removed_references.json", [])

    if not isinstance(missing_raw, list) or not isinstance(helper_raw, list) or not isinstance(extra_edges, list):
        raise ValueError("extensions/*.json files must each contain a JSON array")

    # Validate missing statements
    missing_statements: list[dict] = []
    seen_missing_ids: set[str] = set()
    for i, stmt in enumerate(missing_raw):
        sid = _validate_missing(stmt, auto_ids, i)
        if sid in seen_missing_ids:
            raise ValueError(f"missing_statements: duplicate entry for {sid}")
        seen_missing_ids.add(sid)
        # Normalize: ensure optional fields exist
        stmt.setdefault("proof_text", "")
        stmt.setdefault("introduces", [])
        stmt.setdefault("page", None)
        missing_statements.append(stmt)

    # Validate helpers
    helpers: list[dict] = []
    seen_slugs: set[str] = set()
    for i, helper in enumerate(helper_raw):
        sid = _validate_helper(helper, seen_slugs, auto_ids, i)
        seen_slugs.add(helper["number"])
        helpers.append(helper)

    # Validate extra edges (shape only; dangling-target check happens later)
    for i, edge in enumerate(extra_edges):
        for f in ("source", "target", "edge_type"):
            if f not in edge:
                raise ValueError(
                    f"extra_references[{i}]: missing required field '{f}'"
                )

    # Validate denylist
    removed_edges, removed_pairs = _validate_removed(removed_raw, auto_ids)

    return {
        "missing_statements": missing_statements,
        "helpers": helpers,
        "extra_edges": extra_edges,
        "removed_edges": removed_edges,
        "removed_pairs": removed_pairs,
    }


def _helper_to_pseudo_statement(helper: dict) -> dict:
    """Convert a helper entity into a 'statement' that flows through the rest of the pipeline."""
    return {
        "kind": helper["kind"],
        "number": helper["number"],
        "chapter": None,
        "section": None,
        "subsection": None,
        "page": None,
        "text": "",  # full LaTeX is supplied directly via latex_map
        "proof_text": "",
        "introduces": helper.get("introduces", []) or [],
        "_is_helper": True,
        "_helper_motivation": helper.get("motivation", ""),
    }


def _merge_extensions_into_sources(sources: dict, ext: dict) -> tuple[dict, set[str]]:
    """Append extension data into the sources dict. Returns (sources, all_ids_set)."""
    # Missing statements: append to all the same maps as auto
    for stmt in ext["missing_statements"]:
        sid = _make_id(stmt["kind"], stmt["number"])
        sources["statements"].append(stmt)
        # The hand entry may include statement_latex/proof_latex inline.
        latex_pieces = []
        if stmt.get("statement_latex"):
            latex_pieces.append(stmt["statement_latex"])
        if stmt.get("proof_latex"):
            latex_pieces.append(stmt["proof_latex"])
        if latex_pieces:
            sources["latex"][sid] = {
                "latex": "\n".join(latex_pieces),
                "latex_status": "completed",
            }
        if stmt.get("context_latex"):
            sources["context_latex"][sid] = stmt["context_latex"]
        if stmt.get("name"):
            sources["names"][sid] = stmt["name"]
        if any(k in stmt for k in ("variables", "equations", "preamble")):
            sources["context"][sid] = {
                "variables": stmt.get("variables", []) or [],
                "equations": stmt.get("equations", []) or [],
                "preamble": stmt.get("preamble", "") or "",
            }

    # Helpers: convert + append; they look like statements but with aux: IDs
    for helper in ext["helpers"]:
        pseudo = _helper_to_pseudo_statement(helper)
        sid = _statement_id(pseudo)
        sources["statements"].append(pseudo)
        latex_pieces = [helper["statement_latex"]]
        if helper.get("proof_latex"):
            latex_pieces.append(helper["proof_latex"])
        sources["latex"][sid] = {
            "latex": "\n".join(latex_pieces),
            "latex_status": "completed",
        }
        if helper.get("context_latex"):
            sources["context_latex"][sid] = helper["context_latex"]
        sources["names"][sid] = helper["name"]
        sources["context"][sid] = {
            "variables": helper.get("variables", []) or [],
            "equations": helper.get("equations", []) or [],
            "preamble": helper.get("preamble", "") or "",
        }

    # Denylist: drop auto-derived edges that the user has marked wrong in
    # extensions/removed_references.json (filter runs BEFORE the additive
    # merge, so a pair in both files ends up as the manual add).
    removed_pairs = ext.get("removed_pairs", set())
    if removed_pairs:
        before_pairs = {(e["source"], e["target"]) for e in sources["edges"]}
        sources["edges"] = [e for e in sources["edges"]
                            if (e["source"], e["target"]) not in removed_pairs]
        matched = len(before_pairs & removed_pairs)
        print(f"  Denylist: dropped {matched} edge(s) per removed_references.json")
        unused = [r for r in ext["removed_edges"]
                  if (r["source"], r["target"]) not in before_pairs]
        for u in unused:
            print(f"    WARN: removed_references row did not match any auto edge: "
                  f"{u['source']} → {u['target']}")

    # Extra edges: append, then later cycle-break will run on the merged graph
    sources["edges"] = list(sources["edges"]) + list(ext["extra_edges"])

    all_ids = {_statement_id(s) for s in sources["statements"]}
    return sources, all_ids


# ── Graph operations ───────────────────────────────────────────────────


def _build_graph(edges: list[dict], known_ids: set[str]) -> tuple[dict, dict]:
    """Return (forward, reverse) adjacency dicts of formal-to-formal edges only.

    Forward: source → list of target IDs (deps).
    Reverse: target → list of source IDs (dependents).
    """
    forward: dict[str, set[str]] = defaultdict(set)
    reverse: dict[str, set[str]] = defaultdict(set)
    for e in edges:
        src, tgt = e["source"], e["target"]
        if src not in known_ids or tgt not in known_ids:
            continue
        if src == tgt:
            continue
        forward[src].add(tgt)
        reverse[tgt].add(src)
    return (
        {k: sorted(v) for k, v in forward.items()},
        {k: sorted(v) for k, v in reverse.items()},
    )


def _transitive_deps(node: str, forward: dict[str, list[str]]) -> list[str]:
    """DFS to compute transitive dependency closure (excluding self)."""
    seen: set[str] = set()
    stack = list(forward.get(node, []))
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        stack.extend(forward.get(n, []))
    return sorted(seen)


def _topological_tiers(
    nodes: list[str], forward: dict[str, list[str]]
) -> tuple[list[str], list[list[str]]]:
    """Kahn's algorithm. Returns (linear order, tiers).

    Tier 0 = nodes with no formal deps; tier k = nodes whose deps are all
    in tiers 0..k-1.
    """
    nodes_set = set(nodes)
    deps_remaining: dict[str, set[str]] = {
        n: {d for d in forward.get(n, []) if d in nodes_set} for n in nodes
    }
    dependents_of: dict[str, set[str]] = defaultdict(set)
    for n, deps in deps_remaining.items():
        for d in deps:
            dependents_of[d].add(n)

    tiers: list[list[str]] = []
    order: list[str] = []
    current = sorted(n for n, deps in deps_remaining.items() if not deps)

    placed: set[str] = set()
    while current:
        tiers.append(current)
        order.extend(current)
        next_tier_set: set[str] = set()
        for n in current:
            placed.add(n)
            for dependent in dependents_of.get(n, ()):
                if dependent in placed:
                    continue
                deps_remaining[dependent].discard(n)
                if not deps_remaining[dependent]:
                    next_tier_set.add(dependent)
        current = sorted(next_tier_set)

    leftover = sorted(set(nodes) - placed)
    if leftover:
        tiers.append(leftover)
        order.extend(leftover)

    return order, tiers


# ── Per-entity record ──────────────────────────────────────────────────


def _strip_lead_label(text: str, kind: str, number: str) -> str:
    """Remove redundant 'Theorem 110C ' / 'Definition 110A ' prefix from raw text."""
    label = f"{kind.capitalize()} {number}"
    if text.startswith(label):
        return text[len(label):].lstrip()
    return text


def _build_entity_record(
    stmt: dict,
    sid: str,
    sources: dict,
    forward: dict[str, list[str]],
    reverse: dict[str, list[str]],
    transitive: list[str],
    edges_by_source: dict[str, list[dict]],
    lean_entry: dict,
    kind_map: dict[str, str],
) -> dict:
    is_helper = stmt.get("_is_helper", False)
    kind = stmt["kind"]
    number = stmt["number"]
    name = sources["names"].get(sid, "")

    latex_entry = sources["latex"].get(sid, {})
    statement_latex = latex_entry.get("latex", "") if latex_entry.get("latex_status") == "completed" else ""
    proof_latex = ""
    if "\\begin{proof}" in statement_latex:
        idx = statement_latex.index("\\begin{proof}")
        proof_latex = statement_latex[idx:]
        statement_latex = statement_latex[:idx].rstrip()

    context = sources["context"].get(sid, {})
    variables = context.get("variables", []) or []
    equations = context.get("equations", []) or []
    preamble = context.get("preamble", "") or ""
    context_latex = sources["context_latex"].get(sid, "")

    # Dependencies — take all formal-to-formal edges from this source
    dep_records: list[dict] = []
    seen_dep_ids: set[str] = set()
    for e in edges_by_source.get(sid, []):
        tgt = e["target"]
        if tgt in seen_dep_ids:
            continue
        seen_dep_ids.add(tgt)
        tgt_name = sources["names"].get(tgt, "")
        tgt_prefix, tgt_number = tgt.split(":", 1)
        tgt_kind = kind_map.get(tgt, tgt_prefix)
        dep_records.append({
            "id": tgt,
            "kind": tgt_kind,
            "number": tgt_number,
            "name": tgt_name,
            "edge_type": e.get("edge_type", ""),
            "context": e.get("context", ""),
        })

    statement_text = "" if is_helper else _strip_lead_label(stmt["text"], kind, number)
    subsec = stmt.get("subsection")
    subsection_title = ""
    if subsec is not None:
        try:
            subsection_title = SUBSECTION_TITLES.get(int(subsec), "")
        except (ValueError, TypeError):
            subsection_title = ""

    record = {
        "id": sid,
        "kind": kind,
        "number": number,
        "name": name,
        "is_helper": is_helper,
        "chapter": stmt.get("chapter"),
        "section": stmt.get("section"),
        "subsection": subsec,
        "subsection_title": subsection_title,
        "page": stmt.get("page"),
        "statement_text": statement_text,
        "statement_latex": statement_latex,
        "proof_text": stmt.get("proof_text", ""),
        "proof_latex": proof_latex,
        "context_latex": context_latex,
        "variables": variables,
        "equations": equations,
        "preamble": preamble,
        "introduces": stmt.get("introduces", []) or [],
        "dependencies": dep_records,
        "transitive_dependencies": transitive,
        "dependents": reverse.get(sid, []),
        "lean_file": lean_entry.get("lean_file"),
        "lean_symbol": lean_entry.get("lean_symbol"),
        "formalization_status": lean_entry.get("status", "unformalized"),
    }
    if is_helper:
        record["motivation"] = stmt.get("_helper_motivation", "")
    return record


# ── Output writers ─────────────────────────────────────────────────────


def _write_entities(records: list[dict]) -> None:
    ENTITIES_DIR.mkdir(parents=True, exist_ok=True)
    # Track existing files; remove any whose entity no longer exists (e.g. deleted helper)
    expected = {_id_to_filename(r["id"]) for r in records}
    for existing in ENTITIES_DIR.glob("*.json"):
        if existing.name not in expected:
            existing.unlink()
    for rec in records:
        path = ENTITIES_DIR / _id_to_filename(rec["id"])
        path.write_text(
            json.dumps(rec, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )


def _write_index(records: list[dict]) -> None:
    index = []
    for rec in records:
        index.append({
            "id": rec["id"],
            "name": rec["name"],
            "kind": rec["kind"],
            "is_helper": rec["is_helper"],
            "chapter": rec["chapter"],
            "section": rec["section"],
            "subsection": rec["subsection"],
            "page": rec["page"],
            "n_deps": len(rec["dependencies"]),
            "n_dependents": len(rec["dependents"]),
            "has_proof": bool(rec["proof_text"] or rec["proof_latex"]),
            "lean_file": rec["lean_file"],
            "formalization_status": rec["formalization_status"],
        })
    (OUT_DIR / "index.json").write_text(
        json.dumps(index, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )


def _write_topo_order(order: list[str], tiers: list[list[str]]) -> None:
    payload = {
        "order": order,
        "tiers": [
            {
                "tier": i,
                "ids": tier,
                "description": (
                    "No formal dependencies"
                    if i == 0
                    else f"Depends only on tiers 0..{i - 1}"
                ),
            }
            for i, tier in enumerate(tiers)
        ],
    }
    (OUT_DIR / "topo_order.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )


def _write_by_chapter(records: list[dict]) -> None:
    """Emit chapter views. Helpers (chapter=None) are excluded — see `index.json` for the full list."""
    BY_CHAPTER_DIR.mkdir(parents=True, exist_ok=True)
    by_ch: dict[int, list[dict]] = defaultdict(list)
    for rec in records:
        if rec["chapter"] is None:
            continue
        by_ch[rec["chapter"]].append(rec)

    for ch_num, ch_meta in CHAPTERS.items():
        recs = sorted(by_ch.get(ch_num, []), key=lambda r: (r["subsection"], r["number"]))
        by_section: dict[str, list[dict]] = defaultdict(list)
        for rec in recs:
            by_section[rec["section"]].append(rec)

        sections_payload = []
        for sec_num_int, sec_title in ch_meta["sections"].items():
            sec_str = str(sec_num_int)
            sec_recs = by_section.get(sec_str, [])
            by_subsec: dict[str, list[str]] = defaultdict(list)
            for rec in sec_recs:
                by_subsec[rec["subsection"]].append(rec["id"])
            subsec_payload = [
                {
                    "subsection": ss,
                    "title": SUBSECTION_TITLES.get(int(ss), ""),
                    "entities": ids,
                }
                for ss, ids in sorted(by_subsec.items())
            ]
            sections_payload.append({
                "section": sec_str,
                "title": sec_title,
                "subsections": subsec_payload,
            })

        n_unformalized = sum(1 for r in recs if r["formalization_status"] == "unformalized")
        payload = {
            "chapter": ch_num,
            "title": ch_meta["title"],
            "entity_count": len(recs),
            "n_unformalized": n_unformalized,
            "sections": sections_payload,
        }
        (BY_CHAPTER_DIR / f"ch{ch_num:02d}.json").write_text(
            json.dumps(payload, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )


def _load_lean_status() -> dict[str, dict]:
    path = OUT_DIR / "lean_status.json"
    if not path.exists():
        return {}
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def _write_lean_status(known_ids: list[str], existing: dict[str, dict]) -> None:
    """Preserves existing rows; fills in placeholders for new ids; drops rows for vanished ids."""
    out: dict[str, dict] = {}
    known_set = set(known_ids)
    for sid in known_ids:
        if sid in existing:
            row = existing[sid]
            row.setdefault("lean_file", None)
            row.setdefault("lean_symbol", None)
            row.setdefault("status", "unformalized")
            out[sid] = row
        else:
            out[sid] = {"lean_file": None, "lean_symbol": None, "status": "unformalized"}
    # Note: ids in `existing` but not in `known_set` are dropped — entity was deleted
    dropped = set(existing.keys()) - known_set
    if dropped:
        print(f"  Dropped lean_status rows for vanished entities: {sorted(dropped)}")
    (OUT_DIR / "lean_status.json").write_text(
        json.dumps(out, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )


# ── Regression assertion: no introducer-to-introducer concept edges ────


def _assert_no_homonym_concept_edges(edges: list[dict], statements: list[dict]) -> None:
    """Fail loudly if any uses_concept edge links two entities sharing a name.

    After fix_introduces.py qualifies homonyms ("convergent" → "convergent
    matrix" / "convergent linear multistep method"), these edges should be
    impossible. This is a belt-and-suspenders guard against future
    regressions when entities are added via extensions/.
    """
    names_path = RAW_TEXT_DIR / "statement_names.json"
    if not names_path.exists():
        return

    raw_names = json.loads(names_path.read_text(encoding="utf-8"))
    name_by_id: dict[str, str] = {}
    for long_key, name in raw_names.items():
        sid = _short_id_from_long(long_key)
        if name and isinstance(name, str):
            name_by_id[sid] = name.strip().lower()

    bad = []
    for e in edges:
        if e.get("edge_type") != "uses_concept":
            continue
        s, t = e.get("source"), e.get("target")
        ns, nt = name_by_id.get(s), name_by_id.get(t)
        if ns and nt and ns == nt:
            bad.append((s, t, ns, e.get("context")))

    if bad:
        msg_lines = [
            f"Layer 1 regression: {len(bad)} uses_concept edge(s) link entities "
            f"sharing a name (likely unqualified homonym in introduces field):"
        ]
        for s, t, n, ctx in bad:
            msg_lines.append(f"  {s} → {t}  shared name={n!r}  context={ctx!r}")
        msg_lines.append(
            "Re-run `python -m pipeline.fix_introduces --run-api` to qualify the "
            "homonyms, then re-run Phases 4a, 4c, build_graph, and Phase 8."
        )
        raise AssertionError("\n".join(msg_lines))


# ── Main ───────────────────────────────────────────────────────────────


def main() -> None:
    print("Phase 8: Building formalization-ready data layout ...")

    OUT_DIR.mkdir(parents=True, exist_ok=True)

    sources = _load_auto()
    auto_ids = {_make_id(s["kind"], s["number"]) for s in sources["statements"]}

    # Merge extensions
    ext = _load_extensions(auto_ids)
    n_missing, n_helpers, n_extra_edges, n_removed = (
        len(ext["missing_statements"]), len(ext["helpers"]),
        len(ext["extra_edges"]), len(ext["removed_edges"]),
    )
    if n_missing or n_helpers or n_extra_edges or n_removed:
        print(
            f"  Extensions: +{n_missing} missing statements, "
            f"+{n_helpers} helpers, +{n_extra_edges} extra edges, "
            f"−{n_removed} denied edges"
        )
    sources, all_ids = _merge_extensions_into_sources(sources, ext)

    # Warn on dangling extra-edge targets
    for e in ext["extra_edges"]:
        if e["source"] not in all_ids:
            print(f"  WARNING: extra_reference source {e['source']} is unknown — edge dropped")
        if e["target"] not in all_ids:
            print(f"  WARNING: extra_reference target {e['target']} is unknown — edge dropped")

    # Re-run cycle-breaking on the merged graph (extensions may introduce new cycles)
    page_map = {
        _statement_id(s): (s.get("page") or 0)
        for s in sources["statements"]
    }
    edges_before = len(sources["edges"])
    sources["edges"], cycle_log = break_cycles(sources["edges"], page_map)
    if cycle_log:
        print(
            f"  Re-broke {len(cycle_log)} cycle(s) on merged graph "
            f"(edges {edges_before} → {len(sources['edges'])})"
        )
    # Persist updated cycle-removal audit (overwrites; the merged cycle log
    # supersedes the auto-only one from Phase 4c since it covers extensions too)
    (OUT_DIR / "cycles_removed_merged.json").write_text(
        json.dumps(cycle_log, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    statements = sources["statements"]
    edges = sources["edges"]

    # Emit the final, post-denylist, post-cycle-break edge set so downstream
    # consumers (generate_blueprint, graph viz, etc.) don't re-apply edges we
    # already decided to drop.
    (OUT_DIR / "references_final.json").write_text(
        json.dumps(edges, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    known_ids = [_statement_id(s) for s in statements]
    known_ids_set = set(known_ids)
    kind_map = {_statement_id(s): s["kind"] for s in statements}

    # Index edges by source for per-entity lookup
    edges_by_source: dict[str, list[dict]] = defaultdict(list)
    for e in edges:
        if e["source"] in known_ids_set and e["target"] in known_ids_set:
            edges_by_source[e["source"]].append(e)

    forward, reverse = _build_graph(edges, known_ids_set)
    order, tiers = _topological_tiers(known_ids, forward)

    # Lean status
    existing_lean = _load_lean_status()
    _write_lean_status(known_ids, existing_lean)
    lean_status = _load_lean_status()

    records: list[dict] = []
    for stmt in statements:
        sid = _statement_id(stmt)
        transitive = _transitive_deps(sid, forward)
        rec = _build_entity_record(
            stmt, sid, sources, forward, reverse, transitive,
            edges_by_source, lean_status.get(sid, {}), kind_map,
        )
        records.append(rec)

    _write_entities(records)
    _write_index(records)
    _write_topo_order(order, tiers)
    _write_by_chapter(records)

    by_chapter = defaultdict(int)
    n_helpers_out = 0
    for rec in records:
        if rec["chapter"] is None:
            n_helpers_out += 1
        else:
            by_chapter[rec["chapter"]] += 1
    n_unformalized = sum(1 for r in records if r["formalization_status"] == "unformalized")
    n_with_lean = len(records) - n_unformalized
    n_tier0 = len(tiers[0]) if tiers else 0

    print(f"  Total entities: {len(records)} ({n_helpers_out} helpers, {len(records) - n_helpers_out} textbook)")
    print(f"  Textbook by chapter: {dict(sorted(by_chapter.items()))}")
    print(f"  Tiers: {len(tiers)} (tier-0 ready-to-formalize: {n_tier0})")
    print(f"  Unformalized: {n_unformalized} / With Lean: {n_with_lean}")

    _assert_no_homonym_concept_edges(edges, statements)

    print(f"  Wrote {OUT_DIR}")


if __name__ == "__main__":
    main()
