"""Phase 4c: Break cycles in the dependency graph.

The dependency graph should be a DAG for the LeanBlueprint renderer.
This script removes minimum-confidence back-edges until the graph is acyclic.

Confidence scoring (higher = more trustworthy):
  - Explicit regex reference (uses_theorem/definition/lemma/corollary): 3
  - Equation-to-statement link (uses_equation_from):                    2
  - Concept name match (uses_concept):                                  2
  - LLM-inferred (llm_dependency):                                      1

When breaking a cycle, prefer removing edges with:
  1. Lowest total confidence (sum over all edge_types between source/target)
  2. Among equal confidence: largest page-distance back-edge
     (source appears on later page than target — forward-reference hallucination)

Outputs:
  - references_merged.json (cleaned, cycle-free)
  - cycles_removed.json (audit log)

Usage:
    python -m pipeline.break_cycles
"""
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR


# ── Edge confidence ────────────────────────────────────────────────────

EDGE_WEIGHTS = {
    "uses_theorem": 3,
    "uses_definition": 3,
    "uses_lemma": 3,
    "uses_corollary": 3,
    "uses_equation_from": 2,
    "uses_concept": 2,
    "llm_dependency": 1,
}


def _edge_confidence(edge_types: list[str]) -> int:
    """Total confidence of an edge given all the methods that proposed it."""
    return sum(EDGE_WEIGHTS.get(t, 0) for t in edge_types)


# ── Graph building ─────────────────────────────────────────────────────

KIND_PREFIXES = ("thm:", "def:", "lem:", "cor:")


def _is_formal(node_id: str) -> bool:
    return any(node_id.startswith(p) for p in KIND_PREFIXES)


def _build_graph(
    edges: list[dict],
    page_map: dict[str, int],
) -> tuple[dict[str, set[str]], dict[tuple[str, str], dict]]:
    """Build adjacency + edge metadata.

    Returns:
      - adj: {source: set of targets}
      - edge_info: {(source, target): {types: [...], confidence: N, page_diff: N}}
    """
    # Group edges by (source, target) pair
    grouped: dict[tuple[str, str], list[str]] = defaultdict(list)
    for e in edges:
        if not _is_formal(e["target"]):
            continue
        grouped[(e["source"], e["target"])].append(e["edge_type"])

    adj: dict[str, set[str]] = defaultdict(set)
    edge_info: dict[tuple[str, str], dict] = {}
    for (src, tgt), types in grouped.items():
        adj[src].add(tgt)
        src_page = page_map.get(src, 0)
        tgt_page = page_map.get(tgt, 0)
        edge_info[(src, tgt)] = {
            "types": types,
            "confidence": _edge_confidence(types),
            "page_diff": src_page - tgt_page,  # positive = back-edge
        }

    return dict(adj), edge_info


# ── Cycle detection (DFS) ─────────────────────────────────────────────

def _find_cycle(adj: dict[str, set[str]]) -> list[str] | None:
    """Find any one cycle in the graph via DFS. Returns the cycle path or None."""
    visited: set[str] = set()
    rec_stack: list[str] = []
    rec_set: set[str] = set()

    def dfs(node: str) -> list[str] | None:
        visited.add(node)
        rec_stack.append(node)
        rec_set.add(node)

        for neighbor in adj.get(node, set()):
            if neighbor in rec_set:
                # Found cycle: extract it from rec_stack
                idx = rec_stack.index(neighbor)
                return rec_stack[idx:] + [neighbor]
            if neighbor not in visited:
                result = dfs(neighbor)
                if result:
                    return result

        rec_stack.pop()
        rec_set.discard(node)
        return None

    for node in list(adj.keys()):
        if node not in visited:
            cycle = dfs(node)
            if cycle:
                return cycle
    return None


# ── Edge selection for removal ─────────────────────────────────────────

def _pick_edge_to_remove(
    cycle: list[str],
    edge_info: dict[tuple[str, str], dict],
) -> tuple[str, str]:
    """Pick the edge in the cycle to remove.

    Strategy:
      1. Minimum confidence (remove weakest evidence first)
      2. Tiebreaker: maximum positive page_diff (most forward-referencing)
    """
    cycle_edges = [(cycle[i], cycle[i + 1]) for i in range(len(cycle) - 1)]

    def key(e):
        info = edge_info[e]
        # Sort: (confidence asc, -page_diff asc) = (weakest first, most forward-referencing)
        return (info["confidence"], -info["page_diff"])

    cycle_edges.sort(key=key)
    return cycle_edges[0]


# ── Main cycle-breaking ────────────────────────────────────────────────

def break_cycles(
    edges: list[dict],
    page_map: dict[str, int],
) -> tuple[list[dict], list[dict]]:
    """Remove minimum-confidence back-edges until the graph is acyclic.

    Returns (clean_edges, removed_edges_log).
    """
    adj, edge_info = _build_graph(edges, page_map)

    # Track what's removed (by (source, target) pair)
    removed_pairs: set[tuple[str, str]] = set()
    removal_log: list[dict] = []

    # Repeatedly find and break cycles
    while True:
        cycle = _find_cycle(adj)
        if cycle is None:
            break

        edge_to_remove = _pick_edge_to_remove(cycle, edge_info)
        src, tgt = edge_to_remove

        # Remove from adjacency
        adj[src].discard(tgt)
        removed_pairs.add(edge_to_remove)

        # Record in log
        info = edge_info[edge_to_remove]
        removal_log.append({
            "source": src,
            "target": tgt,
            "edge_types": info["types"],
            "confidence": info["confidence"],
            "page_diff": info["page_diff"],
            "cycle": cycle,
        })

    # Filter original edges list: drop all edges matching a removed pair
    clean_edges = [
        e for e in edges
        if (e["source"], e["target"]) not in removed_pairs
    ]

    return clean_edges, removal_log


# ── Main driver ────────────────────────────────────────────────────────

def main() -> None:
    print("Phase 4c: Breaking cycles in dependency graph ...")

    # Load merged references
    merged_path = RAW_TEXT_DIR / "references_merged.json"
    if not merged_path.exists():
        print(f"  ERROR: {merged_path} not found")
        return
    with open(merged_path) as f:
        edges = json.load(f)

    # Load statements for page map
    with open(RAW_TEXT_DIR / "formal_statements.json") as f:
        statements = json.load(f)

    KIND_PREFIX = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}
    page_map = {
        f"{KIND_PREFIX[s['kind']]}:{s['number']}": s.get("page", 0)
        for s in statements
    }

    # Break cycles
    original_count = len(edges)
    clean_edges, removal_log = break_cycles(edges, page_map)

    # Save clean edges back to merged
    merged_path.write_text(
        json.dumps(clean_edges, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    # Save audit log
    log_path = RAW_TEXT_DIR / "cycles_removed.json"
    log_path.write_text(
        json.dumps(removal_log, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    # Summary
    print(f"  Edges before: {original_count}")
    print(f"  Edges after: {len(clean_edges)}")
    print(f"  Edges removed: {original_count - len(clean_edges)}")
    print(f"  Cycles broken: {len(removal_log)}")
    if removal_log:
        from collections import Counter
        by_confidence = Counter(r["confidence"] for r in removal_log)
        print(f"  Removed by confidence:")
        for conf in sorted(by_confidence.keys()):
            print(f"    confidence={conf}: {by_confidence[conf]} edges")
    print(f"  Wrote {merged_path}")
    print(f"  Audit log: {log_path}")


if __name__ == "__main__":
    main()
