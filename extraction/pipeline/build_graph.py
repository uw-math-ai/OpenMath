"""Phase 4b: Build dependency graph from cross-references.

Creates a JSON graph (nodes + edges), a GraphViz DOT file, and
an interactive HTML visualization.
"""
from __future__ import annotations

import json
from pathlib import Path

from pipeline.config import (
    RAW_TEXT_DIR,
    GRAPH_DIR,
    CHAPTERS,
    chapter_from_subsection,
)


# ── Node shape and color mapping ───────────────────────────────────────

KIND_SHAPES = {
    "theorem": "ellipse",
    "definition": "box",
    "lemma": "diamond",
    "corollary": "hexagon",
}

CHAPTER_COLORS = {
    1: "#e6194b",  # red
    2: "#3cb44b",  # green
    3: "#4363d8",  # blue
    4: "#f58231",  # orange
    5: "#911eb4",  # purple
}


def _make_id(kind: str, number: str) -> str:
    prefix = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}.get(kind, kind[:3])
    return f"{prefix}:{number}"


def build_graph() -> dict:
    """Build the dependency graph from formal statements and references.

    Returns a dict with 'nodes' and 'edges' lists, plus 'stats'.
    """
    # Load formal statements
    with open(RAW_TEXT_DIR / "formal_statements.json", encoding="utf-8") as f:
        statements = json.load(f)

    # Load references
    with open(RAW_TEXT_DIR / "references.json", encoding="utf-8") as f:
        ref_edges = json.load(f)

    # Build nodes
    nodes = []
    node_ids = set()
    for s in statements:
        node_id = _make_id(s["kind"], s["number"])
        node_ids.add(node_id)
        nodes.append({
            "id": node_id,
            "kind": s["kind"],
            "number": s["number"],
            "chapter": s["chapter"],
            "section": s["section"],
            "subsection": s["subsection"],
            "page": s.get("page", 0),
            "has_proof": bool(s.get("proof_text")),
            "text_preview": s["text"][:200],
        })

    # Filter edges to only include formal-to-formal references
    formal_edges = [
        e for e in ref_edges
        if e["source"] in node_ids and e["target"] in node_ids
    ]

    # Build adjacency info
    outgoing: dict[str, list[str]] = {}
    incoming: dict[str, list[str]] = {}
    for e in formal_edges:
        outgoing.setdefault(e["source"], []).append(e["target"])
        incoming.setdefault(e["target"], []).append(e["source"])

    # Enrich nodes with degree info
    for node in nodes:
        nid = node["id"]
        node["out_degree"] = len(outgoing.get(nid, []))
        node["in_degree"] = len(incoming.get(nid, []))

    # Stats
    stats = {
        "total_nodes": len(nodes),
        "total_formal_edges": len(formal_edges),
        "total_all_edges": len(ref_edges),
        "by_kind": {},
        "by_chapter": {},
        "edge_types": {},
    }
    for n in nodes:
        stats["by_kind"][n["kind"]] = stats["by_kind"].get(n["kind"], 0) + 1
        ch_key = f"ch{n['chapter']}"
        stats["by_chapter"][ch_key] = stats["by_chapter"].get(ch_key, 0) + 1
    for e in ref_edges:
        stats["edge_types"][e["edge_type"]] = stats["edge_types"].get(e["edge_type"], 0) + 1

    return {
        "nodes": nodes,
        "edges": formal_edges,
        "all_edges": ref_edges,
        "stats": stats,
    }


def write_dot(graph: dict, path: Path) -> None:
    """Write the graph in GraphViz DOT format."""
    lines = ["digraph dependency_graph {", '  rankdir=LR;', '  node [fontsize=10];']

    for node in graph["nodes"]:
        shape = KIND_SHAPES.get(node["kind"], "ellipse")
        color = CHAPTER_COLORS.get(node["chapter"], "#999999")
        label = f'{node["kind"][0].upper()}.{node["number"]}'
        lines.append(
            f'  "{node["id"]}" [label="{label}", shape={shape}, '
            f'style=filled, fillcolor="{color}40", color="{color}"];'
        )

    for edge in graph["edges"]:
        lines.append(f'  "{edge["source"]}" -> "{edge["target"]}";')

    lines.append("}")
    path.write_text("\n".join(lines), encoding="utf-8")


def write_html(graph: dict, path: Path) -> None:
    """Write an interactive HTML visualization of the graph."""
    nodes_json = json.dumps(graph["nodes"], indent=2)
    edges_json = json.dumps(graph["edges"], indent=2)

    html = f"""<!DOCTYPE html>
<html>
<head>
<title>Butcher ODE Textbook - Dependency Graph</title>
<style>
body {{ font-family: monospace; margin: 20px; background: #1a1a2e; color: #eee; }}
h1 {{ color: #e94560; }}
table {{ border-collapse: collapse; width: 100%; margin-top: 10px; }}
th, td {{ border: 1px solid #444; padding: 6px 10px; text-align: left; }}
th {{ background: #16213e; }}
tr:hover {{ background: #0f3460; }}
.kind-theorem {{ color: #ff6b6b; }}
.kind-definition {{ color: #4ecdc4; }}
.kind-lemma {{ color: #ffe66d; }}
.kind-corollary {{ color: #a8e6cf; }}
.stats {{ display: flex; gap: 20px; flex-wrap: wrap; margin: 20px 0; }}
.stat-card {{ background: #16213e; padding: 15px; border-radius: 8px; min-width: 120px; }}
.stat-value {{ font-size: 24px; font-weight: bold; color: #e94560; }}
.stat-label {{ font-size: 12px; color: #888; }}
#search {{ padding: 8px; width: 300px; background: #16213e; color: #eee; border: 1px solid #444; }}
</style>
</head>
<body>
<h1>Dependency Graph: Butcher's Numerical Methods for ODEs</h1>

<div class="stats" id="stats"></div>

<h2>Search</h2>
<input type="text" id="search" placeholder="Filter by number, kind, or chapter..." oninput="filterTable()">

<h2>Formal Statements ({len(graph['nodes'])} total)</h2>
<table id="nodesTable">
<thead><tr><th>ID</th><th>Kind</th><th>Number</th><th>Ch</th><th>Sec</th><th>Page</th><th>Out</th><th>In</th><th>Proof?</th></tr></thead>
<tbody id="nodesBody"></tbody>
</table>

<h2>Dependencies ({len(graph['edges'])} formal-to-formal edges)</h2>
<table id="edgesTable">
<thead><tr><th>Source</th><th>Target</th><th>Type</th></tr></thead>
<tbody id="edgesBody"></tbody>
</table>

<script>
const nodes = {nodes_json};
const edges = {edges_json};

// Render stats
const stats = document.getElementById('stats');
const kindCounts = {{}};
const chCounts = {{}};
nodes.forEach(n => {{
    kindCounts[n.kind] = (kindCounts[n.kind] || 0) + 1;
    chCounts['Ch' + n.chapter] = (chCounts['Ch' + n.chapter] || 0) + 1;
}});
Object.entries(kindCounts).forEach(([k,v]) => {{
    stats.innerHTML += `<div class="stat-card"><div class="stat-value">${{v}}</div><div class="stat-label">${{k}}s</div></div>`;
}});
stats.innerHTML += `<div class="stat-card"><div class="stat-value">${{edges.length}}</div><div class="stat-label">dependencies</div></div>`;

// Render nodes table
const nodesBody = document.getElementById('nodesBody');
nodes.forEach(n => {{
    const row = `<tr class="kind-${{n.kind}}">
        <td>${{n.id}}</td><td>${{n.kind}}</td><td>${{n.number}}</td>
        <td>${{n.chapter}}</td><td>${{n.section}}</td><td>${{n.page}}</td>
        <td>${{n.out_degree}}</td><td>${{n.in_degree}}</td>
        <td>${{n.has_proof ? 'Y' : ''}}</td></tr>`;
    nodesBody.innerHTML += row;
}});

// Render edges table
const edgesBody = document.getElementById('edgesBody');
edges.forEach(e => {{
    edgesBody.innerHTML += `<tr><td>${{e.source}}</td><td>${{e.target}}</td><td>${{e.edge_type}}</td></tr>`;
}});

function filterTable() {{
    const q = document.getElementById('search').value.toLowerCase();
    document.querySelectorAll('#nodesBody tr').forEach(tr => {{
        tr.style.display = tr.textContent.toLowerCase().includes(q) ? '' : 'none';
    }});
}}
</script>
</body>
</html>"""
    path.write_text(html, encoding="utf-8")


# ── Main driver ────────────────────────────────────────────────────────

def main() -> None:
    print("Phase 4b: Building dependency graph ...")

    GRAPH_DIR.mkdir(parents=True, exist_ok=True)
    graph = build_graph()

    # Write JSON graph
    graph_path = GRAPH_DIR / "dependency_graph.json"
    graph_path.write_text(
        json.dumps(graph, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"  Wrote {graph_path}")

    # Write DOT
    dot_path = GRAPH_DIR / "dependency_graph.dot"
    write_dot(graph, dot_path)
    print(f"  Wrote {dot_path}")

    # Write stats
    stats_path = GRAPH_DIR / "stats.json"
    stats_path.write_text(
        json.dumps(graph["stats"], indent=2),
        encoding="utf-8",
    )
    print(f"  Wrote {stats_path}")

    # Write HTML
    html_path = GRAPH_DIR / "explore.html"
    write_html(graph, html_path)
    print(f"  Wrote {html_path}")

    # Print summary
    s = graph["stats"]
    print(f"\n  Nodes: {s['total_nodes']}")
    print(f"  Formal edges: {s['total_formal_edges']}")
    print(f"  All edges (incl. equations/sections): {s['total_all_edges']}")
    for kind, count in sorted(s["by_kind"].items()):
        print(f"    {kind}: {count}")


if __name__ == "__main__":
    main()
