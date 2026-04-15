#!/usr/bin/env python3
"""Build the blueprint web output with increased recursion limit.

plasTeX can hit Python's default recursion limit (1000) when processing
large documents with deep dependency graphs. This wrapper increases it.

Post-build step: rewrite dependency graph node labels to include the
statement's informal name (e.g., "101A\\nThe Kepler problem").

Usage: python blueprint/build.py
"""
import sys
import os
import re
import json
from pathlib import Path

sys.setrecursionlimit(10000)

# Ensure TeX is on PATH
tex_path = "/usr/local/texlive/2026basic/bin/universal-darwin"
if os.path.isdir(tex_path):
    os.environ["PATH"] = tex_path + ":" + os.environ.get("PATH", "")

# Paths
BLUEPRINT_DIR = Path(__file__).parent
PROJECT_ROOT = BLUEPRINT_DIR.parent
NAMES_PATH = PROJECT_ROOT / "extraction" / "raw_text" / "statement_names.json"
DEP_GRAPH_HTML = BLUEPRINT_DIR / "web" / "dep_graph_document.html"

# Run plasTeX
os.chdir(BLUEPRINT_DIR / "src")
from plasTeX.client import plastex
sys.argv = ["plastex", "-c", "plastex.cfg", "web.tex"]
plastex()


# ── Post-build: update dep graph labels with names ─────────────────────

def _sanitize_for_dot(text: str, max_len: int = 30) -> str:
    """Escape text for DOT label; truncate if too long."""
    # Remove quotes and backslashes that would break DOT
    text = text.replace('"', "'").replace("\\", "")
    if len(text) > max_len:
        text = text[:max_len - 3] + "..."
    return text


def _update_graph_labels() -> None:
    """Rewrite node labels in the generated dependency graph to include names."""
    if not DEP_GRAPH_HTML.exists():
        print(f"  (skip label update — {DEP_GRAPH_HTML} not found)")
        return
    if not NAMES_PATH.exists():
        print(f"  (skip label update — {NAMES_PATH} not found)")
        return

    with open(NAMES_PATH) as f:
        raw_names = json.load(f)

    # Convert "theorem:101A" -> "thm:101A" to match graph node ids
    KIND_PREFIX = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}
    names: dict[str, str] = {}
    for key, value in raw_names.items():
        if ":" in key:
            kind, num = key.split(":", 1)
            prefix = KIND_PREFIX.get(kind, kind[:3])
            names[f"{prefix}:{num}"] = value

    html = DEP_GRAPH_HTML.read_text(encoding="utf-8")

    # The DOT graph is embedded in a .renderDot(`...`) call. Labels are like:
    #   "thm:101A"	[label="101A", shape=ellipse];
    # We want to change to:
    #   "thm:101A"	[label="101A\\nThe Kepler problem", shape=ellipse];
    #
    # The node.id format is "kind:NNN[A-Z]" matching our names_map keys.

    def replacer(m):
        node_id = m.group(1)          # e.g., "thm:101A"
        orig_label = m.group(2)        # e.g., "101A"
        # Look up name
        name = names.get(node_id, "")
        if not name:
            return m.group(0)  # No change
        safe_name = _sanitize_for_dot(name)
        # Prefix with the number+letter (e.g., "101A The Kepler problem")
        new_label = f"{orig_label} {safe_name}"
        return f'"{node_id}"\t[label="{new_label}"'

    # Pattern: "<kind>:<number>"	[label="<orig_label>"
    pattern = re.compile(r'"([a-z]+:\w+)"\s*\[label="([^"]+)"')
    new_html, count = pattern.subn(replacer, html)

    if count:
        DEP_GRAPH_HTML.write_text(new_html, encoding="utf-8")
        print(f"  Updated {count} node labels in dep graph")
    else:
        print(f"  No node labels matched (pattern may need adjustment)")


_update_graph_labels()
