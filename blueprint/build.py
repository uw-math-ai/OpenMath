#!/usr/bin/env python3
"""Build the blueprint web output with increased recursion limit.

plasTeX can hit Python's default recursion limit (1000) when processing
large documents with deep dependency graphs. This wrapper increases it.

Post-build step: rewrite dependency graph node labels.

Usage:
    python blueprint/build.py                   # default: "NNN[A-Z] Name"
    python blueprint/build.py --label=full      # same as default
    python blueprint/build.py --label=number    # only "NNN[A-Z]"
    python blueprint/build.py --label=name      # only "Name"
"""
import sys
import os
import re
import json
import argparse
from pathlib import Path

sys.setrecursionlimit(10000)

# Parse args BEFORE plasTeX grabs sys.argv
parser = argparse.ArgumentParser()
parser.add_argument("--label", choices=["full", "number", "name"], default="full",
                    help="Graph node label format: full (number+name), number (index only), name (name only)")
args, _ = parser.parse_known_args()

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


# ── Post-build: update dep graph labels ────────────────────────────────

def _sanitize_for_dot(text: str, max_len: int = 30) -> str:
    """Escape text for DOT label; truncate if too long."""
    text = text.replace('"', "'").replace("\\", "")
    if len(text) > max_len:
        text = text[:max_len - 3] + "..."
    return text


def _update_graph_labels(label_mode: str = "full") -> None:
    """Rewrite node labels in the generated dependency graph.

    label_mode:
      - "full":   "NNN[A-Z] Name"  (default, most informative)
      - "number": "NNN[A-Z]"        (compact, like the original index)
      - "name":   "Name"            (semantic, without the index)
    """
    if not DEP_GRAPH_HTML.exists():
        print(f"  (skip label update — {DEP_GRAPH_HTML} not found)")
        return
    if not NAMES_PATH.exists():
        print(f"  (skip label update — {NAMES_PATH} not found)")
        return

    with open(NAMES_PATH) as f:
        raw_names = json.load(f)

    KIND_PREFIX = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}
    names: dict[str, str] = {}
    for key, value in raw_names.items():
        if ":" in key:
            kind, num = key.split(":", 1)
            prefix = KIND_PREFIX.get(kind, kind[:3])
            names[f"{prefix}:{num}"] = value

    html = DEP_GRAPH_HTML.read_text(encoding="utf-8")

    def replacer(m):
        node_id = m.group(1)
        prefix_attrs = m.group(2)  # may be empty or contain color/fillcolor/etc
        orig_label = m.group(3)    # e.g., "101A"
        suffix = m.group(4)        # closing quote + rest
        name = names.get(node_id, "")

        if label_mode == "number":
            return m.group(0)  # No change
        elif label_mode == "name":
            if not name:
                return m.group(0)
            new_label = _sanitize_for_dot(name)
        else:  # "full"
            if not name:
                return m.group(0)
            safe_name = _sanitize_for_dot(name)
            new_label = f"{orig_label} {safe_name}"

        return f'"{node_id}"\t[{prefix_attrs}label="{new_label}"{suffix}'

    # Match: "node_id"\s*[<optional prefix attrs>label="<label>"<rest>
    # Prefix attrs can include color, fillcolor, etc. before label
    pattern = re.compile(
        r'"([a-z]+:\w+)"\s*\[((?:[^\]"]|"[^"]*")*?)label="([^"]+)"([^\]]*)'
    )
    new_html, count = pattern.subn(replacer, html)

    if count:
        DEP_GRAPH_HTML.write_text(new_html, encoding="utf-8")
        print(f"  Updated {count} node labels in dep graph (mode: {label_mode})")
    else:
        print(f"  No node labels matched")


_update_graph_labels(args.label)
