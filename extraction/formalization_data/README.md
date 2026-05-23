# `formalization_data/` — formalization-ready view of extraction outputs

> **Reading the data?** For navigation, chapter ordering, the `thm:243A`
> Ch.2→Ch.4 deferral rule, and worked examples, start with
> [`../FORMALIZATION_DATA_GUIDE.md`](../FORMALIZATION_DATA_GUIDE.md).
> **This file is the schema spec** — the exact field types and sources.

This directory is the **single canonical, per-entity, easy-to-load** view of
all 175 formal statements extracted from Butcher's textbook. It is designed
for downstream consumers (Lean formalization workers, planners, dashboards)
that need everything-for-one-theorem in one `json.load`.

Built by `extraction/pipeline/build_formalization_data.py` (Phase 8). All
files except `lean_status.json` are **regenerated** on each pipeline run.

## Layout

```
formalization_data/
├── README.md            (this file)
├── index.json           — compact list of all 175 entities, scannable
├── topo_order.json      — formalization-ready ordering with tiers
├── entities/            — one JSON file per entity, self-contained
│   ├── thm_101A.json
│   ├── def_110A.json
│   └── ...
├── by_chapter/          — chapter/section/subsection-grouped index
│   ├── ch01.json
│   └── ...
└── lean_status.json     — editable; preserved across re-runs
```

## ID convention

`<prefix>:<number>` everywhere, where `prefix ∈ {thm, def, lem, cor}` and
`number` is Butcher's 3-digit-subsection + uppercase-letter (e.g.,
`thm:110C`, `def:381A`).

Filenames replace the colon with underscore: `entities/thm_110C.json`
(colons break Windows tooling and URL parsing).

## `entities/<id>.json` schema

Everything needed to formalize one theorem in Lean:

```json
{
  "id": "thm:110C",
  "kind": "theorem",
  "number": "110C",
  "name": "Existence and uniqueness of solutions",
  "chapter": 1,
  "section": "11",
  "subsection": "110",
  "subsection_title": "Existence and uniqueness of solutions",
  "page": 44,

  "statement_text": "Consider an initial value problem ...",
  "statement_latex": "\\begin{theorem}...\\end{theorem}",
  "proof_text": "Proof. Let M denote ...",
  "proof_latex": "\\begin{proof}...\\end{proof}",
  "context_latex": "\\paragraph{Context} ...",

  "variables": [{"name": "f", "definition": "..."}],
  "equations": [{"tag": "110a", "content": "y'(x) = f(x, y(x))"}],
  "preamble": "Initial value problem ...",
  "introduces": [],

  "dependencies": [
    {"id": "def:110A", "kind": "definition", "number": "110A",
     "name": "Lipschitz condition in its second variable",
     "edge_type": "uses_concept",
     "context": "lipschitz condition in its second variable"},
    {"id": "lem:110B", "kind": "lemma", "number": "110B",
     "name": "Contraction Mapping Fixed Point Existence",
     "edge_type": "llm_dependency", "context": "..."}
  ],
  "transitive_dependencies": ["def:110A", "lem:110B"],
  "dependents": ["lem:319A", "thm:111A"],

  "lean_file": null,
  "lean_symbol": null,
  "formalization_status": "unformalized"
}
```

Field meanings:

| Field | Source |
|---|---|
| `statement_text` / `proof_text` | `raw_text/formal_statements.json` |
| `statement_latex` / `proof_latex` | `raw_text/formal_statements_latex.json` (split apart on `\begin{proof}`) |
| `context_latex` | `raw_text/context_latex.json` |
| `variables`, `equations`, `preamble` | `raw_text/statement_context.json` |
| `name`, `subsection_title` | `raw_text/statement_names.json`, `pipeline.config.SUBSECTION_TITLES` |
| `dependencies` | direct edges in `raw_text/references_merged.json` |
| `transitive_dependencies` | DFS closure of `dependencies` |
| `dependents` | reverse edges (entities that list this one as a dep) |
| `lean_file`, `lean_symbol`, `formalization_status` | `lean_status.json` (initially placeholders) |

`edge_type` values include `uses_concept`, `uses_theorem`, `uses_definition`,
`uses_lemma`, `uses_corollary`, `uses_equation_from`, `llm_dependency`.

## `index.json`

Compact list (one row per entity). Use to enumerate without loading 175
per-entity files. Schema:

```json
{"id": "thm:101A", "name": "...", "kind": "theorem",
 "chapter": 1, "section": "10", "subsection": "101", "page": 26,
 "n_deps": 0, "n_dependents": 0, "has_proof": true,
 "lean_file": null, "formalization_status": "unformalized"}
```

## `topo_order.json`

```json
{
  "order": ["def:110A", "thm:101A", ...],   // valid topological order
  "tiers": [
    {"tier": 0, "ids": [...], "description": "No formal dependencies"},
    {"tier": 1, "ids": [...], "description": "Depends only on tiers 0..0"},
    ...
  ]
}
```

A planner should never assign tier-k work before tier-(k-1) is done. The
graph is cycle-free thanks to `pipeline/break_cycles.py` (Phase 4c).

## `by_chapter/ch0N.json`

Hierarchical chapter → section → subsection → [entity IDs] view, with
section/subsection titles.

## `lean_status.json` — editable, preserved across runs

```json
{
  "thm:101A": {"lean_file": null, "lean_symbol": null, "status": "unformalized"},
  ...
}
```

Status values: `"unformalized"`, `"in_progress"`, `"done"`.

The pipeline **never** auto-detects a mapping from extraction IDs to
existing `OpenMath/*.lean` files (the Lean-side layout is expected to
evolve). When a worker formalizes an entity, it should edit this file
directly. Re-running Phase 8 preserves all populated rows and only adds
placeholder rows for newly-extracted entities.

## Consuming this data

```python
import json, pathlib
from pathlib import Path

ROOT = Path("extraction/formalization_data")

# Load everything quickly
index = json.loads((ROOT / "index.json").read_text())
topo  = json.loads((ROOT / "topo_order.json").read_text())

# Get one entity
ent = json.loads((ROOT / "entities" / "thm_110C.json").read_text())

# Get the formalization queue (tier-0 first)
ready_now = topo["tiers"][0]["ids"]
```
