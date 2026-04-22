# Formalization Data Guide — Reading the Extracted Butcher Content

This file is the **consumer-side guide** for the formalization agent: how to
read the extracted data, navigate the dependency graph, choose a sensible
processing order, and run sanity checks. Workflow design (when to use
Aristotle, sorry-first discipline, status reporting, etc.) is intentionally
out of scope and will be wired separately.

Source: *Numerical Methods for Ordinary Differential Equations*, J. C.
Butcher (Wiley, 2016). 175 entities + structured context + a cleaned
dependency graph in `extraction/formalization_data/`.

The companion documents under `extraction/`:
- [`formalization_data/README.md`](formalization_data/README.md) — **canonical schema spec** (one row per field). Read alongside this guide whenever you need exact field types.
- [`EXTENSIBILITY.md`](EXTENSIBILITY.md) — how to **edit** the data (add missing entities, helpers, fix wrong dep edges).
- [`CLAUDE.md`](CLAUDE.md) — dispatch document for any agent landing in `extraction/`.

---

## §1 File layout

```
extraction/formalization_data/
├── README.md                    # canonical schema spec (read for field types)
├── entities/<id>.json           # one self-contained file per entity (175)
├── index.json                   # flat scannable list (one row per entity)
├── topo_order.json              # dependency-respecting linear order + Kahn tiers
├── by_chapter/ch0N.json         # chapter → section → subsection → entity ids
├── lean_status.json             # editable mapping id → {lean_file, lean_symbol, status}
├── references_final.json        # the full edge list after denylist + cycle-break
└── cycles_removed_merged.json   # audit log of edges dropped to break cycles
```

Source data (do **not** read these directly — they're producer files,
already joined into `entities/`):

```
extraction/raw_text/
├── formal_statements.json       # raw text + introduces field
├── formal_statements_latex.json # cleaned LaTeX bodies
├── statement_context.json       # variables, equations, preamble (structured)
├── context_latex.json           # the surrounding "Context" paragraph
├── statement_names.json         # display names (homonym-disambiguated)
└── references_merged.json       # raw edges (pre-denylist; usually skip this)
```

---

## §2 The per-entity record (`entities/<id>.json`)

Each entity is a single self-contained JSON file. One `json.load()` and you
have everything needed to understand the statement, prove it, and locate
its dependencies — no extra files to consult for the "primary" context.

```python
import json, pathlib
ROOT = pathlib.Path("extraction/formalization_data")
ent = json.loads((ROOT / "entities" / "thm_110C.json").read_text())
```

The fields fall into four categories:

- **Identity & location** (`id`, `kind`, `number`, `name`, `chapter`,
  `section`, `subsection`, `subsection_title`, `page`) — answer "what is
  this and where in Butcher does it live". The `name` field is
  homonym-disambiguated (e.g. `"convergent (matrix)"` for `def:142B`,
  `"convergent (LMM)"` for `def:402A`).
- **Content** (`statement_text` / `statement_latex`, `proof_text` /
  `proof_latex`, `context_latex`, `preamble`, `variables`, `equations`,
  `introduces`) — the actual mathematical material. Always prefer the
  `*_latex` fields over the `*_text` fields (which carry pdftotext noise).
  `introduces` lists *qualified* concepts this entity defines (e.g.
  `["convergent matrix (spectral radius)"]` rather than bare `"convergent"`).
- **Dependency-graph fields** (`dependencies`, `transitive_dependencies`,
  `dependents`) — see §3.
- **Lean status snapshot** (`lean_file`, `lean_symbol`,
  `formalization_status`) — read-only mirror of `lean_status.json`. Phase 8
  refreshes this on every build; trust `lean_status.json` if the two ever
  disagree.

**For the field-by-field schema (types, sources, edge_type vocabulary)
see [`formalization_data/README.md`](formalization_data/README.md).**

### Worked example: `thm:110C` (Picard–Lindelöf existence and uniqueness)

```python
>>> ent = json.loads((ROOT / "entities" / "thm_110C.json").read_text())
>>> ent["name"]
'Existence and uniqueness of solutions'
>>> ent["chapter"], ent["page"]
(1, 44)
>>> ent["statement_latex"][:80]
'\\begin{theorem}\nConsider an initial value problem ...'
>>> [d["id"] for d in ent["dependencies"]]
['def:110A', 'lem:110B']
>>> ent["transitive_dependencies"]
['def:110A', 'lem:110B']
>>> ent["dependents"]
['lem:319A', 'thm:111A']
>>> ent["formalization_status"]
'unformalized'
```

`statement_latex` + `proof_latex` give you the spec. `dependencies` tells
you what to import / reuse from prior Lean proofs. `context_latex` and
`preamble` give surrounding setup that is often essential for unambiguously
restating the theorem in Lean.

---

## §3 Navigating the dependency graph

The three graph fields on each entity:

- `dependencies` — direct deps as full records `{id, kind, number, name, edge_type, context}`. Use `edge_type` to gauge confidence: regex (`uses_theorem` / `uses_definition` / `uses_lemma` / `uses_corollary`), concept (`uses_concept`), and equation-owner (`uses_equation_from`) edges are deterministic; `llm_dependency` is DeepSeek-inferred and lower confidence; `uses` is the manual catch-all from extension files. Hand-curated edges have `context: "manual"`.
- `transitive_dependencies` — flattened closure (just IDs). Useful for "is this entity ready to formalize?" checks.
- `dependents` — reverse edges. Useful for "what breaks if I change this?".

For the canonical edge-type vocabulary see
[`formalization_data/README.md`](formalization_data/README.md). For
**fixing** a wrong or missing edge, see
[`EXTENSIBILITY.md`](EXTENSIBILITY.md) §4.

---

## §4 Other indexed views

### `index.json` — scannable overview

A flat list, one compact row per entity. Useful for filtering or counting
without opening 175 files.

```python
index = json.loads((ROOT / "index.json").read_text())
# Each row: id, name, kind, chapter, subsection, page, n_deps,
#           n_dependents, has_proof, lean_file, formalization_status
unformalized_ch3 = [e for e in index
                    if e["chapter"] == 3 and e["formalization_status"] == "unformalized"]
```

### `topo_order.json` — dependency-respecting order

Provides both a flat `order` (linear topological sort) and `tiers` (Kahn's
algorithm levels — entities in tier `k` depend only on tiers `0..k-1`).

```python
topo = json.loads((ROOT / "topo_order.json").read_text())
flat_order = topo["order"]              # 175 ids, deps before users
ready_now  = topo["tiers"][0]["ids"]    # ~17 entities with zero deps
```

The flat `order` is **chapter-agnostic** — it freely interleaves Ch.1
through Ch.5 by dependency.

### `by_chapter/ch0N.json` — hierarchical view

Chapter → section → subsection → entity-ids tree, using
`pipeline.config.SUBSECTION_TITLES` for the section/subsection labels.
Helpers (`chapter == null`) are NOT in this view; for them, use
`index.json` filtered by `is_helper`.

```python
ch3 = json.loads((ROOT / "by_chapter/ch03.json").read_text())
for sect in ch3["sections"]:
    for subsec in sect["subsections"]:
        print(subsec["subsection"], subsec["entities"])
```

### `references_final.json` — final edge list

The full edge set after `extensions/removed_references.json` is applied,
manual additions are merged, and cycle-breaking has run on the
extension-merged graph. Use this when you want to walk edges directly
(`generate_blueprint.py` reads it). Most consumers can stay inside the
per-entity `dependencies` / `transitive_dependencies` fields and never
touch this file.

`raw_text/references_merged.json` is the **pre-denylist** edge set —
historical/debugging only. **Don't read it for live use.**

---

## §5 Order to consume entities

Use the topological data in `topo_order.json`. The graph is a DAG with two
slight caveats:

### §5.1 Cross-chapter forward edges — exactly 3

The graph contains exactly **3 edges where source is in an earlier chapter
than target**, all from one entity:

| from | to | reason |
|---|---|---|
| `thm:243A` (Ch.2) | `def:402A` (Ch.4) | Butcher previews "convergent LMM" in Ch.2 |
| `thm:243A` (Ch.2) | `def:403A` (Ch.4) | Butcher previews "stable LMM" in Ch.2 |
| `thm:243A` (Ch.2) | `def:404B` (Ch.4) | Butcher previews "consistent LMM" in Ch.2 |

These are mathematically correct — Butcher states the equivalence theorem
in Ch.2 as a preview before formally defining its terms in Ch.4. They are
NOT in the denylist.

If you process strictly chapter by chapter (Ch.1 → Ch.5), **defer
`thm:243A` from Ch.2 until the end of Ch.4** — by then its three
dependencies are available.

The `topo_order.json` flat order naturally places `thm:243A` after its
deps, so consuming entities by topo position rather than by chapter
trivially handles this.

### §5.2 Intra-chapter forward references — 91 edges

Within a chapter, some statements reference higher-numbered subsections
(e.g. `def:356A` references `thm:356C`). This is normal in Butcher's
writing style — a definition may forward-reference a theorem that follows
in the same sub-topic. **Use `topo_order.json` position within the
chapter, not Butcher number, when you need an in-chapter order.**

### §5.3 Helpers (`aux:*`) have no chapter

Helpers added via `extensions/helper_entities.json` (currently 0 of them,
but the mechanism is live) have `chapter == null`. They do NOT appear in
any `by_chapter/` file. They appear in `index.json`, `topo_order.json`,
and `entities/`, and their `transitive_dependencies` field tells you when
they become consumable.

### §5.4 Tier structure (current snapshot)

13 tiers total. Tier 0 (zero formal dependencies) has 17 entities
distributed across Ch.1, Ch.3, Ch.4, Ch.5. Each subsequent tier depends
only on lower-numbered tiers. Run this to get current numbers:

```python
import collections
topo = json.loads((ROOT / "topo_order.json").read_text())
for i, t in enumerate(topo["tiers"]):
    by_ch = collections.Counter(e.split(":",1)[1][0] for e in t["ids"])
    print(f"Tier {i}: {len(t['ids'])} entities, chapters {dict(sorted(by_ch.items()))}")
```

---

## §6 `lean_status.json` — the editable progress map

```json
{
  "thm:101A": {"lean_file": null, "lean_symbol": null, "status": "unformalized"},
  "def:110A": {"lean_file": "OpenMath/Lipschitz.lean",
               "lean_symbol": "Lipschitz.condition",
               "status": "done"},
  ...
}
```

- Keys are entity IDs in short form (`thm:NNNX`, `def:NNNX`, `aux:<slug>`).
- `status`: `"unformalized"` | `"in_progress"` | `"done"`.
- `lean_file` / `lean_symbol`: `null` until the entity is formalized.

This is the **only** file in `formalization_data/` that the formalization
side edits. It is **preserved across Phase 8 re-runs** — the build only
adds rows for newly-introduced entities and drops rows for entities that
vanished. Populated rows are never overwritten.

The same mapping is mirrored read-only into each `entities/<id>.json`'s
`lean_file` / `lean_symbol` / `formalization_status` fields. Always trust
`lean_status.json` if the two ever disagree (they shouldn't — Phase 8 keeps
them in sync).

---

## §7 Extending the data (when extraction got something wrong)

If during formalization you discover the extracted data is wrong — missed
entity, wrong dep edge, missing dep edge, or you need a reusable Lean-side
helper — the fix lives in `extraction/extensions/`. Read
[`EXTENSIBILITY.md`](EXTENSIBILITY.md) for the recipes. Quick map:

| Situation | File | EXTENSIBILITY § |
|---|---|---|
| Butcher has a theorem we missed | `extensions/missing_statements.json` | §2 |
| Need a reusable Lean helper not in Butcher | `extensions/helper_entities.json` | §3 |
| Graph missing a real dependency edge | `extensions/extra_references.json` | §4.1 |
| Graph has a wrong dependency edge | `extensions/removed_references.json` | §4.2 |

After editing any of the above, re-run from `extraction/`:

```bash
python -m pipeline.build_formalization_data
```

This regenerates `entities/*.json`, `index.json`, `topo_order.json`,
`by_chapter/*.json`, and `references_final.json`. Your `lean_status.json`
edits are preserved.

---

## §8 Sanity checks

Run anytime to confirm the data is internally consistent:

```bash
# Topological order is valid — every dep precedes its user.
python -c "
import json, pathlib
ROOT = pathlib.Path('extraction/formalization_data')
topo = json.load(open(ROOT/'topo_order.json'))
pos = {i: n for n, i in enumerate(topo['order'])}
for p in (ROOT/'entities').glob('*.json'):
    e = json.load(open(p))
    for d in e['transitive_dependencies']:
        assert pos.get(d, -1) < pos[e['id']], f'{e[\"id\"]} precedes dep {d}'
print('topo order valid')
"

# Forward cross-chapter edges should be exactly 3 (thm:243A → Ch.4 deps).
python -c "
import json
def ch(s): return int(s.split(':')[1][0]) if ':' in s and s.split(':')[1][0].isdigit() else None
edges = json.load(open('extraction/formalization_data/references_final.json'))
fwd = [e for e in edges if ch(e['source']) and ch(e['target']) and ch(e['target']) > ch(e['source'])]
assert len(fwd) == 3 and all(e['source']=='thm:243A' for e in fwd), fwd
print('forward cross-chapter edges: 3, all from thm:243A')
"

# Total entity count and chapter distribution.
python -c "
import json, collections
index = json.load(open('extraction/formalization_data/index.json'))
print('total entities:', len(index))
print('by chapter:', dict(collections.Counter(e['chapter'] for e in index)))
"
```

If any check fails, the extraction data is in an inconsistent state —
re-run Phase 8 (`python -m pipeline.build_formalization_data`) before
formalizing on top of it.
