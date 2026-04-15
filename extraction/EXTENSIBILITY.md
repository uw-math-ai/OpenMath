# Extensibility Plan: Adding Entities Outside the Auto-Extraction Pipeline

This document is the **single source of truth** for how to add formal
content to the project that did not (or cannot) come from the automatic
PDF extraction pipeline. It is written for **future agents doing
Lean formalization** — read this before adding any new theorem,
definition, lemma, or helper.

## When to use this

You are formalizing in Lean and you discover **one of two situations**:

| Situation | Example | What to do |
|---|---|---|
| **A. Missed textbook entity** — the auto-extractor failed to capture a theorem/definition/lemma/corollary that appears in Butcher | "I'm proving `thm:212A` and it cites `Theorem 235B`, but `entities/thm_235B.json` doesn't exist" | §2 — add to `extensions/missing_statements.json` |
| **B. New helper for formalization** — you need a lemma/definition that is NOT in Butcher but is genuinely useful for the Lean proof, possibly reusable | "I need a Grönwall-type bound to close `thm:212A`" | §3 — add to `extensions/helper_entities.json` |

If neither fits — STOP. Do not invent textbook entities; do not save
single-use scaffolding to extensions. Helpers must be **reusable**.

## Invariants (these never change)

1. **Auto-extracted JSONs in `raw_text/` are regenerated on every pipeline
   run.** Never hand-edit them — your edits will vanish.
2. **All hand-written content lives in `extraction/extensions/`.**
   This directory is the only place that survives extraction re-runs.
3. **IDs in `entities/` are globally unique.** Auto-extracted IDs use
   Butcher numbering (`thm:NNNX`); helpers use the `aux:` prefix.
4. **Phase 8 (`build_formalization_data.py`) is the merge point.** It
   reads auto-extracted data + `extensions/*` and produces the unified
   per-entity view that workers consume.
5. **Cycle-breaking and topological sort run on the merged graph**, so
   helpers and missing statements are first-class citizens of the
   formalization queue.

## File layout (after implementation)

```
extraction/
├── extensions/                   # ALL hand-curated content lives here
│   ├── README.md                 # Brief pointer back to this file
│   ├── missing_statements.json   # Textbook entities the extractor missed
│   ├── helper_entities.json      # Lean-side helpers (aux: prefix)
│   └── extra_references.json     # Manual dependency edges
└── formalization_data/           # Generated; do not hand-edit
    └── entities/
        ├── thm_NNNX.json         # textbook (auto + missing)
        └── aux_<slug>.json       # helpers
```

## §1 ID conventions

| Prefix | Use for | Number/slug format | Example |
|---|---|---|---|
| `thm:` `def:` `lem:` `cor:` with **Butcher number** | Textbook entities (auto OR missing) | `<3-digit subsection><uppercase letter>` | `thm:235B`, `def:381A` |
| `aux:` | Lean-side helpers (NOT in Butcher) | `<snake_case_slug>` | `aux:gronwall_exp_bound`, `aux:lipschitz_pos_constant` |

**Slug rules for helpers:**
- snake_case, lowercase only, ASCII
- 3-50 characters
- Descriptive: `gronwall_exp_bound`, NOT `helper1` or `lemma_a`
- Unique across all helpers — check `entities/` first

The filename derives mechanically: `entities/aux_gronwall_exp_bound.json`.

## §2 Recipe: Add a missing textbook entity

**Step 1.** Confirm it's actually in Butcher's textbook. Open the PDF
(or grep `raw_text/full_text.txt`) and verify the page number, the
exact statement, and any proof.

**Step 2.** Open `extraction/extensions/missing_statements.json` and
append a new object to the array:

```json
{
  "kind": "theorem",
  "number": "235B",
  "chapter": 2,
  "section": "23",
  "subsection": "235",
  "page": 119,
  "text": "Theorem 235B Suppose that... [exact textbook wording]",
  "proof_text": "Proof. ... [exact textbook wording, or empty if proof is omitted]",
  "introduces": [],
  "name": "Order conditions for explicit fourth-order RK",
  "statement_latex": "\\begin{theorem}\nSuppose that...\n\\end{theorem}",
  "proof_latex": "\\begin{proof}\n...\n\\end{proof}",
  "context_latex": "\\paragraph{Context}\n...",
  "variables": [{"name": "...", "definition": "..."}],
  "equations": [{"tag": "235a", "content": "..."}],
  "preamble": "Brief setup paragraph"
}
```

Required fields: `kind`, `number`, `chapter`, `section`, `subsection`,
`text`. Everything else is optional but strongly recommended (the more
you provide, the less the next agent has to dig up).

**Step 3.** If the new entity references other entities (or is referenced
BY others), add edges in `extensions/extra_references.json`:

```json
[
  {"source": "thm:235B", "target": "def:230A", "edge_type": "uses_definition", "context": "manual"},
  {"source": "thm:236A", "target": "thm:235B", "edge_type": "uses_theorem", "context": "manual"}
]
```

**Step 4.** Rebuild Phase 8:

```bash
cd extraction && python -m pipeline.build_formalization_data
```

**Step 5.** Verify:

```bash
ls formalization_data/entities/thm_235B.json   # exists
python -c "import json; d=json.load(open('formalization_data/entities/thm_235B.json')); print(d['name'], len(d['dependencies']))"
```

The new entity is now in `index.json`, `topo_order.json`, the chapter
view, and `lean_status.json` (as `unformalized` placeholder).

## §3 Recipe: Add a helper entity invented for formalization

Use this ONLY when:
- The helper is needed in Lean but is NOT in Butcher's textbook, AND
- The helper is **reusable** — at least two distinct theorems will use
  it, OR it formalizes a generally-useful concept.

For one-off scaffolding inside a single proof, just put a `private` lemma
in the Lean file. Don't spam the extensions directory.

**Step 1.** Pick a slug (see §1 rules) and a kind (`theorem`,
`definition`, `lemma`, or `corollary`).

**Step 2.** Open `extraction/extensions/helper_entities.json` and append:

```json
{
  "kind": "lemma",
  "number": "gronwall_exp_bound",
  "name": "Grönwall exponential bound",
  "motivation": "Needed for thm:212A global error bound; reusable for any Lipschitz-bound recursion. Adds a stand-alone library lemma.",
  "statement_latex": "\\begin{lemma}\nLet $\\alpha:[a,b]\\to\\mathbb{R}_{\\ge 0}$ ... then $\\alpha(x)\\le E(x)\\exp(L(x-a))$.\n\\end{lemma}",
  "proof_latex": "\\begin{proof}\n... (informal mathematical proof)\n\\end{proof}",
  "preamble": "Stand-alone analysis lemma; no Butcher-specific context.",
  "variables": [
    {"name": "L", "definition": "Lipschitz constant, real and nonnegative"},
    {"name": "α", "definition": "nonnegative function on [a,b]"}
  ],
  "equations": [],
  "introduces": ["Grönwall's inequality"]
}
```

Required: `kind`, `number` (the slug), `name`, `motivation`,
`statement_latex`. Recommended: everything else.

**Note on fields:** unlike textbook entries, helpers have no
`chapter`/`section`/`subsection`/`page` — Phase 8 sets these to `null`.
The build script also sets `subsection_title` to empty.

**Step 3.** If the helper depends on other entities (or is used by
existing entities), add edges in `extensions/extra_references.json`:

```json
[
  {"source": "thm:212A", "target": "aux:gronwall_exp_bound", "edge_type": "uses_lemma", "context": "manual"},
  {"source": "aux:gronwall_exp_bound", "target": "def:110A", "edge_type": "uses_concept", "context": "manual"}
]
```

**Step 4.** Rebuild and verify (same as §2 step 4-5).

The helper now appears in `entities/aux_gronwall_exp_bound.json`,
the dependency graph, and the formalization queue. Tier-0 grows if the
helper has no deps.

## §4 Editing `lean_status.json`

When you finish formalizing an entity in Lean, update **only** the
relevant row in `formalization_data/lean_status.json`:

```json
"thm:212A": {
  "lean_file": "OpenMath/EulerConvergence.lean",
  "lean_symbol": "EulerConvergence.global_error_bound",
  "status": "done"
}
```

Status values: `unformalized` | `in_progress` | `done`.

This file is preserved across `build_formalization_data.py` re-runs
(the build only adds rows for new IDs, never overwrites populated ones).

## §5 Build pipeline behavior

For agents adding entities — you don't run any of this manually; just
re-run Phase 8 (`python -m pipeline.build_formalization_data`) after
editing `extensions/*.json`. Here's what happens internally:

1. Load auto-extracted statements + auto edges from `raw_text/`.
2. Load `extensions/missing_statements.json`; **fail loudly** on ID
   collision with auto-extracted IDs (means re-extraction now covers it
   — delete the manual entry) or duplicate manual entries.
3. Load `extensions/helper_entities.json`; **fail loudly** on invalid
   slug, duplicate slug, or collision with auto-extracted ID.
4. Load `extensions/extra_references.json`; append to the edge pool.
   Targets that name unknown IDs are kept in the file but **warn** at
   build time and dropped from the per-entity dependency view (so
   forward-references to entities you'll add later don't crash the build).
5. Re-run cycle-breaking on the merged graph by calling
   `break_cycles.break_cycles(edges, page_map)`. Helpers without a page
   default to page 0 for the page-distance heuristic. The resulting
   audit log is written to `formalization_data/cycles_removed_merged.json`
   (the auto-only `raw_text/cycles_removed.json` from Phase 4c is also
   preserved as the pre-extension snapshot).
6. Compute transitive closure, topological tiers, and write all
   output files. Helpers (chapter=None) are excluded from
   `by_chapter/*.json` but appear in `index.json`, `topo_order.json`,
   `entities/*.json`, and `lean_status.json`.
7. `lean_status.json` rows for entities that no longer exist (e.g.
   you deleted a helper) are dropped, with a notice on stdout.

## §6 Blueprint integration

The LaTeX blueprint (`blueprint/src/`) currently renders only Butcher
chapters. Helpers should still appear in the blueprint so the dep graph
is complete and the rendered web has them.

Plan: `pipeline/generate_blueprint.py` adds a final chapter
**"Auxiliary Results"** to the blueprint, listing all `aux:*` entities
ordered by dependency tier. Each gets its own `\begin{lemma}\label{...}`
block with `\uses{...}` reflecting its dependencies. Missing-statement
additions slot into their normal Butcher chapter (no blueprint change
needed beyond Phase 8 picking them up).

## §7 Don'ts

- **Don't edit files in `raw_text/`.** They get clobbered.
- **Don't edit files in `formalization_data/entities/`.** They get
  regenerated. Edit the source in `extensions/` and re-run Phase 8.
- **Don't reuse a Butcher number for a helper.** Use `aux:<slug>`.
- **Don't add to extensions for one-off proof scaffolding.** Use
  `private` Lean lemmas.
- **Don't skip `motivation` for helpers.** Future agents need to know
  whether to reuse an existing helper or write a new one. Vague
  motivations lead to duplicate helpers.
- **Don't claim a helper exists when it doesn't.** Before adding
  `aux:gronwall_exp_bound`, grep `entities/aux_*.json` for similar
  names — the helper you want may already exist.

## §8 Quick checklist for agents

```
[ ] Identified the situation: Missed textbook entity (§2) or new helper (§3)?
[ ] For helpers: confirmed reusability — at least two callers, or genuinely
    library-quality. Not single-use scaffolding.
[ ] For missing textbook: confirmed it's actually in the PDF with page number.
[ ] Picked the right ID prefix (thm/def/lem/cor for textbook; aux for helpers).
[ ] For helpers: chose a descriptive snake_case slug, checked it doesn't
    already exist in entities/.
[ ] Added the JSON entry to the right extensions/*.json file with all
    required fields.
[ ] Added dependency edges to extensions/extra_references.json if relevant.
[ ] Ran `python -m pipeline.build_formalization_data` and confirmed the new
    entity file exists in formalization_data/entities/.
[ ] When the Lean proof lands, updated lean_status.json with file/symbol/status.
```

## Implementation status

| Step | Status |
|---|---|
| `extraction/extensions/` directory + empty placeholders + `README.md` | DONE |
| `build_formalization_data.py` loads, validates, merges extensions | DONE |
| Re-runs cycle-breaking on the merged graph (imports `break_cycles.break_cycles`) | DONE |
| Per-entity records carry `is_helper` flag, `motivation` field for helpers | DONE |
| `lean_status.json` placeholders for new entities; drops rows for vanished entities | DONE |
| `generate_blueprint.py` "Auxiliary Results" chapter for `aux:*` entities | TODO — see §6 |
| `CLAUDE.md` pointer to this file | DONE |

The extension workflow is **active**. Add entries to
`extensions/missing_statements.json` or `extensions/helper_entities.json`,
re-run Phase 8, and they appear in `formalization_data/`. Blueprint
rendering of helpers is the only remaining piece.
