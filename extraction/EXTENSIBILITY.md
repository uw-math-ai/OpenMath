# Extensibility Plan: Adding Entities Outside the Auto-Extraction Pipeline

This document is the **single source of truth** for how to add formal
content to the project that did not (or cannot) come from the automatic
PDF extraction pipeline. It is written for **future agents doing
Lean formalization** — read this before adding any new theorem,
definition, lemma, or helper.

## When to use this

You are formalizing in Lean and you discover **one of three situations**:

| Situation | Example | What to do |
|---|---|---|
| **A. Missed textbook entity** — the auto-extractor failed to capture a theorem/definition/lemma/corollary that appears in Butcher | "I'm proving `thm:212A` and it cites `Theorem 235B`, but `entities/thm_235B.json` doesn't exist" | §2 — add to `extensions/missing_statements.json` |
| **B. New helper for formalization** — you need a lemma/definition that is NOT in Butcher but is genuinely useful for the Lean proof, possibly reusable | "I need a Grönwall-type bound to close `thm:212A`" | §3 — add to `extensions/helper_entities.json` |
| **C. Wrong or missing dependency edge** — an auto-derived edge is mathematically wrong (LLM hallucination, homonym mis-target, parallel concepts) OR a legitimate reference is missing from the graph | "`thm:111A` (Ch.1) is listed as depending on `def:520A` (Ch.5), but they're unrelated" (drop) • "My proof cites `def:110A` but the graph has no edge" (add) | §4 — edit `extensions/extra_references.json` (add) or `extensions/removed_references.json` (remove) |

If none fit — STOP. Do not invent textbook entities; do not save
single-use scaffolding to extensions; do not tweak the graph as a
matter of taste. Helpers must be **reusable**; edge edits must be
**mathematically justified**.

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
├── extensions/                    # ALL hand-curated content lives here
│   ├── README.md                  # Brief pointer back to this file
│   ├── missing_statements.json    # Textbook entities the extractor missed  [§2]
│   ├── helper_entities.json       # Lean-side helpers (aux: prefix)         [§3]
│   ├── extra_references.json      # Manually-added dependency edges         [§4.1]
│   └── removed_references.json    # Manually-denied (auto) dependency edges [§4.2]
└── formalization_data/            # Generated; do not hand-edit
    ├── entities/
    │   ├── thm_NNNX.json          # textbook (auto + missing)
    │   └── aux_<slug>.json        # helpers
    └── references_final.json      # post-denylist, post-cycle-break edges
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
BY others), add edges per [§4.1](#41-add-an-edge-extra_referencesjson). Short
example:

```json
// extensions/extra_references.json
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
existing entities), add edges per [§4.1](#41-add-an-edge-extra_referencesjson).
Short example:

```json
// extensions/extra_references.json
[
  {"source": "thm:212A", "target": "aux:gronwall_exp_bound", "edge_type": "uses_lemma", "context": "manual"},
  {"source": "aux:gronwall_exp_bound", "target": "def:110A", "edge_type": "uses_concept", "context": "manual"}
]
```

**Step 4.** Rebuild and verify (same as §2 step 4-5).

The helper now appears in `entities/aux_gronwall_exp_bound.json`,
the dependency graph, and the formalization queue. Tier-0 grows if the
helper has no deps.

## §4 Recipe: Edit dependency edges

The auto-derived dependency graph is built by three layers of extractors
(regex, concept matching, LLM) and occasionally produces wrong edges, or
misses real ones. Hand-curated corrections live in two parallel files —
both in `extensions/`, both survive every pipeline re-run.

### §4.1 Add an edge (`extra_references.json`)

Use when: the graph is missing a legitimate cross-reference your proof
actually depends on.

```json
// extensions/extra_references.json
[
  {"source": "thm:235B", "target": "def:230A", "edge_type": "uses_definition", "context": "manual: cites Def 230A in proof"}
]
```

- **Required** fields: `source`, `target`, `edge_type`.
- **Optional**: `context` (a short human note; recommended).
- **Allowed `edge_type` values**: follow the auto-derived vocabulary —
  `uses_definition`, `uses_theorem`, `uses_lemma`, `uses_corollary`,
  `uses_concept`, `uses_equation_from`. Use the catch-all `"uses"` if
  none fit (common for helpers).
- Unknown IDs (source or target) produce a warning at build time and the
  edge is silently dropped from the per-entity view. That's
  intentional — it lets you add forward references to entities you plan
  to add later.

### §4.2 Remove a (wrong) auto-derived edge (`removed_references.json`)

Use when: an auto-derived edge is mathematically wrong — typically an
LLM hallucination, a homonym mis-target, or two parallel concepts being
conflated. If you find yourself deleting the same phantom edge from the
rendered graph twice, stop and denylist it.

```json
// extensions/removed_references.json
[
  {"source": "thm:111A", "target": "def:520A",
   "reason": "Ch1 linear-ODE superposition theorem has no mathematical dep on Ch5 GLM stability matrix; LLM false positive"}
]
```

- **Required** fields: `source`, `target`.
- **Required for discipline**: `reason` — a one-line human-readable
  justification. Missing reasons produce a build-time warning.
  Unexplained denials rot: the next person who doesn't understand why
  you denied the edge will quietly undo the denial.
- The denylist is **pair-based**, not type-based — it drops every edge
  between `source` and `target` regardless of `edge_type` (regex,
  concept, LLM are all filtered the same way).
- Unknown IDs produce a warning (not a failure); the entry is retained
  in case the user has pre-denied an edge that a future re-extraction
  will produce.
- Rows that don't match any auto edge produce a `WARN: removed_references
  row did not match any auto edge` at build time — this usually means
  the edge has since disappeared (upstream extractor was improved) and
  the row can be deleted.

### §4.3 Precedence and edge cases

- **Denylist is applied *before* the additive merge.** So `(A, B)`
  present in *both* `removed_references.json` and `extra_references.json`
  results in: the auto edge is dropped, the manual edge is then added
  back (now with `context: "manual"`). Net: the manual edge wins. Useful
  for overriding an auto-derived edge with a differently-annotated one.
- **Cycle-breaking runs after both.** The denylist and additions both
  feed into the cycle-break pass, so you cannot use `extra_references`
  to force a cycle.
- The final edge set that the blueprint and downstream consumers see is
  serialized to `formalization_data/references_final.json` — inspect
  this file rather than `raw_text/references_merged.json` when auditing
  the graph.

### §4.4 Rebuild and verify

```bash
cd extraction && python -m pipeline.build_formalization_data
```

Expected log lines for a working denylist:
```
  Extensions: +N missing statements, +M helpers, +X extra edges, −Y denied edges
  Denylist: dropped Y edge(s) per removed_references.json
```

Failure modes and what they mean:
- `WARN: removed_references row did not match any auto edge: A → B` —
  `(A, B)` isn't in the current auto graph; consider removing it.
- `WARNING: removed_references[i]: source 'X' is not a known auto-extracted ID` —
  `X` isn't in either `raw_text/formal_statements.json` or
  `extensions/missing_statements.json`/`helper_entities.json`; usually a typo.
- `WARNING: removed_references[i] (A → B) has no 'reason'` — add a
  one-line justification before committing.

## §5 Editing `lean_status.json`

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

## §6 Build pipeline behavior

For agents adding entities — you don't run any of this manually; just
re-run Phase 8 (`python -m pipeline.build_formalization_data`) after
editing `extensions/*.json`. Here's what happens internally:

1. Load auto-extracted statements + auto edges from `raw_text/`.
2. Load `extensions/missing_statements.json`; **fail loudly** on ID
   collision with auto-extracted IDs (means re-extraction now covers it
   — delete the manual entry) or duplicate manual entries.
3. Load `extensions/helper_entities.json`; **fail loudly** on invalid
   slug, duplicate slug, or collision with auto-extracted ID.
4. Load `extensions/removed_references.json`; validate shape and IDs;
   remove every matching `(source, target)` pair from the current edge
   pool (applied **before** the additive merge, so a pair in both
   `removed_references.json` and `extra_references.json` ends up as the
   manual add). Warn on unmatched rows and unknown IDs.
5. Load `extensions/extra_references.json`; append to the edge pool.
   Targets that name unknown IDs are kept in the file but **warn** at
   build time and dropped from the per-entity dependency view (so
   forward-references to entities you'll add later don't crash the build).
6. Re-run cycle-breaking on the merged graph by calling
   `break_cycles.break_cycles(edges, page_map)`. Helpers without a page
   default to page 0 for the page-distance heuristic. The resulting
   audit log is written to `formalization_data/cycles_removed_merged.json`
   (the auto-only `raw_text/cycles_removed.json` from Phase 4c is also
   preserved as the pre-extension snapshot).
7. Serialize the final edge set (auto minus denylist plus additions
   minus cycle-break removals) to
   `formalization_data/references_final.json`. Downstream consumers
   such as `generate_blueprint.py` read this file — never
   `raw_text/references_merged.json` — to see the corrected graph.
8. Compute transitive closure, topological tiers, and write all
   output files. Helpers (chapter=None) are excluded from
   `by_chapter/*.json` but appear in `index.json`, `topo_order.json`,
   `entities/*.json`, and `lean_status.json`.
9. `lean_status.json` rows for entities that no longer exist (e.g.
   you deleted a helper) are dropped, with a notice on stdout.
10. Assert that no `uses_concept` edge links two entities sharing the
    same display name in `statement_names.json` (Layer-1 regression
    guard against the homonym bug). Build fails loudly if triggered.

## §7 Blueprint integration

The LaTeX blueprint (`blueprint/src/`) currently renders only Butcher
chapters. Helpers should still appear in the blueprint so the dep graph
is complete and the rendered web has them.

Plan: `pipeline/generate_blueprint.py` adds a final chapter
**"Auxiliary Results"** to the blueprint, listing all `aux:*` entities
ordered by dependency tier. Each gets its own `\begin{lemma}\label{...}`
block with `\uses{...}` reflecting its dependencies. Missing-statement
additions slot into their normal Butcher chapter (no blueprint change
needed beyond Phase 8 picking them up).

## §8 Don'ts

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
- **Don't use `removed_references.json` for taste.** It is for
  known-wrong auto-derived edges, not "edges I don't like". Every entry
  removes real signal from the graph; justify it mathematically.
- **Don't omit the `reason` on a denylist row.** Unexplained denials
  rot — the next person who doesn't understand why you denied the edge
  will silently un-deny it and the bug returns.

## §9 Quick checklist for agents

```
[ ] Identified the situation: Missed textbook entity (§2), new helper (§3),
    or wrong/missing dep edge (§4)?
[ ] For helpers: confirmed reusability — at least two callers, or genuinely
    library-quality. Not single-use scaffolding.
[ ] For missing textbook: confirmed it's actually in the PDF with page number.
[ ] Picked the right ID prefix (thm/def/lem/cor for textbook; aux for helpers).
[ ] For helpers: chose a descriptive snake_case slug, checked it doesn't
    already exist in entities/.
[ ] Added the JSON entry to the right extensions/*.json file with all
    required fields.
[ ] Added missing dependency edges to extensions/extra_references.json (§4.1)
    if the new entity references others.
[ ] If I noticed a wrong auto-derived edge while working: added it to
    extensions/removed_references.json with a mathematical reason (§4.2).
[ ] Ran `python -m pipeline.build_formalization_data` and confirmed the new
    entity file exists in formalization_data/entities/; Denylist log line
    matches what I expected; no unused-row warnings.
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
| Denylist mechanism (`removed_references.json`) in Phase 8, with precedence + warnings | DONE |
| `formalization_data/references_final.json` emitted; `generate_blueprint.py` reads it | DONE |
| Layer-1 regression assert (no `uses_concept` edge between homonyms) | DONE |
| `generate_blueprint.py` "Auxiliary Results" chapter for `aux:*` entities | TODO — see §7 |
| `CLAUDE.md` pointer to this file | DONE |

The extension workflow is **active** across all four extension files
(`missing_statements.json`, `helper_entities.json`, `extra_references.json`,
`removed_references.json`). Re-run Phase 8 after any edit and the
changes flow through per-entity JSONs, the topological order, the final
edge list, and the blueprint. Blueprint rendering of `aux:*` helpers is
the only remaining piece.
