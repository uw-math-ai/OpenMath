# OpenMath — Autonomous Lean 4 Formalization

## Project

Semi-autonomous formalization of *A First Course in the Numerical Analysis of Differential Equations* (Arieh Iserles, Cambridge) in Lean 4 / Mathlib.

## Core Workflow

1. **Read `.prover-state/strategy.md`** for what to work on this cycle.
2. **Sorry-first (ABSOLUTE RULE)**: When formalizing new content, write the full proof structure with `sorry` at every step. Verify it compiles (`lake env lean <file>`). Then close sorry's one by one.
3. **Aristotle-first (MANDATORY)**: After writing the sorry-first structure, batch-submit ~5 sorry's/sub-lemmas to Aristotle (free compute!). Sleep 30 minutes. Check results, incorporate proofs, fix partials. Only manually prove what Aristotle failed on.
4. **Prove remaining**: Use Lean LSP tools (`lean_goal`, `lean_multi_attempt`, search tools) for what Aristotle didn't solve.
5. **Write results**: Before finishing, write `.prover-state/task_results/cycle_<NNN>.md` documenting what you tried, what worked, what failed, and suggested next steps. If blocked, write an issue file in `.prover-state/issues/`.
6. **Commit**: Verify all modified files compile, then commit and push.

## Rules

- **Follow the strategy.** Do not cherry-pick easy goals or freelance.
- If Mathlib is missing something, **build it yourself** as a helper lemma. "Mathlib gap" is never a final answer.
- **Never increase `maxHeartbeats`** above 200000. Decompose the proof instead.
- **Maximize Aristotle usage.** It is free compute. Submit ~5 jobs per cycle in batch, sleep 30 min, then process results. Do not poll repeatedly — one check after 30 min is enough.
- A cycle with zero changes is **unacceptable**. At minimum, decompose a sorry or write an issue.
- If stuck on a sorry, write a structured issue file in `.prover-state/issues/` explaining **WHY** (not just "it's hard").
- Prefer `lake env lean OpenMath/Foo.lean` to check individual files over `lake build`.
- Keep proofs modular: one theorem per lemma, extract shared infrastructure into helper files.

## Build Commands

```bash
lake env lean OpenMath/Foo.lean    # verify single file (preferred)
lake build                          # full build (uses cached .olean)
```

**IMPORTANT**: The NVMe lean toolchain at `/tmp/lean4-toolchain/bin` should be first in PATH. If `lake` commands hang, check that PATH starts with `/tmp/lake-bin:/tmp/lean4-toolchain/bin`. The GPFS-hosted lean toolchain (`~/.elan/...`) causes multi-minute hangs on this cluster.

## What to Formalize

**Data guide: [`extraction/FORMALIZATION_DATA_GUIDE.md`](extraction/FORMALIZATION_DATA_GUIDE.md)** — explains the extracted Butcher content (file layout, per-entity JSON, dependency graph, chapter-by-chapter order with the `thm:243A` Ch.2→Ch.4 deferral, and `lean_status.json` semantics). Read this to understand what data is available; workflow is wired separately.

Per-theorem content (statement, LaTeX, dependencies, prior-formalization status) is in `extraction/formalization_data/entities/<id>.json`. Schema spec: `extraction/formalization_data/README.md`. Each theorem should be:
- Stated as closely to the textbook as possible
- Proved in full (no sorry's in committed code, unless mid-restructuring)
- Documented with a reference to the textbook section

The legacy `plan.md` (Iserles-based tracking, partially complete) is retained as a historical record of earlier formalization work in `OpenMath/*.lean` but is no longer the primary roadmap.

## Adding new entities

If you discover a textbook theorem the extractor missed, OR you need a reusable helper lemma not in Butcher, **read [`extraction/EXTENSIBILITY.md`](extraction/EXTENSIBILITY.md) before doing anything**. Hand-edit only files under `extraction/extensions/`; never edit `extraction/raw_text/` or `extraction/formalization_data/entities/` (both are regenerated). When you finish formalizing an entity in Lean, update its row in `extraction/formalization_data/lean_status.json`.

## Task Results Format

Write to `.prover-state/task_results/cycle_<NNN>.md`:

```markdown
# Cycle NNN Results

## Worked on
[which sorry / theorem / infrastructure]

## Approach
[what you tried]

## Result
[SUCCESS / FAILED — explanation]

## Dead ends
[approaches that didn't work and why]

## Discovery
[anything learned that's useful for future cycles]

## Suggested next approach
[what the planner should consider]
```

## Issue File Format

Write to `.prover-state/issues/<descriptive_name>.md`:

```markdown
# Issue: <descriptive title>

## Blocker
[what's blocking progress]

## Context
[relevant Lean code / error messages]

## What was tried
[approaches attempted]

## Possible solutions
[ideas for resolution]
```
