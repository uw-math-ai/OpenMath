# OpenMath — Autonomous Lean 4 Formalization

## Project

Semi-autonomous formalization of *A First Course in the Numerical Analysis of Differential Equations* (Arieh Iserles, Cambridge) in Lean 4 / Mathlib.

## Core Workflow

1. **Read `.prover-state/strategy.md`** for what to work on this cycle.
2. **Sorry-first (ABSOLUTE RULE)**: When formalizing new content, write the full proof structure with `sorry` at every step. Verify it compiles (`lake env lean <file>`). Then close sorry's one by one.
3. **Prove**: Use Lean LSP tools (`lean_goal`, `lean_multi_attempt`, search tools). Decompose hard sorry's into sub-lemmas. Submit truly hard lemmas to Aristotle.
4. **Write results**: Before finishing, write `.prover-state/task_results/cycle_<NNN>.md` documenting what you tried, what worked, what failed, and suggested next steps. If blocked, write an issue file in `.prover-state/issues/`.
5. **Commit**: Verify all modified files compile, then commit and push.

## Rules

- **Follow the strategy.** Do not cherry-pick easy goals or freelance.
- If Mathlib is missing something, **build it yourself** as a helper lemma. "Mathlib gap" is never a final answer.
- **Never increase `maxHeartbeats`** above 200000. Decompose the proof instead.
- Do not poll Aristotle repeatedly. Submit jobs, then work on proofs yourself.
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

Follow the textbook chapter by chapter. The current target is in `plan.md`. Each theorem should be:
- Stated as closely to the textbook as possible
- Proved in full (no sorry's in committed code, unless mid-restructuring)
- Documented with a reference to the textbook section

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
