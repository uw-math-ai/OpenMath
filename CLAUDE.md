# OpenMath — Autonomous Lean 4 Formalization

## Project

Semi-autonomous formalization of *Numerical Methods for Ordinary Differential Equations* (J.C. Butcher, 3rd edition) in Lean 4 / Mathlib.

**Textbook source**: The extracted text lives in `extraction/raw_text/` (`ch01.txt`–`ch05.txt`, `full_text.txt`). Section numbers in entity IDs (e.g. `thm:110C`, `def:110A`) are Butcher's numbering. Do **not** attribute theorems to Iserles — the source is Butcher.

## Core Workflow

1. **Read `.prover-state/strategy.md`** for what to work on this cycle.
2. **Load formalization data (MANDATORY)**: Before writing any Lean code for entity `<id>`, read `extraction/formalization_data/entities/<id>.json` for the statement, proof text, LaTeX, and dependency list. The Lean statement must be derivable from `statement_latex`. If you cannot match it, file an issue explaining the gap — do not silently weaken the statement.
3. **Sorry-first (ABSOLUTE RULE)**: When formalizing new content, write the full proof structure with `sorry` at every step. Verify it compiles (`lake env lean <file>`). Then close sorry's one by one.
4. **Aristotle-first (MANDATORY)**: After writing the sorry-first structure, batch-submit ~5 sorry's/sub-lemmas to Aristotle (free compute!). Sleep 30 minutes. Check results, incorporate proofs, fix partials. Only manually prove what Aristotle failed on.
5. **Prove remaining**: Use Lean LSP tools (`lean_goal`, `lean_multi_attempt`, search tools) for what Aristotle didn't solve.
6. **Pre-commit faithfulness check (MANDATORY)**: Before committing, run the checklist in the section below.
7. **Write results**: Before finishing, write `.prover-state/task_results/cycle_<NNN>.md` documenting what you tried, what worked, what failed, and suggested next steps. If blocked, write an issue file in `.prover-state/issues/`.
8. **Commit**: Verify all modified files compile, then commit and push.

## Rules

- **Follow the strategy.** Do not cherry-pick easy goals or freelance.
- Do **not** introduce `axiom` or `constant` declarations. If a proof seems to require one, stop and write a blocker issue explaining what is missing.
- For every new `class` or `structure`, provide at least one concrete witness/instance in the same cycle (or write an issue explaining why this is currently impossible). Do not continue proving against abstractions with no evidence of non-vacuity.
- New `class`/`structure` definitions must match the textbook meaning of the concept. If you use an equivalent formulation, add an explicit equivalence lemma.
- Before creating any new definition, use Lean LSP search tools to check whether an equivalent Mathlib definition already exists and reuse it when possible.
- If Mathlib is missing something, **build it yourself** as a helper lemma. "Mathlib gap" is never a final answer.
- **Never increase `maxHeartbeats`** above 200000. Decompose the proof instead.
- **Maximize Aristotle usage.** It is free compute. Submit ~5 jobs per cycle in batch, sleep 30 min, then process results. Do not poll repeatedly — one check after 30 min is enough.
- A cycle with zero changes is **unacceptable**. At minimum, decompose a sorry or write an issue.
- If stuck on a sorry, write a structured issue file in `.prover-state/issues/` explaining **WHY** (not just "it's hard").
- Prefer `lake env lean OpenMath/Foo.lean` to check individual files over `lake build`.
- Keep proofs modular: one theorem per lemma, extract shared infrastructure into helper files.

## Pre-Commit Faithfulness Checklist

Run this before every commit that introduces a new `def`, `structure`, or `theorem`.

### For every new `def` of a named mathematical concept:

- [ ] Open `extraction/formalization_data/entities/<id>.json` and quote the textbook statement.
- [ ] Confirm the Lean type matches the textbook definition. If using an equivalent reformulation, prove the equivalence explicitly as a separate lemma.
- [ ] **Definition smuggling check**: you are NOT allowed to define a concept (e.g. "convergence") as the algebraic conditions that characterize it, then claim the characterization theorem is proved. The definition must capture the *primary* mathematical meaning; the characterization must be a genuine theorem.

### For every new `class` or `structure` with `Prop` fields:

- [ ] Label each field clearly as either a *hypothesis* (something the user must supply) or a *conclusion* (something that should be derived).
- [ ] Any field that is mathematically a *consequence* of the other fields must either be proved inline or left as `sorry` with an explicit comment — it must NOT be silently placed as a hypothesis.

### For every new `theorem` or `lemma`:

- [ ] **Tautology check**: does the conclusion appear verbatim as one of the hypotheses? If yes, this is a bug — escalate to an issue.
- [ ] **Identity check**: if the proof is a single `exact h`, `h_exact`, or `id`, ask yourself whether this theorem is doing real work. If it merely re-exports a hypothesis with a new name, it is a vacuous theorem.
- [ ] **Hypothesis strength check**: are any hypotheses stronger than the textbook requires? If a hypothesis can be weakened and the proof still goes through, weaken it. Extra hypotheses that are not in the textbook statement must be documented with justification.
- [ ] **Absent theorem check**: if a comment says a theorem "will be proved with sorry" or "is stated below", verify the theorem actually exists. A promised `sorry` that is never written is an invisible gap.

### Escalate immediately (do not wait for the next Planner cycle) if:

- A theorem conclusion equals one of its hypotheses.
- A `structure` field encodes what should be a theorem conclusion.
- A definition of a named concept diverges from the textbook without a proved equivalence.
- A proof comment promises content that is not present in the file.

Write an issue to `.prover-state/issues/` describing the specific pattern and which theorem is affected.

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

Per-theorem context (statement, LaTeX, dependencies, prior-formalization status) is available in `extraction/formalization_data/entities/<id>.json`. See `extraction/formalization_data/README.md` for the schema.

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

## Faithfulness check
For each new `def` or `theorem` introduced this cycle:
- Entity ID and textbook statement (quoted from formalization_data):
  > ...
- Lean statement captures: [same content / weaker / stronger / different]
- If different: justification for divergence

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
