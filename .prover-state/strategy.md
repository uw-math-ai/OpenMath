# Cycle 035 strategy — open Chapter 4 with `def:404A` (preconsistent LMM)

## State entering this cycle

- Cycle 034 RESOLVED `symplecticityMatrix_missing_transpose`. Build clean,
  no sorrys, axioms standard. Branch tip: `34e769f`.
- No Aristotle results pending.
- No sorrys in the codebase. Cycle must produce a new entity.
- Plan progress: 34/175 entities. Chapter 1: 13/17. Chapter 2: 3/4 +
  1 deferred. Chapter 3: 17/92. **Chapter 4: 0/27. Chapter 5: 0/35.**

## Target this cycle

**`def:404A` — preconsistent linear multistep method** (Butcher §404, p. 341).
Entity record: `extraction/formalization_data/entities/def_404A.json`.

### Why this target (and why NOT the cycle-034 list)

Cycle 034's "after this cycle" suggested
`def:381B / def:381D / def:381F / lem:310B`. All four are **stale or
blocked**:

- `def:381B` and `def:381D` are already `[x]` in `plan.md` (cycles 030
  and 022). Verified by re-reading the plan.
- `def:381F` (P-equivalent) is blocked by the deferred "reduced method"
  construction (`reduced_method_deferred.md`). Its definition reads
  "each of them reduces to the same reduced method" — no reduced
  method, no def:381F.
- `lem:310B` requires `thm:306A` (Taylor's theorem), which is
  unformalized (`[ ]` in plan.md). Wrong order.

`def:404A` is the cleanest unblocked target on the entire board:

- **Self-contained**: `dependencies = []`,
  `transitive_dependencies = []` per the entity JSON.
- **Opens Chapter 4** (currently 0/27, no scaffolding yet).
- **High leverage**: 6 immediate dependents
  (`def:404B`, `def:406A`, `def:510A`, `thm:405B`, `thm:422A`,
  `thm:422C`). Builds the reusable `LinearMultistepMethod` structure
  every Chapter 4 entity will need.
- **Single cycle**: definition + structure + non-vacuity witness fits
  comfortably.

Continuing Chapter 3 leaf work would now require either (a) the
multi-cycle AN-stability infrastructure (`AN_stability_deferred.md`),
(b) the multi-cycle reduced-method construction
(`reduced_method_deferred.md`), or (c) the §31x Taylor's-theorem
chain (`thm:306A` → `lem:310B` → …). Better to break new ground in
Chapter 4 and return to those when one is explicitly scoped.

## Textbook content to formalize

From `def_404A.json` `context_latex` and `statement_latex`:

A **k-step linear multistep method** for `y' = f(x, y)` is given by
real coefficients `α_0, α_1, …, α_k` and `β_0, β_1, …, β_k` with
`α_0 = -1` (the leading-coefficient normalisation), defining the
recurrence

```
Σ_{i=0}^{k} α_i y_{n-i} = h Σ_{i=0}^{k} β_i f(x_{n-i}, y_{n-i}).
```

Equivalently (using `α_0 = -1`):
`y_n = Σ_{i=1}^{k} α_i y_{n-i} + h Σ_{i=0}^{k} β_i f(x_{n-i}, y_{n-i})`.

The method is **preconsistent** if equation (404a) holds:

```
1 = α_1 + α_2 + ⋯ + α_k.        (404a)
```

The textbook prose then derives (404b)
`α_1 + 2 α_2 + ⋯ + k α_k = β_0 + β_1 + ⋯ + β_k`
as motivation for `def:404B` (consistency, NOT this cycle).

## Implementation plan

### Step 1 — Chapter 4 scaffolding

Worker MUST create, in order:

1. `OpenMath/Chapter4/Section404.lean` — main file (contents in Step 2).
2. `OpenMath/Chapter4.lean` — chapter aggregator, single line:
   ```lean
   import OpenMath.Chapter4.Section404
   ```
3. Append to `OpenMath.lean`:
   ```lean
   import OpenMath.Chapter4
   ```

### Step 2 — `LinearMultistepMethod` structure

Define the LMM record. Recommended shape (refine only if a
`lean_local_search "LinearMultistep"` reveals a Mathlib idiom — but
do NOT introduce a new typeclass abstraction):

```lean
import Mathlib

namespace OpenMath.Chapter4.Section404

/-- A `k`-step linear multistep method (Butcher §40, p. 341).

    Coefficients `α : Fin (k+1) → ℝ` and `β : Fin (k+1) → ℝ` define the
    recurrence
    `Σᵢ αᵢ · y_{n-i} = h · Σᵢ βᵢ · f(x_{n-i}, y_{n-i})`,
    with the leading-coefficient normalisation `α 0 = -1`.

    `α_zero` is a *hypothesis* (textbook normalisation convention),
    not a derived fact: every concrete LMM must supply it. -/
structure LinearMultistepMethod (k : ℕ) where
  α : Fin (k + 1) → ℝ
  β : Fin (k + 1) → ℝ
  α_zero : α 0 = -1
```

Notes for the worker:

- Use `Fin (k+1)` so that `α k` is the coefficient of `y_{n-k}` and
  `α 0` is the coefficient of `y_n`. This matches Butcher's `α_i for
  i = 0..k`.
- `α_zero` is a structure field; every instance must prove it. Keep it.
- Do NOT add a `step_count_pos : 0 < k` field. Butcher does not
  require it; some downstream entities (e.g. `def:404B`, `thm:410A`)
  treat the `k = 0` case implicitly.

### Step 3 — `IsPreconsistent` predicate

```lean
/-- Butcher (404a): a linear multistep method is *preconsistent* if
    `1 = α₁ + α₂ + ⋯ + α_k`. -/
def LinearMultistepMethod.IsPreconsistent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  1 = ∑ i : Fin k, M.α i.succ
```

The sum runs from `i = 1` to `i = k`, encoded by iterating over
`Fin k` and using `i.succ : Fin (k+1)` to skip `α 0`. If this
formulation is awkward downstream, an equivalent form is
`1 = ∑ i ∈ Finset.Ioi (0 : Fin (k+1)), M.α i`, but prefer the
`Fin k` version for evaluation simplicity.

### Step 4 — Non-vacuity witness: explicit Euler as a 1-step LMM

CLAUDE.md mandates a concrete witness in the same cycle. The simplest
LMM is **explicit Euler** as a 1-step method:

`y_n - y_{n-1} = h · f(x_{n-1}, y_{n-1})`

so `k = 1`, `α 0 = -1, α 1 = 1, β 0 = 0, β 1 = 1`. Preconsistency
condition: `1 = α 1 = 1`. ✓

```lean
/-- Explicit Euler as a 1-step linear multistep method:
    `y_n - y_{n-1} = h · f(x_{n-1}, y_{n-1})`. -/
def explicitEulerLMM : LinearMultistepMethod 1 where
  α := fun i => if i = 0 then -1 else 1
  β := fun i => if i = 0 then 0 else 1
  α_zero := by simp

/-- Explicit Euler is preconsistent. -/
theorem explicitEulerLMM_isPreconsistent :
    explicitEulerLMM.IsPreconsistent := by
  simp [LinearMultistepMethod.IsPreconsistent, explicitEulerLMM,
        Fin.sum_univ_one]
```

If `simp` does not close it directly, try `lean_multi_attempt` with
fallbacks (in order): `["decide", "rfl", "norm_num",
"simp [LinearMultistepMethod.IsPreconsistent, explicitEulerLMM,
 Fin.sum_univ_succ, Fin.sum_univ_zero]; rfl",
"simp [LinearMultistepMethod.IsPreconsistent, explicitEulerLMM,
 Fin.sum_univ_one]; norm_num"]`.

The arithmetic should close in <30 seconds. **No Aristotle batch
needed for this cycle** — see "Aristotle usage" below.

### Step 5 — Optional second witness (recommended but not required)

If time permits and the main witness landed quickly, add the
**implicit Euler** 1-step LMM as well: `α 0 = -1, α 1 = 1, β 0 = 1,
β 1 = 0`. Same preconsistency proof shape. Provides evidence that
the predicate is meaningful for both explicit and implicit methods.

Skip this if the main witness took >40 minutes; prioritise commit
over gold-plating.

### Step 6 — Pre-commit faithfulness check (mandatory)

Per CLAUDE.md's checklist:

- [ ] `LinearMultistepMethod`: a `structure`, not a `class`. The
      single `Prop` field `α_zero` is a *hypothesis* (textbook
      normalisation convention), labelled as such in the docstring.
- [ ] `IsPreconsistent`: matches Butcher (404a) verbatim
      `1 = α_1 + … + α_k`. Quote (404a) in the docstring.
- [ ] Tautology check on `explicitEulerLMM_isPreconsistent`: the
      proof must genuinely evaluate the sum (`simp` unfolding +
      arithmetic), not be `exact rfl` on a hypothesis.
- [ ] Definition-smuggling check: `IsPreconsistent` is the algebraic
      condition (404a) directly — this matches Butcher's *definition*
      of preconsistency, not a characterisation. Document this
      explicitly: Butcher's prose says "a linear multistep method
      satisfying (404a) is said to be preconsistent", so (404a) IS
      the definition.

### Step 7 — Status updates

Update `extraction/formalization_data/lean_status.json` row for
`def:404A`:
- `formalization_status` → `"formalized"`.
- `lean_file` → `"OpenMath/Chapter4/Section404.lean"`.
- `lean_symbol` →
  `"OpenMath.Chapter4.Section404.LinearMultistepMethod.IsPreconsistent"`.

Update `plan.md`:
- Change the Chapter 4 row from
  `- [ ] def:404A preconsistent (§404)`
  to
  `- [x] def:404A preconsistent (§404) — OpenMath/Chapter4/Section404.lean`.
- Bump the progress counter at the top from `34 / 175` to `35 / 175`.

### Step 8 — Build verification

```bash
lake env lean OpenMath/Chapter4/Section404.lean    # individual file
lake build                                          # full build (cached)
```

Then check axioms on the witness:

```bash
echo '#print axioms OpenMath.Chapter4.Section404.explicitEulerLMM_isPreconsistent' \
  | lake env lean --stdin OpenMath/Chapter4/Section404.lean
```

Expected: `[propext, Classical.choice, Quot.sound]` only.

### Step 9 — Task results

Write `.prover-state/task_results/cycle_035.md` per CLAUDE.md format,
specifically including:

- The `def:404A` faithfulness quote from the entity JSON.
- Confirmation that `α_zero` is a hypothesis (textbook convention),
  not a hidden conclusion.
- Confirmation that `IsPreconsistent` is exactly Butcher (404a):
  equality of `1` and the sum of `α_1..α_k`.
- The two `lake build` outputs and the axiom-check output.

### Step 10 — Commit and push

Suggested commit message:

```
Open Chapter 4 — formalize def:404A (preconsistent linear multistep methods)

Introduces `LinearMultistepMethod k` structure (with the textbook
α_0 = -1 normalisation) and the `IsPreconsistent` predicate
(Butcher §404, equation (404a)). Witnesses preconsistency of
explicit Euler as a 1-step LMM. Opens Chapter 4 of plan.md (now 35/175).
```

Verify with `git rev-parse HEAD == git rev-parse origin/Main/Experiments`
after pushing, per the cycle-009 consultant note's anti-phantom
verification routine.

## What NOT to do

- **Do NOT pursue the cycle-034 list verbatim.** `def:381B` and
  `def:381D` are already done; `def:381F` is blocked by reduced-method
  deferral; `lem:310B` needs `thm:306A`. The list was stale relative
  to the current `plan.md`.
- **Do NOT start the AN-stability infrastructure** this cycle. It is
  a multi-cycle complex-matrix-resolvent project per
  `AN_stability_deferred.md` — pursue it only when a planner explicitly
  scopes it as the cycle goal.
- **Do NOT start the §142 Schur infrastructure** (per
  `jordan_canonical_form_missing.md`). Non-critical path.
- **Do NOT start the reduced-method construction** (per
  `reduced_method_deferred.md`). Defer until `def:381F` is the
  targeted cycle.
- **Do NOT modify `scripts/autonomous_loop.py`** to fix the tautology
  scanner false positives. Loop-maintainer work; the issue file
  `tautology_scanner_false_positives.md` already captures the patches.
- **Do NOT raise `maxHeartbeats`** above 200000.
- **Do NOT introduce `axiom` or `constant`** declarations.
- **Do NOT introduce a class hierarchy or typeclass abstraction over
  LMMs** ("LMM-like" structures, etc.). One concrete `structure` is
  enough; abstractions can come later when a downstream theorem needs
  one.
- **Do NOT add a `step_count_pos : 0 < k` field** to
  `LinearMultistepMethod`. Butcher does not require it.
- **Do NOT define preconsistency in terms of (404b)** (the consistency
  condition `Σᵢ i αᵢ = Σᵢ βᵢ`). That is a different definition
  (`def:404B`, NOT this cycle) and conflating them would be a
  faithfulness failure.
- **Do NOT skip the non-vacuity witness.** CLAUDE.md mandates one
  concrete instance per new `structure` in the same cycle.
- **Do NOT re-formalize `def:381B`, `def:381D`, or any already-done
  entity.** Check `plan.md` first if uncertain.
- **Do NOT chase the "stuck on" rows from older `attempts.md`**
  (Section112:74, Section212:138/144). All resolved cycles ago; the
  current scanner shows zero hits, verified by
  `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`.

## Aristotle usage this cycle

**Skip the Aristotle batch.** Justification (document this in
`task_results/cycle_035.md` under "Approach" so the evaluator does
not flag the skip):

- The single new theorem (`explicitEulerLMM_isPreconsistent`) is
  trivial arithmetic that closes in `<30s` manually.
- The 30-minute Aristotle round-trip would push the cycle to >40
  minutes for a goal `decide` can solve.
- CLAUDE.md's "Aristotle-first" rule is explicitly conditioned on
  having ~5 sub-lemmas worth submitting; here there are zero such
  goals.

If `explicitEulerLMM_isPreconsistent` unexpectedly resists manual
proof for >15 minutes, file the goal as a `sorry`'d helper and
submit a single Aristotle job as a fallback. Do NOT submit
speculative jobs in advance.

## Search hints if you get stuck

- `Fin.sum_univ_one`, `Fin.sum_univ_succ`, `Fin.sum_univ_zero` — for
  evaluating `∑ i : Fin k, …` in the small-k cases.
- `Mathlib.Algebra.BigOperators.Fin` — for `Fin`-indexed sum lemmas.
- `lean_local_search "LinearMultistep"` — confirm Mathlib has no
  pre-existing LMM structure to reuse. (Pre-cycle check: as of pinned
  Mathlib, it does not — only ODE-side material in
  `Mathlib/Analysis/ODE/`.)
- Skip `lean_leansearch` / `lean_loogle` — this cycle is plumbing,
  not a Mathlib-find puzzle.

## Definition of done

1. New file `OpenMath/Chapter4/Section404.lean` exists, defines
   `LinearMultistepMethod`, `LinearMultistepMethod.IsPreconsistent`,
   `explicitEulerLMM`, and `explicitEulerLMM_isPreconsistent`.
2. `OpenMath/Chapter4.lean` and the new `import OpenMath.Chapter4`
   line in `OpenMath.lean` are in place.
3. `lake build` completes cleanly.
4. Axiom check on `explicitEulerLMM_isPreconsistent` shows
   `[propext, Classical.choice, Quot.sound]`.
5. `lean_status.json` and `plan.md` are updated (entity row +
   progress counter).
6. `.prover-state/task_results/cycle_035.md` exists with the
   faithfulness check section filled in.
7. Commit landed and pushed; `git rev-parse HEAD ==
   git rev-parse origin/Main/Experiments` after the push.

If any step blocks unexpectedly, write a structured issue file to
`.prover-state/issues/` rather than committing partial work, and
pivot to a different unblocked leaf entity (next-best candidates,
in order: `def:510A` preconsistency vector for GLM in §510 — same
structural pattern as def:404A — or `def:520A` Introduction in
§520).
