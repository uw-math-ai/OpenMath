# Cycle 028 Results

## Worked on
`def:357B` — algebraically stable Runge–Kutta methods (Butcher §357,
p. 271). New file `OpenMath/Chapter3/Section357.lean` reusing
`symplecticityMatrix` from cycle 027's `Section370`.

## Approach
1. Verified `Matrix.PosSemidef` is provided by
   `Mathlib.LinearAlgebra.Matrix.PosDef` and that
   `Matrix.PosSemidef.zero` exists in this Mathlib pin (line 112 of the
   Mathlib source).
2. Created `OpenMath/Chapter3/Section357.lean` with
   * `IsAlgebraicallyStable {s} (R : RKTableau s) : Prop :=
        (∀ i, 0 < R.b i) ∧ (symplecticityMatrix R).PosSemidef`
   * Concrete witness `implicitMidpoint_isAlgebraicallyStable` proved
     via `fin_cases + norm_num` for the positivity conjunct, and by
     rewriting the symplecticity matrix to `0` using
     `implicitMidpoint_isSymplectic` (cycle 027) and closing with
     `Matrix.PosSemidef.zero`.
3. Hooked the new file into `OpenMath/Chapter3.lean` (alphabetical
   placement between Section355 and Section370).
4. Updated `extraction/formalization_data/lean_status.json` and
   `plan.md` (progress 28 → 29 / 175).

## Result
SUCCESS — `lake build` clean for the new module and `Chapter3.lean`
re-verifies without errors. 0 sorries in `OpenMath/`, 0 tautology-
scanner hits.

## Faithfulness check
- Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/def_357B.json`):
  > A Runge–Kutta method (A, b, c) is 'algebraically stable' if
  > b_i > 0, for i = 1, 2, ..., s, and if the matrix M, given by
  > M = diag(b)A + A diag(b) − bb^⊤ (357d), is positive
  > semi-definite.
- Lean statement captures: **same content**.
  `IsAlgebraicallyStable R := (∀ i, 0 < R.b i) ∧
   (symplecticityMatrix R).PosSemidef`. The first conjunct is the
  textbook positivity clause `b_i > 0`; the second uses the same
  matrix `M` already defined as `symplecticityMatrix` in `Section370`
  (Butcher's (357d) and (370a) refer to the *same* matrix), now
  required to be PSD via `Matrix.PosSemidef`. No reformulation, no
  extra hypotheses, no missing clauses.
- For `implicitMidpoint_isAlgebraicallyStable`:
  * Tautology check: not applicable — definition; the theorem's
    conclusion is `IsAlgebraicallyStable implicitMidpoint`, not a
    hypothesis re-export.
  * Identity check: proof is `refine ⟨?_,?_⟩; intro i; fin_cases i;
    norm_num [implicitMidpoint]; rw […]; exact
    Matrix.PosSemidef.zero` — does real work via the matrix-zero
    rewrite; not `exact h_…`.
  * Hypothesis strength check: theorem is hypothesis-free; cannot be
    weakened.
- Definition smuggling check: `IsAlgebraicallyStable` is a `Prop`,
  not a `class`/`structure`. No `Prop` field that is a derived
  consequence.
- LLM-extracted dependency edge `def:357B → def:357A` is documented
  in the file's docstring as **not a real mathematical dependency**;
  Butcher presents algebraic stability as a sufficient condition for
  B/BN-stability, not the other way round.

## Dead ends
None. The strategy's plan executed in one pass; the named lemma
`Matrix.PosSemidef.zero` worked on the first try, and `fin_cases +
norm_num` discharged the single weight `b 0 = 1 > 0`.

## Discovery
* `Matrix.PosSemidef.zero` is the canonical zero-matrix PSD lemma in
  this Mathlib pin (file `Mathlib/LinearAlgebra/Matrix/PosDef.lean`
  line 112). Useful for any future stability proofs that reduce to
  the zero-matrix case.
* The strategy's observation that Butcher's `M` in (357d) is
  *literally* the same object as `M` in (370a) was correct and let us
  reuse `symplecticityMatrix` directly without any refactor or
  helper-file split. The implicit midpoint method now serves as a
  shared concrete witness for both `IsSymplectic` and
  `IsAlgebraicallyStable`.

## Suggested next approach
The §357 stability stack is unfinished. `def:357A` (B-stability) is
flagged in the strategy as a degenerate extraction (statement_text
is just commentary); a faithful B-stability formalization needs the
non-autonomous ODE / one-sided Lipschitz / dissipativity setup from
the surrounding §357 prose, which is a multi-cycle infrastructure
investment.

Concrete options for cycle 029:

1. **`thm:357C` / `thm:357D`** — the Burrage–Butcher sufficiency
   theorems showing that algebraic stability implies BN-stability.
   These are the natural consumers of `IsAlgebraicallyStable`, but
   they depend on the §356 dissipativity setup which is itself
   unbuilt.
2. **`thm:331A`-style order-condition formalization** — independent
   of §357, lower infrastructure barrier.
3. **§356 dissipativity infrastructure** (`def:356A`, `def:356B`,
   `cor:356D`, `thm:356C`) as a prerequisite for §357. This is the
   most natural unblocker for `def:357A` and `thm:357C/D`.

A planner deciding §357's path forward should weigh the §356
dissipativity buildup (option 3) — it's the dependency root that
unblocks the rest of §357.
