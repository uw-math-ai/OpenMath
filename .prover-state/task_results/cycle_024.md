# Cycle 024 Results

## Worked on
`lem:322A` — Butcher Lemma 322A, "Methods of order 4" auxiliary linear-algebra
lemma. New file `OpenMath/Chapter3/Section322.lean` introducing the theorem
`order_four_block_zero_decomposition`.

## Approach
Followed the planner's primary plan verbatim:

1. Read `extraction/formalization_data/entities/lem_322A.json` to confirm
   the textbook statement and proof.
2. Looked up Mathlib lemma names via `Explore` agent — found:
   * `Matrix.exists_vecMul_eq_zero_iff` (left null vector ⇔ det = 0)
   * `Matrix.exists_mulVec_eq_zero_iff` (right null vector ⇔ det = 0)
   * `Matrix.det_fin_three`, `Matrix.det_mul`, `Matrix.vecMul_vecMul`,
     `Matrix.mulVec_mulVec`, `Matrix.zero_vecMul`, `Matrix.mulVec_zero`.
3. Wrote a single-theorem file with the exact textbook hypothesis encoding:
   * `h_block : ∀ i, (P*Q) i 2 = 0 ∧ (P*Q) 2 i = 0` — third row & column zero.
   * `h_det  : (P*Q) 0 0 * (P*Q) 1 1 - (P*Q) 0 1 * (P*Q) 1 0 ≠ 0` — 2×2 block non-singular.
4. Closed the proof manually (no Aristotle needed): `det_fin_three` plus the
   third-row/column zeros gives `det (P*Q) = 0`; `Matrix.det_mul` gives
   `det P * det Q = 0`; case-split. In each case extract a non-zero null
   vector (left or right), expand `(u ᵥ* (P*Q)) j` using `Fin.sum_univ_three`,
   and solve the resulting 2×2 system using `h_det`.
5. Added a concrete witness `example` with `P = !![1,0,0; 0,1,0; 0,0,0]`,
   `Q = 1`. Conclusion (`∀ j, P 2 j = 0`) verified by `fin_cases j`.
6. Verified `lake env lean OpenMath/Chapter3/Section322.lean` (exit 0),
   `lake build OpenMath.Chapter3.Section322` (success), `#print axioms`
   shows only `propext, Classical.choice, Quot.sound`.
7. Bookkeeping: added import to `OpenMath/Chapter3.lean`; flipped
   `[ ]` → `[x]` for `lem:322A` in `plan.md` and bumped progress
   `24/175` → `25/175`; updated `lean_status.json`.

Aristotle was NOT used this cycle — the proof was short enough to
hand-prove and the Mathlib lemma lookup landed on the first try.

## Result
SUCCESS — `lem:322A` fully formalised, zero `sorry`, axiom check clean,
both `lake build` and per-file `lake env lean` pass, witness example
non-vacuous.

## Faithfulness check
For `theorem order_four_block_zero_decomposition`:

* **Entity ID and textbook statement** (quoted from
  `extraction/formalization_data/entities/lem_322A.json`):

  > If `P` and `Q` are each `3 × 3` matrices such that their product
  > has the form
  >
  >     PQ = ⎡ r₁₁ r₁₂ 0 ⎤
  >          ⎢ r₂₁ r₂₂ 0 ⎥
  >          ⎣  0   0  0 ⎦
  >
  > where `det [r₁₁ r₁₂ ; r₂₁ r₂₂] ≠ 0`, then either the last row of
  > `P` is zero or the last column of `Q` is zero.

* **Lean statement captures**: same content. Hypothesis `h_block` says
  literally that the third row and column of `P*Q` are zero (which
  encodes "PQ has the form with `0`s in the third row/column" and lets
  us define `rᵢⱼ = (P*Q) (i-1) (j-1)`). Hypothesis `h_det` says
  literally `r₁₁ r₂₂ - r₁₂ r₂₁ ≠ 0`. Conclusion is the disjunction
  `(∀ j, P 2 j = 0) ∨ (∀ i, Q i 2 = 0)` which says "the last row of
  P is zero or the last column of Q is zero".

* **Specialisation justification**: textbook works over an unspecified
  field; Lean version specialises to `ℝ` because (a) it is the field
  used by the surrounding Runge–Kutta context in Butcher §3, and
  (b) `Matrix.exists_{vecMul,mulVec}_eq_zero_iff` requires
  `[CommRing A] [IsDomain A]`, which `ℝ` satisfies. Generalising to a
  parametric field would only add typeclass bookkeeping; per the
  cycle-024 strategy's "Things NOT to try" list, we deliberately do
  NOT generalise this cycle.

* **Tautology check**: conclusion is a non-trivial disjunction. Not
  one of the hypotheses.

* **Identity check**: proof is multi-step (det = 0, case split,
  null-vector extraction, 2×2 system, basis-expansion). No part is
  `exact h` or `:= id`.

* **Hypothesis-strength check**: hypotheses match the textbook
  literally; nothing is stronger than required. No "extra" hypotheses.

* **Definition smuggling check**: no new `def` or `structure`
  introduced this cycle, only one `theorem`. Nothing to smuggle.

## Dead ends
None of substance. Two minor friction points:

1. **Wrong import path for matrix bracket notation**. First wrote
   `import Mathlib.Data.Matrix.Notation`; that file does not exist in
   the current Mathlib (the syntax `!![...]` is in
   `Mathlib.LinearAlgebra.Matrix.Notation`). Fixed in one edit.
2. **Missing `Real` instance import**. After fixing (1), got cascade of
   `OfNat ℝ 0` / `CommRing ℝ` synth failures. Added
   `import Mathlib.Data.Real.Basic` and the issue cleared.

Both are infrastructure noise, not mathematical dead ends.

## Discovery
Reusable lemma-name knowledge for future linear-algebra theorems:

* `Matrix.exists_vecMul_eq_zero_iff : (∃ v ≠ 0, v ᵥ* M = 0) ↔ M.det = 0`
  — under `[CommRing A] [IsDomain A] [DecidableEq n]`.
* `Matrix.exists_mulVec_eq_zero_iff : (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0`
  — same hypotheses.
* Both live in `Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`.
* `Matrix.vecMul_vecMul : v ᵥ* M ᵥ* N = v ᵥ* (M * N)` and
  `Matrix.mulVec_mulVec : M *ᵥ N *ᵥ v = (M * N) *ᵥ v` are simp lemmas
  in `Mathlib.Data.Matrix.Mul`.
* For `Fin 3` sum unfolding, `Fin.sum_univ_three` works directly:
  `∑ i : Fin 3, f i = f 0 + f 1 + f 2`. Required showing the goal as
  a sum first via `show ∑ i : Fin 3, ... = ...` then `rw`.
* The `linarith [h ▸ hgoal]` pattern is useful for finishing
  "expansion + value of the sum" arguments cleanly.

These will be reusable for any future `lem:32xx` / `lem:33xx`
linear-algebra arguments in Butcher Chapter 3.

## Suggested next approach
For cycle 025, candidates that look immediately tractable:

1. **`def:323A` and `thm:323B`** (next §323 entries in plan.md) —
   "Methods of order 5" continuation. They sit right after our
   §322 work in the textbook order; first check their dependency
   list and whether they need the order-4 theorem proper (which we
   have NOT yet formalised) before committing.

2. **`thm:142D` / `thm:142E` / `thm:142C`** (Chapter 1 §142) —
   the matrix-power Convergence/Stability cluster. Three remaining
   Ch.1 entities. They are linear-algebra adjacent so the lemma
   names found this cycle (`exists_*Mul_eq_zero_iff`, `det_fin_three`)
   may transfer. Check whether `jordan_canonical_form_missing.md`
   actually blocks all three or just §142.

3. **Backup work**: scope `thm:381G` partition-algebra
   infrastructure (the planner-listed fallback for cycle 024). This
   cycle did not need to use the fallback, so the scoping work
   remains untouched and is still a productive cycle if no
   short-form lemma is available.

Recommend the planner pick option (1) or (2) — both keep the
Aristotle quota healthy and stay zero-dependency in the same way
`lem:322A` did.
