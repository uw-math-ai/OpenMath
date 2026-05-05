# Cycle 134 Results

## Worked on
`def:542A` (Runge–Kutta stability) — strengthen non-vacuity by exhibiting a
substantive `r = 2` witness `padded2DEulerGLM_isRKStable` alongside the
cycle 130 vacuous-by-`r=1` witness `explicitEulerGLM_isRKStable`.

## Approach
Reused `padded2DEulerGLM : GeneralLinearMethod 1 2` from cycle 133. The
strategy specified inserting after `explicitEulerGLM_isRKStable` (line 543)
and before the §551 header (line 545); however `padded2DEulerGLM` is
defined at line 632 inside the §551 block, so the new theorems must come
*after* `padded2DEulerGLM_isIRKStable`. Placed the new theorems right
before the §520D header to keep all `padded2DEulerGLM` content grouped.

Three theorems added to `OpenMath/Chapter5/Section520.lean`:

1. `padded2DEulerGLM_stabilityMatrix (z : ℂ) :
       padded2DEulerGLM.stabilityMatrix z = !![1 + z, 0; 0, 0]`
   Proof structure mirrors `explicitEulerGLM_stabilityMatrix`: prove
   `(1 - z • complexify A) = 1` (since `A = !![0]`), `rw [hA, inv_one]`,
   then `ext i j; fin_cases i <;> fin_cases j <;> simp [...]`.
2. `padded2DEulerGLM_stabilityFunction (w z : ℂ) :
       padded2DEulerGLM.stabilityFunction w z = w * (w - (1 + z))`
   Used `Matrix.det_fin_two`, `Matrix.smul_apply`, `ring`.
3. `padded2DEulerGLM_isRKStable : padded2DEulerGLM.IsRKStable`
   With `R(z) := 1 + z`, after `rw [padded2DEulerGLM_stabilityFunction]`,
   `simp [pow_one]` closes the goal (Lean reduces `(2 : ℕ) - 1 = 1` by
   defeq, no `norm_num` needed).

## Result
**SUCCESS** — all three theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Cycle 130/133 witnesses
remain axiom-clean (regression check passed):

* `padded2DEulerGLM_stabilityMatrix` — axiom-clean
* `padded2DEulerGLM_stabilityFunction` — axiom-clean
* `padded2DEulerGLM_isRKStable` — axiom-clean
* `explicitEulerGLM_isRKStable` — axiom-clean (preserved)
* `padded2DEulerGLM_isIRKStable` — axiom-clean (preserved)
* `explicitEulerGLM_isIRKStable` — axiom-clean (preserved)

`lake build OpenMath.Chapter5.Section520` succeeds in 5.3s with no
warnings.

## Faithfulness check

### `padded2DEulerGLM_stabilityMatrix`
- Entity ID: N/A (computational closed-form lemma about a witness object,
  not a textbook concept).
- Lean statement captures: same content as the textbook formula
  `M(z) = V + zB(I−zA)⁻¹U` evaluated at the four blocks of
  `padded2DEulerGLM`.
- Tautology check: conclusion `M(z) = !![1+z, 0; 0, 0]` is not a
  hypothesis (zero hypotheses).
- Identity check: proof is non-trivial — unfolds the resolvent, computes
  the matrix product entry-by-entry.

### `padded2DEulerGLM_stabilityFunction`
- Entity ID: N/A (computational closed-form lemma).
- Lean statement captures: same content as `Φ(w,z) = det(wI − M(z))`
  applied to the closed-form `M(z)`.
- Tautology check: conclusion is a `=`, not a hypothesis.
- Identity check: proof is non-trivial — invokes `Matrix.det_fin_two`
  and ring normalisation.

### `padded2DEulerGLM_isRKStable` — entity ID `def:542A`
- Textbook statement (from `entities/def_542A.json` `statement_latex`):
  > "A general linear method `(A, U, B, V)` has Runge–Kutta stability
  > (RK stability) if its characteristic polynomial, given by
  > `Φ(w,z) = det(wI − V − zB(I−zA)⁻¹U)`, has the form
  > `Φ(w,z) = w^{r−1}(w − R(z))`. The rational function `R(z)` is the
  > stability function of the method."
- Lean statement captures: **same content** as cycle 130. The
  `IsRKStable` predicate (line 525-528) is unchanged. This theorem
  exhibits a second inhabitant (`padded2DEulerGLM`) of the same
  predicate. No divergence.
- Tautology check: conclusion `padded2DEulerGLM.IsRKStable` is not a
  hypothesis (zero hypotheses).
- Identity check: proof is not `exact h` — produces an explicit
  `R := fun z => 1 + z` and proves the `∀ w z` factorisation by
  unfolding to the closed-form `Φ(w, z) = w · (w − (1+z))` from
  theorem 2.
- Substantive vs vacuous: **substantive**. With `r = 2`,
  `w^(r−1) = w^1 = w`, so the factorisation states
  `Φ(w, z) = w · (w − R(z))`, which is a genuine claim that
  `Φ(·, z)` has `w = 0` as a root for every `z`. The cycle 130
  `r = 1` witness has `w^0 = 1`, making the factorisation a trivial
  restatement of `Φ(w, z) = w − R(z)`.

## Dead ends
None. All three proofs went through on the first try as the strategy
predicted, with only minor cleanup:
* The `Fin.sum_univ_succ` / `Fin.sum_univ_zero` simp arguments in step 1
  flagged as unused by the linter — removed (the matrix-literal simp
  lemmas in `Mathlib.Data.Matrix.Notation` already handle the small-`Fin`
  summations, matching cycle 133's finding).
* `Matrix.one_apply` was unused in step 2 — removed (after
  `rw [Matrix.det_fin_two]`, the `1`-matrix indexing simplifies via
  default simp-set).
* The trailing `ring` after `simp [pow_one]` in step 3 was redundant
  ("no goals to be solved") because `simp [pow_one]` together with the
  `R := fun z => 1 + z` β-reduction and Lean's defeq `(2 : ℕ) - 1 = 1`
  fully closes the goal — removed.

## Discovery
* The pattern `simp [pow_one]` already discharges
  `w * (w - R z) = w ^ (r - 1) * (w - R z)` when `r = 2` (Nat sub) by
  defeq — no need for `show (2 : ℕ) - 1 = 1 from rfl` or `norm_num`.
  Useful for any future r=2 witness for a `w^(r-1) · (w − R z)`-shape
  factorisation.
* `Matrix.det_fin_two` followed by `simp [Matrix.smul_apply]; ring`
  is the canonical recipe for explicit 2×2 stability-function
  computations on `wI − M(z)` shapes — same recipe will work for any
  `r = 2` GLM whose `M(z)` has been put in closed form.

## Suggested next approach
1. **`thm:551B` — Single Non Zero Eigenvalue Stability**
   (Butcher §551, p. 460+). Read
   `extraction/formalization_data/entities/thm_551B.json` to classify
   the prerequisite stack. This is the natural successor: with
   `def:551A` IRK-stability and `def:542A` RK-stability both formalized
   with substantive r=2 witnesses, the §551 theorem connecting the two
   is now reachable. Likely needs `det(wI − M(z))` computed in terms
   of the IRK structure matrices `(B, U, A, X)` — the
   `padded2DEulerGLM_stabilityMatrix` / `padded2DEulerGLM_isIRKStable`
   pair already provides a regression test for any closed-form result.
2. **Open the next leaf-node Chapter 3 entity** — `def:381F`
   P-equivalent, `lem:351A` criteria for A-stability, or one of the
   §302 enumeration lemmas. These are independent of the §551 stack
   and provide breadth.
3. **Negative-witness work on `def:520E` A-stability** —
   `R(z) = 1 + z` for `padded2DEulerGLM`/`explicitEulerGLM` is *not*
   A-stable (instability at `z = -2 + 0i`: `|R(-2)| = |-1| = 1` but
   `|R(z)| > 1` for `z` slightly to the right). A negative-witness
   theorem `¬ explicitEulerGLM.IsAStable` would be a different shape
   from cycles 130–134's positive-witness pattern. Defer until the
   §551 frontier is clearer.
