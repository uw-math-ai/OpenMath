/-
Cycle 126 Aristotle Job: close `instabilityRegion_imp_spectralRadius_ge_one`
(sub-lemma D4 of Butcher Theorem 520D, p. 419).

This is the contrapositive of:
  spectralRadius ℂ Mz < 1 → ∃ C, ∀ k, ‖Mz^k‖ ≤ C
i.e., a uniform power-norm bound exists when the spectral radius is < 1.
The classical Mathlib chain: spectralRadius < 1 implies every charpoly /
minpoly root has norm < 1, hence (by §142's
`minpoly_roots_lt_one_imp_convergent`) the matrix is convergent
(`Tendsto (Mz^n) atTop (𝓝 0)`), hence power-bounded.

Recommended proof outline:
1. Suppose `spectralRadius ℂ Mz < 1`.
2. Show: every root `μ` of `(minpoly ℂ Mz)` satisfies `‖μ‖ < 1`.
   (Use `Matrix.minpoly_dvd_charpoly`, `Matrix.mem_spectrum_iff_isRoot_charpoly`,
   `le_iSup₂` to pass `(‖μ‖₊ : ℝ≥0∞) ≤ spectralRadius`, then ENNReal /
   NNReal casts.)
3. Apply `OpenMath.Chapter1.Section142.minpoly_roots_lt_one_imp_convergent`
   to conclude `Tendsto (fun n => Mz^n) atTop (𝓝 0)`.
4. From the Tendsto, derive `BddAbove (range (fun n => ‖Mz^n‖))` via
   `Filter.Tendsto.bddAbove_range` (needs `Tendsto.norm` first), and
   extract a uniform bound `C`.

Key Mathlib lemmas:
- `Matrix.mem_spectrum_iff_isRoot_charpoly`
- `Matrix.minpoly_dvd_charpoly`
- `minpoly.ne_zero (Matrix.isIntegral A)` (so `Polynomial.mem_roots` applies)
- `Polynomial.IsRoot.dvd`
- `le_iSup₂`
- `ENNReal.coe_lt_one_iff`
- `Filter.Tendsto.norm` (`norm_zero`)
- `Filter.Tendsto.bddAbove_range`
- `Set.mem_range_self`
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import OpenMath.Chapter1.Section142

set_option maxHeartbeats 400000

open Matrix
open scoped Matrix.Norms.Operator

/-- Standalone form of cycle 126 sub-lemma D4. -/
theorem instabilityRegion_imp_spectralRadius_ge_one
    {r : ℕ} (Mz : Matrix (Fin r) (Fin r) ℂ)
    (hz : ¬ ∃ C : ℝ, ∀ k : ℕ, ‖Mz ^ k‖ ≤ C) :
    1 ≤ spectralRadius ℂ Mz := by
  by_contra h_lt
  push_neg at h_lt
  -- h_lt : spectralRadius ℂ Mz < 1
  apply hz
  -- Step 1: minpoly roots have norm < 1
  have h_minpoly : ∀ μ : ℂ, μ ∈ (minpoly ℂ Mz).roots → ‖μ‖ < 1 := by
    intro μ hμ_root
    have hμ_minpoly : (minpoly ℂ Mz).IsRoot μ :=
      (Polynomial.mem_roots (minpoly.ne_zero (Matrix.isIntegral Mz))).mp hμ_root
    have h_dvd : minpoly ℂ Mz ∣ Mz.charpoly := Mz.minpoly_dvd_charpoly
    have hμ_charpoly : Mz.charpoly.IsRoot μ := hμ_minpoly.dvd h_dvd
    have hμ_spec : μ ∈ spectrum ℂ Mz :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ_charpoly
    -- (‖μ‖₊ : ℝ≥0∞) ≤ spectralRadius < 1
    have h_le : (‖μ‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ Mz :=
      le_iSup₂ (f := fun k _ => (‖k‖₊ : ℝ≥0∞)) μ hμ_spec
    have h_lt' : (‖μ‖₊ : ℝ≥0∞) < 1 := lt_of_le_of_lt h_le h_lt
    have h_lt_nn : ‖μ‖₊ < (1 : NNReal) := ENNReal.coe_lt_one_iff.mp h_lt'
    exact_mod_cast h_lt_nn
  -- Step 2: convergent
  have h_conv : OpenMath.Chapter1.Section142.Convergent Mz :=
    OpenMath.Chapter1.Section142.minpoly_roots_lt_one_imp_convergent Mz h_minpoly
  -- Step 3: power-bounded
  have h_norm_tend :
      Filter.Tendsto (fun n : ℕ => ‖Mz ^ n‖) Filter.atTop (nhds 0) := by
    have := h_conv.norm
    simpa using this
  obtain ⟨C, hC⟩ : BddAbove (Set.range (fun n : ℕ => ‖Mz ^ n‖)) :=
    h_norm_tend.bddAbove_range
  exact ⟨C, fun k => hC (Set.mem_range_self k)⟩
