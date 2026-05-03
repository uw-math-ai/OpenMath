import Mathlib

/-! Cycle 092 — Aristotle batch for `thm:513A` infrastructure helpers.

Self-contained file with the GLM structure inlined and five
infrastructure helpers as `sorry`s. The helpers are:

* `runningMaxNorm` family (Helper 1) — port of
  `LinearMultistepMethod.runningMaxAbs` from
  `OpenMath/Chapter4/Section404.lean:5651–5719`.
* `unit_vector_witness_of_not_stable` (Helper 2) — extract a
  unit-norm sequence `w` with unbounded `‖V^n *ᵥ w n‖` from the
  negation of `IsStable` (the row-realiser construction).
* `glmZeroIterate` and `glmZeroIterate_isGLMSolution` (Helper 3) —
  for `f ≡ 0`, the sequence `y_seq n := V^n *ᵥ y₀` is a GLM
  iteration.
* `glmZeroIterate_const_smul` (Helper 4) — closure under scalar
  multiplication.
* `unbounded_zero_iterate_contra` (Helper 5) — the record-index
  argument that derives a contradiction from convergence to zero
  of the rescaled sequence.
-/

open Matrix
open scoped BigOperators Topology

namespace AristotleBatch092

/-- A general linear method (Butcher §510) with `s` internal stages
and `r` input/output values. -/
structure GeneralLinearMethod (s r : ℕ) where
  A : Matrix (Fin s) (Fin s) ℝ
  U : Matrix (Fin s) (Fin r) ℝ
  B : Matrix (Fin r) (Fin s) ℝ
  V : Matrix (Fin r) (Fin r) ℝ

/-- Iteration recurrence (def:511, used by def:512A). -/
def GeneralLinearMethod.IsGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (f : ℝ → ℝ)
    (y_seq : ℕ → Fin r → ℝ) : Prop :=
  ∀ n : ℕ, ∃ Y : Fin s → ℝ,
    (∀ i, Y i = (∑ j, M.A i j * (h * f (Y j)))
                + (∑ j, M.U i j * y_seq n j))
    ∧ (∀ i, y_seq (n + 1) i = (∑ j, M.B i j * (h * f (Y j)))
                              + (∑ j, M.V i j * y_seq n j))

/-- Cycle 091 helper, included for `glmZeroIterate_isGLMSolution`. -/
theorem isGLMSolution_zero_iff {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y_seq : ℕ → Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) y_seq ↔
    ∀ n : ℕ, ∀ i : Fin r,
      y_seq (n + 1) i = ∑ j : Fin r, M.V i j * y_seq n j := by
  unfold GeneralLinearMethod.IsGLMSolution
  constructor
  · intro hSol n i
    obtain ⟨Y, _hStage, hOut⟩ := hSol n
    have h1 := hOut i
    simp only [mul_zero, Finset.sum_const_zero, zero_add] at h1
    exact h1
  · intro hHom n
    refine ⟨fun i => ∑ j, M.U i j * y_seq n j, ?_, ?_⟩
    · intro i
      simp only [mul_zero, Finset.sum_const_zero, zero_add]
    · intro i
      simp only [mul_zero, Finset.sum_const_zero, zero_add]
      exact hHom n i

/-! ## Helper 1 — `runningMaxNorm` family

Direct port of `runningMaxAbs` family from `Section404.lean`,
specialised to a real-valued sequence (we apply it to
`fun n => ‖V^n *ᵥ w n‖`).
-/

/-- Running maximum of a real-valued sequence. -/
def runningMaxNorm (z : ℕ → ℝ) : ℕ → ℝ
  | 0     => z 0
  | n + 1 => max (runningMaxNorm z n) (z (n + 1))

theorem runningMaxNorm_monotone (z : ℕ → ℝ) :
    Monotone (runningMaxNorm z) := by
  sorry

theorem runningMaxNorm_ge (z : ℕ → ℝ) (n : ℕ) :
    z n ≤ runningMaxNorm z n := by
  sorry

theorem runningMaxNorm_atTop_of_unbounded
    {z : ℕ → ℝ} (hz : ∀ C : ℝ, ∃ n, C < z n) :
    Filter.Tendsto (runningMaxNorm z) Filter.atTop Filter.atTop := by
  sorry

theorem runningMaxNorm_record_above
    {z : ℕ → ℝ} (hz_nn : ∀ n, 0 ≤ z n) (hz : ∀ C : ℝ, ∃ n, C < z n)
    (N : ℕ) :
    ∃ n, N ≤ n ∧ z n = runningMaxNorm z n := by
  sorry

/-! ## Helper 2 — unit-norm witness extractor

From `¬ M.IsStable` (i.e. `∀ C, ∃ n, C < ‖M.V^n‖`), extract a
sequence `w : ℕ → Fin r → ℝ` with `‖w n‖ ≤ 1` and
`‖V^n *ᵥ w n‖` unbounded.

Construction (textbook): for each `n`, pick the row of `V^n` with
maximal ℓ¹ row-sum (this row achieves the linfty operator norm),
and set `w n j := sign((V^n) i_n j)` (cast as `±1`). Then
`((V^n) *ᵥ w n) i_n` equals the row's ℓ¹ norm = `‖V^n‖`, so
`‖V^n *ᵥ w n‖ ≥ ‖V^n‖` is unbounded.
-/

theorem unit_vector_witness_of_not_stable
    {s r : ℕ} {M : GeneralLinearMethod s r}
    (h_ns : ∀ C : ℝ, ∃ n, C < ‖M.V ^ n‖) :
    ∃ w : ℕ → Fin r → ℝ,
      (∀ n, ‖w n‖ ≤ 1) ∧
      (∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖) := by
  sorry

/-! ## Helpers 3 and 4 — `glmZeroIterate` -/

/-- The pure-`V` iterate from a starting vector `y₀`: the value at
step `n` is `V^n *ᵥ y₀`. -/
def GeneralLinearMethod.glmZeroIterate {s r : ℕ}
    (M : GeneralLinearMethod s r) (y₀ : Fin r → ℝ) (n : ℕ) :
    Fin r → ℝ :=
  (M.V ^ n) *ᵥ y₀

theorem GeneralLinearMethod.glmZeroIterate_isGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y₀ : Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) (M.glmZeroIterate y₀) := by
  sorry

theorem GeneralLinearMethod.glmZeroIterate_const_smul {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y₀ : Fin r → ℝ) (c : ℝ) :
    M.IsGLMSolution h (fun _ => 0)
      (fun n i => c * (M.glmZeroIterate y₀ n) i) := by
  sorry

/-! ## Helper 5 — Vector-version contradiction extractor -/

theorem unbounded_zero_iterate_contra
    {s r : ℕ} {M : GeneralLinearMethod s r}
    {w : ℕ → Fin r → ℝ}
    (_hw_unit : ∀ n, ‖w n‖ ≤ 1)
    (hw_unbd : ∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖)
    (hY : Filter.Tendsto
            (fun n : ℕ => ‖(M.V ^ n) *ᵥ w n‖ /
                            runningMaxNorm
                              (fun i => ‖(M.V ^ i) *ᵥ w i‖) n)
            Filter.atTop (nhds 0)) :
    False := by
  sorry

end AristotleBatch092
