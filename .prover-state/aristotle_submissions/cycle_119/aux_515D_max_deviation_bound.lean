/-
Cycle 119 Aristotle Job 3: close the body of
`aux_515D_max_deviation_bound_tendsto_zero` (cycle 118's narrowed
scalar helper). This is the final §515D sorry of OpenMath.

Target conclusion: existence of a non-negative `δ_seq : ℕ → ℝ` tending
to 0 such that for all `n > 0`, `i : Fin r`,
    `|Y n n i − (u i · yex(x) + v i · h_n · deriv yex(x))| ≤ δ_seq n`,
where `h_n := (x − x₀)/n`.

The intended composition: build δ_seq from the geometric closed-form
output of `aux_515D_per_step_recurrence`, scale by `Real.exp(α·Δx)` via
`aux_515D_one_add_pow_le_exp`, and use `aux_515D_squeeze` (or direct
limit reasoning) to push to 0. The starting deviation goes to 0 via
`hφ` composed with `tendsto_const_div_atTop_nhds_zero_nat`.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Matrix
open scoped BigOperators Topology

namespace AristotleSandbox

/-- GLM data for sandboxing. -/
structure GeneralLinearMethod (s r : ℕ) where
  A : Matrix (Fin s) (Fin s) ℝ
  U : Matrix (Fin s) (Fin r) ℝ
  B : Matrix (Fin r) (Fin s) ℝ
  V : Matrix (Fin r) (Fin r) ℝ

def GeneralLinearMethod.IsStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ‖M.V ^ n‖ ≤ C

def GeneralLinearMethod.IsGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (f : ℝ → ℝ)
    (y_seq : ℕ → Fin r → ℝ) : Prop :=
  ∀ n : ℕ, ∃ Y : Fin s → ℝ,
    (∀ i, Y i = (∑ j, M.A i j * (h * f (Y j)))
                + (∑ j, M.U i j * y_seq n j))
    ∧ (∀ i, y_seq (n + 1) i = (∑ j, M.B i j * (h * f (Y j)))
                              + (∑ j, M.V i j * y_seq n j))

def GeneralLinearMethod.glmAbscissae {s r : ℕ}
    (M : GeneralLinearMethod s r) (v : Fin r → ℝ) : Fin s → ℝ :=
  M.A *ᵥ (fun _ => 1) + M.U *ᵥ v

/-- Cycle 114: M-matrix construction of ell_U, phi_A. -/
axiom aux_515D_construct_ell_U_phi_A
    {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ)
    (U : Matrix (Fin s) (Fin r) ℝ)
    {h₀ L : ℝ} (h₀_pos : 0 < h₀) (hL : 0 ≤ L)
    (c : Fin s → ℝ) (hc_nonneg : ∀ i, 0 ≤ c i)
    (h_norm : ‖((h₀ * L) • A.map (fun a => |a|) :
                 Matrix (Fin s) (Fin s) ℝ)‖ < 1) :
    ∃ ell_U phi_A : Fin s → ℝ,
      (∀ i, 0 ≤ ell_U i) ∧
      (∀ i, 0 ≤ phi_A i) ∧
      (∀ i, ell_U i - h₀ * L * (∑ j, |A i j| * ell_U j)
              = ∑ j, |U i j|) ∧
      (∀ i, phi_A i - h₀ * L * (∑ j, |A i j| * phi_A j)
              = (1/2) * (c i)^2 + ∑ j, |A i j * c j|)

/-- Cycle 116 strengthened lem:515B: local-step error bound. -/
axiom GeneralLinearMethod.localStepError_bound {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {h h₀ L M_bound α β δ_max : ℝ}
    (hh : 0 ≤ h) (hh_le : h ≤ h₀) (h₀_pos : 0 < h₀)
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (f : ℝ → ℝ) (hf_lip : LipschitzWith L.toNNReal f)
    (yex : ℝ → ℝ)
    (hy_C1 : ContDiff ℝ 1 yex)
    (hy_ode : ∀ t, deriv yex t = f (yex t))
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    (c : Fin s → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_def : c = M.glmAbscissae v)
    (ell_U phi_A : Fin s → ℝ)
    (hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |M.A i j| * ell_U j)
                    = ∑ j, |M.U i j|)
    (hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |M.A i j| * phi_A j)
                    = (1/2) * (c i)^2 + ∑ j, |M.A i j * c j|)
    (hα_def : ∀ i, L * (∑ j, |M.B i j| * ell_U j) ≤ α)
    (hβ_def : ∀ i, L^2 * M_bound *
                ((1/2) * |u i| + |v i|
                 + (∑ j, |M.B i j * c j|)
                 + h₀ * L * (∑ j, |M.B i j| * phi_A j)) ≤ β)
    (yt_prev δ : Fin r → ℝ)
    (hδ_def : ∀ k, δ k = yt_prev k -
                          (u k * yex xn1 + v k * h * deriv yex xn1))
    (hδ_max : ∀ k, |δ k| ≤ δ_max)
    (hδ_max_nonneg : 0 ≤ δ_max)
    (Y : Fin s → ℝ)
    (hY_stage : ∀ i, Y i = h * (∑ j, M.A i j * f (Y j))
                          + ∑ j, M.U i j * yt_prev j)
    (hy_M_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
        |yex t| ≤ M_bound)
    (hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
        |deriv yex t| ≤ L * M_bound)
    (hy_M_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h), |yex t| ≤ M_bound)
    (hy'_LM_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h),
        |deriv yex t| ≤ L * M_bound)
    (h_norm : ‖((h₀ * L) • M.A.map (fun x => |x|) : Matrix (Fin s) (Fin s) ℝ)‖ < 1) :
    ∃ K : Fin r → ℝ,
      (∀ i,
        h * (∑ j, M.B i j * f (Y j))
          + (∑ j, M.V i j * yt_prev j)
          - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
          = (∑ j, M.V i j * δ j) + K i)
      ∧ (∀ i, |K i| ≤ α * h * δ_max + β * h^2)

/-- Cycle 113 sub-lemma A: per-step recurrence ⇒ geometric closed form. -/
axiom aux_515D_per_step_recurrence
    {V_norm α β h : ℝ}
    (hV_nn : 0 ≤ V_norm) (hα_nn : 0 ≤ α) (hβ_nn : 0 ≤ β) (hh : 0 ≤ h)
    (δ : ℕ → ℝ) (hδ_nn : ∀ m, 0 ≤ δ m)
    (hrec : ∀ m, δ (m + 1) ≤ V_norm * δ m + α * h * δ m + β * h^2) :
    ∀ n, δ n ≤ (V_norm + α * h)^n * δ 0
              + β * h^2 * (∑ k ∈ Finset.range n, (V_norm + α * h)^k)

/-- Cycle 113 sub-lemma B: discrete Grönwall closed form (sum form). -/
axiom aux_515D_gronwall_bound
    (u : ℕ → ℝ) (a α β h : ℝ)
    (ha : 0 ≤ a) (hα_pos : 0 < α) (hβ_nn : 0 ≤ β) (hh : 0 ≤ h)
    (hu0 : u 0 ≤ a)
    (hu_rec : ∀ m, 1 ≤ m →
      u m ≤ a + α * h * (∑ i ∈ Finset.Ico 1 m, u i)
              + β * h^2 * (m : ℝ))
    (n : ℕ) :
    u n ≤ Real.exp (α * (n : ℝ) * h) * a
            + (Real.exp (α * (n : ℝ) * h) - 1) * (β * h / α)

/-- Cycle 113: (1+c)^n ≤ exp(n·c) for c ≥ 0. -/
axiom aux_515D_one_add_pow_le_exp (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    (1 + c) ^ n ≤ Real.exp (↑n * c)

/-- Cycle 112 sub-lemma C: squeeze the bounded sequence to zero. -/
axiom aux_515D_squeeze
    {α β : ℝ} (hα_pos : 0 < α) (hβ_nn : 0 ≤ β)
    (Δx : ℝ) (hΔx_pos : 0 < Δx)
    (δ : ℕ → ℝ) (δ0_seq : ℕ → ℝ)
    (hδ_nn : ∀ n, 0 ≤ δ n)
    (hδ0_tendsto : Filter.Tendsto δ0_seq Filter.atTop (nhds 0))
    (h_bound : ∀ n : ℕ, 0 < n →
      δ n ≤ Real.exp (α * Δx) * δ0_seq n
            + (Real.exp (α * Δx) - 1) * (β * (Δx / (n : ℝ)) / α)) :
    Filter.Tendsto δ Filter.atTop (nhds 0)

/-- THE TARGET:
**Sub-lemma E for `aux_515D_componentwise_deviation_tendsto_zero`** —
existence of a uniform max-abs deviation bound sequence that tends to 0.

For some non-negative scalar sequence `δ_seq : ℕ → ℝ` tending to 0, the
deviation `Y n n i − (u i · yex(x) + v i · h_n · deriv yex(x))` is
uniformly bounded over `i : Fin r` by `δ_seq n` (eventually for `n > 0`).

This is the final §515D sorry. Closing it closes
`aux_515D_componentwise_deviation_tendsto_zero`, then
`aux_515D_output_tendsto`, then `stable_consistent_isConvergent`,
then thm:515D — the Chapter 5 capstone. -/
theorem aux_515D_max_deviation_bound_tendsto_zero {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    {u v : Fin r → ℝ}
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {φ : ℝ → Fin r → ℝ}
    (hφ : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                          (nhds 0) (nhds (u i * y₀)))
    {x : ℝ} (hxx : x₀ < x)
    {M_bound : ℝ} (hM_nn : 0 ≤ M_bound)
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound)
    (hyex'_LM : ∀ t ∈ Set.Icc x₀ x, |deriv yex t| ≤ (L : ℝ) * M_bound)
    (h_norm : ‖(((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|) :
                 Matrix (Fin s) (Fin s) ℝ)‖ < 1)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))) :
    ∃ δ_seq : ℕ → ℝ,
      (∀ n, 0 ≤ δ_seq n) ∧
      Filter.Tendsto δ_seq Filter.atTop (nhds 0) ∧
      ∀ n : ℕ, 0 < n → ∀ i : Fin r,
        |Y n n i - (u i * yex x + v i * ((x - x₀) / (n : ℝ)) * deriv yex x)|
          ≤ δ_seq n := by
  sorry

end AristotleSandbox
