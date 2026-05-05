import Mathlib

/-! Cycle 116 — Aristotle batch for `aux_515D_output_tendsto` body
composition (Butcher §515D). The cycle 110–115 sub-lemmas are
declared as `axiom`s so the prover can attempt the body composition
*independently* of the Lean source tree.

The target is:

  theorem aux_515D_output_tendsto_target ... : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop (nhds (fun i => u i * yex x))

The proof should:

1. Use `aux_515D_construct_ell_U_phi_A` to obtain `ell_U` and `phi_A`.
2. For each step `m < n`, use `localStepError_bound` to obtain a per-step
   error bound (with K_m and the residual decomposition).
3. Combine into the per-step recurrence δ (m+1) ≤ V_norm·δ m + α·h·δ m + β·h².
4. Apply `aux_515D_per_step_recurrence` to get the closed-form bound.
5. Convert to the form needed by `aux_515D_gronwall_bound` and apply.
6. Apply `aux_515D_squeeze` with δ0_seq → 0 (from the φ tendsto hypothesis).

If the body proof is too long, focus on the high-level structure with
intermediate `have` statements and let later cycles fill in routine
algebraic steps.
-/

open scoped BigOperators

namespace AristotleBatch116

universe u_s u_r

-- Stand-in placeholder for `GeneralLinearMethod` (treated abstractly here).
variable (s r : ℕ)

/-- Place-holder for the GLM: any record with the matrices we need. We
    abstract away the encoding so Aristotle can focus on the body.
    The actual file will use `GeneralLinearMethod s r`. -/
structure AbstractGLM where
  A : Matrix (Fin s) (Fin s) ℝ
  U : Matrix (Fin s) (Fin r) ℝ
  B : Matrix (Fin r) (Fin s) ℝ
  V : Matrix (Fin r) (Fin r) ℝ

variable {s r}

-- AXIOMS (these are theorems in the actual file, but the prover does
-- not need their bodies — only their signatures.)

axiom IsStable {s r : ℕ} (M : AbstractGLM s r) : Prop

axiom IsGLMSolution {s r : ℕ} (M : AbstractGLM s r)
  (h : ℝ) (f : ℝ → ℝ) (y_seq : ℕ → Fin r → ℝ) : Prop

/-- M-matrix construction of (ell_U, phi_A). Cycle 114. -/
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

/-- Per-step recurrence ⇒ closed-form bound. Cycle 113 (Aristotle). -/
axiom aux_515D_per_step_recurrence
    {V_norm α β h : ℝ}
    (hV_nn : 0 ≤ V_norm) (hα_nn : 0 ≤ α) (hβ_nn : 0 ≤ β) (hh : 0 ≤ h)
    (δ : ℕ → ℝ) (hδ_nn : ∀ m, 0 ≤ δ m)
    (hrec : ∀ m, δ (m + 1) ≤ V_norm * δ m + α * h * δ m + β * h^2) :
    ∀ n, δ n ≤ (V_norm + α * h)^n * δ 0
              + β * h^2 * (∑ k ∈ Finset.range n, (V_norm + α * h)^k)

/-- Discrete Grönwall closed-form. Cycle 113 (Aristotle). -/
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

/-- Squeeze argument. Cycle 112 (manual). -/
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

/-- Strengthened `localStepError_bound` (cycle 116 Phase 2). -/
axiom localStepError_bound_strengthened
    {s r : ℕ}
    (M : AbstractGLM s r)
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
    (hc_def : True)  -- abstract placeholder for c = M.glmAbscissae v
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
    -- Strengthened (cycle 116): localized M_bound hypotheses.
    (hy_M_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
        |yex t| ≤ M_bound)
    (hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
        |deriv yex t| ≤ L * M_bound)
    (hy_M_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h), |yex t| ≤ M_bound)
    (hy'_LM_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h),
        |deriv yex t| ≤ L * M_bound)
    (h_norm : ‖((h₀ * L) • M.A.map (fun x => |x|) :
                 Matrix (Fin s) (Fin s) ℝ)‖ < 1) :
    ∃ K : Fin r → ℝ,
      (∀ i,
        h * (∑ j, M.B i j * f (Y j))
          + (∑ j, M.V i j * yt_prev j)
          - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
          = (∑ j, M.V i j * δ j) + K i)
      ∧ (∀ i, |K i| ≤ α * h * δ_max + β * h^2)

/-- TARGET (sorry to fill): output convergence of the GLM iteration. -/
theorem aux_515D_output_tendsto_target {s r : ℕ}
    (M : AbstractGLM s r)
    (hStab : IsStable M)
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
    -- Strengthened (cycle 116) hypotheses inherited from IsConvergent.
    (M_bound : ℝ) (hM_nn : 0 ≤ M_bound)
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound)
    (hyex'_LM : ∀ t ∈ Set.Icc x₀ x, |deriv yex t| ≤ (L : ℝ) * M_bound)
    (h_norm : ‖((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|)‖ < 1)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      IsGLMSolution M ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))) :
    Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
        (nhds (fun i => u i * yex x)) := by
  sorry

end AristotleBatch116
