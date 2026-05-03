import Mathlib

/-! Cycle 103 — Aristotle batch for `lem:515B` (Butcher §515) sub-lemmas.

Self-contained file with three sorry-first sub-lemmas decomposing the
local-step error propagation bound (515B) of Butcher's §515. The
textbook proof (p. 414) writes:

  K_i^[n] = h Σ B_{ij}·(f(Y_j) − f(Ŷ_j)) − R_i,

where Ŷ_j = exact stage value y(x_{n-1} + h c_j), Y_j = computed
stage value, η_j = Ŷ_j − Y_j, δ_k = ỹ_k^[n-1] − y_k^[n-1], R_i is
the (515b)-bound residual, and ‖K^[n]‖ ≤ h α max|δ| + β h².

The four moving parts:

1. **Residual decomposition** (closed manually in the project file).
2. **Lipschitz bridge**: `|h Σ B·(f(Ŷ) − f(Y))| ≤ h L Σ|B|·|η|`.
3. **η contraction**: `|η_j| ≤ ell_U_j · max|δ| + h² L² M ϕ_A_j`,
   given the per-stage estimate and positivity of `(I − h₀ L|A|)^{−1}`.
4. **Main combination** (the full `localStepError_bound`).

This batch contains (2), (3), and (4). For (3), `ell_U` and `phi_A`
are taken as parameters with their defining linear-system side
conditions (RHS = `Σ|U_{jk}|` and `½c_j² + Σ|A_{jk}c_k|`), avoiding
the need to construct `(I − h₀ L|A|)^{-1}` explicitly.

Variable conventions (matching `OpenMath/Chapter5/Section515.lean`):

* `M : GeneralLinearMethod s r` with submatrices `A, U, B, V`;
  here we use the four submatrices as bare parameters.
* `f : ℝ → ℝ`, Lipschitz with constant `L ≥ 0`.
* `yex : ℝ → ℝ`, `C¹`, with `yex'(t) = f(yex(t))` and `|yex t| ≤ M`.
* `c : Fin s → ℝ` with `0 ≤ c i` (abscissae).
* `0 ≤ h ≤ h₀`, `0 ≤ L`, `0 ≤ M`, `0 ≤ δ_max`.
-/

open Matrix
open scoped BigOperators

namespace AristotleBatch103

/-- **Sub-lemma 1** — Lipschitz bridge.

`f` Lipschitz with constant `L` implies, for `Y_hat, Y : Fin s → ℝ`,
`B : Matrix (Fin r) (Fin s) ℝ`, `h ≥ 0`, `i : Fin r`,
`|h Σ_j B_{ij}·(f(Ŷ_j) − f(Y_j))| ≤ h·L · Σ_j |B_{ij}| · |Ŷ_j − Y_j|`.

Proof sketch: |Σ| ≤ Σ |·|, then Lipschitz on `f`, then sum reorganization
(see `aux_T4_bound` in the project for an analogous closed proof). -/
theorem aux_515B_lipschitz_bridge {s r : ℕ}
    {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf_lip : LipschitzWith L.toNNReal f)
    (B : Matrix (Fin r) (Fin s) ℝ)
    (Y_hat Y : Fin s → ℝ)
    (h : ℝ) (hh : 0 ≤ h) (i : Fin r) :
    |h * ∑ j, B i j * (f (Y_hat j) - f (Y j))|
      ≤ h * L * ∑ j, |B i j| * |Y_hat j - Y j| := by
  sorry

/-- **Sub-lemma 2** — η contraction via `(I − h₀ L|A|)^{−1}` positivity.

Given the per-stage contraction estimate
`|η_j − Σ_k U_{jk}·δ_k| ≤ h L Σ_k|A_{jk}|·|η_k| + h² L² M (½c_j² + Σ|A_{jk}·c_k|)`,
with `|δ_k| ≤ δ_max` and `h ≤ h₀`, conclude
`|η_j| ≤ ell_U_j · δ_max + h² L² M · phi_A_j`,
where `ell_U`, `phi_A` solve the two linear systems with right-hand
sides `Σ_k|U_{jk}|` and `½c_j² + Σ|A_{jk} c_k|` respectively.

Proof sketch: by triangle inequality, `|η_j| ≤ |Σ U·δ| + h L Σ|A|·|η| + h² L² M (½c² + Σ|A c|)`
            ≤ Σ|U_{jk}|·δ_max + h₀ L Σ|A|·|η| + h² L² M (½c² + Σ|A c|).
Now `(I − h₀ L|A|) (η − ell_U·δ_max − h² L² M phi_A) ≤ 0` componentwise
by the linear-system side conditions. By positivity of `(I − h₀ L|A|)^{-1}`
(when h₀ L ‖A‖_∞ < 1, but more weakly: when |A| has entries ≥ 0 and
the operator I − h₀L|A| has a nonneg inverse), we conclude
`η_j − ell_U_j · δ_max − h² L² M · phi_A_j ≤ 0`. -/
theorem aux_515B_eta_contraction {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ)
    (U : Matrix (Fin s) (Fin r) ℝ)
    {h h₀ L M_bound δ_max : ℝ}
    (hh : 0 ≤ h) (hh_le : h ≤ h₀) (h₀_pos : 0 < h₀)
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hδ_max_nonneg : 0 ≤ δ_max)
    (c : Fin s → ℝ) (hc_nonneg : ∀ i, 0 ≤ c i)
    (ell_U phi_A η : Fin s → ℝ)
    (hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |A i j| * ell_U j)
                    = ∑ j, |U i j|)
    (hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |A i j| * phi_A j)
                    = (1/2) * (c i)^2 + ∑ j, |A i j * c j|)
    (δ : Fin r → ℝ)
    (hδ_max : ∀ k, |δ k| ≤ δ_max)
    (hcontraction : ∀ j, |η j - ∑ k, U j k * δ k|
                          ≤ h * L * (∑ k, |A j k| * |η k|)
                            + h^2 * L^2 * M_bound *
                              ((1/2) * (c j)^2 + ∑ k, |A j k * c k|)) :
    ∀ j, |η j| ≤ ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j := by
  sorry

/-- **Sub-lemma 3** — Main combination: full Lemma 515B.

This is the top-level claim of `lem:515B`. The strategy decomposes
into the residual decomposition, the Lipschitz bridge, and the η
contraction; this lemma combines them into the K bound

  `|K_i| ≤ α · h · δ_max + β · h²`,

where K_i is uniquely identified by the propagation identity
`ỹ^[n]_i − y^[n]_i = Σ V·δ + K_i`, and α, β are upper-bound proxy
parameters.

This is the same statement as `GeneralLinearMethod.localStepError_bound`
in the project file, but with the GLM's submatrices `A, U, B, V`
unpacked and named to keep the file self-contained for Aristotle. -/
theorem aux_515B_main_combination {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ)
    (U : Matrix (Fin s) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ)
    (V : Matrix (Fin r) (Fin r) ℝ)
    {h h₀ L M_bound α β δ_max : ℝ}
    (hh : 0 ≤ h) (hh_le : h ≤ h₀) (h₀_pos : 0 < h₀)
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (f : ℝ → ℝ) (hf_lip : LipschitzWith L.toNNReal f)
    (yex : ℝ → ℝ)
    (hy_C1 : ContDiff ℝ 1 yex)
    (hy_ode : ∀ t, deriv yex t = f (yex t))
    (hy_M : ∀ t, |yex t| ≤ M_bound)
    (hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (hVu : V *ᵥ u = u) (hUu : U *ᵥ u = (fun _ => 1))
    (hCons : B *ᵥ (fun _ => 1) + V *ᵥ v = u + v)
    (c : Fin s → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_def : c = A *ᵥ (fun _ => 1) + U *ᵥ v)
    (ell_U phi_A : Fin s → ℝ)
    (hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |A i j| * ell_U j)
                    = ∑ j, |U i j|)
    (hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |A i j| * phi_A j)
                    = (1/2) * (c i)^2 + ∑ j, |A i j * c j|)
    (hα_def : ∀ i, L * (∑ j, |B i j| * ell_U j) ≤ α)
    (hβ_def : ∀ i, L^2 * M_bound *
                ((1/2) * |u i| + |v i|
                 + (∑ j, |B i j * c j|)
                 + h₀ * L * (∑ j, |B i j| * phi_A j)) ≤ β)
    (yt_prev δ : Fin r → ℝ)
    (hδ_def : ∀ k, δ k = yt_prev k -
                          (u k * yex xn1 + v k * h * deriv yex xn1))
    (hδ_max : ∀ k, |δ k| ≤ δ_max)
    (hδ_max_nonneg : 0 ≤ δ_max)
    (Y : Fin s → ℝ)
    (hY_stage : ∀ i, Y i = h * (∑ j, A i j * f (Y j))
                          + ∑ j, U i j * yt_prev j) :
    ∃ K : Fin r → ℝ,
      (∀ i,
        h * (∑ j, B i j * f (Y j))
          + (∑ j, V i j * yt_prev j)
          - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
          = (∑ j, V i j * δ j) + K i)
      ∧ (∀ i, |K i| ≤ α * h * δ_max + β * h^2) := by
  sorry

end AristotleBatch103
