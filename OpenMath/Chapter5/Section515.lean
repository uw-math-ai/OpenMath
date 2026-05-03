import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import OpenMath.Chapter5.Section512
import OpenMath.Chapter5.MMatrix

/-!
# Butcher §515 — Stability and consistency imply convergence (Lemma 515A)

This file opens §515 ("Stability and consistency imply convergence") of
Butcher 2008. The core target is `lem:515A`, which gives the
*stage-wise* and *output-wise* local truncation error bounds for a
general linear method applied to a Lipschitz autonomous-scalar ODE
`y'(x) = f(y(x))`.

## Textbook statement (quoted verbatim from `entities/lem_515A.json`)

> Assume `h ≤ h₀`, with `h₀ L ‖A‖_∞ < 1`. Define `ϕ ∈ ℝ^s` by
> `Σ_j (δ_{ij} − h₀ L |a_{ij}|) ϕ_j = ½ c_i² + Σ_j |a_{ij} c_j|`.
> Let `y_i^{[n−1]} = u_i y(x_{n−1}) + v_i h y'(x_{n−1})`,
> `y_i^{[n]} = u_i y(x_n) + v_i h y'(x_n)` for `i = 1, …, r`, and
> `Ŷ_i = y(x_{n−1} + h c_i)` for `i = 1, …, s`, where
> `c = A·𝟙 + U·v`. Let `Ŷ_i^∗` be the value computed exactly from
> `y^{[n−1]}`. Assume `f` is Lipschitz with constant `L` and the
> exact solution satisfies `‖y(x)‖ ≤ M`, `‖y'(x)‖ ≤ L M`. Then
>
>     ‖ Ŷ_i − h Σ_{j=1}^s a_{ij} f(Ŷ_j) − Σ_{j=1}^r U_{ij} y_j^{[n−1]} ‖
>       ≤ h² L² M ( ½ c_i² + Σ_{j=1}^s |a_{ij} c_j| ),                  (515a)
>
>     ‖ y_i^{[n]} − h Σ_{j=1}^s b_{ij} f(Ŷ_j) − Σ_{j=1}^r V_{ij} y_j^{[n−1]} ‖
>       ≤ h² L² M ( ½ |u_i| + |v_i| + Σ_{j=1}^s |b_{ij} c_j| ).         (515b)

## Encoding choices

* **Autonomous-scalar `f : ℝ → ℝ`.** Same convention as §512.
* **`c` as a parameter, not a definition (this cycle).** The
  abscissae vector `c = A·𝟙 + U·v` is set up as a definition
  `glmAbscissae` for downstream reuse, but the lemma takes `c` as a
  *parameter* with side condition `c = A·𝟙 + U·v`, to keep helpers
  decoupled from `IsConsistent`'s existential `v`. See cycle 100
  strategy for the rationale.
* **`ϕ` (the `ell` vector) deferred.** The textbook's defining
  linear system `(I − h₀ L |A|) ϕ = ½ c² + |A| |c|` is *not*
  consumed by the inequalities (515a) and (515b) themselves — it
  enters only at lem:515B, where the full local-error bound
  `‖Ŷ_i − Ŷ_i^∗‖ ≤ h² L² M ϕ_i` is derived. Cycle 100 therefore
  scaffolds (515a) and (515b) only and leaves `ϕ` for cycle 101.
* **Per `Section512.lean`**, the input vectors are encoded as
  `y_j^{[n−1]} = u_j · y(x_{n−1}) + v_j · h · y'(x_{n−1})` and
  `y_j^{[n]} = u_j · y(x_{n−1} + h) + v_j · h · y'(x_{n−1} + h)`
  (since `x_n = x_{n−1} + h`).

## Sub-lemma scaffold

The textbook proof of (515a) decomposes the residual as
`T1 + T2 + T3 + T4`, where:

* `T1 = Ŷ_i − y(x_{n−1}) − h ∫₀^{c_i} f(y(x_{n−1} + hξ)) dξ`     [= 0 by FTC]
* `T2 = y(x_{n−1}) + c_i h y'(x_{n−1}) − Σ U_{ij} y_j^{[n−1]} − Σ a_{ij} h y'(x_{n−1})`
                                                                  [= 0 by `c = A·𝟙 + U·v` and the input identities]
* `T3 = h ∫₀^{c_i} (f(y(x_{n−1} + hξ)) − y'(x_{n−1})) dξ`         [≤ ½ h² L² M c_i² by Lipschitz]
* `T4 = −h Σ a_{ij} (f(y(x_{n−1} + h c_j)) − y'(x_{n−1}))`        [≤ h² L² M Σ|a_{ij} c_j|]

The first preliminary `‖y(x + hξ) − y(x)‖ ≤ |ξ| h L M`
(`aux_y_diff_norm_bound`) is closed manually below; the four
`Tk` bounds are submitted to Aristotle in the cycle-100 batch.

## Non-vacuity

The abscissae `c = A·𝟙 + U·v` for `explicitEulerGLM` (with `v = 0`)
collapses to `c = (fun _ => 0)`. Witness lemma
`explicitEulerGLM_glmAbscissae_eq_zero`.
-/

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped BigOperators Topology
open scoped Matrix.Norms.Frobenius

/-! ## §515 setup — abscissae vector `c = A·𝟙 + U·v` -/

/-- **Butcher §515 setup**: the abscissae vector
`c = A·𝟙 + U·v ∈ ℝ^s` for a GLM `(A, U, B, V)` with consistency
auxiliary vector `v ∈ ℝ^r`.

This is an auxiliary computational object (Butcher §515 introduces
it just before lem:515A as part of the local-truncation-error
analysis); it is NOT a textbook definition with its own number. The
lemma `lem:515A` takes a *parameter* `c` with side condition
`c = M.glmAbscissae v` rather than referring to this `def` directly,
to keep helper bounds decoupled from `IsConsistent`'s existential
`v`. -/
def GeneralLinearMethod.glmAbscissae {s r : ℕ}
    (M : GeneralLinearMethod s r) (v : Fin r → ℝ) : Fin s → ℝ :=
  M.A *ᵥ (fun _ => 1) + M.U *ᵥ v

/-- Non-vacuity: for `explicitEulerGLM` with `v = 0`, the abscissae
vector collapses to the zero vector. -/
theorem explicitEulerGLM_glmAbscissae_eq_zero :
    explicitEulerGLM.glmAbscissae (fun _ => 0) = (fun _ => 0) := by
  funext i
  fin_cases i
  simp [GeneralLinearMethod.glmAbscissae, explicitEulerGLM, dotProduct]

/-! ## Preliminary: pointwise bound on `|y(x + hξ) − y(x)|`

This is Butcher's first preliminary at the start of the §515
proof: by FTC and the hypothesis `|y'(x)| ≤ L M`,

  `|y(x_{n−1} + hξ) − y(x_{n−1})| ≤ |ξ| h L M`.

Reused from the proof structure of `Section404.exact_solution_norm_bound`,
adapted to allow `ξ` of either sign and to expose `L · M` as the
derivative bound directly. -/

/-- **Preliminary bound** for §515 (Butcher 2008, p. 412): if `y` is
a `C¹` solution to `y'(t) = f(y(t))` with `|f(y(t))| ≤ L · M_bound`
for all `t`, then for any `x`, `h ≥ 0`, and `ξ ∈ ℝ`,

  `|y(x + h·ξ) − y(x)| ≤ h · |ξ| · (L · M_bound)`.

The bound is symmetric in the sign of `ξ` (handled by `|ξ|` and
`|h·ξ| = h · |ξ|` for `h ≥ 0`). -/
lemma aux_y_diff_norm_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (x h : ℝ) (hh : 0 ≤ h) (ξ : ℝ) :
    |y (x + h * ξ) - y x| ≤ h * |ξ| * (L * M_bound) := by
  -- Step 1: f∘y is continuous (it equals deriv y, which is continuous from C¹ y).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  -- Step 2: HasDerivAt y (f (y t)) t at every t.
  have hderiv : ∀ t, HasDerivAt y (f (y t)) t := by
    intro t
    have hdiff := (hy_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t
    have ht := hdiff.hasDerivAt
    rw [hy_ode t] at ht
    exact ht
  -- Step 3: integrability.
  have hint : IntervalIntegrable (fun t => f (y t)) MeasureTheory.volume
                x (x + h * ξ) := hfy_cont.intervalIntegrable _ _
  -- Step 4: FTC.
  have hFTC : ∫ t in x..(x + h * ξ), f (y t) = y (x + h * ξ) - y x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  -- Step 5: bound the integral by L * M_bound.
  have hC : ∀ t ∈ Set.uIoc x (x + h * ξ), ‖f (y t)‖ ≤ L * M_bound := by
    intro t _
    rw [Real.norm_eq_abs]
    exact hf_y_bound t
  have hbound :
      |∫ t in x..(x + h * ξ), f (y t)| ≤ (L * M_bound) * |h * ξ| := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hC
    rw [Real.norm_eq_abs] at hb
    have hsub : (x + h * ξ) - x = h * ξ := by ring
    rw [hsub] at hb
    exact hb
  rw [hFTC] at hbound
  -- Step 6: |h * ξ| = h * |ξ| since h ≥ 0.
  have habs : |h * ξ| = h * |ξ| := by
    rw [abs_mul, abs_of_nonneg hh]
  rw [habs] at hbound
  calc |y (x + h * ξ) - y x|
      ≤ (L * M_bound) * (h * |ξ|) := hbound
    _ = h * |ξ| * (L * M_bound) := by ring

/-! ## Sub-lemmas for the (515a) decomposition

The textbook proof of (515a) decomposes the residual as `T1 + T2 + T3 + T4`,
proving `T1 = T2 = 0` (FTC + algebraic identity using `c = A·𝟙 + U·v`)
and `T3, T4` bounded via Lipschitz of `f` plus `aux_y_diff_norm_bound`. -/

/-- **(T1 ≡ 0)** FTC telescoping: if `y` is `C¹` with `y'(t) = f(y(t))`,
then `y(x + h·c_i) − y(x) − h·∫₀^{c_i} f(y(x + h·ξ)) dξ = 0`. -/
private theorem aux_T1_eq_zero
    {f : ℝ → ℝ}
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (x h c_i : ℝ) :
    y (x + h * c_i) - y x
      - h * ∫ ξ in (0 : ℝ)..c_i, f (y (x + h * ξ)) = 0 := by
  -- Continuity of f∘y (= deriv y).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  -- HasDerivAt y (f (y t)) t.
  have hderiv_y : ∀ t, HasDerivAt y (f (y t)) t := by
    intro t
    have hdiff := (hy_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t
    have ht := hdiff.hasDerivAt
    rw [hy_ode t] at ht
    exact ht
  -- Chain rule: G(c) = y(x + h*c) has derivative h * f(y(x + h*c)).
  have hG : ∀ c, HasDerivAt (fun c => y (x + h * c)) (h * f (y (x + h * c))) c := by
    intro c
    have h_inner : HasDerivAt (fun c : ℝ => x + h * c) h c := by
      have h1 : HasDerivAt (fun c : ℝ => h * c) h c := by
        simpa using (hasDerivAt_id c).const_mul h
      exact h1.const_add x
    have h_chain := (hderiv_y (x + h * c)).comp c h_inner
    convert h_chain using 1
    ring
  -- Continuity & integrability of the integrand.
  have hG'_cont : Continuous (fun c => h * f (y (x + h * c))) := by
    have hc1 : Continuous (fun c : ℝ => x + h * c) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact continuous_const.mul (hfy_cont.comp hc1)
  have hG'_int : IntervalIntegrable (fun c => h * f (y (x + h * c)))
                  MeasureTheory.volume 0 c_i :=
    hG'_cont.intervalIntegrable _ _
  -- FTC.
  have hFTC : ∫ c in (0:ℝ)..c_i, h * f (y (x + h * c))
              = y (x + h * c_i) - y (x + h * 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun c _ => hG c) hG'_int
  have hzero : x + h * 0 = x := by ring
  rw [hzero] at hFTC
  -- Pull h out of the integral.
  have hpull : ∫ c in (0:ℝ)..c_i, h * f (y (x + h * c))
              = h * ∫ c in (0:ℝ)..c_i, f (y (x + h * c)) :=
    intervalIntegral.integral_const_mul h _
  rw [hpull] at hFTC
  linarith

/-- **(T2 ≡ 0)** Algebraic identity using `c = A·𝟙 + U·v` and `U·u = 𝟙`:
`y(x) + c_i·h·y'(x) − Σ U_{ij}(u_j·y(x) + v_j·h·y'(x)) − Σ A_{ij}·h·y'(x) = 0`. -/
private theorem aux_T2_eq_zero {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (U : Matrix (Fin s) (Fin r) ℝ)
    (u v : Fin r → ℝ)
    (hUu : U *ᵥ u = (fun _ => 1))
    (c : Fin s → ℝ)
    (hc : c = A *ᵥ (fun _ => 1) + U *ᵥ v)
    {y : ℝ → ℝ} (x h : ℝ) (i : Fin s) :
    y x + c i * h * deriv y x
      - (∑ j, U i j * (u j * y x + v j * h * deriv y x))
      - (∑ j, A i j * h * deriv y x) = 0 := by
  -- Σ U_{ij} u_j = (U *ᵥ u) i = 1 (rfl-unfold of mulVec/dotProduct).
  have hUu_apply : (U *ᵥ u) i = ∑ j, U i j * u j := rfl
  have hUv_apply : (U *ᵥ v) i = ∑ j, U i j * v j := rfl
  have hA1_apply : (A *ᵥ (fun _ => (1:ℝ))) i = ∑ j, A i j := by
    show ∑ j, A i j * 1 = _
    simp
  have hUu_i : (∑ j, U i j * u j) = 1 := by
    rw [← hUu_apply, hUu]
  -- Distribute the U-sum into a y(x)-part and an h·y'(x)-part.
  have hU_split :
      (∑ j, U i j * (u j * y x + v j * h * deriv y x))
        = (∑ j, U i j * u j) * y x + (∑ j, U i j * v j) * h * deriv y x := by
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    · rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
  -- Σ A_{ij} h y'(x) = (Σ A_{ij}) * h * y'(x).
  have hA_split : (∑ j, A i j * h * deriv y x)
                = (∑ j, A i j) * h * deriv y x := by
    rw [Finset.sum_mul, Finset.sum_mul]
  -- c i = (A *ᵥ 1) i + (U *ᵥ v) i = Σ A_{ij} + Σ U_{ij} v_j.
  have hc_i : c i = (∑ j, A i j) + (∑ j, U i j * v j) := by
    rw [hc]
    show (A *ᵥ (fun _ => 1)) i + (U *ᵥ v) i = _
    rw [hA1_apply, hUv_apply]
  rw [hU_split, hA_split, hUu_i, hc_i]
  ring

/-- **(T3 bound)** With `0 ≤ c_i`, by Lipschitz of `f` and `aux_y_diff_norm_bound`:
`|h · ∫₀^{c_i} (f(y(x+hξ)) − f(y x)) dξ| ≤ ½ h² L² M c_i²`.

**Faithfulness divergence**: textbook treats `c_i ∈ ℝ`; we restrict to
`c_i ≥ 0`. The bound is sign-symmetric (proof for `c_i < 0` requires
sign-flipping the integration interval), but all standard GLMs (explicit
Euler `c = 0`, classical RK `c ∈ [0,1]`, Gauss `c ∈ (0,1)`) satisfy
`c_i ≥ 0`. The `c_i < 0` case can be added as a follow-up. -/
private theorem aux_T3_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (x h : ℝ) (hh : 0 ≤ h) (c_i : ℝ) (hc_i : 0 ≤ c_i) :
    |h * ∫ ξ in (0 : ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))|
      ≤ (1/2) * h^2 * L^2 * M_bound * c_i^2 := by
  -- Continuity of f∘y.
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]; exact hy_C1.continuous_deriv le_rfl
  -- Per-point Lipschitz bridge: |f(a) - f(b)| ≤ L * |a - b|.
  have hLip_abs : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b| := by
    intro a b
    have hd := hf_lip.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hcoe : (Real.toNNReal L : ℝ) = L := Real.coe_toNNReal L hL
    rw [hcoe] at hd
    exact hd
  -- The pointwise bound on |f(y(x+hξ)) - f(y x)| for ξ ∈ [0, c_i].
  have hpt_bound : ∀ ξ ∈ Set.Icc (0:ℝ) c_i,
      |f (y (x + h * ξ)) - f (y x)| ≤ h * ξ * (L * (L * M_bound)) := by
    intro ξ hξ
    have h1 : |f (y (x + h * ξ)) - f (y x)|
              ≤ L * |y (x + h * ξ) - y x| := hLip_abs _ _
    have h2 : |y (x + h * ξ) - y x| ≤ h * |ξ| * (L * M_bound) :=
      aux_y_diff_norm_bound hL hM hy_C1 hy_ode hf_y_bound x h hh ξ
    have hξ_nn : 0 ≤ ξ := hξ.1
    have habs_ξ : |ξ| = ξ := abs_of_nonneg hξ_nn
    rw [habs_ξ] at h2
    have h3 : L * |y (x + h * ξ) - y x| ≤ L * (h * ξ * (L * M_bound)) := by
      exact mul_le_mul_of_nonneg_left h2 hL
    calc |f (y (x + h * ξ)) - f (y x)|
        ≤ L * |y (x + h * ξ) - y x| := h1
      _ ≤ L * (h * ξ * (L * M_bound)) := h3
      _ = h * ξ * (L * (L * M_bound)) := by ring
  -- Step 1: |h * ∫…| = h * |∫…| since 0 ≤ h.
  have habs_h : |h * ∫ ξ in (0:ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))|
              = h * |∫ ξ in (0:ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))| := by
    rw [abs_mul, abs_of_nonneg hh]
  rw [habs_h]
  -- Step 2: |∫ g| ≤ ∫ |g|.
  have hint_g : IntervalIntegrable (fun ξ => f (y (x + h * ξ)) - f (y x))
                  MeasureTheory.volume 0 c_i := by
    have hc1 : Continuous (fun ξ : ℝ => x + h * ξ) :=
      continuous_const.add (continuous_const.mul continuous_id)
    have hf_yshift : Continuous (fun ξ => f (y (x + h * ξ))) := hfy_cont.comp hc1
    exact (hf_yshift.sub continuous_const).intervalIntegrable _ _
  have habs_int : |∫ ξ in (0:ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))|
                ≤ ∫ ξ in (0:ℝ)..c_i, |f (y (x + h * ξ)) - f (y x)| :=
    intervalIntegral.abs_integral_le_integral_abs hc_i
  -- Step 3: ∫ |g| ≤ ∫ (h * ξ * L² M).
  have hint_abs : IntervalIntegrable (fun ξ => |f (y (x + h * ξ)) - f (y x)|)
                  MeasureTheory.volume 0 c_i := hint_g.abs
  have hint_lin : IntervalIntegrable (fun ξ => h * ξ * (L * (L * M_bound)))
                  MeasureTheory.volume 0 c_i := by
    refine (((continuous_const.mul continuous_id).mul continuous_const)).intervalIntegrable _ _
  have hmono : ∫ ξ in (0:ℝ)..c_i, |f (y (x + h * ξ)) - f (y x)|
              ≤ ∫ ξ in (0:ℝ)..c_i, h * ξ * (L * (L * M_bound)) :=
    intervalIntegral.integral_mono_on hc_i hint_abs hint_lin hpt_bound
  -- Step 4: ∫ (h * ξ * (L * (L * M))) = h * (L * (L * M)) * c_i² / 2.
  have hint_eval : ∫ ξ in (0:ℝ)..c_i, h * ξ * (L * (L * M_bound))
                = h * (L * (L * M_bound)) * (c_i^2 / 2) := by
    have hrw : (fun ξ : ℝ => h * ξ * (L * (L * M_bound)))
              = (fun ξ : ℝ => (h * (L * (L * M_bound))) * ξ) := by
      funext ξ; ring
    rw [hrw, intervalIntegral.integral_const_mul, integral_id]
    ring
  -- Combine.
  calc h * |∫ ξ in (0:ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))|
      ≤ h * ∫ ξ in (0:ℝ)..c_i, |f (y (x + h * ξ)) - f (y x)| := by
          exact mul_le_mul_of_nonneg_left habs_int hh
    _ ≤ h * ∫ ξ in (0:ℝ)..c_i, h * ξ * (L * (L * M_bound)) := by
          exact mul_le_mul_of_nonneg_left hmono hh
    _ = h * (h * (L * (L * M_bound)) * (c_i^2 / 2)) := by rw [hint_eval]
    _ = (1/2) * h^2 * L^2 * M_bound * c_i^2 := by ring

/-- **(T4 bound)** Lipschitz of `f` at the discrete abscissae, using
`aux_y_diff_norm_bound`:
`|h · Σ_j A_{ij}·(f(y(x+h·c_j)) − f(y x))| ≤ h² L² M Σ_j |A_{ij}·c_j|`.

Generalized in cycle 102 to allow distinct row/column dimensions
(`Fin r`/`Fin s`) so it can be re-used at row index in (515b)
where `M.B : Matrix (Fin r) (Fin s) ℝ`. -/
private theorem aux_T4_bound {s r : ℕ}
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (A : Matrix (Fin r) (Fin s) ℝ)
    (c : Fin s → ℝ)
    (x h : ℝ) (hh : 0 ≤ h) (i : Fin r) :
    |h * ∑ j, A i j * (f (y (x + h * c j)) - f (y x))|
      ≤ h^2 * L^2 * M_bound * ∑ j, |A i j * c j| := by
  -- Lipschitz bridge.
  have hLip_abs : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b| := by
    intro a b
    have hd := hf_lip.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hcoe : (Real.toNNReal L : ℝ) = L := Real.coe_toNNReal L hL
    rw [hcoe] at hd
    exact hd
  -- |h * Σ| = h * |Σ|.
  have habs_h : |h * ∑ j, A i j * (f (y (x + h * c j)) - f (y x))|
              = h * |∑ j, A i j * (f (y (x + h * c j)) - f (y x))| := by
    rw [abs_mul, abs_of_nonneg hh]
  rw [habs_h]
  -- |Σ| ≤ Σ |·|.
  have habs_sum : |∑ j, A i j * (f (y (x + h * c j)) - f (y x))|
                ≤ ∑ j, |A i j * (f (y (x + h * c j)) - f (y x))| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Per summand: |A_{ij} * (f(y(x+hc_j)) - f(y x))| ≤ |A_{ij}*c_j| * h * (L * (L*M)).
  have hpt : ∀ j, |A i j * (f (y (x + h * c j)) - f (y x))|
                ≤ |A i j * c j| * (h * (L * (L * M_bound))) := by
    intro j
    have h1 : |f (y (x + h * c j)) - f (y x)|
              ≤ L * |y (x + h * c j) - y x| := hLip_abs _ _
    have h2 : |y (x + h * c j) - y x| ≤ h * |c j| * (L * M_bound) :=
      aux_y_diff_norm_bound hL hM hy_C1 hy_ode hf_y_bound x h hh (c j)
    have hLM_nn : 0 ≤ L * M_bound := mul_nonneg hL hM
    have h3 : L * |y (x + h * c j) - y x| ≤ L * (h * |c j| * (L * M_bound)) :=
      mul_le_mul_of_nonneg_left h2 hL
    have hf_diff_bound : |f (y (x + h * c j)) - f (y x)|
                ≤ h * |c j| * (L * (L * M_bound)) := by
      calc |f (y (x + h * c j)) - f (y x)|
          ≤ L * |y (x + h * c j) - y x| := h1
        _ ≤ L * (h * |c j| * (L * M_bound)) := h3
        _ = h * |c j| * (L * (L * M_bound)) := by ring
    have hAij_nn : 0 ≤ |A i j| := abs_nonneg _
    -- |A_{ij} * (f - f)| = |A_{ij}| * |f - f| ≤ |A_{ij}| * (h * |c_j| * (L * (L * M)))
    --                    = |A_{ij} * c_j| * (h * (L * (L * M)))
    calc |A i j * (f (y (x + h * c j)) - f (y x))|
        = |A i j| * |f (y (x + h * c j)) - f (y x)| := abs_mul _ _
      _ ≤ |A i j| * (h * |c j| * (L * (L * M_bound))) :=
          mul_le_mul_of_nonneg_left hf_diff_bound hAij_nn
      _ = (|A i j| * |c j|) * (h * (L * (L * M_bound))) := by ring
      _ = |A i j * c j| * (h * (L * (L * M_bound))) := by rw [abs_mul]
  -- Sum the per-summand bound.
  have hsum_bound : ∑ j, |A i j * (f (y (x + h * c j)) - f (y x))|
                  ≤ ∑ j, |A i j * c j| * (h * (L * (L * M_bound))) :=
    Finset.sum_le_sum (fun j _ => hpt j)
  -- Pull the constant h * (L * (L * M)) out of the right sum.
  have hsum_pull : ∑ j, |A i j * c j| * (h * (L * (L * M_bound)))
                = (∑ j, |A i j * c j|) * (h * (L * (L * M_bound))) := by
    rw [← Finset.sum_mul]
  rw [hsum_pull] at hsum_bound
  calc h * |∑ j, A i j * (f (y (x + h * c j)) - f (y x))|
      ≤ h * ∑ j, |A i j * (f (y (x + h * c j)) - f (y x))| :=
          mul_le_mul_of_nonneg_left habs_sum hh
    _ ≤ h * ((∑ j, |A i j * c j|) * (h * (L * (L * M_bound)))) :=
          mul_le_mul_of_nonneg_left hsum_bound hh
    _ = h^2 * L^2 * M_bound * ∑ j, |A i j * c j| := by ring

/-- **(T3' bound)** Pointwise Lipschitz bridge for the (515b) output-side
expansion of `v_i · h · y'(xn)`: with `xn = xn1 + h`, by Lipschitz of `f`
and `aux_y_diff_norm_bound` at `ξ = 1`,
`|v_i · h · (f(y(xn1+h)) − f(y xn1))| ≤ |v_i| · h² L² M`.

Cycle 102 helper for `localStageError_bound_b`. The shape is genuinely
new — `aux_T3_bound` integrates over `[0, c_i]` whereas this is a
single point evaluation. -/
private theorem aux_T3'_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (x h : ℝ) (hh : 0 ≤ h) (vi : ℝ) :
    |vi * h * (f (y (x + h)) - f (y x))|
      ≤ |vi| * (h^2 * L^2 * M_bound) := by
  -- Lipschitz bridge.
  have hLip_abs : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b| := by
    intro a b
    have hd := hf_lip.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hcoe : (Real.toNNReal L : ℝ) = L := Real.coe_toNNReal L hL
    rw [hcoe] at hd
    exact hd
  -- |y(x+h) - y x| ≤ h * (L * M_bound) via aux_y_diff_norm_bound at ξ = 1.
  have hy_diff_bound : |y (x + h) - y x| ≤ h * (L * M_bound) := by
    have h1 := aux_y_diff_norm_bound hL hM hy_C1 hy_ode hf_y_bound x h hh 1
    have hxh : x + h * 1 = x + h := by ring
    rw [hxh, abs_one, mul_one] at h1
    exact h1
  -- |f(y(x+h)) - f(y x)| ≤ h * L * (L * M_bound).
  have hf_diff_bound : |f (y (x + h)) - f (y x)| ≤ h * L * (L * M_bound) := by
    calc |f (y (x + h)) - f (y x)|
        ≤ L * |y (x + h) - y x| := hLip_abs _ _
      _ ≤ L * (h * (L * M_bound)) := mul_le_mul_of_nonneg_left hy_diff_bound hL
      _ = h * L * (L * M_bound) := by ring
  -- |vi * h * (f - f)| = |vi| * h * |f - f| (using h ≥ 0).
  have habs1 : |vi * h * (f (y (x + h)) - f (y x))|
              = |vi| * h * |f (y (x + h)) - f (y x)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hh]
  rw [habs1]
  have hvih_nn : 0 ≤ |vi| * h := mul_nonneg (abs_nonneg _) hh
  calc |vi| * h * |f (y (x + h)) - f (y x)|
      ≤ |vi| * h * (h * L * (L * M_bound)) :=
        mul_le_mul_of_nonneg_left hf_diff_bound hvih_nn
    _ = |vi| * (h^2 * L^2 * M_bound) := by ring

/-- **(T2 ≡ 0, output-side)** Algebraic identity using `V·u = u`
and consistency `B·𝟙 + V·v = u + v`:
`u_i · y(xn1) + (u_i + v_i) · h · y'(xn1) − Σ V_{ij}(u_j·y(xn1) + v_j·h·y'(xn1)) − Σ B_{ij}·h·y'(xn1) = 0`. -/
private theorem aux_T2_b_eq_zero {s r : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (V : Matrix (Fin r) (Fin r) ℝ)
    (u v : Fin r → ℝ)
    (hVu : V *ᵥ u = u)
    (hCons : B *ᵥ (fun _ => 1) + V *ᵥ v = u + v)
    {y : ℝ → ℝ} (xn1 h : ℝ) (i : Fin r) :
    u i * y xn1 + (u i + v i) * h * deriv y xn1
      - (∑ j, V i j * (u j * y xn1 + v j * h * deriv y xn1))
      - (∑ j, B i j * h * deriv y xn1) = 0 := by
  -- Σ V_{ij} u_j = (V *ᵥ u) i = u_i.
  have hVu_apply : (V *ᵥ u) i = ∑ j, V i j * u j := rfl
  have hVv_apply : (V *ᵥ v) i = ∑ j, V i j * v j := rfl
  have hB1_apply : (B *ᵥ (fun _ => (1:ℝ))) i = ∑ j, B i j := by
    show ∑ j, B i j * 1 = _
    simp
  have hVu_i : (∑ j, V i j * u j) = u i := by
    rw [← hVu_apply, hVu]
  -- (B·𝟙 + V·v)_i = (u + v)_i  ⇒  Σ B_{ij} + Σ V_{ij} v_j = u_i + v_i.
  have hCons_i : (∑ j, B i j) + (∑ j, V i j * v j) = u i + v i := by
    have h := congrFun hCons i
    rw [Pi.add_apply, Pi.add_apply] at h
    rw [hB1_apply, hVv_apply] at h
    exact h
  -- Distribute the V-sum into a y(xn1)-part and an h·y'(xn1)-part.
  have hV_split :
      (∑ j, V i j * (u j * y xn1 + v j * h * deriv y xn1))
        = (∑ j, V i j * u j) * y xn1 + (∑ j, V i j * v j) * h * deriv y xn1 := by
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    · rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
  have hB_split : (∑ j, B i j * h * deriv y xn1)
                = (∑ j, B i j) * h * deriv y xn1 := by
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hV_split, hB_split, hVu_i]
  linear_combination -(h * deriv y xn1) * hCons_i

/-! ## Lemma 515A — local truncation error bounds

The two main inequalities (515a) and (515b) of Butcher's lem:515A.
Stated sorry-first this cycle; the textbook proof (T1+T2+T3+T4
decomposition, with `T1 = T2 = 0` and `T3, T4` bounded by FTC +
Lipschitz) will be filled in next cycle, after the Aristotle batch
on the four `Tk` sub-bounds returns. -/

/-- **Lemma 515A (a)** — Stage-wise local truncation error bound for
a GLM `(A, U, B, V)` applied to the autonomous IVP
`y'(x) = f(y(x))` with `f` Lipschitz of constant `L` and exact
solution `y` bounded by `‖y(x)‖ ≤ M_bound`, `‖y'(x)‖ ≤ L · M_bound`.

For `c_i = (A·𝟙 + U·v)_i` and `Ŷ_i = y(x_{n−1} + h c_i)`,

  `|Ŷ_i − h Σ_j a_{ij} f(Ŷ_j) − Σ_j U_{ij} y_j^{[n−1]}|`
  `≤ h² L² M (½ c_i² + Σ_j |a_{ij} c_j|)`.

This is inequality (515a) of `entities/lem_515A.json`.

The `u`/`v` parameters are the consistency vectors of `M`: the
hypotheses `M.V *ᵥ u = u`, `M.U *ᵥ u = 1`, and the implicit
`B·𝟙 + V·v = u + v` (consistency 510c) are encoded inline so the
lemma can be reused without an `IsConsistent` extraction. The side
condition `c = A·𝟙 + U·v` matches the textbook setup.

**Faithfulness divergence**: extra hypothesis `∀ i, 0 ≤ c i` (cycle 101).
The textbook (515a) is sign-symmetric in `c_i`, but the cycle-101
proof of `aux_T3_bound` covers only the `c_i ≥ 0` case (see its
docstring). All standard GLMs (explicit Euler, classical RK, Gauss)
satisfy `c ∈ [0, 1]`. -/
theorem GeneralLinearMethod.localStageError_bound_a {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {h L M_bound : ℝ}
    (_hh : 0 ≤ h) (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    (f : ℝ → ℝ) (_hf_lip : LipschitzWith L.toNNReal f)
    (yex : ℝ → ℝ)
    (_hy_C1 : ContDiff ℝ 1 yex)
    (_hy_ode : ∀ t, deriv yex t = f (yex t))
    (_hy_M : ∀ t, |yex t| ≤ M_bound)
    (_hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (_hVu : M.V *ᵥ u = u) (_hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    (c : Fin s → ℝ)
    (_hc_nonneg : ∀ i, 0 ≤ c i)
    (_hc_def : c = M.glmAbscissae v) :
    ∀ i : Fin s,
      |yex (xn1 + h * c i)
        - h * (∑ j, M.A i j * f (yex (xn1 + h * c j)))
        - (∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1))|
      ≤ h^2 * L^2 * M_bound *
        ((1/2) * (c i)^2 + ∑ j, |M.A i j * c j|) := by
  intro i
  -- Bridge: |f(yex t)| ≤ L * M_bound from |deriv yex t| ≤ L * M_bound via hy_ode.
  have hf_yex_bound : ∀ t, |f (yex t)| ≤ L * M_bound := by
    intro t; rw [← _hy_ode t]; exact _hy'_LM t
  -- T1 = 0 (FTC telescoping).
  have hT1 : yex (xn1 + h * c i) - yex xn1
              - h * ∫ ξ in (0 : ℝ)..(c i), f (yex (xn1 + h * ξ)) = 0 :=
    aux_T1_eq_zero _hy_C1 _hy_ode xn1 h (c i)
  -- T2 = 0 (algebraic identity using c = A·𝟙 + U·v and U·u = 𝟙).
  have hc_def_eq : c = M.A *ᵥ (fun _ => 1) + M.U *ᵥ v := by
    rw [_hc_def]; rfl
  have hT2 : yex xn1 + c i * h * deriv yex xn1
              - (∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1))
              - (∑ j, M.A i j * h * deriv yex xn1) = 0 :=
    aux_T2_eq_zero M.A M.U u v _hUu c hc_def_eq xn1 h i
  -- T3 bound (Lipschitz + integral of |ξ|).
  have hT3 : |h * ∫ ξ in (0:ℝ)..(c i), (f (yex (xn1 + h * ξ)) - f (yex xn1))|
              ≤ (1/2) * h^2 * L^2 * M_bound * (c i)^2 :=
    aux_T3_bound _hL _hM _hf_lip _hy_C1 _hy_ode hf_yex_bound
      xn1 h _hh (c i) (_hc_nonneg i)
  -- T4 bound (Lipschitz + |Σ| ≤ Σ |·|).
  have hT4 : |h * ∑ j, M.A i j * (f (yex (xn1 + h * c j)) - f (yex xn1))|
              ≤ h^2 * L^2 * M_bound * ∑ j, |M.A i j * c j| :=
    aux_T4_bound _hL _hM _hf_lip _hy_C1 _hy_ode hf_yex_bound
      M.A c xn1 h _hh i
  -- Continuity of integrand for splitting T3.
  have hfy_cont : Continuous (fun t => f (yex t)) := by
    have heq : (fun t => f (yex t)) = deriv yex := by
      funext t; exact (_hy_ode t).symm
    rw [heq]; exact _hy_C1.continuous_deriv le_rfl
  have hf_yex_shift_cont : Continuous (fun ξ : ℝ => f (yex (xn1 + h * ξ))) := by
    have hc1 : Continuous (fun ξ : ℝ => xn1 + h * ξ) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact hfy_cont.comp hc1
  have hint_g_shift : IntervalIntegrable (fun ξ => f (yex (xn1 + h * ξ)))
                      MeasureTheory.volume 0 (c i) :=
    hf_yex_shift_cont.intervalIntegrable _ _
  -- T3 expansion: h * ∫ (f(...) - f(yex xn1)) = h * ∫ f(...) - h * c_i * f(yex xn1).
  have hT3_expand :
      h * ∫ ξ in (0:ℝ)..(c i), (f (yex (xn1 + h * ξ)) - f (yex xn1))
        = h * (∫ ξ in (0:ℝ)..(c i), f (yex (xn1 + h * ξ)))
          - h * (c i) * f (yex xn1) := by
    rw [intervalIntegral.integral_sub hint_g_shift intervalIntegrable_const,
        intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  -- T4 expansion: h * Σ A_{ij}(f - f(yex xn1)) = h * Σ A_{ij} f - Σ_j A_{ij} h f(yex xn1).
  have hT4_expand :
      h * ∑ j, M.A i j * (f (yex (xn1 + h * c j)) - f (yex xn1))
        = h * (∑ j, M.A i j * f (yex (xn1 + h * c j)))
          - (∑ j, M.A i j * h * f (yex xn1)) := by
    have hsum_distrib :
        (∑ j, M.A i j * (f (yex (xn1 + h * c j)) - f (yex xn1)))
          = (∑ j, M.A i j * f (yex (xn1 + h * c j)))
            - (∑ j, M.A i j * f (yex xn1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsum_distrib, mul_sub, Finset.mul_sum]
    rw [show (∑ j, M.A i j * h * f (yex xn1)) = h * (∑ j, M.A i j * f (yex xn1)) from ?_]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- Bridge from `deriv yex xn1` to `f (yex xn1)` in the T2 sum.
  have hy'0 : deriv yex xn1 = f (yex xn1) := _hy_ode xn1
  have hsumA_swap :
      (∑ j, M.A i j * h * deriv yex xn1) = (∑ j, M.A i j * h * f (yex xn1)) := by
    rw [hy'0]
  -- Algebraic identity: LHS = T3v - T4v.
  set T3v := h * ∫ ξ in (0:ℝ)..(c i), (f (yex (xn1 + h * ξ)) - f (yex xn1)) with hT3v_def
  set T4v := h * ∑ j, M.A i j * (f (yex (xn1 + h * c j)) - f (yex xn1)) with hT4v_def
  set Iv := ∫ ξ in (0:ℝ)..(c i), f (yex (xn1 + h * ξ)) with hIv_def
  set SAfb := ∑ j, M.A i j * f (yex (xn1 + h * c j)) with hSAfb_def
  set Uinp := ∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1) with hUinp_def
  set SAhy := ∑ j, M.A i j * h * deriv yex xn1 with hSAhy_def
  set SAhf := ∑ j, M.A i j * h * f (yex xn1) with hSAhf_def
  -- Now hT1: yex(xn1 + h c_i) - yex xn1 - h * Iv = 0
  -- hT2: yex xn1 + c_i * h * y'0 - Uinp - SAhy = 0
  -- hT3_expand: T3v = h * Iv - h * c_i * f(yex xn1)
  -- hT4_expand: T4v = h * SAfb - SAhf
  -- hsumA_swap: SAhy = SAhf
  -- hy'0: deriv yex xn1 = f (yex xn1)
  -- Goal: |yex(xn1 + h c_i) - h * SAfb - Uinp| ≤ ...
  -- We claim: yex(xn1 + h c_i) - h * SAfb - Uinp = T3v - T4v.
  have hdecomp :
      yex (xn1 + h * c i) - h * SAfb - Uinp = T3v - T4v := by
    linear_combination hT1 + hT2 - hT3_expand + hT4_expand + hsumA_swap
                       - (c i * h) * hy'0
  rw [hdecomp]
  -- |T3v - T4v| ≤ |T3v| + |T4v| ≤ T3_bound + T4_bound = goal
  calc |T3v - T4v|
      ≤ |T3v| + |T4v| := abs_sub _ _
    _ ≤ (1/2) * h^2 * L^2 * M_bound * (c i)^2
          + h^2 * L^2 * M_bound * ∑ j, |M.A i j * c j| := add_le_add hT3 hT4
    _ = h^2 * L^2 * M_bound * ((1/2) * (c i)^2 + ∑ j, |M.A i j * c j|) := by ring

/-- **Lemma 515A (b)** — Output-wise local truncation error bound for
a GLM `(A, U, B, V)`. With the same setup as
`localStageError_bound_a`, and using
`y_i^{[n]} = u_i · y(x_{n−1} + h) + v_i · h · y'(x_{n−1} + h)`
(since `x_n = x_{n−1} + h`),

  `|y_i^{[n]} − h Σ_j b_{ij} f(Ŷ_j) − Σ_j V_{ij} y_j^{[n−1]}|`
  `≤ h² L² M (½ |u_i| + |v_i| + Σ_j |b_{ij} c_j|)`.

This is inequality (515b) of `entities/lem_515A.json`. -/
theorem GeneralLinearMethod.localStageError_bound_b {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {h L M_bound : ℝ}
    (_hh : 0 ≤ h) (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    (f : ℝ → ℝ) (_hf_lip : LipschitzWith L.toNNReal f)
    (yex : ℝ → ℝ)
    (_hy_C1 : ContDiff ℝ 1 yex)
    (_hy_ode : ∀ t, deriv yex t = f (yex t))
    (_hy_M : ∀ t, |yex t| ≤ M_bound)
    (_hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (_hVu : M.V *ᵥ u = u) (_hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    (c : Fin s → ℝ)
    (_hc_nonneg : ∀ i, 0 ≤ c i)
    (_hc_def : c = M.glmAbscissae v) :
    ∀ i : Fin r,
      |(u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
        - h * (∑ j, M.B i j * f (yex (xn1 + h * c j)))
        - (∑ j, M.V i j * (u j * yex xn1 + v j * h * deriv yex xn1))|
      ≤ h^2 * L^2 * M_bound *
        ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|) := by
  intro i
  -- Bridge: |f(yex t)| ≤ L * M_bound from |deriv yex t| ≤ L * M_bound via hy_ode.
  have hf_yex_bound : ∀ t, |f (yex t)| ≤ L * M_bound := by
    intro t; rw [← _hy_ode t]; exact _hy'_LM t
  -- T1 = 0 (FTC telescoping at c_i := 1, then bridge xn1 + h * 1 = xn1 + h).
  have hT1 : yex (xn1 + h) - yex xn1
              - h * ∫ ξ in (0 : ℝ)..1, f (yex (xn1 + h * ξ)) = 0 := by
    have h0 := aux_T1_eq_zero _hy_C1 _hy_ode xn1 h 1
    have hxh : xn1 + h * 1 = xn1 + h := by ring
    rw [hxh] at h0
    exact h0
  -- T2 = 0 (output-side algebraic identity using V·u = u and B·𝟙 + V·v = u + v).
  have hT2 : u i * yex xn1 + (u i + v i) * h * deriv yex xn1
              - (∑ j, M.V i j * (u j * yex xn1 + v j * h * deriv yex xn1))
              - (∑ j, M.B i j * h * deriv yex xn1) = 0 :=
    aux_T2_b_eq_zero M.B M.V u v _hVu _hCons xn1 h i
  -- T3 bound at c_i := 1 (then 1^2 = 1 gives ½ h² L² M_bound).
  have hT3 : |h * ∫ ξ in (0:ℝ)..1, (f (yex (xn1 + h * ξ)) - f (yex xn1))|
              ≤ (1/2) * h^2 * L^2 * M_bound := by
    have h0 := aux_T3_bound _hL _hM _hf_lip _hy_C1 _hy_ode hf_yex_bound
                xn1 h _hh 1 (by norm_num : (0:ℝ) ≤ 1)
    simpa using h0
  -- T3' bound (point-evaluation Lipschitz, new helper this cycle).
  have hT3' : |v i * h * (f (yex (xn1 + h)) - f (yex xn1))|
              ≤ |v i| * (h^2 * L^2 * M_bound) :=
    aux_T3'_bound _hL _hM _hf_lip _hy_C1 _hy_ode hf_yex_bound
      xn1 h _hh (v i)
  -- T4 bound for B (after row-dim refactor of aux_T4_bound).
  have hT4 : |h * ∑ j, M.B i j * (f (yex (xn1 + h * c j)) - f (yex xn1))|
              ≤ h^2 * L^2 * M_bound * ∑ j, |M.B i j * c j| :=
    aux_T4_bound _hL _hM _hf_lip _hy_C1 _hy_ode hf_yex_bound
      M.B c xn1 h _hh i
  -- Continuity of integrand for splitting T3 over [0, 1].
  have hfy_cont : Continuous (fun t => f (yex t)) := by
    have heq : (fun t => f (yex t)) = deriv yex := by
      funext t; exact (_hy_ode t).symm
    rw [heq]; exact _hy_C1.continuous_deriv le_rfl
  have hf_yex_shift_cont : Continuous (fun ξ : ℝ => f (yex (xn1 + h * ξ))) := by
    have hc1 : Continuous (fun ξ : ℝ => xn1 + h * ξ) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact hfy_cont.comp hc1
  have hint_g_shift : IntervalIntegrable (fun ξ => f (yex (xn1 + h * ξ)))
                      MeasureTheory.volume 0 1 :=
    hf_yex_shift_cont.intervalIntegrable _ _
  -- T3 expansion: h * ∫_0^1 (f - f(yex xn1)) = h * ∫_0^1 f - h * 1 * f(yex xn1).
  have hT3_expand :
      h * ∫ ξ in (0:ℝ)..1, (f (yex (xn1 + h * ξ)) - f (yex xn1))
        = h * (∫ ξ in (0:ℝ)..1, f (yex (xn1 + h * ξ)))
          - h * 1 * f (yex xn1) := by
    rw [intervalIntegral.integral_sub hint_g_shift intervalIntegrable_const,
        intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  -- T4 expansion: h * Σ B_{ij}(f - f(yex xn1)) = h * Σ B_{ij} f - Σ_j B_{ij} h f(yex xn1).
  have hT4_expand :
      h * ∑ j, M.B i j * (f (yex (xn1 + h * c j)) - f (yex xn1))
        = h * (∑ j, M.B i j * f (yex (xn1 + h * c j)))
          - (∑ j, M.B i j * h * f (yex xn1)) := by
    have hsum_distrib :
        (∑ j, M.B i j * (f (yex (xn1 + h * c j)) - f (yex xn1)))
          = (∑ j, M.B i j * f (yex (xn1 + h * c j)))
            - (∑ j, M.B i j * f (yex xn1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsum_distrib, mul_sub, Finset.mul_sum]
    rw [show (∑ j, M.B i j * h * f (yex xn1)) = h * (∑ j, M.B i j * f (yex xn1)) from ?_]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- Bridge from `deriv yex xn1` and `deriv yex (xn1+h)` to `f(yex …)`.
  have hy'0 : deriv yex xn1 = f (yex xn1) := _hy_ode xn1
  have hy'h : deriv yex (xn1 + h) = f (yex (xn1 + h)) := _hy_ode (xn1 + h)
  have hsumB_swap :
      (∑ j, M.B i j * h * deriv yex xn1) = (∑ j, M.B i j * h * f (yex xn1)) := by
    rw [hy'0]
  -- Set up abbreviations matching the (515a) pattern.
  set T3v := h * ∫ ξ in (0:ℝ)..1, (f (yex (xn1 + h * ξ)) - f (yex xn1)) with hT3v_def
  set T3'v := v i * h * (f (yex (xn1 + h)) - f (yex xn1)) with hT3'v_def
  set T4v := h * ∑ j, M.B i j * (f (yex (xn1 + h * c j)) - f (yex xn1)) with hT4v_def
  set Iv := ∫ ξ in (0:ℝ)..1, f (yex (xn1 + h * ξ)) with hIv_def
  set SBfb := ∑ j, M.B i j * f (yex (xn1 + h * c j)) with hSBfb_def
  set Vinp := ∑ j, M.V i j * (u j * yex xn1 + v j * h * deriv yex xn1) with hVinp_def
  set SBhy := ∑ j, M.B i j * h * deriv yex xn1 with hSBhy_def
  set SBhf := ∑ j, M.B i j * h * f (yex xn1) with hSBhf_def
  -- Algebraic claim: LHS = u i * T3v + T3'v − T4v.
  have hdecomp :
      (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h)) - h * SBfb - Vinp
        = u i * T3v + T3'v - T4v := by
    linear_combination
        u i * hT1 + hT2 - u i * hT3_expand + hT4_expand + hsumB_swap
        - (u i + v i) * h * hy'0 + v i * h * hy'h
  rw [hdecomp]
  -- |u i * T3v + T3'v - T4v| ≤ |u i| * |T3v| + |T3'v| + |T4v|
  --                          ≤ ½ |u i| h² L² M + |v i| h² L² M + h² L² M Σ |B_{ij} c_j|.
  have hT3_scaled : |u i * T3v| ≤ |u i| * ((1/2) * h^2 * L^2 * M_bound) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hT3 (abs_nonneg _)
  calc |u i * T3v + T3'v - T4v|
      ≤ |u i * T3v + T3'v| + |T4v| := abs_sub _ _
    _ ≤ (|u i * T3v| + |T3'v|) + |T4v| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (|u i| * ((1/2) * h^2 * L^2 * M_bound) + |v i| * (h^2 * L^2 * M_bound))
          + h^2 * L^2 * M_bound * ∑ j, |M.B i j * c j| :=
          add_le_add (add_le_add hT3_scaled hT3') hT4
    _ = h^2 * L^2 * M_bound * ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|) := by ring

/-! ## Lemma 515B — local-step error propagation (cycle 103)

This is Butcher's `lem:515B` (p. 414): the per-step relation between
exact and computed solutions of a stable, consistent GLM. The textbook
proof has four moving parts:

1. **Residual decomposition** (algebraic): split the local-step
   residual into an exact-side residual plus a `V·δ` correction.
   Closed manually below.

2. **Lipschitz bridge**: replace `f(Y_j) − f(Ŷ_j)` by `L·|Y_j − Ŷ_j|`
   inside `h Σ B_{ij}·(...)`.

3. **η contraction**: bound `|Y_j − Ŷ_j|` via positivity of
   `(I − h₀ L|A|)^{−1}`, given the per-stage contraction estimate.

4. **Main combination**: combine (1)–(3) into the full `K` bound.

**Encoding choices for cycle 103**:

* `α`, `β`, `δ_max` are **proxy parameters** with upper-bound side
  conditions. This sidesteps `Finset.sup'`-non-emptiness plumbing
  and matches how cycles 100/102 took the abscissae vector `c` as a
  parameter. Any user-supplied upper bound works.

* `ell_U` and `phi_A` are taken as **parameters with linear-system
  side conditions**. The textbook constructs them as the unique
  solutions to `(I − h₀ L|A|) x = rhs` for two different right-hand
  sides (row-sums of `|U|` for `ell_U`; `½c² + |A||c|` for `phi_A`),
  but we do not yet have matrix-inversion infrastructure for
  `(I − h₀ L|A|)`. A future cycle will discharge these side
  conditions in a single sweep. -/

/-- **(515B residual decomposition)** Algebraic identity used by the
textbook proof to identify `K_i^[n]`.

With `δ_k := yt_prev_k − y_prev_k`,

  `(u_i y(x_n) + v_i h y'(x_n)) − Σ V_{ij}·y_prev_j − h Σ B_{ij}·f(Y_j)`
  ` = Σ V_{ij}·δ_j + ((u_i y(x_n) + v_i h y'(x_n)) − Σ V_{ij}·yt_prev_j − h Σ B_{ij}·f(Y_j))`.

Pure algebra; `Finset.sum_sub_distrib` plus `ring`. -/
private theorem aux_515B_residual_decomposition {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {h : ℝ}
    (yt_prev y_prev δ : Fin r → ℝ)
    (hδ_def : ∀ k, δ k = yt_prev k - y_prev k)
    (Y : Fin s → ℝ)
    (f : ℝ → ℝ)
    (yex : ℝ → ℝ)
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (i : Fin r) :
    (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
      - (∑ j, M.V i j * y_prev j)
      - h * (∑ j, M.B i j * f (Y j))
    = (∑ j, M.V i j * δ j)
      + ((u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
         - (∑ j, M.V i j * yt_prev j)
         - h * (∑ j, M.B i j * f (Y j))) := by
  have hsplit : (∑ j, M.V i j * y_prev j)
              = (∑ j, M.V i j * yt_prev j) - (∑ j, M.V i j * δ j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hδ_def j]; ring
  rw [hsplit]; ring

/-- **(515B Lipschitz bridge)** `f` Lipschitz with constant `L`
implies, for `Y_hat, Y : Fin s → ℝ`, `B : Matrix (Fin r) (Fin s) ℝ`,
`h ≥ 0`, `i : Fin r`,

  `|h Σ_j B_{ij}·(f(Ŷ_j) − f(Y_j))| ≤ h·L · Σ_j |B_{ij}| · |Ŷ_j − Y_j|`.

Sorry-first this cycle; proof is a Lipschitz application + triangle
inequality + sum reorganization (analogous to `aux_T4_bound`). -/
private theorem aux_515B_lipschitz_bridge {s r : ℕ}
    {f : ℝ → ℝ} {L : ℝ}
    (_hL : 0 ≤ L) (_hf_lip : LipschitzWith L.toNNReal f)
    (B : Matrix (Fin r) (Fin s) ℝ)
    (Y_hat Y : Fin s → ℝ)
    (h : ℝ) (_hh : 0 ≤ h) (i : Fin r) :
    |h * ∑ j, B i j * (f (Y_hat j) - f (Y j))|
      ≤ h * L * ∑ j, |B i j| * |Y_hat j - Y j| := by
  -- Lipschitz bridge: |f a - f b| ≤ L * |a - b|.
  have hLip_abs : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b| := by
    intro a b
    have hd := _hf_lip.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hcoe : (Real.toNNReal L : ℝ) = L := Real.coe_toNNReal L _hL
    rw [hcoe] at hd
    exact hd
  -- |h * Σ| = h * |Σ|.
  have habs_h : |h * ∑ j, B i j * (f (Y_hat j) - f (Y j))|
              = h * |∑ j, B i j * (f (Y_hat j) - f (Y j))| := by
    rw [abs_mul, abs_of_nonneg _hh]
  rw [habs_h]
  -- |Σ| ≤ Σ |·|.
  have habs_sum : |∑ j, B i j * (f (Y_hat j) - f (Y j))|
                ≤ ∑ j, |B i j * (f (Y_hat j) - f (Y j))| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Per-summand bound: |B_{ij} * (f(Ŷ_j) - f(Y_j))| ≤ |B_{ij}| * |Ŷ_j - Y_j| * L.
  have hpt : ∀ j, |B i j * (f (Y_hat j) - f (Y j))|
                ≤ |B i j| * |Y_hat j - Y j| * L := by
    intro j
    have h1 : |f (Y_hat j) - f (Y j)| ≤ L * |Y_hat j - Y j| := hLip_abs _ _
    have hBij_nn : 0 ≤ |B i j| := abs_nonneg _
    calc |B i j * (f (Y_hat j) - f (Y j))|
        = |B i j| * |f (Y_hat j) - f (Y j)| := abs_mul _ _
      _ ≤ |B i j| * (L * |Y_hat j - Y j|) :=
          mul_le_mul_of_nonneg_left h1 hBij_nn
      _ = |B i j| * |Y_hat j - Y j| * L := by ring
  -- Sum the per-summand bound.
  have hsum_bound : ∑ j, |B i j * (f (Y_hat j) - f (Y j))|
                  ≤ ∑ j, |B i j| * |Y_hat j - Y j| * L :=
    Finset.sum_le_sum (fun j _ => hpt j)
  -- Pull L out of the right sum.
  have hsum_pull : ∑ j, |B i j| * |Y_hat j - Y j| * L
                = (∑ j, |B i j| * |Y_hat j - Y j|) * L := by
    rw [← Finset.sum_mul]
  rw [hsum_pull] at hsum_bound
  calc h * |∑ j, B i j * (f (Y_hat j) - f (Y j))|
      ≤ h * ∑ j, |B i j * (f (Y_hat j) - f (Y j))| :=
          mul_le_mul_of_nonneg_left habs_sum _hh
    _ ≤ h * ((∑ j, |B i j| * |Y_hat j - Y j|) * L) :=
          mul_le_mul_of_nonneg_left hsum_bound _hh
    _ = h * L * ∑ j, |B i j| * |Y_hat j - Y j| := by ring

/-- **(515B η contraction)** Given the per-stage contraction estimate

  `|η_j − Σ_k U_{jk}·δ_k| ≤ h L Σ_k|A_{jk}|·|η_k|`
                          `+ h² L² M (½c_j² + Σ|A_{jk}·c_k|)`,

with `|δ_k| ≤ δ_max` and `h ≤ h₀`, positivity of `(I − h₀ L|A|)^{−1}`
yields

  `|η_j| ≤ ell_U_j · δ_max + h² L² M · phi_A_j`,

where `ell_U`, `phi_A` solve the two linear systems with right-hand
sides `Σ_k|U_{jk}|` and `½c_j² + Σ|A_{jk} c_k|` respectively.

Faithfulness divergence: the textbook tacitly assumes "h₀ small
enough"; the explicit hypothesis `‖(h₀ L) • |A|‖ < 1` (Frobenius
norm) surfaces this assumption — it is what the M-matrix
comparison principle from `OpenMath/Chapter5/MMatrix.lean` requires.
See `.prover-state/issues/lem_515B_eta_contraction_deferred.md`. -/
private theorem aux_515B_eta_contraction {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ)
    (U : Matrix (Fin s) (Fin r) ℝ)
    {h h₀ L M_bound δ_max : ℝ}
    (_hh : 0 ≤ h) (_hh_le : h ≤ h₀) (_h₀_pos : 0 < h₀)
    (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    (_hδ_max_nonneg : 0 ≤ δ_max)
    (c : Fin s → ℝ) (_hc_nonneg : ∀ i, 0 ≤ c i)
    (ell_U phi_A η : Fin s → ℝ)
    (_hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (_hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (_hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |A i j| * ell_U j)
                    = ∑ j, |U i j|)
    (_hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |A i j| * phi_A j)
                    = (1/2) * (c i)^2 + ∑ j, |A i j * c j|)
    (δ : Fin r → ℝ)
    (_hδ_max : ∀ k, |δ k| ≤ δ_max)
    (_hcontraction : ∀ j, |η j - ∑ k, U j k * δ k|
                          ≤ h * L * (∑ k, |A j k| * |η k|)
                            + h^2 * L^2 * M_bound *
                              ((1/2) * (c j)^2 + ∑ k, |A j k * c k|))
    (_h_norm : ‖((h₀ * L) • A.map (fun x => |x|) : Matrix (Fin s) (Fin s) ℝ)‖ < 1) :
    ∀ j, |η j| ≤ ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j := by
  -- Set up the M-matrix M_pos = (h₀ * L) • |A| and the target vector.
  set M_pos : Matrix (Fin s) (Fin s) ℝ := (h₀ * L) • A.map (fun x => |x|)
    with hMpos_def
  let target : Fin s → ℝ :=
    fun j => ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j
  let absη : Fin s → ℝ := fun j => |η j|
  -- M_pos is entrywise non-negative.
  have hh₀L_nn : 0 ≤ h₀ * L := mul_nonneg _h₀_pos.le _hL
  have hMpos_nn : M_pos.EntrywiseNonneg := by
    intro i j
    show 0 ≤ ((h₀ * L) • A.map (fun x => |x|)) i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact mul_nonneg hh₀L_nn (abs_nonneg _)
  -- Useful arithmetic facts.
  have hh2L2M_nn : 0 ≤ h^2 * L^2 * M_bound :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) _hM
  -- Entrywise formula for M_pos.
  have hMpos_apply : ∀ i k, M_pos i k = h₀ * L * |A i k| := by
    intro i k
    rw [hMpos_def]
    show ((h₀ * L) • A.map (fun x => |x|)) i k = h₀ * L * |A i k|
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  -- Compute (M_pos *ᵥ v) i = h₀*L * Σ_k |A i k| * v k.
  have hMpos_mulVec : ∀ (v : Fin s → ℝ) (i : Fin s),
      (M_pos *ᵥ v) i = h₀ * L * ∑ k, |A i k| * v k := by
    intro v i
    have h1 : (M_pos *ᵥ v) i = ∑ k, M_pos i k * v k := rfl
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hMpos_apply]; ring
  -- Per-row key inequality: absη j - h₀L Σ|A_jk| absη_k ≤ target j - h₀L Σ|A_jk| target_k.
  have hkey_arith : ∀ j,
      absη j - h₀ * L * (∑ k, |A j k| * absη k)
        ≤ target j - h₀ * L * (∑ k, |A j k| * target k) := by
    intro j
    have hcontr := _hcontraction j
    have hellU_j := _hellU_eq j
    have hphiA_j := _hphiA_eq j
    -- Triangle inequality: |η j| ≤ |η j - Σ U_jk δ_k| + |Σ U_jk δ_k|.
    have htriangle : |η j| ≤ |η j - ∑ k, U j k * δ k| + |∑ k, U j k * δ k| := by
      have hsplit : η j = (η j - ∑ k, U j k * δ k) + (∑ k, U j k * δ k) := by ring
      conv_lhs => rw [hsplit]
      exact abs_add_le _ _
    -- Bound |Σ U_jk δ_k| ≤ Σ |U_jk| * δ_max.
    have hUδ_bound : |∑ k, U j k * δ k| ≤ ∑ k, |U j k| * δ_max := by
      calc |∑ k, U j k * δ k|
          ≤ ∑ k, |U j k * δ k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, |U j k| * |δ k| := by
              refine Finset.sum_congr rfl (fun k _ => ?_); rw [abs_mul]
        _ ≤ ∑ k, |U j k| * δ_max :=
              Finset.sum_le_sum (fun k _ =>
                mul_le_mul_of_nonneg_left (_hδ_max k) (abs_nonneg _))
    -- Combine triangle + contraction + δ-bound.
    have hAη_nn : 0 ≤ ∑ k, |A j k| * |η k| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hsum_mul : (∑ k, |U j k| * δ_max) = (∑ k, |U j k|) * δ_max := by
      rw [Finset.sum_mul]
    have hcombined : |η j|
        ≤ (∑ k, |U j k|) * δ_max
          + h * L * (∑ k, |A j k| * |η k|)
          + h^2 * L^2 * M_bound *
            ((1/2) * (c j)^2 + ∑ k, |A j k * c k|) := by
      have hUδ' : |∑ k, U j k * δ k| ≤ (∑ k, |U j k|) * δ_max := by
        rw [← hsum_mul]; exact hUδ_bound
      linarith [htriangle, hcontr, hUδ']
    -- Substitute the side equations.
    have h_sumU : ∑ k, |U j k| = ell_U j - h₀ * L * ∑ k, |A j k| * ell_U k :=
      hellU_j.symm
    have h_phi : (1/2) * (c j)^2 + ∑ k, |A j k * c k|
                  = phi_A j - h₀ * L * ∑ k, |A j k| * phi_A k :=
      hphiA_j.symm
    rw [h_sumU, h_phi] at hcombined
    -- Use h ≤ h₀ to upgrade `h*L*...` term to `h₀*L*...`.
    have h_h_le : h * L * ∑ k, |A j k| * |η k|
                  ≤ h₀ * L * ∑ k, |A j k| * |η k| := by
      have hLA_nn : 0 ≤ L * ∑ k, |A j k| * |η k| := mul_nonneg _hL hAη_nn
      have : h * (L * ∑ k, |A j k| * |η k|)
              ≤ h₀ * (L * ∑ k, |A j k| * |η k|) :=
        mul_le_mul_of_nonneg_right _hh_le hLA_nn
      linarith
    -- Algebraic identity: Σ |A_jk| * target k = (Σ|A_jk| ell_U_k)·δ_max
    --                                          + h²L²M·(Σ|A_jk| phi_A_k).
    have hsum_target_split :
        ∑ k, |A j k| * target k
          = (∑ k, |A j k| * ell_U k) * δ_max
            + h^2 * L^2 * M_bound * (∑ k, |A j k| * phi_A k) := by
      have hpoint : ∀ k, |A j k| * target k
                          = |A j k| * (ell_U k * δ_max)
                            + |A j k| * (h^2 * L^2 * M_bound * phi_A k) := by
        intro k
        show |A j k| * (ell_U k * δ_max + h^2 * L^2 * M_bound * phi_A k) = _
        ring
      calc ∑ k, |A j k| * target k
          = ∑ k, (|A j k| * (ell_U k * δ_max)
                  + |A j k| * (h^2 * L^2 * M_bound * phi_A k)) :=
            Finset.sum_congr rfl (fun k _ => hpoint k)
        _ = (∑ k, |A j k| * (ell_U k * δ_max))
            + (∑ k, |A j k| * (h^2 * L^2 * M_bound * phi_A k)) :=
            Finset.sum_add_distrib
        _ = (∑ k, |A j k| * ell_U k) * δ_max
            + h^2 * L^2 * M_bound * (∑ k, |A j k| * phi_A k) := by
            congr 1
            · rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
            · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
    -- Conclude the per-row inequality.
    show |η j| - h₀ * L * (∑ k, |A j k| * |η k|)
          ≤ (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j)
            - h₀ * L * (∑ k, |A j k| * target k)
    rw [hsum_target_split]
    linarith [hcombined, h_h_le]
  -- Translate to (1 - M_pos) *ᵥ (target - absη) ≥ 0 entrywise.
  have hkey_matrix : ∀ j, 0 ≤ ((1 - M_pos) *ᵥ (target - absη)) j := by
    intro j
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, hMpos_mulVec]
    -- Goal: 0 ≤ (target - absη) j - h₀ * L * ∑ k, |A j k| * (target - absη) k.
    have hsum_distrib : ∑ k, |A j k| * (target - absη) k
                        = (∑ k, |A j k| * target k)
                          - (∑ k, |A j k| * absη k) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show |A j k| * (target k - absη k) = _; ring
    rw [hsum_distrib]
    have hkey_j := hkey_arith j
    show 0 ≤ (target j - absη j)
              - h₀ * L * ((∑ k, |A j k| * target k) - (∑ k, |A j k| * absη k))
    linarith [hkey_j]
  -- Apply the M-matrix comparison principle.
  have h_target_minus_absη_nn : ∀ j, 0 ≤ (target - absη) j :=
    Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg
      hMpos_nn _h_norm hkey_matrix
  intro j
  have hj := h_target_minus_absη_nn j
  show |η j| ≤ ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j
  have heq : (target - absη) j
              = (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j) - |η j| := rfl
  linarith [heq ▸ hj]

/-- **Butcher Lemma 515B** — Local-step error propagation across one
GLM step.

Under the conditions of Lemma 515A, the exact and computed solutions
in one step are related by

  `ỹ_i^[n] − y_i^[n] = Σ_j V_{ij}(ỹ_j^[n−1] − y_j^[n−1]) + K_i^[n]`,

with `‖K^[n]‖ ≤ h α max|ỹ^[n−1] − y^[n−1]| + β h²`.

This is `lem:515B` of `entities/lem_515B.json`.

**Encoding deviations from textbook**:

1. The `Finset.sup'`-style maxima `max_{i=1}^r |ỹ_i^[n−1] − y_i^[n−1]|`,
   `max_{i=1}^s |ℓ_i|` (for α), and `max_{i=1}^s [...]` (for β) are
   abstracted as proxy parameters `δ_max`, `α`, `β` with upper-bound
   side conditions. This is *strictly weaker* than the textbook
   (which fixes the maxima) and faithful in the sense that the
   conclusion is preserved under any valid choice.

2. The two "ell"-vectors `ell_U` and `phi_A` (textbook's `ℓ` for α
   and `ϕ` ≡ `ℓ` for β-via-515A) are taken as parameters with their
   defining linear-system side conditions. A future cycle will
   construct them via `(I − h₀ L|A|)`-inversion infrastructure.

3. `‖K^[n]‖_∞ = max_i |K_i|` is encoded pointwise as `∀ i, |K i| ≤ ...`,
   which is equivalent.

4. The α-constant is encoded as `α ≥ L Σ_j |B_{ij}| ell_U_j` for
   each `i`, rather than the textbook's `α = L max_i |ℓ_i|`. Our
   form is what falls out of the analysis (the textbook formula
   appears to assume `Σ_j |B_{ij}| ≤ 1`, which is not stated). The
   user can supply `α := L · (max_i Σ_j |B_{ij}| ell_U_j)` to match
   the analysis tightly.

The textbook proof structure is formalized via the three sub-lemmas
above. Cycle 104 closes the main combination via:
* `aux_515B_residual_decomposition` (algebraic identity).
* `aux_515B_lipschitz_bridge` (closed cycle 104).
* `aux_515B_eta_contraction` (closed cycle 107 via M-matrix
  comparison principle from `OpenMath/Chapter5/MMatrix.lean`; the
  Frobenius-norm hypothesis `‖(h₀ L) • |A|‖ < 1` is propagated up
  to this signature).
* `localStageError_bound_a` and `localStageError_bound_b` (515A). -/
theorem GeneralLinearMethod.localStepError_bound {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {h h₀ L M_bound α β δ_max : ℝ}
    (_hh : 0 ≤ h) (_hh_le : h ≤ h₀) (_h₀_pos : 0 < h₀)
    (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    (f : ℝ → ℝ) (_hf_lip : LipschitzWith L.toNNReal f)
    (yex : ℝ → ℝ)
    (_hy_C1 : ContDiff ℝ 1 yex)
    (_hy_ode : ∀ t, deriv yex t = f (yex t))
    (_hy_M : ∀ t, |yex t| ≤ M_bound)
    (_hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (_hVu : M.V *ᵥ u = u) (_hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    (c : Fin s → ℝ)
    (_hc_nonneg : ∀ i, 0 ≤ c i)
    (_hc_def : c = M.glmAbscissae v)
    (ell_U phi_A : Fin s → ℝ)
    (_hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (_hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (_hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |M.A i j| * ell_U j)
                    = ∑ j, |M.U i j|)
    (_hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |M.A i j| * phi_A j)
                    = (1/2) * (c i)^2 + ∑ j, |M.A i j * c j|)
    (_hα_def : ∀ i, L * (∑ j, |M.B i j| * ell_U j) ≤ α)
    (_hβ_def : ∀ i, L^2 * M_bound *
                ((1/2) * |u i| + |v i|
                 + (∑ j, |M.B i j * c j|)
                 + h₀ * L * (∑ j, |M.B i j| * phi_A j)) ≤ β)
    (yt_prev δ : Fin r → ℝ)
    (_hδ_def : ∀ k, δ k = yt_prev k -
                          (u k * yex xn1 + v k * h * deriv yex xn1))
    (_hδ_max : ∀ k, |δ k| ≤ δ_max)
    (_hδ_max_nonneg : 0 ≤ δ_max)
    (Y : Fin s → ℝ)
    (_hY_stage : ∀ i, Y i = h * (∑ j, M.A i j * f (Y j))
                          + ∑ j, M.U i j * yt_prev j)
    (_h_norm : ‖((h₀ * L) • M.A.map (fun x => |x|) : Matrix (Fin s) (Fin s) ℝ)‖ < 1) :
    ∃ K : Fin r → ℝ,
      (∀ i,
        h * (∑ j, M.B i j * f (Y j))
          + (∑ j, M.V i j * yt_prev j)
          - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
          = (∑ j, M.V i j * δ j) + K i)
      ∧ (∀ i, |K i| ≤ α * h * δ_max + β * h^2) := by
  -- Phantom variables: exact ODE values at abscissae and exact previous values.
  let Yhat : Fin s → ℝ := fun j => yex (xn1 + h * c j)
  let y_prev : Fin r → ℝ := fun k => u k * yex xn1 + v k * h * deriv yex xn1
  let η : Fin s → ℝ := fun j => Y j - Yhat j
  -- 515A (b) bound: exact-side residual R_i.
  have hRi : ∀ i : Fin r, |(u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
                - h * (∑ j, M.B i j * f (Yhat j))
                - (∑ j, M.V i j * y_prev j)|
                ≤ h^2 * L^2 * M_bound *
                  ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|) :=
    M.localStageError_bound_b _hh _hL _hM f _hf_lip yex _hy_C1 _hy_ode
        _hy_M _hy'_LM xn1 u v _hVu _hUu _hCons c _hc_nonneg _hc_def
  -- 515A (a) bound: per-stage exact residual.
  have hres_j : ∀ j : Fin s, |Yhat j - h * (∑ k, M.A j k * f (Yhat k))
                               - (∑ k, M.U j k * y_prev k)|
                            ≤ h^2 * L^2 * M_bound *
                              ((1/2) * (c j)^2 + ∑ k, |M.A j k * c k|) :=
    M.localStageError_bound_a _hh _hL _hM f _hf_lip yex _hy_C1 _hy_ode
        _hy_M _hy'_LM xn1 u v _hVu _hUu _hCons c _hc_nonneg _hc_def
  -- η contraction estimate: the per-stage Lipschitz + residual bound.
  have hη_contr : ∀ j, |η j - ∑ k, M.U j k * δ k|
                        ≤ h * L * (∑ k, |M.A j k| * |η k|)
                          + h^2 * L^2 * M_bound *
                            ((1/2) * (c j)^2 + ∑ k, |M.A j k * c k|) := by
    intro j
    -- Algebraic key identity: η_j - Σ U·δ
    --   = h Σ A·(f(Y) - f(Ŷ)) - residual_j.
    have hkey : η j - (∑ k, M.U j k * δ k)
                = h * (∑ k, M.A j k * (f (Y k) - f (Yhat k)))
                  - (Yhat j - h * (∑ k, M.A j k * f (Yhat k))
                            - (∑ k, M.U j k * y_prev k)) := by
      have hY := _hY_stage j
      have hUδ : (∑ k, M.U j k * δ k)
                  = (∑ k, M.U j k * yt_prev k) - (∑ k, M.U j k * y_prev k) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [_hδ_def k]; ring
      have hAdiff : h * (∑ k, M.A j k * (f (Y k) - f (Yhat k)))
                    = h * (∑ k, M.A j k * f (Y k))
                      - h * (∑ k, M.A j k * f (Yhat k)) := by
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
      show Y j - Yhat j - (∑ k, M.U j k * δ k) = _
      rw [hY, hUδ, hAdiff]; ring
    -- Bound the Lipschitz piece via aux_515B_lipschitz_bridge.
    -- Note: `|η k|` reduces definitionally to `|Y k - Yhat k|` since `η` is a `let`.
    have hbridge' : |h * (∑ k, M.A j k * (f (Y k) - f (Yhat k)))|
                    ≤ h * L * ∑ k, |M.A j k| * |η k| :=
      aux_515B_lipschitz_bridge (s := s) (r := s) _hL _hf_lip M.A Y Yhat h _hh j
    calc |η j - ∑ k, M.U j k * δ k|
        = |h * (∑ k, M.A j k * (f (Y k) - f (Yhat k)))
            - (Yhat j - h * (∑ k, M.A j k * f (Yhat k))
               - (∑ k, M.U j k * y_prev k))| := by rw [hkey]
      _ ≤ |h * (∑ k, M.A j k * (f (Y k) - f (Yhat k)))|
            + |Yhat j - h * (∑ k, M.A j k * f (Yhat k))
               - (∑ k, M.U j k * y_prev k)| := abs_sub _ _
      _ ≤ h * L * (∑ k, |M.A j k| * |η k|)
            + h^2 * L^2 * M_bound *
              ((1/2) * (c j)^2 + ∑ k, |M.A j k * c k|) :=
          add_le_add hbridge' (hres_j j)
  -- Apply aux_515B_eta_contraction.
  have hη_bound : ∀ j, |η j| ≤ ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j :=
    aux_515B_eta_contraction (s := s) (r := r) M.A M.U _hh _hh_le _h₀_pos _hL _hM
      _hδ_max_nonneg c _hc_nonneg ell_U phi_A η _hell_U_nonneg _hphi_A_nonneg
      _hellU_eq _hphiA_eq δ _hδ_max hη_contr _h_norm
  -- Construct K and prove the two clauses.
  refine ⟨fun i => h * (∑ j, M.B i j * f (Y j))
          + (∑ j, M.V i j * yt_prev j)
          - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
          - (∑ j, M.V i j * δ j), ?_, ?_⟩
  · -- Identity clause: trivial by `ring`.
    intro i; ring
  · -- Bound clause.
    intro i
    -- Beta-reduce the K-witness in the goal.
    show |h * (∑ j, M.B i j * f (Y j))
            + (∑ j, M.V i j * yt_prev j)
            - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
            - (∑ j, M.V i j * δ j)| ≤ α * h * δ_max + β * h^2
    -- K i = h Σ B·(f(Y) - f(Ŷ)) - R_i  (algebra).
    have hK_rel : h * (∑ j, M.B i j * f (Y j))
                  + (∑ j, M.V i j * yt_prev j)
                  - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
                  - (∑ j, M.V i j * δ j)
                  = h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))
                    - ((u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
                       - h * (∑ j, M.B i j * f (Yhat j))
                       - (∑ j, M.V i j * y_prev j)) := by
      have hVδ : (∑ j, M.V i j * δ j)
                  = (∑ j, M.V i j * yt_prev j) - (∑ j, M.V i j * y_prev j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [_hδ_def k]; ring
      have hBdiff : h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))
                    = h * (∑ j, M.B i j * f (Y j))
                      - h * (∑ j, M.B i j * f (Yhat j)) := by
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
      rw [hVδ, hBdiff]; ring
    rw [hK_rel]
    -- Now |LHS - R_i| ≤ |LHS| + |R_i|.
    -- |LHS| := |h Σ B·(f(Y) - f(Ŷ))| ≤ h L Σ|B|·|η|  (aux_515B_lipschitz_bridge).
    -- Note: `|η j|` reduces definitionally to `|Y j - Yhat j|` since `η` is a `let`.
    have hbridge_eta : |h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))|
                        ≤ h * L * ∑ j, |M.B i j| * |η j| :=
      aux_515B_lipschitz_bridge (s := s) (r := r) _hL _hf_lip M.B Y Yhat h _hh i
    -- Bound Σ|B|·|η| ≤ Σ|B|·(ell_U·δ_max + h²L²M·phi_A) using hη_bound.
    have hsum_eta_bound : (∑ j, |M.B i j| * |η j|)
                          ≤ ∑ j, |M.B i j| *
                              (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j) :=
      Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hη_bound j) (abs_nonneg _))
    have hhL_nn : 0 ≤ h * L := mul_nonneg _hh _hL
    have hbridge_full : |h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))|
                        ≤ h * L * (∑ j, |M.B i j| *
                            (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j)) :=
      hbridge_eta.trans (mul_le_mul_of_nonneg_left hsum_eta_bound hhL_nn)
    -- Algebraic split: Σ|B|·(ell_U·δ_max + h²L²M·phi_A)
    --   = (Σ|B|·ell_U)·δ_max + h²L²M·(Σ|B|·phi_A).
    have hsum_split : (∑ j, |M.B i j| *
                        (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j))
                      = (∑ j, |M.B i j| * ell_U j) * δ_max
                        + h^2 * L^2 * M_bound * (∑ j, |M.B i j| * phi_A j) := by
      have hsplit : (∑ j, |M.B i j| *
                        (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j))
                    = (∑ j, |M.B i j| * (ell_U j * δ_max))
                      + (∑ j, |M.B i j| * (h^2 * L^2 * M_bound * phi_A j)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring
      rw [hsplit]
      congr 1
      · rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
      · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    -- Use _hα_def i, _hβ_def i, and h ≤ h₀ to combine.
    have hα_i : L * (∑ j, |M.B i j| * ell_U j) ≤ α := _hα_def i
    have hβ_i : L^2 * M_bound *
                  ((1/2) * |u i| + |v i|
                   + (∑ j, |M.B i j * c j|)
                   + h₀ * L * (∑ j, |M.B i j| * phi_A j)) ≤ β := _hβ_def i
    -- Step A: h L (Σ|B|·ell_U) δ_max ≤ α h δ_max.
    have hsumBℓ_nn : 0 ≤ ∑ j, |M.B i j| * ell_U j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (_hell_U_nonneg j))
    have hsumBϕ_nn : 0 ≤ ∑ j, |M.B i j| * phi_A j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (_hphi_A_nonneg j))
    have hδmax_nn : 0 ≤ δ_max := _hδ_max_nonneg
    have hh2_nn : 0 ≤ h^2 := by positivity
    have hhL2M_nn : 0 ≤ h^2 * L^2 * M_bound :=
      mul_nonneg (mul_nonneg hh2_nn (by positivity)) _hM
    have hStepA : h * L * ((∑ j, |M.B i j| * ell_U j) * δ_max)
                  ≤ α * h * δ_max := by
      have h1 : h * L * ((∑ j, |M.B i j| * ell_U j) * δ_max)
                = h * δ_max * (L * (∑ j, |M.B i j| * ell_U j)) := by ring
      rw [h1]
      have hhδ_nn : 0 ≤ h * δ_max := mul_nonneg _hh hδmax_nn
      calc h * δ_max * (L * (∑ j, |M.B i j| * ell_U j))
          ≤ h * δ_max * α := mul_le_mul_of_nonneg_left hα_i hhδ_nn
        _ = α * h * δ_max := by ring
    -- Step B: h L (h²L²M Σ|B|·phi_A) ≤ h² L² M (h₀ L Σ|B|·phi_A) (h ≤ h₀).
    have hLsumBϕ_nn : 0 ≤ L * (∑ j, |M.B i j| * phi_A j) :=
      mul_nonneg _hL hsumBϕ_nn
    have hStepB : h * L * (h^2 * L^2 * M_bound * (∑ j, |M.B i j| * phi_A j))
                  ≤ h^2 * L^2 * M_bound * (h₀ * L * (∑ j, |M.B i j| * phi_A j)) := by
      have heq : h * L * (h^2 * L^2 * M_bound * (∑ j, |M.B i j| * phi_A j))
                  = h^2 * L^2 * M_bound * (h * L * (∑ j, |M.B i j| * phi_A j)) := by ring
      rw [heq]
      have hLsumBϕ_nn' : 0 ≤ L * (∑ j, |M.B i j| * phi_A j) := hLsumBϕ_nn
      have hmono : h * L * (∑ j, |M.B i j| * phi_A j)
                    ≤ h₀ * L * (∑ j, |M.B i j| * phi_A j) := by
        have : h * (L * (∑ j, |M.B i j| * phi_A j))
                ≤ h₀ * (L * (∑ j, |M.B i j| * phi_A j)) :=
          mul_le_mul_of_nonneg_right _hh_le hLsumBϕ_nn'
        linarith [this]
      exact mul_le_mul_of_nonneg_left hmono hhL2M_nn
    -- Combine A and B: bridge_full bound ≤ α h δ_max + h² L² M (h₀ L Σ|B|·phi_A).
    have hbridge_combined : |h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))|
                            ≤ α * h * δ_max
                              + h^2 * L^2 * M_bound *
                                (h₀ * L * (∑ j, |M.B i j| * phi_A j)) := by
      calc |h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))|
          ≤ h * L * (∑ j, |M.B i j| *
                (ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j)) := hbridge_full
        _ = h * L * ((∑ j, |M.B i j| * ell_U j) * δ_max
                      + h^2 * L^2 * M_bound * (∑ j, |M.B i j| * phi_A j)) := by
              rw [hsum_split]
        _ = h * L * ((∑ j, |M.B i j| * ell_U j) * δ_max)
            + h * L * (h^2 * L^2 * M_bound * (∑ j, |M.B i j| * phi_A j)) := by ring
        _ ≤ α * h * δ_max
            + h^2 * L^2 * M_bound * (h₀ * L * (∑ j, |M.B i j| * phi_A j)) :=
              add_le_add hStepA hStepB
    -- Now combine with |R_i|.
    have hRi_i := hRi i
    -- The bound: α h δ_max + h² L² M (½|u_i| + |v_i| + Σ|B·c| + h₀ L Σ|B|·phi_A) ≤ α h δ_max + β h^2.
    have hcombine : α * h * δ_max
                    + (h^2 * L^2 * M_bound *
                        (h₀ * L * (∑ j, |M.B i j| * phi_A j))
                       + h^2 * L^2 * M_bound *
                          ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|))
                    ≤ α * h * δ_max + β * h^2 := by
      -- Rearrange to: α h δ_max + h² · (L²M(...))   ≤ α h δ_max + β h²
      have hkey : (h^2 * L^2 * M_bound *
                      (h₀ * L * (∑ j, |M.B i j| * phi_A j))
                     + h^2 * L^2 * M_bound *
                        ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|))
                  = h^2 * (L^2 * M_bound *
                      ((1/2) * |u i| + |v i|
                       + (∑ j, |M.B i j * c j|)
                       + h₀ * L * (∑ j, |M.B i j| * phi_A j))) := by ring
      rw [hkey]
      have hh2_nn' : 0 ≤ h^2 := hh2_nn
      have hmono : h^2 * (L^2 * M_bound *
                      ((1/2) * |u i| + |v i|
                       + (∑ j, |M.B i j * c j|)
                       + h₀ * L * (∑ j, |M.B i j| * phi_A j)))
                    ≤ h^2 * β := mul_le_mul_of_nonneg_left hβ_i hh2_nn'
      linarith [hmono]
    -- Final triangle.
    calc |h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))
            - ((u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
               - h * (∑ j, M.B i j * f (Yhat j))
               - (∑ j, M.V i j * y_prev j))|
        ≤ |h * (∑ j, M.B i j * (f (Y j) - f (Yhat j)))|
            + |(u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
               - h * (∑ j, M.B i j * f (Yhat j))
               - (∑ j, M.V i j * y_prev j)| := abs_sub _ _
      _ ≤ (α * h * δ_max
            + h^2 * L^2 * M_bound *
              (h₀ * L * (∑ j, |M.B i j| * phi_A j)))
          + h^2 * L^2 * M_bound *
              ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|) :=
          add_le_add hbridge_combined hRi_i
      _ ≤ α * h * δ_max + β * h^2 := by linarith [hcombine]

/-! ## §515 capstone — Theorem 515D (stability + consistency ⇒ convergence) -/

/-- **Sub-lemma for `thm:515D`**: under stability + consistency, the
GLM iteration's *output* sequence `Y n n` converges to `u · yex(x)`
as `n → ∞`.

Proof outline (deferred to cycles 110+):
1. Iterate `localStepError_bound` across `n` steps to obtain a
   discrete-Grönwall recurrence in
   `δ_n m := max_i |Y n m i − (u_i · yex(x_{n,m}) + v_i · h_n · y'(x_{n,m}))|`,
   where `x_{n,m} := x₀ + m · h_n` and `h_n = (x − x₀)/n`.
2. Apply `discrete_gronwall_exp_bound` (Chapter 4 helper) to absorb
   the linear-in-error term into an exponential.
3. Squeeze as `h_n → 0` using `hφ` (which forces δ_n 0 → 0) and
   stability (which absorbs the `V^k` factor uniformly in `n`).

This is an *internal helper* for the §515 capstone, not a Butcher
entity. -/
private theorem aux_515D_output_tendsto {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (_hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (_hyex_x₀ : yex x₀ = y₀)
    (_hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    {u v : Fin r → ℝ}
    (_hVu : M.V *ᵥ u = u) (_hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {φ : ℝ → Fin r → ℝ}
    (_hφ : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                          (nhds 0) (nhds (u i * y₀)))
    {x : ℝ} (_hxx : x₀ < x)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (_hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))) :
    Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
        (nhds (fun i => u i * yex x)) := by
  sorry

/-- **Sub-lemma for `thm:515D`**: under stability + consistency,
the GLM iteration's *internal-stage* sequence `Y_int n` converges to
the constant function `fun _ => yex(x)` as `n → ∞`.

Proof outline (deferred to cycle 109): from the stage equation
`Y_int n i = h_n · ∑_j A_{ij} f(Y_int n j) + ∑_j U_{ij} Y n n j`,
take `n → ∞`:
* The first summand vanishes because `h_n → 0` and `f` is bounded
  along the trajectory (Lipschitz of `f` plus convergence of `Y n n`
  imply boundedness of `f(Y_int n j)` along a subsequence).
* The second summand tends to `(U *ᵥ (fun i => u i · yex x)) i =
  yex(x) · (U *ᵥ u) i = yex(x) · 1 = yex(x)` by continuity of
  `Matrix.mulVec` and the output convergence assumption.

This is the easier of the two sub-lemmas — pure linear-algebra
limit. It is an *internal helper* for the §515 capstone. -/
private theorem aux_515D_stage_tendsto {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (_hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (_hyex_x₀ : yex x₀ = y₀)
    (_hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    {u v : Fin r → ℝ}
    (_hVu : M.V *ᵥ u = u) (_hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {φ : ℝ → Fin r → ℝ}
    (_hφ : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                          (nhds 0) (nhds (u i * y₀)))
    {x : ℝ} (_hxx : x₀ < x)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (_hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))) :
    Filter.Tendsto Y_int Filter.atTop (nhds (fun _ => yex x)) := by
  sorry

/-- **Theorem 515D** (Butcher 2008, p. 417) — *A stable and consistent
general linear method is convergent.*

The textbook proof iterates the per-step error bound from
`lem:515B` (here: `localStepError_bound`) across `n` steps, applies
discrete Grönwall to absorb the linear-in-error term into an
exponential, then takes `h → 0` (i.e. `n → ∞`).

The proof below factors through two internal helpers:
* `aux_515D_output_tendsto` — output convergence `Y n n → u · yex(x)`.
* `aux_515D_stage_tendsto` — stage convergence `Y_int n → yex(x)`.

The `u ≠ 0` clause follows directly from `U·u = 𝟙`: evaluating at
index `⟨0, hs⟩ : Fin s` gives `(U·u) ⟨0, hs⟩ = 1`, contradicting
`u = 0`.

**Faithfulness divergence**: the hypothesis `hs : 0 < s` is a
strengthening of Butcher's flat statement. The textbook implicitly
assumes the GLM has at least one internal stage — the `s = 0` case
is genuinely degenerate (for `(s, r) = (0, 0)` the IsConvergent
statement is vacuously False since `Fin 0 → ℝ` has only the zero
inhabitant, so `u ≠ 0` is impossible; the textbook's flat statement
is therefore also incorrect at that corner case). See
`.prover-state/issues/thm_515D_s_zero_degenerate.md` for the full
analysis.

This is `thm:515D` of `entities/thm_515D.json`. -/
theorem GeneralLinearMethod.stable_consistent_isConvergent
    {s r : ℕ} (hs : 0 < s) (M : GeneralLinearMethod s r)
    (hStab : M.IsStable) (hCons : M.IsConsistent) :
    M.IsConvergent := by
  intro f L hf_lip x₀ y₀ yex hyex_x₀ hyex_ode
  obtain ⟨u, v, ⟨hVu, hUu⟩, hCons_eq⟩ := hCons
  refine ⟨u, ?_, ?_⟩
  · -- u ≠ 0: evaluate `U·u = 𝟙` at index `⟨0, hs⟩` to get
    -- `(U·u) ⟨0, hs⟩ = 1`. If `u = 0` then `U·u = 0`, giving `1 = 0`.
    intro hu0
    have h1 : (M.U *ᵥ u) ⟨0, hs⟩ = (fun _ : Fin s => (1 : ℝ)) ⟨0, hs⟩ :=
      congrFun hUu ⟨0, hs⟩
    rw [hu0] at h1
    simp [Matrix.mulVec, dotProduct] at h1
  · intro φ hφ x hxx Y Y_int hY_props
    refine ⟨?_, ?_⟩
    · exact aux_515D_output_tendsto M hStab hf_lip hyex_x₀ hyex_ode
              hVu hUu hCons_eq hφ hxx Y Y_int hY_props
    · exact aux_515D_stage_tendsto M hStab hf_lip hyex_x₀ hyex_ode
              hVu hUu hCons_eq hφ hxx Y Y_int hY_props

end OpenMath.Chapter5.Section510
