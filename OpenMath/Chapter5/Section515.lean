import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import OpenMath.Chapter5.Section512

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
condition `c = A·𝟙 + U·v` matches the textbook setup. -/
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
    (_hc_def : c = M.glmAbscissae v) :
    ∀ i : Fin s,
      |yex (xn1 + h * c i)
        - h * (∑ j, M.A i j * f (yex (xn1 + h * c j)))
        - (∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1))|
      ≤ h^2 * L^2 * M_bound *
        ((1/2) * (c i)^2 + ∑ j, |M.A i j * c j|) := by
  -- Sorry-first: the proof is the T1+T2+T3+T4 decomposition described
  -- in the file docstring. Cycle 100 leaves this sorry; the four
  -- sub-bounds are submitted to Aristotle in
  -- `.prover-state/aristotle_submissions/cycle_100/`.
  sorry

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
    (_hc_def : c = M.glmAbscissae v) :
    ∀ i : Fin r,
      |(u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
        - h * (∑ j, M.B i j * f (yex (xn1 + h * c j)))
        - (∑ j, M.V i j * (u j * yex xn1 + v j * h * deriv yex xn1))|
      ≤ h^2 * L^2 * M_bound *
        ((1/2) * |u i| + |v i| + ∑ j, |M.B i j * c j|) := by
  -- Sorry-first: same T1+T2+T3+T4 decomposition as (515a) but with
  -- output-side coefficients (B/V instead of A/U). Cycle 100 leaves
  -- this sorry; closure tracks (515a).
  sorry

end OpenMath.Chapter5.Section510
