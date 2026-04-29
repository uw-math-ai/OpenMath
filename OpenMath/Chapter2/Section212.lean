import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OpenMath.Chapter1.Section110

/-!
# Butcher §212 — Global truncation error of the Euler method

This file formalizes the entities of subsection 212 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

Contents:

* `EulerSetup` — the bundled hypotheses Butcher lays out in eqs.
  (212a)–(212e), encoded as a `structure`.
* `step_error_bound` — the per-step inequality obtained by subtracting
  (212a) from (212e) and applying (212d).
* `global_truncation_error_L_zero` — Theorem 212A, `L = 0` case.
* `global_truncation_error_L_pos` — Theorem 212A, `L > 0` case.

## Faithfulness notes

Butcher's Lipschitz hypothesis on `f` is global on the time interval
`[x₀, xₙ]`. Here we attach it pointwise to every `t : ℝ` (i.e.
`∀ t, LipschitzWith ⟨L, hL_nn⟩ (f t)`). This is **not** stronger than
Butcher: we only ever apply `hf_lip` at a step value `t = xₖ`, so any
Lipschitz hypothesis on a superset of the step values is admissible.
The polymorphic codomain `E` (any `[NormedAddCommGroup E] [NormedSpace ℝ E]`)
matches Butcher's `‖·‖` without committing to the inner-product structure
of `ℝ^N`.

The `hy_lte` field encodes Butcher's eq. (212e) plus his stated
assumption `‖E(x)‖ ≤ m`: the *bound* form, not the equality form. This
is the form actually used in the proof (Butcher subtracts and bounds
in one step).
-/

namespace OpenMath.Chapter2.Section212

open scoped NNReal Topology
open Real Set

/-- Butcher §212 — the bundled setup for the Euler-method global error
analysis.

Every field is an *input* (a hypothesis Butcher states), not a derived
conclusion:

* `n, x` — the step grid. `hx_mono` says `x` is strictly increasing.
* `H, hH_pos, hH_max` — maximum step size.
* `L, hL_nn` — Lipschitz constant for `f`.
* `m, hm_nn` — bound on the local truncation error.
* `f, hf_lip` — the ODE right-hand side, Lipschitz in its second
  variable (matches `def:110A`, with the time domain weakened to all
  of `ℝ`; we only ever use `hf_lip` at step values, so this is
  equivalent to Butcher's `t ∈ [x₀, xₙ]` form).
* `y` — the exact solution (data, not constructed here).
* `ŷ` — the numerical approximation: Euler iterates at step values,
  linear interpolation off-step (eq. 212a).
* `hŷ_interp` — eq. (212a): the Euler step + linear-interpolation
  recurrence relating `ŷ` at `t ∈ [xₖ, xₖ₊₁]` to its value at `xₖ`.
* `hy_lte` — eq. (212e) bounded form: `y` deviates from its Euler
  predictor by at most `(t - xₖ)² · m` on `[xₖ, xₖ₊₁]`. -/
structure EulerSetup
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  n      : ℕ
  x      : Fin (n + 1) → ℝ
  hx_mono : StrictMono x
  H      : ℝ
  hH_pos : 0 < H
  hH_max : ∀ k : Fin n, x k.succ - x k.castSucc ≤ H
  L      : ℝ≥0
  m      : ℝ
  hm_nn  : 0 ≤ m
  f      : ℝ → E → E
  hf_lip : ∀ t, LipschitzWith L (f t)
  y      : ℝ → E
  ŷ      : ℝ → E
  hŷ_interp : ∀ k : Fin n, ∀ t ∈ Set.Icc (x k.castSucc) (x k.succ),
      ŷ t = ŷ (x k.castSucc)
        + (t - x k.castSucc) • f (x k.castSucc) (ŷ (x k.castSucc))
  hy_lte : ∀ k : Fin n, ∀ t ∈ Set.Icc (x k.castSucc) (x k.succ),
      ‖y t - (y (x k.castSucc)
              + (t - x k.castSucc) • f (x k.castSucc) (y (x k.castSucc)))‖
        ≤ (t - x k.castSucc) ^ 2 * m

namespace EulerSetup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : EulerSetup E)

/-- Step length is non-negative since the grid is strictly increasing. -/
lemma step_nonneg (S : EulerSetup E) (k : Fin S.n) :
    0 ≤ S.x k.succ - S.x k.castSucc := by
  have : S.x k.castSucc < S.x k.succ :=
    S.hx_mono (by exact_mod_cast Nat.lt_succ_self k.val)
  linarith

/-- Step length is bounded by `H ≥ 0`. -/
lemma H_nonneg (S : EulerSetup E) : 0 ≤ S.H := S.hH_pos.le

/-- Per-step error inequality (eq. (212d) + (212a) − (212e)).

Subtracting (212a) from (212e), bounding the local-truncation residual
by `(xₖ₊₁ - xₖ)² · m ≤ (xₖ₊₁ - xₖ) · H · m` and applying Lipschitz to
the `f` difference, we obtain
`α(xₖ₊₁) ≤ (1 + (xₖ₊₁ - xₖ) · L) · α(xₖ) + (xₖ₊₁ - xₖ) · H · m`. -/
lemma step_error_bound (S : EulerSetup E) (k : Fin S.n) :
    ‖S.y (S.x k.succ) - S.ŷ (S.x k.succ)‖
      ≤ (1 + (S.x k.succ - S.x k.castSucc) * (S.L : ℝ))
          * ‖S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc)‖
        + (S.x k.succ - S.x k.castSucc) * S.H * S.m := by
  -- Set δ := xₖ₊₁ - xₖ ≥ 0, x₀ := xₖ.
  set δ : ℝ := S.x k.succ - S.x k.castSucc with hδ_def
  have hδ_nn : 0 ≤ δ := S.step_nonneg k
  have hδ_le_H : δ ≤ S.H := S.hH_max k
  -- Membership of `xₖ₊₁` in `[xₖ, xₖ₊₁]`.
  have h_mem : S.x k.succ ∈ Set.Icc (S.x k.castSucc) (S.x k.succ) :=
    ⟨by linarith, le_rfl⟩
  -- Apply `hŷ_interp` and `hy_lte` at `t = xₖ₊₁`.
  have hŷ := S.hŷ_interp k _ h_mem
  have hy := S.hy_lte k _ h_mem
  -- `t - xₖ` at `t = xₖ₊₁` simplifies to δ.
  have hsub : S.x k.succ - S.x k.castSucc = δ := rfl
  rw [hsub] at hŷ hy
  -- Difference: y(xₖ₊₁) - ŷ(xₖ₊₁) = (y xₖ - ŷ xₖ) + δ • (f(xₖ,y xₖ) - f(xₖ,ŷ xₖ)) + R,
  -- where R is the local-truncation residual with ‖R‖ ≤ δ² · m ≤ δ · H · m.
  have key :
      S.y (S.x k.succ) - S.ŷ (S.x k.succ)
        = (S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc))
          + δ • (S.f (S.x k.castSucc) (S.y (S.x k.castSucc))
                 - S.f (S.x k.castSucc) (S.ŷ (S.x k.castSucc)))
          + (S.y (S.x k.succ)
             - (S.y (S.x k.castSucc)
                + δ • S.f (S.x k.castSucc) (S.y (S.x k.castSucc)))) := by
    rw [hŷ]; module
  -- Now bound by triangle.
  rw [key]
  -- Bound the scalar-multiplied f-difference by Lipschitz.
  have h_lip :
      ‖S.f (S.x k.castSucc) (S.y (S.x k.castSucc))
       - S.f (S.x k.castSucc) (S.ŷ (S.x k.castSucc))‖
        ≤ (S.L : ℝ) * ‖S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc)‖ := by
    have := (S.hf_lip (S.x k.castSucc)).dist_le_mul
              (S.y (S.x k.castSucc)) (S.ŷ (S.x k.castSucc))
    simp only [dist_eq_norm] at this
    exact this
  have h_smul :
      ‖δ • (S.f (S.x k.castSucc) (S.y (S.x k.castSucc))
            - S.f (S.x k.castSucc) (S.ŷ (S.x k.castSucc)))‖
        = δ * ‖S.f (S.x k.castSucc) (S.y (S.x k.castSucc))
                - S.f (S.x k.castSucc) (S.ŷ (S.x k.castSucc))‖ := by
    rw [norm_smul, Real.norm_of_nonneg hδ_nn]
  -- Now hy_lte bounds the residual by δ² · m ≤ δ · H · m.
  have h_resid : ‖S.y (S.x k.succ)
                  - (S.y (S.x k.castSucc)
                     + δ • S.f (S.x k.castSucc) (S.y (S.x k.castSucc)))‖
                  ≤ δ ^ 2 * S.m := hy
  have h_resid' : δ ^ 2 * S.m ≤ δ * S.H * S.m := by
    have := mul_le_mul_of_nonneg_right hδ_le_H S.hm_nn
    have hδ2 : δ ^ 2 = δ * δ := by ring
    nlinarith [hδ_nn, S.hm_nn, hδ_le_H]
  -- Assemble.
  calc ‖_‖
      ≤ ‖(S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc))
            + δ • (S.f (S.x k.castSucc) (S.y (S.x k.castSucc))
                   - S.f (S.x k.castSucc) (S.ŷ (S.x k.castSucc)))‖
        + ‖S.y (S.x k.succ)
           - (S.y (S.x k.castSucc)
              + δ • S.f (S.x k.castSucc) (S.y (S.x k.castSucc)))‖ :=
        norm_add_le _ _
    _ ≤ (‖S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc)‖
          + δ * ‖S.f (S.x k.castSucc) (S.y (S.x k.castSucc))
                  - S.f (S.x k.castSucc) (S.ŷ (S.x k.castSucc))‖)
        + δ ^ 2 * S.m := by
          gcongr
          · calc _ ≤ _ := norm_add_le _ _
                 _ = _ := by rw [h_smul]
    _ ≤ (‖S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc)‖
          + δ * ((S.L : ℝ) * ‖S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc)‖))
        + δ * S.H * S.m := by
          have hlhs : δ * ‖_‖ ≤ δ * ((S.L : ℝ) * ‖_‖) :=
            mul_le_mul_of_nonneg_left h_lip hδ_nn
          linarith
    _ = (1 + δ * (S.L : ℝ))
          * ‖S.y (S.x k.castSucc) - S.ŷ (S.x k.castSucc)‖
        + δ * S.H * S.m := by ring

end EulerSetup

/-- Butcher §212 Theorem 212A — Euler global truncation error, `L = 0` case.

If the Lipschitz constant `L` is zero, the global error at every step
value `xₖ` is bounded by the initial error plus the accumulated
local-truncation contribution `H · m · (xₖ - x₀)`. -/
theorem global_truncation_error_L_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : EulerSetup E) (hL0 : S.L = 0) :
    ∀ k : Fin (S.n + 1),
      ‖S.y (S.x k) - S.ŷ (S.x k)‖
        ≤ ‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖
          + S.H * S.m * (S.x k - S.x ⟨0, by omega⟩) := by
  intro k
  rcases k with ⟨k, hk⟩
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hk' : k < S.n + 1 := by omega
      have hk_S_n : k < S.n := by omega
      have ih' := ih hk'
      -- Apply the per-step bound at `⟨k, hk_S_n⟩ : Fin S.n`.
      have hstep := S.step_error_bound ⟨k, hk_S_n⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      -- With L = 0, the per-step bound collapses.
      have hL_coe : (S.L : ℝ) = 0 := by exact_mod_cast hL0
      rw [hL_coe] at hstep
      simp only [mul_zero, add_zero, one_mul] at hstep
      -- Combine the IH with the per-step bound.
      have hδ_nn : 0 ≤ S.x ⟨k + 1, hk⟩ - S.x ⟨k, hk'⟩ :=
        S.step_nonneg ⟨k, hk_S_n⟩
      have hδ_le_H : S.x ⟨k + 1, hk⟩ - S.x ⟨k, hk'⟩ ≤ S.H :=
        S.hH_max ⟨k, hk_S_n⟩
      calc ‖S.y (S.x ⟨k + 1, hk⟩) - S.ŷ (S.x ⟨k + 1, hk⟩)‖
          ≤ ‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖
            + (S.x ⟨k + 1, hk⟩ - S.x ⟨k, hk'⟩) * S.H * S.m := hstep
        _ ≤ (‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖
              + S.H * S.m * (S.x ⟨k, hk'⟩ - S.x ⟨0, by omega⟩))
            + (S.x ⟨k + 1, hk⟩ - S.x ⟨k, hk'⟩) * S.H * S.m := by linarith
        _ = ‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖
              + S.H * S.m * (S.x ⟨k + 1, hk⟩ - S.x ⟨0, by omega⟩) := by ring

/-- Butcher §212 Theorem 212A — Euler global truncation error, `L > 0` case.

When the Lipschitz constant `L` is positive, the global error grows
exponentially in `(xₖ - x₀) · L`, with an additive term `Hm/L · (exp(...) - 1)`
from the accumulated local-truncation errors.

Following Butcher's argument: setting `φ(k) := α(xₖ) + Hm/L`, the per-step
bound rearranges to `φ(k+1) ≤ (1 + δₖ·L) · φ(k) ≤ exp(δₖ·L) · φ(k)`. By
induction, `φ(k) ≤ exp((xₖ - x₀)·L) · φ(0)`. Subtracting `Hm/L` gives the
stated bound. -/
theorem global_truncation_error_L_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : EulerSetup E) (hL : 0 < (S.L : ℝ)) :
    ∀ k : Fin (S.n + 1),
      ‖S.y (S.x k) - S.ŷ (S.x k)‖
        ≤ Real.exp ((S.x k - S.x ⟨0, by omega⟩) * (S.L : ℝ))
            * ‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖
          + (Real.exp ((S.x k - S.x ⟨0, by omega⟩) * (S.L : ℝ)) - 1) / (S.L : ℝ)
              * S.H * S.m := by
  -- Define the auxiliary `φ(k) := α(xₖ) + Hm/L`.
  set c : ℝ := S.H * S.m / (S.L : ℝ) with hc_def
  have hHm_nn : 0 ≤ S.H * S.m := mul_nonneg S.H_nonneg S.hm_nn
  have hc_nn : 0 ≤ c := div_nonneg hHm_nn hL.le
  -- Key induction: φ(k) ≤ exp((xₖ - x₀)·L) · φ(0).
  have key :
      ∀ k : Fin (S.n + 1),
        ‖S.y (S.x k) - S.ŷ (S.x k)‖ + c
          ≤ Real.exp ((S.x k - S.x ⟨0, by omega⟩) * (S.L : ℝ))
              * (‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖ + c) := by
    intro k
    rcases k with ⟨k, hk⟩
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hk' : k < S.n + 1 := by omega
        have hk_S_n : k < S.n := by omega
        have ih' := ih hk'
        -- Per-step bound at `⟨k, hk_S_n⟩ : Fin S.n`.
        have hstep := S.step_error_bound ⟨k, hk_S_n⟩
        simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
        set δ : ℝ := S.x ⟨k + 1, hk⟩ - S.x ⟨k, hk'⟩ with hδ_def
        have hδ_nn : 0 ≤ δ := S.step_nonneg ⟨k, hk_S_n⟩
        have hδL_nn : 0 ≤ δ * (S.L : ℝ) := mul_nonneg hδ_nn hL.le
        -- Rearrange the per-step bound: α(xₖ₊₁) + c ≤ (1 + δL)·(α(xₖ) + c).
        -- Use δ·H·m ≤ δ·L·c, since c = Hm/L gives Hm = cL, so δ·H·m = δ·L·c.
        have hHm_eq : S.H * S.m = c * (S.L : ℝ) := by
          rw [hc_def]; field_simp
        have hα_nn : 0 ≤ ‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖ := norm_nonneg _
        have hbound : ‖S.y (S.x ⟨k + 1, hk⟩) - S.ŷ (S.x ⟨k + 1, hk⟩)‖ + c
                        ≤ (1 + δ * (S.L : ℝ))
                            * (‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖ + c) := by
          have hδSHm : δ * S.H * S.m = δ * (S.L : ℝ) * c := by
            have : δ * (S.H * S.m) = δ * (c * (S.L : ℝ)) := by rw [hHm_eq]
            linarith [this]
          calc ‖S.y (S.x ⟨k + 1, hk⟩) - S.ŷ (S.x ⟨k + 1, hk⟩)‖ + c
              ≤ ((1 + δ * (S.L : ℝ))
                    * ‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖
                  + δ * S.H * S.m) + c := by linarith
            _ = (1 + δ * (S.L : ℝ))
                  * (‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖ + c) := by
                rw [hδSHm]; ring
        -- Now bound by exp.
        have h_exp : 1 + δ * (S.L : ℝ) ≤ Real.exp (δ * (S.L : ℝ)) := by
          have := Real.add_one_le_exp (δ * (S.L : ℝ))
          linarith
        have hφ_nn : 0 ≤ ‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖ + c := by
          linarith
        -- Combine.
        have hφk_nn : 0 ≤ Real.exp ((S.x ⟨k, hk'⟩ - S.x ⟨0, by omega⟩) * (S.L : ℝ)) :=
          (Real.exp_pos _).le
        calc ‖S.y (S.x ⟨k + 1, hk⟩) - S.ŷ (S.x ⟨k + 1, hk⟩)‖ + c
            ≤ (1 + δ * (S.L : ℝ))
                * (‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖ + c) := hbound
          _ ≤ Real.exp (δ * (S.L : ℝ))
                * (‖S.y (S.x ⟨k, hk'⟩) - S.ŷ (S.x ⟨k, hk'⟩)‖ + c) :=
              mul_le_mul_of_nonneg_right h_exp hφ_nn
          _ ≤ Real.exp (δ * (S.L : ℝ))
                * (Real.exp ((S.x ⟨k, hk'⟩ - S.x ⟨0, by omega⟩) * (S.L : ℝ))
                    * (‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖ + c)) := by
              exact mul_le_mul_of_nonneg_left ih' (Real.exp_pos _).le
          _ = Real.exp ((S.x ⟨k + 1, hk⟩ - S.x ⟨0, by omega⟩) * (S.L : ℝ))
                * (‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖ + c) := by
              rw [← mul_assoc, ← Real.exp_add]
              congr 2
              show δ * (S.L : ℝ) + (S.x ⟨k, hk'⟩ - S.x ⟨0, by omega⟩) * (S.L : ℝ)
                = (S.x ⟨k + 1, hk⟩ - S.x ⟨0, by omega⟩) * (S.L : ℝ)
              rw [hδ_def]; ring
  -- Use `key` and rearrange.
  intro k
  have hk := key k
  -- hk : α(xₖ) + c ≤ exp(...) · (α(x₀) + c)
  -- Want: α(xₖ) ≤ exp(...) · α(x₀) + (exp(...) - 1)/L · H · m
  -- Note: c = H·m/L, so c · L = H·m and (exp(...) - 1) · c = (exp(...) - 1)/L · H · m.
  set E0 : ℝ := Real.exp ((S.x k - S.x ⟨0, by omega⟩) * (S.L : ℝ)) with hE0_def
  set α0 : ℝ := ‖S.y (S.x ⟨0, by omega⟩) - S.ŷ (S.x ⟨0, by omega⟩)‖ with hα0_def
  set αk : ℝ := ‖S.y (S.x k) - S.ŷ (S.x k)‖ with hαk_def
  have hk' : αk + c ≤ E0 * (α0 + c) := hk
  have h_eq : (E0 - 1) / (S.L : ℝ) * S.H * S.m = (E0 - 1) * c := by
    rw [hc_def]; field_simp
  rw [h_eq]
  have : αk ≤ E0 * α0 + (E0 - 1) * c := by linarith
  exact this

/-! ## Concrete witness

Constructing a non-trivial `EulerSetup` requires solving an ODE — well outside
the scope of this file. We satisfy the project's "every new structure must
have a witness" rule with the degenerate `n = 0` instance: the step grid is
the singleton `Fin 1`, all the `∀ k : Fin 0` fields are vacuous, and `f, y, ŷ`
are arbitrary. This proves that the `EulerSetup` structure is non-vacuous. -/

/-- A trivial `EulerSetup` instance with empty step grid (`n = 0`). -/
def EulerSetup.trivial : EulerSetup ℝ where
  n      := 0
  x      := fun _ => 0
  hx_mono := fun a b hab => by
    -- `Fin 1` is a singleton, so the strictly-mono hypothesis is vacuous.
    have h1 : a.val = 0 := Nat.lt_one_iff.mp a.isLt
    have h2 : b.val = 0 := Nat.lt_one_iff.mp b.isLt
    have : a = b := Fin.ext (h1.trans h2.symm)
    exact absurd hab (by simp [this])
  H      := 1
  hH_pos := by norm_num
  hH_max := fun k => k.elim0
  L      := 0
  m      := 0
  hm_nn  := le_rfl
  f      := fun _ _ => 0
  hf_lip := fun _ => by
    simp [LipschitzWith]
  y      := fun _ => 0
  ŷ      := fun _ => 0
  hŷ_interp := fun k => k.elim0
  hy_lte    := fun k => k.elim0

end OpenMath.Chapter2.Section212
