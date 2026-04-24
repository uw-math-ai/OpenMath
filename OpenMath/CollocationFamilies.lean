import OpenMath.CollocationAlgStability
import OpenMath.GaussLegendre3

/-!
# Theorem 359C: Algebraic Stability of Collocation Families

Iserles §3.5.9, Theorem 359C: the classical collocation families
(Gauss–Legendre, Radau IA) are algebraically stable. This follows from
Theorem 358A once their nodes are shown to lie on the algebraic-stability
boundary `P_s^* − θ P_{s-1}^*` for appropriate `θ ≥ 0`.

## Main Results

- `gaussLegendreNodes_hasAlgStabilityBoundaryNodes`: GL nodes satisfy the
  boundary condition with θ = 0
- `thm_359C_gaussLegendre`: any collocation method with GL nodes is
  algebraically stable
- `thm_359C_radauI`: any collocation method whose nodes are zeros of
  `P_s^* − P_{s-1}^*` is algebraically stable (θ = 1)
- Concrete corollaries for `rkGaussLegendre2` and `rkGaussLegendre3`

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 3.5.9.
-/

open Finset Real Polynomial

namespace ButcherTableau

variable {s : ℕ}

/-! ## Bridge: Gauss–Legendre nodes → algebraic-stability boundary nodes -/

/-- Gauss–Legendre nodes are zeros of `P_s^*`, which equals
`algStabilityBoundaryPoly s 0` (i.e., θ = 0). -/
theorem gaussLegendreNodes_hasAlgStabilityBoundaryNodes
    (t : ButcherTableau s) (hGL : t.HasGaussLegendreNodes) :
    t.HasAlgStabilityBoundaryNodes := by
  refine ⟨0, le_refl 0, fun i => ?_⟩
  simp only [algStabilityBoundaryPoly, eval_sub, eval_mul, eval_C, zero_mul,
    sub_zero, shiftedLegendreStarPoly_eval]
  exact hGL i

/-! ## Theorem 359C: abstract versions -/

/-- **Theorem 359C (Gauss–Legendre case)**: any collocation Runge–Kutta method
whose nodes are Gauss–Legendre quadrature points is algebraically stable.

This is an immediate corollary of Theorem 358A with θ = 0. -/
theorem thm_359C_gaussLegendre
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hGL : t.HasGaussLegendreNodes) :
    t.IsAlgStable :=
  thm_358A_if t hcoll (gaussLegendreNodes_hasAlgStabilityBoundaryNodes t hGL)

/-- **Theorem 359C (Radau I case)**: any collocation Runge–Kutta method
whose nodes are zeros of `P_s^* − P_{s-1}^*` is algebraically stable.

This is Theorem 358A with θ = 1. -/
theorem thm_359C_radauI
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hRadauI : ∀ i, (algStabilityBoundaryPoly s 1).eval (t.c i) = 0) :
    t.IsAlgStable :=
  thm_358A_if t hcoll ⟨1, le_of_lt one_pos, hRadauI⟩

/-! ## Concrete corollaries: GL2 -/

private theorem sqrt3_sq' : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- `rkGaussLegendre2` has Gauss–Legendre nodes: `shiftedLegendreP 2 (c i) = 0`. -/
theorem rkGaussLegendre2_hasGaussLegendreNodes :
    rkGaussLegendre2.HasGaussLegendreNodes :=
  gaussLegendre2_hasGL

/-- `rkGaussLegendre2` satisfies the collocation conditions `IsCollocation`. -/
theorem rkGaussLegendre2_isCollocation :
    rkGaussLegendre2.IsCollocation := by
  refine ⟨by norm_num, rkGaussLegendre2_B4.mono (by omega),
    rkGaussLegendre2_C2, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [rkGaussLegendre2] at hij ⊢ <;>
    nlinarith [sqrt3_sq', Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num),
               Real.sqrt_pos_of_pos (show (3 : ℝ) > 0 by norm_num)]

/-- **GL2 is algebraically stable** (via Theorem 359C / 358A). -/
theorem rkGaussLegendre2_algStable_via_358A :
    rkGaussLegendre2.IsAlgStable :=
  thm_359C_gaussLegendre _ rkGaussLegendre2_isCollocation
    rkGaussLegendre2_hasGaussLegendreNodes

/-! ## Concrete corollaries: GL3 -/

private theorem sqrt15_sq' : Real.sqrt 15 ^ 2 = 15 :=
  Real.sq_sqrt (by norm_num : (15 : ℝ) ≥ 0)

/-- `rkGaussLegendre3` has Gauss–Legendre nodes: `shiftedLegendreP 3 (c i) = 0`. -/
theorem rkGaussLegendre3_hasGaussLegendreNodes :
    rkGaussLegendre3.HasGaussLegendreNodes := by
  intro ⟨i, hi⟩
  simp only [shiftedLegendreP_three]
  interval_cases i
  · simp [rkGaussLegendre3]
    nlinarith [sqrt15_sq', Real.sqrt_pos_of_pos (show (15 : ℝ) > 0 by norm_num)]
  · simp [rkGaussLegendre3]; ring
  · simp [rkGaussLegendre3]
    nlinarith [sqrt15_sq', Real.sqrt_pos_of_pos (show (15 : ℝ) > 0 by norm_num)]

/-- `rkGaussLegendre3` satisfies the collocation conditions `IsCollocation`. -/
theorem rkGaussLegendre3_isCollocation :
    rkGaussLegendre3.IsCollocation := by
  refine ⟨by norm_num, rkGaussLegendre3_B6.mono (by omega),
    rkGaussLegendre3_C3, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [rkGaussLegendre3] at hij ⊢ <;>
    nlinarith [sqrt15_sq', Real.sqrt_pos_of_pos (show (15 : ℝ) > 0 by norm_num)]

/-- **GL3 is algebraically stable** (via Theorem 359C / 358A). -/
theorem rkGaussLegendre3_algStable_via_358A :
    rkGaussLegendre3.IsAlgStable :=
  thm_359C_gaussLegendre _ rkGaussLegendre3_isCollocation
    rkGaussLegendre3_hasGaussLegendreNodes

end ButcherTableau
