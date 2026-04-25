import OpenMath.CollocationAlgStability
import OpenMath.GaussLegendre3
import OpenMath.RadauIA2
import OpenMath.RadauIA3
import OpenMath.RadauIIA3

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

/-! ## Theorem 359B: Radau IIA family-level algebraic stability

Iserles §3.5.9, Theorem 359B: any collocation Runge–Kutta method whose
abscissae are the Radau IIA quadrature points (the right-endpoint Radau
nodes, with `c_s = 1`) is algebraically stable.

The Radau IIA nodes on `[0, 1]` are the zeros of `P_s^* − P_{s-1}^*` —
note that `P_n^*(1) = 1` in the textbook sign convention used in this
project, so this combination automatically vanishes at `x = 1`. Feeding
this through Theorem 358A with `θ = 1 ≥ 0` yields algebraic stability.
-/

/-- A Butcher tableau has **Radau IIA nodes** if its abscissae are the zeros
of the boundary polynomial `algStabilityBoundaryPoly s 1 = P_s^* − P_{s-1}^*`.

Under the textbook sign convention (`P_n^*(1) = 1`), this combination
vanishes at `x = 1`, so the right endpoint is always a Radau IIA node. -/
def HasRadauIIANodes (t : ButcherTableau s) : Prop :=
  ∀ i : Fin s, (algStabilityBoundaryPoly s 1).eval (t.c i) = 0

/-- Radau IIA nodes lie on the algebraic-stability boundary with `θ = 1 ≥ 0`. -/
theorem radauIIANodes_hasAlgStabilityBoundaryNodes
    (t : ButcherTableau s) (hRadau : t.HasRadauIIANodes) :
    t.HasAlgStabilityBoundaryNodes :=
  ⟨1, le_of_lt one_pos, hRadau⟩

/-- **Theorem 359B (Radau IIA)**: any collocation Runge–Kutta method whose
nodes are Radau IIA quadrature points is algebraically stable.

Immediate corollary of Theorem 358A with `θ = 1`. -/
theorem thm_359B_radauIIA
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hRadau : t.HasRadauIIANodes) :
    t.IsAlgStable :=
  thm_358A_if t hcoll (radauIIANodes_hasAlgStabilityBoundaryNodes t hRadau)

/-! ## Concrete corollary: Radau IIA 3-stage -/

private theorem sqrt6_sq' : Real.sqrt 6 ^ 2 = 6 :=
  Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)

/-- The nodes of `rkRadauIIA3` are zeros of `algStabilityBoundaryPoly 3 1`. -/
theorem rkRadauIIA3_hasRadauIIANodes :
    rkRadauIIA3.HasRadauIIANodes := by
  intro ⟨i, hi⟩
  simp only [algStabilityBoundaryPoly, eval_sub, eval_mul, eval_C, one_mul,
    shiftedLegendreStarPoly_eval, shiftedLegendreP_three]
  show (20 * (rkRadauIIA3.c ⟨i, hi⟩) ^ 3 - 30 * (rkRadauIIA3.c ⟨i, hi⟩) ^ 2 +
    12 * (rkRadauIIA3.c ⟨i, hi⟩) - 1) - shiftedLegendreP 2 (rkRadauIIA3.c ⟨i, hi⟩) = 0
  rw [shiftedLegendreP_two]
  interval_cases i
  · simp [rkRadauIIA3]
    nlinarith [sqrt6_sq', Real.sqrt_pos_of_pos (show (6 : ℝ) > 0 by norm_num)]
  · simp [rkRadauIIA3]
    nlinarith [sqrt6_sq', Real.sqrt_pos_of_pos (show (6 : ℝ) > 0 by norm_num)]
  · simp [rkRadauIIA3]; ring

/-- `rkRadauIIA3` satisfies the collocation conditions `IsCollocation`. -/
theorem rkRadauIIA3_isCollocation :
    rkRadauIIA3.IsCollocation := by
  refine ⟨by norm_num, rkRadauIIA3_B5.mono (by omega), rkRadauIIA3_C3, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [rkRadauIIA3] at hij ⊢ <;>
    nlinarith [sqrt6_sq', Real.sqrt_pos_of_pos (show (6 : ℝ) > 0 by norm_num)]

/-- **Radau IIA 3-stage is algebraically stable** (via Theorem 359B / 358A). -/
theorem rkRadauIIA3_algStable_via_358A :
    rkRadauIIA3.IsAlgStable :=
  thm_359B_radauIIA _ rkRadauIIA3_isCollocation rkRadauIIA3_hasRadauIIANodes

/-! ## Radau IA boundary-node facts

The left-endpoint Radau polynomial is `P_s^* + P_{s-1}^*`, represented here
as `algStabilityBoundaryPoly s (-1)`. Unlike the Radau IIA side, this cannot
be fed directly to Theorem 358A because that theorem requires `θ ≥ 0`.
-/

/-- A Butcher tableau has **Radau IA nodes** if its abscissae are zeros of
`algStabilityBoundaryPoly s (-1) = P_s^* + P_{s-1}^*`.

This is kept distinct from `HasRadauIIANodes`: the live proof of Theorem 358A
only covers nonnegative boundary parameters. -/
def HasRadauIANodes (t : ButcherTableau s) : Prop :=
  ∀ i : Fin s, (algStabilityBoundaryPoly s (-1)).eval (t.c i) = 0

/-- The nodes of `rkRadauIA2` are zeros of `algStabilityBoundaryPoly 2 (-1)`. -/
theorem rkRadauIA2_hasRadauIANodes :
    rkRadauIA2.HasRadauIANodes := by
  intro ⟨i, hi⟩
  simp only [algStabilityBoundaryPoly, eval_sub, eval_mul, eval_C, neg_mul,
    shiftedLegendreStarPoly_eval, shiftedLegendreP_two]
  rw [show 2 - 1 = 1 by norm_num]
  ring_nf
  rw [shiftedLegendreP_one]
  interval_cases i
  · simp [rkRadauIA2]
  · simp [rkRadauIA2]
    norm_num

/-- The nodes of `rkRadauIA3` are zeros of `algStabilityBoundaryPoly 3 (-1)`. -/
theorem rkRadauIA3_hasRadauIANodes :
    rkRadauIA3.HasRadauIANodes := by
  intro ⟨i, hi⟩
  simp only [algStabilityBoundaryPoly, eval_sub, eval_mul, eval_C, neg_mul,
    shiftedLegendreStarPoly_eval, shiftedLegendreP_three]
  rw [show 3 - 1 = 2 by norm_num]
  ring_nf
  rw [shiftedLegendreP_two]
  interval_cases i
  · simp [rkRadauIA3]
  · simp [rkRadauIA3]
    nlinarith [sqrt6_sq', Real.sqrt_pos_of_pos (show (6 : ℝ) > 0 by norm_num)]
  · simp [rkRadauIA3]
    nlinarith [sqrt6_sq', Real.sqrt_pos_of_pos (show (6 : ℝ) > 0 by norm_num)]

end ButcherTableau
