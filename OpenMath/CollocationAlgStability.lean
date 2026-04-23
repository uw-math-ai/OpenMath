import OpenMath.Legendre
import OpenMath.StiffEquations

/-!
# Theorem 358A: Algebraic Stability of Collocation Methods

This module contains the sorry-first scaffold for the collocation/algebraic-stability
characterization from Iserles, Theorem 358A:

* a collocation Runge–Kutta method is algebraically stable if and only if its
  abscissae are zeros of a polynomial of the form `P_s^* - θ P_{s-1}^*` with
  `θ ≥ 0`.

The development is kept polynomial-first so it can reuse Mathlib's
`Polynomial.shiftedLegendre` together with the bridge already proved in
`OpenMath.Legendre`.
-/

open Polynomial

namespace ButcherTableau

variable {s : ℕ}

/-- The mapped shifted Legendre polynomial viewed in `ℝ[X]`. -/
noncomputable def shiftedLegendrePoly (n : ℕ) : ℝ[X] :=
  Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)

/-- The polynomial `P_s^* - θ P_{s-1}^*` in the polynomial model used for Theorem 358A. -/
noncomputable def algStabilityBoundaryPoly (s : ℕ) (θ : ℝ) : ℝ[X] :=
  shiftedLegendrePoly s - Polynomial.C θ * shiftedLegendrePoly (s - 1)

/-- The theorem-local collocation interface used for Theorem 358A.

We package only the existing assumptions already available in the project:
`B(s)`, `C(s)`, and injective nodes. -/
def IsCollocation (t : ButcherTableau s) : Prop :=
  0 < s ∧ t.SatisfiesB s ∧ t.SatisfiesC s ∧ Function.Injective t.c

/-- The nodes lie on a shifted-Legendre algebraic-stability boundary. -/
def HasAlgStabilityBoundaryNodes (t : ButcherTableau s) : Prop :=
  ∃ θ : ℝ, 0 ≤ θ ∧ ∀ i : Fin s, (algStabilityBoundaryPoly s θ).eval (t.c i) = 0

/-- The node polynomial has positive leading coefficient. -/
lemma nodePoly_leadingCoeff_pos (t : ButcherTableau s) :
    0 < (nodePoly t).leadingCoeff := by
  rw [(nodePoly_monic t).leadingCoeff]
  norm_num

/-- The live `(358c)` zero statement extracted from the transformed matrix
input behind algebraic stability.

This is the actual theorem-local seam for Theorem 358A: once this interval form
is proved from `hAlg.posdef_M`, the moment formulation below follows from the
existing polynomial/integral bridge in `OpenMath.Legendre`. -/
lemma nodePoly_interval_zero_aux_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
  sorry

/-- The live `(358c)` sign statement for degree-`s - 1` test polynomials with
positive leading coefficient.

This is the one-sided companion to
`nodePoly_interval_zero_aux_of_algStable`, and is the input needed later to
extract `θ ≥ 0` from the boundary-polynomial description. -/
lemma nodePoly_interval_nonpos_aux_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree = s - 1 → 0 < q.leadingCoeff →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x ≤ 0 := by
  sorry

/-- Matrix-to-polynomial bridge for Theorem 358A.

Under the collocation and algebraic-stability hypotheses, the node polynomial is
orthogonal to every polynomial of degree at most `s - 2`, phrased via
`polyMomentN` on `[0,1]`. -/
lemma nodePoly_polyMoment_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 → polyMomentN (2 * s) (nodePoly t * q) = 0 := by
  intro q hq
  have hq' : q.natDegree < s := by
    omega
  rw [polyMomentN_eq_intervalIntegral_of_natDegree_lt (N := 2 * s) (p := (nodePoly t * q))]
  · exact nodePoly_interval_zero_aux_of_algStable t hcoll hAlg q hq
  · exact nodePoly_mul_natDegree_lt t q hq'

/-- Interval-integral form of the node-polynomial orthogonality bridge. -/
lemma nodePoly_interval_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
  exact nodePoly_interval_zero_aux_of_algStable t hcoll hAlg

/-- A degree-`s` polynomial with positive leading coefficient and orthogonal to
all polynomials of degree at most `s - 2` must be a positive multiple of
`P_s^* - θ P_{s-1}^*`. -/
lemma orthogonal_degree_eq_boundaryPoly
    (hs : 0 < s) {φ : ℝ[X]}
    (hdeg : φ.natDegree = s) (hlc : 0 < φ.leadingCoeff)
    (horth : ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, (φ * q).eval x = 0) :
    ∃ θ a : ℝ, 0 < a ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ := by
  sorry

/-- Sign extraction for the `θ` parameter in the boundary polynomial.

This is the theorem-local version of the step obtained by testing against
`P_{s-1}^*`. -/
lemma boundary_theta_nonneg_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    {θ a : ℝ} (ha : 0 < a)
    (hnode : nodePoly t = Polynomial.C a * algStabilityBoundaryPoly s θ) :
    0 ≤ θ := by
  sorry

/-- Theorem 358A, `only if` direction. -/
theorem thm_358A_only_if
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    t.HasAlgStabilityBoundaryNodes := by
  obtain ⟨θ, a, ha, hnode⟩ :
      ∃ θ a : ℝ, 0 < a ∧ nodePoly t = Polynomial.C a * algStabilityBoundaryPoly s θ := by
    apply orthogonal_degree_eq_boundaryPoly
    · exact hcoll.1
    · exact nodePoly_natDegree t
    · exact nodePoly_leadingCoeff_pos t
    · exact nodePoly_interval_orthogonal_of_algStable t hcoll hAlg
  refine ⟨θ, boundary_theta_nonneg_of_algStable t hcoll hAlg ha hnode, ?_⟩
  intro i
  have hEval := congrArg (fun p : ℝ[X] => p.eval (t.c i)) hnode
  have hEval' : 0 = a * (algStabilityBoundaryPoly s θ).eval (t.c i) := by
    simpa [Polynomial.eval_mul, Polynomial.eval_C] using
      (nodePoly_eval_node t i).symm.trans hEval
  have ha_ne : a ≠ 0 := by linarith
  exact (mul_eq_zero.mp hEval'.symm).resolve_left ha_ne

/-- Theorem 358A, `if` direction. -/
theorem thm_358A_if
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) :
    t.IsAlgStable := by
  sorry

/-- **Theorem 358A**: a collocation Runge–Kutta method is algebraically stable
iff its nodes are zeros of `P_s^* - θ P_{s-1}^*` for some `θ ≥ 0`. -/
theorem thm_358A
    (t : ButcherTableau s) (hcoll : t.IsCollocation) :
    t.IsAlgStable ↔ t.HasAlgStabilityBoundaryNodes := by
  constructor
  · exact thm_358A_only_if t hcoll
  · exact thm_358A_if t hcoll

end ButcherTableau
