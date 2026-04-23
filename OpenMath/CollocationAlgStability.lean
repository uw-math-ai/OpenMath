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

/-- Matrix-to-polynomial bridge for Theorem 358A.

Under the collocation and algebraic-stability hypotheses, the node polynomial is
orthogonal to every polynomial of degree at most `s - 2`, phrased via
`polyMomentN` on `[0,1]`. -/
lemma nodePoly_polyMoment_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 → polyMomentN (2 * s) (nodePoly t * q) = 0 := by
  sorry

/-- Interval-integral form of the node-polynomial orthogonality bridge. -/
lemma nodePoly_interval_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
  sorry

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
  sorry

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
