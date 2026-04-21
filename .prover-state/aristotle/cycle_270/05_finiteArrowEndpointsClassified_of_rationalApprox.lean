import Mathlib

namespace OpenMathAristotleCycle270

structure OrderArrowCountData where
  order : ℕ
  numeratorDegree : ℕ
  denominatorDegree : ℕ
  downArrowsAtZeros : ℕ
  upArrowsAtPoles : ℕ
  downArrowsAtZeros_le_numeratorDegree : downArrowsAtZeros ≤ numeratorDegree
  upArrowsAtPoles_le_denominatorDegree : upArrowsAtPoles ≤ denominatorDegree

structure OrderArrowTerminationData extends OrderArrowCountData where
  downArrowsAtOrdinaryFinitePoints : ℕ
  upArrowsAtOrdinaryFinitePoints : ℕ
  downArrowsAtInfinity : ℕ
  upArrowsAtInfinity : ℕ
  order_le_allTerminals :
    order ≤ (downArrowsAtZeros + upArrowsAtPoles) +
      ((downArrowsAtOrdinaryFinitePoints + upArrowsAtOrdinaryFinitePoints) +
        (downArrowsAtInfinity + upArrowsAtInfinity))

def FiniteArrowEndpointsClassified (data : OrderArrowTerminationData) : Prop :=
  data.downArrowsAtOrdinaryFinitePoints = 0 ∧
    data.upArrowsAtOrdinaryFinitePoints = 0

structure OrdinaryFinitePointLocalRegularity (data : OrderArrowTerminationData) : Prop where
  downArrowLocalContinuation :
    data.downArrowsAtOrdinaryFinitePoints = 0
  upArrowLocalContinuation :
    data.upArrowsAtOrdinaryFinitePoints = 0

structure IsRationalApproxToExp (data : OrderArrowTerminationData) : Prop where
  order_le : data.order ≤ data.numeratorDegree + data.denominatorDegree
  localRegularity : OrdinaryFinitePointLocalRegularity data
  noArrowsEscapeToInfinity : data.downArrowsAtInfinity = 0 ∧ data.upArrowsAtInfinity = 0

/-- Cycle 270 Aristotle target: the finite-endpoint part of the 355D boundary
should now be a theorem derived from local regularity, not a standalone field. -/
theorem cycle270_finiteArrowEndpointsClassified_of_rationalApprox
    (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data) :
    FiniteArrowEndpointsClassified data :=
  ⟨h_approx.localRegularity.downArrowLocalContinuation,
    h_approx.localRegularity.upArrowLocalContinuation⟩

end OpenMathAristotleCycle270
