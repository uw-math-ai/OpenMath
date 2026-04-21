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

/-- Cycle 270 Aristotle target: package the local regularity input into the
finite endpoint classification used by 355D. -/
theorem cycle270_finiteArrowEndpointsClassified_of_localRegularity
    (data : OrderArrowTerminationData)
    (hlocal : OrdinaryFinitePointLocalRegularity data) :
    FiniteArrowEndpointsClassified data :=
  ⟨hlocal.downArrowLocalContinuation, hlocal.upArrowLocalContinuation⟩

end OpenMathAristotleCycle270
