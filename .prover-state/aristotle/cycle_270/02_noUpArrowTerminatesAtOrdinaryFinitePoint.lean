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

structure OrdinaryFinitePointLocalRegularity (data : OrderArrowTerminationData) : Prop where
  downArrowLocalContinuation :
    data.downArrowsAtOrdinaryFinitePoints = 0
  upArrowLocalContinuation :
    data.upArrowsAtOrdinaryFinitePoints = 0

/-- Cycle 270 Aristotle target: the up-arrow half of the ordinary finite local
regularity bridge. -/
theorem cycle270_noUpArrowTerminatesAtOrdinaryFinitePoint
    (data : OrderArrowTerminationData)
    (hlocal : OrdinaryFinitePointLocalRegularity data) :
    data.upArrowsAtOrdinaryFinitePoints = 0 :=
  hlocal.upArrowLocalContinuation

end OpenMathAristotleCycle270
