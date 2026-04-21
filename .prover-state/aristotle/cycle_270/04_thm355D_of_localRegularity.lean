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

def NoArrowsEscapeToInfinity (data : OrderArrowTerminationData) : Prop :=
  data.downArrowsAtInfinity = 0 ∧ data.upArrowsAtInfinity = 0

def SatisfiesArrowCountInequality (data : OrderArrowCountData) : Prop :=
  data.order ≤ data.downArrowsAtZeros + data.upArrowsAtPoles

theorem satisfiesArrowCountInequality_of_endpointClassification
    (data : OrderArrowTerminationData)
    (hfinite : FiniteArrowEndpointsClassified data)
    (hinfty : NoArrowsEscapeToInfinity data) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData := by
  rcases hfinite with ⟨hdownFinite, hupFinite⟩
  rcases hinfty with ⟨hdownInf, hupInf⟩
  dsimp [SatisfiesArrowCountInequality]
  simpa [FiniteArrowEndpointsClassified, NoArrowsEscapeToInfinity,
    hdownFinite, hupFinite, hdownInf, hupInf] using data.order_le_allTerminals

/-- Cycle 270 Aristotle target: the 355D reduction once local regularity handles
ordinary finite endpoints and infinity is still treated separately. -/
theorem cycle270_thm355D_of_localRegularity
    (data : OrderArrowTerminationData)
    (hlocal : OrdinaryFinitePointLocalRegularity data)
    (hinfty : NoArrowsEscapeToInfinity data) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData :=
  satisfiesArrowCountInequality_of_endpointClassification data
    ⟨hlocal.downArrowLocalContinuation, hlocal.upArrowLocalContinuation⟩ hinfty

end OpenMathAristotleCycle270
