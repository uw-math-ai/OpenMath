import Mathlib

/-- Finite count data attached to the order arrows of a rational approximation. -/
structure OrderArrowCountData where
  order : ℕ
  numeratorDegree : ℕ
  denominatorDegree : ℕ
  downArrowsAtZeros : ℕ
  upArrowsAtPoles : ℕ
  downArrowsAtZeros_le_numeratorDegree : downArrowsAtZeros ≤ numeratorDegree
  upArrowsAtPoles_le_denominatorDegree : upArrowsAtPoles ≤ denominatorDegree

/-- The inequality asserted by Theorem 355D. -/
def SatisfiesArrowCountInequality (data : OrderArrowCountData) : Prop :=
  data.order ≤ data.downArrowsAtZeros + data.upArrowsAtPoles

structure IsRationalApproxToExp (data : OrderArrowCountData) : Prop where
  order_le : data.order ≤ data.numeratorDegree + data.denominatorDegree

/-- **Theorem 355D**: the arrow counts satisfy `ñ + d̃ ≥ p`.
The remaining gap is the global arrow-trajectory/topology argument showing that
every order arrow is accounted for by a zero, a pole, or a controlled escape to
infinity. -/
theorem thm_355D (data : OrderArrowCountData)
    (h_approx : IsRationalApproxToExp data) :
    SatisfiesArrowCountInequality data := by
  sorry
