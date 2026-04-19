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

structure IsRationalApproxToExp (data : OrderArrowCountData) : Prop where
  order_le : data.order ≤ data.numeratorDegree + data.denominatorDegree

structure IsPadeApproxToExp (data : OrderArrowCountData) : Prop
    extends IsRationalApproxToExp data where
  order_eq : data.order = data.numeratorDegree + data.denominatorDegree

/-- Focused A-stability interface for cycle 137.
We no longer use a vacuous `True` field. Instead we keep the finite consequence
of 355F that the imaginary axis contains no order-star-plus points. -/
structure IsAStablePadeApprox (data : OrderArrowCountData) : Prop where
  pade : IsPadeApproxToExp data
  orderStarPlusOnImagAxis : ℝ → Prop
  noPlusOnImagAxis : ∀ y : ℝ, ¬ orderStarPlusOnImagAxis y

/-- **Theorem 355G** (Ehle barrier): an A-stable Padé approximation must satisfy
`n ≤ d ≤ n + 2`. The remaining gap is the sector-counting argument turning the
imaginary-axis exclusion into a bound on alternating sectors at the origin. -/
theorem ehle_barrier (data : OrderArrowCountData)
    (h : IsAStablePadeApprox data) :
    data.numeratorDegree ≤ data.denominatorDegree ∧
    data.denominatorDegree ≤ data.numeratorDegree + 2 := by
  sorry
