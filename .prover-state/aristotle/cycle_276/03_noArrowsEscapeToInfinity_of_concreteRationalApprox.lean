import OpenMath.OrderStars

namespace OpenMath

/-- Scratch placeholder for the still-missing `R`-dependent analytic hypothesis.
This stays out of the live theorem boundary in `OrderStars.lean`. -/
axiom IsConcreteRationalApproxToExp (R : ℂ → ℂ)
    (data : OrderArrowTerminationData) : Prop

axiom cycle276_noRealizedDownArrowInfinityBranch_of_concreteRationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (hconcrete : IsConcreteRationalApproxToExp R data) :
    NoRealizedDownArrowInfinityBranch R

axiom cycle276_noRealizedUpArrowInfinityBranch_of_concreteRationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (hconcrete : IsConcreteRationalApproxToExp R data) :
    NoRealizedUpArrowInfinityBranch R

theorem cycle276_noArrowsEscapeToInfinity_of_concreteRationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (hconcrete : IsConcreteRationalApproxToExp R data)
    (hreal : RealizesInfinityBranchGerms R data) :
    NoArrowsEscapeToInfinity data := by
  exact noArrowsEscapeToInfinity_of_noRealizedArrowInfinityBranches hreal
    (cycle276_noRealizedDownArrowInfinityBranch_of_concreteRationalApprox
      R data hconcrete)
    (cycle276_noRealizedUpArrowInfinityBranch_of_concreteRationalApprox
      R data hconcrete)

end OpenMath
