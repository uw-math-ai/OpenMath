import OpenMath.OrderStars

namespace OpenMath

theorem cycle271_noDownArrowBranchEscapesToInfinity_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (branch : GlobalDownArrowBranch R) :
    ¬ EscapesEveryClosedBall branch.toGlobalOrderArrowBranch := by
  sorry

end OpenMath
