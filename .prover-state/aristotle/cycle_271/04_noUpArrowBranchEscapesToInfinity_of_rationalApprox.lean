import OpenMath.OrderStars

namespace OpenMath

theorem cycle271_noUpArrowBranchEscapesToInfinity_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (branch : GlobalUpArrowBranch R) :
    ¬ EscapesEveryClosedBall branch.toGlobalOrderArrowBranch := by
  sorry

end OpenMath
