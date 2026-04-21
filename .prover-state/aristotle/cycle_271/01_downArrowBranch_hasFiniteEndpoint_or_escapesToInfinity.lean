import OpenMath.OrderStars

namespace OpenMath

theorem cycle271_downArrowBranch_hasFiniteEndpoint_or_escapesToInfinity
    (R : ℂ → ℂ) (branch : GlobalDownArrowBranch R) :
    (∃ endpoint : OrderArrowFiniteEndpoint,
      HasFiniteEndpoint branch.toGlobalOrderArrowBranch endpoint) ∨
      EscapesEveryClosedBall branch.toGlobalOrderArrowBranch := by
  sorry

end OpenMath
