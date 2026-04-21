import OpenMath.OrderStars

namespace OpenMath

theorem cycle271_upArrowBranch_hasFiniteEndpoint_or_escapesToInfinity
    (R : ℂ → ℂ) (branch : GlobalUpArrowBranch R) :
    (∃ endpoint : OrderArrowFiniteEndpoint,
      HasFiniteEndpoint branch.toGlobalOrderArrowBranch endpoint) ∨
      EscapesEveryClosedBall branch.toGlobalOrderArrowBranch := by
  sorry

end OpenMath
