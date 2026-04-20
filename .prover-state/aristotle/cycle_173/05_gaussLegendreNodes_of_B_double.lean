import OpenMath.Legendre

namespace OpenMath
namespace ButcherTableau

variable {s : ℕ} (t : ButcherTableau s)

/-- Aristotle target for the forward half of Corollary 342D. -/
theorem cycle173_gaussLegendreNodes_of_B_double
    (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes := by
  sorry

end ButcherTableau
end OpenMath
