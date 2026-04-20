import OpenMath.Legendre
import OpenMath.ShiftedLegendreDivision

namespace OpenMath
namespace ButcherTableau

variable {s : ℕ} (t : ButcherTableau s)

/-- Isolate the `s < k ≤ 2s` range needed in `gaussLegendre_B_double`. -/
theorem cycle173_gaussian_range_setup
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * s) (hks : ¬ k ≤ s) :
    ∃ j, j < s ∧ k = s + (j + 1) := by
  sorry

end ButcherTableau
end OpenMath
