import OpenMath.ButcherGroup

namespace ButcherTableau

theorem cycle517_G1_eq_one_iff_target {p : ℕ} (g : G1 p) :
    g = G1.one p ↔ ∀ τ : BTree, (hτ : τ.order ≤ p) →
      G1.bSeriesHomAt p τ hτ g = 0 := by
  sorry

end ButcherTableau
