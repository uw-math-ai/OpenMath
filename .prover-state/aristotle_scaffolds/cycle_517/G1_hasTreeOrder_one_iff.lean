import OpenMath.ButcherGroup

namespace ButcherTableau

theorem cycle517_G1_hasTreeOrder_one_iff_target (p : ℕ) :
    G1.hasTreeOrder (G1.one p) ↔
      ∀ τ : BTree, τ.order ≤ p → (0 : ℝ) = 1 / (τ.density : ℝ) := by
  sorry

end ButcherTableau
