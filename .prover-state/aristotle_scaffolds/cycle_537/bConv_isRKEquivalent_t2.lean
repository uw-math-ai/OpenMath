import OpenMath.ButcherGroup.Section384

namespace ButcherTableau

theorem cycle537_bConv_isRKEquivalent_t2_target
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂')
    (φ : BTree → ℝ) (τ : BTree) :
    ButcherProduct.bConv φ t₂ τ = ButcherProduct.bConv φ t₂' τ := by
  sorry

end ButcherTableau
