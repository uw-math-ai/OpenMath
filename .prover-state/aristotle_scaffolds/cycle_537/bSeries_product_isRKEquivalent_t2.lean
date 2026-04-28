import OpenMath.ButcherGroup.Section384

namespace ButcherTableau

theorem cycle537_bSeries_product_isRKEquivalent_t2_target
    {s t : ℕ} (t₁ : ButcherTableau s)
    {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂') (τ : BTree) :
    (ButcherProduct t₁ t₂).bSeries τ = (ButcherProduct t₁ t₂').bSeries τ := by
  sorry

end ButcherTableau
