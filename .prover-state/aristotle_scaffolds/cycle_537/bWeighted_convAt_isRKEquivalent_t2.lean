import OpenMath.ButcherGroup.Section384

open Finset

namespace ButcherTableau

theorem cycle537_bWeighted_convAt_isRKEquivalent_t2_target
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂')
    (coef : BTree → ℝ) (τ : BTree) :
    (∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ coef τ i)
      = ∑ i : Fin t, t₂'.b i * ButcherProduct.convAt t₂' coef τ i := by
  sorry

end ButcherTableau
