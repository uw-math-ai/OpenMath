import OpenMath.ButcherGroup.Section384

namespace ButcherTableau

theorem cycle537_convAt_isRKEquivalent_t2_target
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂')
    (coef : BTree → ℝ) (τ : BTree) (i : Fin t) :
    ∃ i', ButcherProduct.convAt t₂' coef τ i'
      = ButcherProduct.convAt t₂ coef τ i := by
  sorry

end ButcherTableau
