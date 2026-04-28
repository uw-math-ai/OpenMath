import OpenMath.ButcherGroup.Section384

namespace ButcherTableau

theorem cycle537_convAt_perm_t2_aux
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (σ : Equiv.Perm (Fin t))
    (hA : ∀ i j, t₂'.A (σ i) (σ j) = t₂.A i j)
    (coef : BTree → ℝ) (τ : BTree) (i : Fin t) :
    ButcherProduct.convAt t₂' coef τ (σ i)
      = ButcherProduct.convAt t₂ coef τ i := by
  sorry

end ButcherTableau
