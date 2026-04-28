import OpenMath.ButcherGroup

namespace ButcherTableau

/-- Cut-side `b`-weighted sum after the upper-left block reduction. -/
theorem cycle519_bSeries_castAdd_corollary
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) :
    (∑ i : Fin s, t₁.b i *
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i))
      = ∑ i : Fin s, t₁.b i * t₁.elementaryWeight τ i := by
  sorry

end ButcherTableau
