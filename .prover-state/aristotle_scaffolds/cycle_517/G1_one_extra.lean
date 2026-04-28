import OpenMath.ButcherGroup

namespace ButcherTableau

theorem cycle517_QuotEquiv_bSeriesHom_mk_target {s : ℕ}
    (t : ButcherTableau s) (τ : BTree) :
    (QuotEquiv.mk t).bSeriesHom τ = ∑ i, t.b i * t.elementaryWeight τ i := by
  sorry

theorem cycle517_IsG1Equiv_bSeriesHom_eq_target {s u p : ℕ}
    {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsG1Equiv p q₁ q₂) {τ : BTree} (hτ : τ.order ≤ p) :
    q₁.bSeriesHom τ = q₂.bSeriesHom τ := by
  sorry

end ButcherTableau
