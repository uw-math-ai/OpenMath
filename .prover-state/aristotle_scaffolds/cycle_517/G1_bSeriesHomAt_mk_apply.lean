import OpenMath.ButcherGroup

namespace ButcherTableau

theorem cycle517_G1_bSeriesHomAt_mk_apply_target {p s : ℕ}
    (q : QuotEquiv s) (τ : BTree) (hτ : τ.order ≤ p) :
    G1.bSeriesHomAt p τ hτ (G1.mk (p := p) q) = q.bSeriesHom τ := by
  sorry

end ButcherTableau
