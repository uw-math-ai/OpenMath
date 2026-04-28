import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau
namespace QuotEquiv

-- Headline §384 leaf compatibility: the b-weighted elementary-weight sum
-- of `(t₁ ⊗ t₂)` at the leaf tree decomposes as the sum of the two
-- factors' leaf b-series. This is a thin packaging of `butcherProduct_b_sum`.
example {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (product q₁ q₂).bSeriesHom .leaf
      = q₁.bSeriesHom .leaf + q₂.bSeriesHom .leaf := by
  sorry

end QuotEquiv
end ButcherTableau
