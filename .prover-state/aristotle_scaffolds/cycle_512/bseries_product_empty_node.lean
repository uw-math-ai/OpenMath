import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau
namespace QuotEquiv

-- §384 compatibility on the empty-children node tree. Since
-- `elementaryWeight (.node []) i = 1` (the empty `foldr`), this case
-- reduces to the same b-sum identity as leaf.
example {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (product q₁ q₂).bSeriesHom (.node []) =
      q₁.bSeriesHom (.node []) + q₂.bSeriesHom (.node []) := by
  sorry

end QuotEquiv
end ButcherTableau
