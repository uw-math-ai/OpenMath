import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

/-- Cross-stage congruence of `IsG1Equiv` under `QuotEquiv.product`.
    Two pairs of quotient methods that agree on every Butcher-series
    coefficient up to order `p` produce products that also agree
    up to order `p`. -/
theorem IsG1Equiv.product_congr_target {p : ℕ}
    {s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q')
    (hr : IsG1Equiv p r r') :
    IsG1Equiv p (q.product r) (q'.product r') := by
  sorry

end ButcherTableau
