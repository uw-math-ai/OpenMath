import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Bridge: `bSeriesConvAug` is `bSeriesConv` plus the root-prune correction.

The augmented convolution differs from the asymmetric `bSeriesConv` only
in the contribution of the unique `(none, α τ)` admissible-cut entry,
which the asymmetric convolution filters out. -/
theorem bSeriesConvAug_eq_bSeriesConv_add (α β : AugSeries) (τ : BTree) :
    bSeriesConvAug α β τ
      = bSeriesConv α.toFun β.toFun τ + α.toFun τ * β.emptyVal := by
  sorry

end ButcherTableau
