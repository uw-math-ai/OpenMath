import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Cycle 418, Job D: pointwise AB3 truncation residual bound.

Mirror of `ab2_pointwise_residual_bound` from
`OpenMath/LMMAB2Convergence.lean` (lines 415–494). The AB3 residual is
`y(t+3h) - y(t+2h) - h*(23/12*y'(t+2h) - 16/12*y'(t+h) + 5/12*y'(t))`.

Algebraic decomposition (where `R_y(k) = y(t+kh) - y(t) - kh*y'(t)
- (kh)²/2*y''(t) - (kh)³/6*y'''(t)` and
`R_y'(k) = y'(t+kh) - y'(t) - kh*y''(t) - (kh)²/2*y'''(t)`):

```
residual = R_y(3) - R_y(2) - (23h/12)*R_y'(2) + (16h/12)*R_y'(1)
```

Combined bound:
```
|R_y(3)| ≤ M/24 * (3h)^4 = 27M/8 * h^4
|R_y(2)| ≤ M/24 * (2h)^4 = 2M/3 * h^4
(23h/12)*|R_y'(2)| ≤ (23h/12)*(M/6)*(2h)^3 = 23/9 * M * h^4
(16h/12)*|R_y'(1)| ≤ (16h/12)*(M/6)*h^3 = 2/9 * M * h^4
Total ≤ (27/8 + 2/3 + 25/9) M h^4 = 491/72 * M * h^4
```
A safe over-estimate `K = 7 * M` works (since `491/72 ≈ 6.82 < 7`). -/

namespace LMM

theorem cycle418_ab3_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 3 * h) - y (t + 2 * h)
        - h * ((23 / 12) * deriv y (t + 2 * h)
              - (16 / 12) * deriv y (t + h)
              + (5 / 12) * deriv y t)|
      ≤ (7 : ℝ) * M * h ^ 4 := by
  sorry

end LMM
