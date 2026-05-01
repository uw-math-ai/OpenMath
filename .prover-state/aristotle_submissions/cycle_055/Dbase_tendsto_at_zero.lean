import Mathlib

open scoped NNReal Topology

/-- **`Dbase`-style ratio is continuous at `h = 0` (cycle 055/056).**

Helper for §406D outer assembly: the constant
```
((1/2) · Σᵢ (i+1)² · |α(i+1)| + Σᵢ (i+1) · |β(i+1)|) · L · M_bound
  / (1 - h · L · |β 0|)
```
is continuous at `h = 0` since the numerator is constant and the
denominator tends to 1.
-/
private lemma Dbase_tendsto_at_zero
    {k : ℕ} (α β : Fin (k + 1) → ℝ) (L M_bound : ℝ) :
    Filter.Tendsto
      (fun h : ℝ =>
        ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |β i.succ|)
        * L * M_bound / (1 - h * L * |β 0|))
      (nhds 0)
      (nhds (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |α i.succ|)
              + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |β i.succ|)
            * L * M_bound)) := by
  sorry
