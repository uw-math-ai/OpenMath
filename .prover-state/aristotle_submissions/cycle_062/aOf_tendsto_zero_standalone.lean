import Mathlib

open scoped NNReal Topology

/-- **Cycle 062 helper: bracket × tail-sum tends to 0 as `h → 0`.**

The bracket `Θ + (Θ + 1) · Cbase(h) · h · k + 1` tends to a finite
limit (`Θ + 1`, since `Cbase(h) · h → 0`). The tail
`Σ |yPrime k α (u h) i|` tends to 0 if each `u h j → 0`. So the
product → 0. This is the cycle 057 `a_m_tendsto_zero` re-stated for
the cycle 062 wrapper. -/
private lemma cycle_062_a_m_tendsto_zero
    {k : ℕ} (α : Fin k → ℝ) (β0 : ℝ) (Θ L : ℝ)
    (sumα sumβ : ℝ)
    (hCbase_lim : Filter.Tendsto
      (fun h : ℝ => L * (|β0| * sumα + sumβ) / (1 - h * L * |β0|))
      (nhds 0) (nhds (L * (|β0| * sumα + sumβ))))
    (tail : ℝ → ℝ)
    (htail : Filter.Tendsto tail (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun h : ℝ =>
        (Θ + (Θ + 1) * (L * (|β0| * sumα + sumβ) / (1 - h * L * |β0|))
            * h * (k : ℝ) + 1)
          * tail h)
      (nhds 0) (nhds 0) := by
  sorry
