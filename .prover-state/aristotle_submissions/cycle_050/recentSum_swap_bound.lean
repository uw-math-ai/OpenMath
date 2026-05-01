import Mathlib

open scoped NNReal Topology

/-- **Index-arithmetic adapter for `thm:406D` (cycle 050).**
The "recent-window sum" `Σ_{j:Fin k} g(i − (j+1))` summed over
`i ∈ Ico k n` is bounded by `k` copies of the total sum
`Σ_{p ∈ Ico 0 n} g p`, because each `g p` appears in the recent
window for at most `k` later indices. -/
private lemma recentSum_swap_bound
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    (k n : ℕ) :
    (∑ i ∈ Finset.Ico k n, ∑ j : Fin k, g (i - (j.val + 1)))
      ≤ (k : ℝ) * ∑ p ∈ Finset.Ico 0 n, g p := by
  sorry
