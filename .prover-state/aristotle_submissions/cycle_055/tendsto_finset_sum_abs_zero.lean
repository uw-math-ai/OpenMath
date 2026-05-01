import Mathlib

open scoped NNReal Topology

/-- **Sum of absolute values tends to 0 (cycle 055/056 helper).**

If each component of a finite-sum family tends to 0 in absolute value,
then the sum of absolute values tends to 0. Pure Tendsto/finite-sum
combinator; used by §406D outer assembly. -/
private lemma tendsto_finset_sum_abs_zero
    {ι : Type*} (s : Finset ι) {f : ℝ → ι → ℝ}
    (hf : ∀ i ∈ s, Filter.Tendsto (fun h : ℝ => f h i) (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun h : ℝ => ∑ i ∈ s, |f h i|)
      (nhds 0) (nhds 0) := by
  sorry
