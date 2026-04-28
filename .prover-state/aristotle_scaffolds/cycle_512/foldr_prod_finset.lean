import Mathlib

open Finset

-- The list-foldr product reduces to a Finset.prod over the list's index
-- finset. This is the load-bearing connection between the recursive shape
-- of `BTree.elementaryWeight` and Mathlib's `Finset.prod_add`.
example {α : Type*} (children : List α) (f : α → ℝ) :
    children.foldr (fun child acc => acc * f child) 1
      = ∏ i ∈ Finset.univ, f (children.get i) := by
  sorry
