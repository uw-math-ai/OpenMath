import Mathlib

open Finset

/-- List-level combinator: a `foldr`-style product of binomial sums
expands as a Finset.powerset-indexed sum over which factor is taken
from each list position. -/
theorem cycle518_foldr_mul_add_eq_powerset_sum {α : Type*}
    (children : List α) (x y : α → ℝ) :
    children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ k ∈ T, x children[k]) * ∏ k ∈ Finset.univ \ T, y children[k] := by
  sorry
