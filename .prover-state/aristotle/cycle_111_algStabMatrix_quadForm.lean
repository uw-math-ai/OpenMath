import OpenMath.ANStability

open Finset

noncomputable section

namespace ButcherTableau

variable {s : ℕ}

/--
Expand the algebraic stability quadratic form into the `2β - α²` identity:

`∑ᵢⱼ vᵢ Mᵢⱼ vⱼ = 2 * ∑ᵢⱼ bᵢ vᵢ aᵢⱼ vⱼ - (∑ᵢ bᵢ vᵢ)^2`
-/
theorem cycle111_algStabMatrix_quadForm_eq (t : ButcherTableau s) (v : Fin s → ℝ) :
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      2 * (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j) -
        (∑ i : Fin s, t.b i * v i) ^ 2 := by
  sorry

end ButcherTableau
