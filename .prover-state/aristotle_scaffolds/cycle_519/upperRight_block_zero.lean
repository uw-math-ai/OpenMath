import OpenMath.ButcherGroup

namespace ButcherTableau

/-- Upper-right block of the Butcher product matrix is zero. -/
theorem cycle519_upperRight_block_zero
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (i : Fin s) (j : Fin t) :
    (ButcherProduct t₁ t₂).A (Fin.castAdd t i) (Fin.natAdd s j) = 0 := by
  sorry

end ButcherTableau
