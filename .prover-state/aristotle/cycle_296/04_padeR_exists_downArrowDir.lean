import OpenMath.PadeOrderStars

open Complex

noncomputable section

def padePhiErrorConst (n d : ℕ) : ℝ :=
  ((-1 : ℝ) ^ d) * ((n.factorial : ℝ) * (d.factorial : ℝ)) /
    (((n + d).factorial : ℝ) * ((n + d + 1).factorial : ℝ))

theorem padeR_exists_downArrowDir
    (n d : ℕ) :
    ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
  sorry
