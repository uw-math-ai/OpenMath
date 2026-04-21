import OpenMath.PadeOrderStars

open Complex

noncomputable section

def padePhiErrorConst (n d : ℕ) : ℝ :=
  ((-1 : ℝ) ^ d) * ((n.factorial : ℝ) * (d.factorial : ℝ)) /
    (((n + d).factorial : ℝ) * ((n + d + 1).factorial : ℝ))

theorem padeR_exp_neg_leading_term
    (n d : ℕ) :
    ∃ g : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
        z ^ (n + d + 2) * g z := by
  sorry
