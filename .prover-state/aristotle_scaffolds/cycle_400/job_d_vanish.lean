import OpenMath.LMMTruncationOp

/-! Cycle 400, Job D: vanishing Taylor truncation identity.

  Hint: combine `truncationOp_polynomial_evalShift_eq_zero_of_HasOrder`
  with `taylorPoly_natDegree_le`. -/

namespace LMM

variable {s : ℕ}

theorem truncationOp_taylorPoly_eq_zero_of_HasOrder_diag
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (y : ℕ → ℝ → ℝ) :
    m.truncationOp h
        (fun u => (taylorPoly y t p).eval (u - t))
        (fun u => (taylorPoly y t p).derivative.eval (u - t))
        t = 0 := by
  sorry

end LMM
