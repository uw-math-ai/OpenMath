import OpenMath.LMMTruncationOp

/-! Cycle 400, Job C: leading-coefficient Taylor truncation identity.

  Hint: invoke `truncationOp_polynomial_evalShift_eq_leading_of_HasOrder`
  with `P := taylorPoly y t (p + 1)` and degree bound from
  `taylorPoly_natDegree_le`. Then rewrite `P.coeff (p+1)` using
  `taylorPoly_coeff` and cancel the factorial. -/

namespace LMM

variable {s : ℕ}

theorem truncationOp_taylorPoly_eq_leading_of_HasOrder_diag
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (y : ℕ → ℝ → ℝ) :
    m.truncationOp h
        (fun u => (taylorPoly y t (p + 1)).eval (u - t))
        (fun u => (taylorPoly y t (p + 1)).derivative.eval (u - t))
        t
      = y (p + 1) t * m.errorConstant p * h ^ (p + 1) := by
  sorry

end LMM
