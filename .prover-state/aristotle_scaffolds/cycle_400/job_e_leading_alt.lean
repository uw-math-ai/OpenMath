import OpenMath.LMMTruncationOp

/-! Cycle 400, Job E: cross-validation alternate proof of the leading
    Taylor truncation identity using a decomposition.

    The Taylor polynomial of degree `p+1` decomposes as
      `taylorPoly y t (p+1) = taylorPoly y t p
        + Polynomial.C (y (p+1) t / (p+1)!) * X^(p+1)`.
    This gives an alternate proof by linearity of `truncationOp`. -/

namespace LMM

variable {s : ℕ}

theorem truncationOp_taylorPoly_eq_leading_of_HasOrder_alt
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (y : ℕ → ℝ → ℝ) :
    m.truncationOp h
        (fun u => (taylorPoly y t (p + 1)).eval (u - t))
        (fun u => (taylorPoly y t (p + 1)).derivative.eval (u - t))
        t
      = y (p + 1) t * m.errorConstant p * h ^ (p + 1) := by
  sorry

end LMM
