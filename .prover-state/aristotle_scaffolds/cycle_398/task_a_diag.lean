import OpenMath.LMMTruncationOp

/-! Cycle 398 diagnostic: Task A — translated leading-coefficient identity.

The live version of this theorem already exists in
`OpenMath/LMMTruncationOp.lean` and has been proven via the
`truncationOp_translation` reduction to
`truncationOp_polyDegSucc_eq_leading_of_HasOrder`.

This scaffold asks Aristotle to find an *independent* proof for cross-check. -/

namespace LMM

variable {s : ℕ}

/-- DIAGNOSTIC: Find a proof that does *not* simply rewrite by
    `truncationOp_translation`. -/
theorem truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder_diag
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (a : Fin (p + 2) → ℝ) :
    m.truncationOp h
        (fun u => ∑ k : Fin (p + 2), a k * (u - t) ^ (k : ℕ))
        (fun u => ∑ k : Fin (p + 2),
            a k * ((k : ℕ) : ℝ) * (u - t) ^ ((k : ℕ) - 1))
        t
      = a (Fin.last (p + 1))
          * ((p + 1).factorial : ℝ) * m.errorConstant p * h ^ (p + 1) := by
  sorry

end LMM
