import OpenMath.LMMTruncationOp

/-! Cycle 400, Job B: coefficient formula for the local taylorPoly. -/

namespace LMM

theorem taylorPoly_coeff_diag
    (y : ℕ → ℝ → ℝ) (t : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (taylorPoly y t n).coeff k = y k t / (k.factorial : ℝ) := by
  sorry

end LMM
