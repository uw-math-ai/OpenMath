import OpenMath.LMMTruncationOp

/-! Cycle 400, Job A: degree bound for the local taylorPoly. -/

namespace LMM

theorem taylorPoly_natDegree_le_diag
    (y : ℕ → ℝ → ℝ) (t : ℝ) (n : ℕ) :
    (taylorPoly y t n).natDegree ≤ n := by
  sorry

end LMM
