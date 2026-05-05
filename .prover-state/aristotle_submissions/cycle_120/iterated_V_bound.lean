/-
Cycle 120 Aristotle Job 4: close the body of `aux_515D_iterated_V_bound`.

Goal: from power-boundedness `∃ C, 0 ≤ C ∧ ∀ k, ‖V^k‖ ≤ C` (the data
of `M.IsStable`), deduce that there exists a constant `C' ≥ 0` such
that for every iteration count `k` and every input vector `x`, the
sup-of-abs of the matrix-vector product `(V^k *ᵥ x)` is bounded by
`C' · sup-of-abs of x`.

This is the load-bearing lemma for `aux_515D_max_deviation_geometric_bound`
— it converts the abstract operator-norm power bound `‖V^k‖ ≤ C` into
the concrete sup'-form bound needed when chaining
`aux_515D_per_step_recurrence`'s geometric closed form.

The proof should bridge the matrix Frobenius norm `‖V^k‖` (Mathlib
default) to the ∞-operator norm via `Matrix.linfty_opNorm` (max row
sum of absolute entries) and apply `Matrix.linfty_opNorm_mulVec`.

Concretely: `Matrix.linfty_opNorm M ≤ √r · ‖M‖_F` (Frobenius), and
`‖M *ᵥ x‖_∞ ≤ Matrix.linfty_opNorm M · ‖x‖_∞` for the row-vector
representation. Then bridge `‖x‖_∞ = sup'_i |x i|`.

Pick `C' := √r · C` (or whatever Mathlib's bridge gives) and combine.
-/
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.LInfty

open Matrix
open scoped BigOperators

set_option maxHeartbeats 200000

/-- **Iterated V bound from power-boundedness** (Path A from
`.prover-state/issues/aux_515D_iterated_V_bound.md`).

If `V` is power-bounded (`∃ C, ∀ k, ‖V^k‖ ≤ C`), then there exists a
non-negative constant `C'` such that for every `k` and every vector
`x`, the sup-of-abs of `(V^k *ᵥ x)` is bounded by
`C' · sup-of-abs of x`.

This is the load-bearing lemma for `aux_515D_max_deviation_geometric_bound`
— it converts power-boundedness (the `M.IsStable` data) into the
sup'-form bound needed when chaining `aux_515D_per_step_recurrence`'s
geometric closed form. -/
theorem aux_515D_iterated_V_bound {r : ℕ}
    (V : Matrix (Fin r) (Fin r) ℝ)
    (hStab : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖V ^ k‖ ≤ C)
    [Nonempty (Fin r)] :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ k : ℕ, ∀ x : Fin r → ℝ,
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |((V ^ k) *ᵥ x) i|)
      ≤ C' * Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |x i|) := by
  sorry
