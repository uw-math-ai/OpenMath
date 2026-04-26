import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAM7VectorConvergence

/-! ## Adams--Moulton 8-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM8 scalar quantitative convergence chain in
`OpenMath/LMMAM8Convergence.lean`.  The implicit AM8 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.

This cycle (454) lands the trajectory predicate, the textbook local truncation
residual unfolding, and the supporting tenth-order vector Taylor ladder
(promoted public in `LMMAM7VectorConvergence`).  The remaining pieces of the
chain — the one-step Lipschitz/error recurrence, the ten-term residual algebra
split, the pointwise/local residual bound, and the global headline — are
scoped to a follow-up cycle: they require porting the AM8 scalar
(`LMMAM8Convergence`) chain at full size, plus the kernel-discipline
`clear_value` + four-helper extraction pattern from cycle 444's AM7 vector
chain.
-/

namespace LMM

/-- AM8 vector trajectory predicate.  The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM8TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 8)
      = y (n + 7)
        + h • ((1070017 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h) (y (n + 8))
             + (4467094 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             - (4604594 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             + (5595358 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             - (5033120 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (3146338 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (1291214 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (312874 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (33953 / 3628800 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM8 vector residual: the value of the local truncation error of
the AM8 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am8VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 8 * h) - y (t + 7 * h)
    - h • ((1070017 / 3628800 : ℝ) • deriv y (t + 8 * h)
          + (4467094 / 3628800 : ℝ) • deriv y (t + 7 * h)
          - (4604594 / 3628800 : ℝ) • deriv y (t + 6 * h)
          + (5595358 / 3628800 : ℝ) • deriv y (t + 5 * h)
          - (5033120 / 3628800 : ℝ) • deriv y (t + 4 * h)
          + (3146338 / 3628800 : ℝ) • deriv y (t + 3 * h)
          - (1291214 / 3628800 : ℝ) • deriv y (t + 2 * h)
          + (312874 / 3628800 : ℝ) • deriv y (t + h)
          - (33953 / 3628800 : ℝ) • deriv y t)

theorem am8Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am8VecResidual h t y
      = y (t + 8 * h) - y (t + 7 * h)
          - h • ((1070017 / 3628800 : ℝ) • deriv y (t + 8 * h)
                + (4467094 / 3628800 : ℝ) • deriv y (t + 7 * h)
                - (4604594 / 3628800 : ℝ) • deriv y (t + 6 * h)
                + (5595358 / 3628800 : ℝ) • deriv y (t + 5 * h)
                - (5033120 / 3628800 : ℝ) • deriv y (t + 4 * h)
                + (3146338 / 3628800 : ℝ) • deriv y (t + 3 * h)
                - (1291214 / 3628800 : ℝ) • deriv y (t + 2 * h)
                + (312874 / 3628800 : ℝ) • deriv y (t + h)
                - (33953 / 3628800 : ℝ) • deriv y t) := by
  rfl

/-- Pure module-algebra identity: the AM8 vector residual structure
rewrites to a ten-term abstract split where each chunk is an order-9 (or
order-10) Taylor remainder. -/
private lemma am8Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 d8
        dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd : E) (h : ℝ) :
    y8 - y7
        - h • ((1070017 / 3628800 : ℝ) • d8
              + (4467094 / 3628800 : ℝ) • d7
              - (4604594 / 3628800 : ℝ) • d6
              + (5595358 / 3628800 : ℝ) • d5
              - (5033120 / 3628800 : ℝ) • d4
              + (3146338 / 3628800 : ℝ) • d3
              - (1291214 / 3628800 : ℝ) • d2
              + (312874 / 3628800 : ℝ) • d1
              - (33953 / 3628800 : ℝ) • d0)
      = (y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd)
        - (y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd
            - ((7 * h) ^ 9 / 362880) • ddddddddd)
        - (1070017 * h / 3628800 : ℝ)
            • (d8 - d0 - (8 * h) • dd
                - ((8 * h) ^ 2 / 2) • ddd
                - ((8 * h) ^ 3 / 6) • dddd
                - ((8 * h) ^ 4 / 24) • ddddd
                - ((8 * h) ^ 5 / 120) • dddddd
                - ((8 * h) ^ 6 / 720) • ddddddd
                - ((8 * h) ^ 7 / 5040) • dddddddd
                - ((8 * h) ^ 8 / 40320) • ddddddddd)
        - (4467094 * h / 3628800 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd
                - ((7 * h) ^ 8 / 40320) • ddddddddd)
        + (4604594 * h / 3628800 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd
                - ((6 * h) ^ 8 / 40320) • ddddddddd)
        - (5595358 * h / 3628800 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd
                - ((5 * h) ^ 8 / 40320) • ddddddddd)
        + (5033120 * h / 3628800 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd
                - ((4 * h) ^ 8 / 40320) • ddddddddd)
        - (3146338 * h / 3628800 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd
                - ((3 * h) ^ 8 / 40320) • ddddddddd)
        + (1291214 * h / 3628800 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd
                - ((2 * h) ^ 8 / 40320) • ddddddddd)
        - (312874 * h / 3628800 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd
                - (h ^ 7 / 5040) • dddddddd
                - (h ^ 8 / 40320) • ddddddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

/-- Pure ring identity for the upper bound on the AM8 vector residual.
The exact coefficient `4555920744497/6858432000 ≈ 664.28` is slackened to
`665` in the next helper. -/
private lemma am8Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 3628800 * (8 * h) ^ 10 + M / 3628800 * (7 * h) ^ 10
      + (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
      + (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
      + (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
      + (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
      + (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
      + (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
      + (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
      + (312874 * h / 3628800) * (M / 362880 * h ^ 9)
      = (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 := by
  ring

end LMM
