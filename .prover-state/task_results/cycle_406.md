# Cycle 406 Results

## Worked on
Forward-Euler scalar convergence chain in `OpenMath/LMMTruncationOp.lean`.
Built the missing one-step error recurrence interface that feeds
`lmm_error_bound_from_local_truncation`, instantiated at `s = 1` (forward
Euler) for a Lipschitz scalar ODE with a `C^3` exact solution, and
assembled the textbook `O(h)` global error theorem.

## Approach
Followed the sorry-first / Aristotle-first workflow exactly.

1. Appended the five-step scaffold to the end of
   `OpenMath/LMMTruncationOp.lean`:
   `forwardEulerIter`, `forwardEuler_localTruncationError_eq`,
   `forwardEuler_one_step_error_bound`,
   `forwardEuler_local_residual_bound`,
   `forwardEuler_global_error_bound`. The first three were closed
   manually before submitting Aristotle; the last two carried `sorry`.
2. Verified the scaffold compiled with the standard
   `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
   OpenMath/LMMTruncationOp.lean` (warnings only on the two scaffold
   sorries).
3. Submitted a five-job Aristotle batch and slept via `sleep 1800`
   before one refresh pass. Two of the five (the headline residual /
   global bounds) had not finished by the 30-min wait window and were
   later canceled; the three completed helper bundles (Job C uniform
   second-derivative bound on `[a, b]`, Job D pointwise Lagrange
   remainder, Job E residual = local truncation bridge) supplied the
   ingredients to close both remaining sorries manually.
4. Transplanted Job C and Job D as private helpers
   `iteratedDeriv_two_bounded_on_Icc` and
   `forwardEuler_pointwise_residual_bound` inside
   `OpenMath/LMMTruncationOp.lean` (sorry-free, dropped the unused
   third-derivative variant from Job C since the residual proof only
   needs `|y''|`). Job E was redundant with the manually proved
   `forwardEuler_localTruncationError_eq` and was not transplanted.
5. Closed `forwardEuler_local_residual_bound` by picking the compact
   sample interval `[t₀, t₀ + T + 1]`, extracting `M ≥ |y''|` via the
   Job C helper, restricting `h ≤ 1`, and applying the Job D pointwise
   Lagrange remainder. Constants: `(C, δ) = (M/2, 1)`.
6. Closed `forwardEuler_global_error_bound` by combining
   `forwardEuler_one_step_error_bound` (with the `deriv y = f(·, y)`
   bridge) and `forwardEuler_local_residual_bound` to instantiate the
   recurrence consumed by `lmm_error_bound_from_local_truncation` at
   `p = 1`, with the initial-error term vanishing because
   `forwardEulerIter h f t₀ y₀ 0 = y₀ = y t₀`.

## Statement signatures committed

```lean
noncomputable def LMM.forwardEulerIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) : ℕ → ℝ

theorem LMM.forwardEuler_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    forwardEuler.localTruncationError h t y
      = y (t + h) - y t - h * deriv y t

theorem LMM.forwardEuler_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ : ℝ) (y : ℝ → ℝ) (n : ℕ) :
    |forwardEulerIter h f t₀ y₀ (n + 1)
        - y (t₀ + ((n : ℝ) + 1) * h)|
      ≤ (1 + h * L)
          * |forwardEulerIter h f t₀ y₀ n - y (t₀ + (n : ℝ) * h)|
        + |y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
            - h * f (t₀ + (n : ℝ) * h) (y (t₀ + (n : ℝ) * h))|

theorem LMM.forwardEuler_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        t₀ + (n : ℝ) * h ∈ Set.Icc t₀ (t₀ + T) →
        |y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
            - h * deriv y (t₀ + (n : ℝ) * h)|
          ≤ C * h ^ 2

theorem LMM.forwardEuler_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ N : ℕ, (N : ℝ) * h ≤ T →
        |forwardEulerIter h f t₀ (y t₀) N - y (t₀ + (N : ℝ) * h)|
          ≤ K * h
```

The constant assembled in the global theorem is `T * exp(L T) * C` where
`C = M/2` and `M` is any uniform bound on `|y''|` over `[t₀, t₀ + T + 1]`.

## Sorry status
- (1) `forwardEulerIter` — sorry-free by construction.
- (2) `forwardEuler_localTruncationError_eq` — sorry-free.
- (3) `forwardEuler_one_step_error_bound` — sorry-free.
- (4) `forwardEuler_local_residual_bound` — sorry-free.
- (5) `forwardEuler_global_error_bound` — sorry-free.

`OpenMath/LMMTruncationOp.lean` is sorry-free. `lake build
OpenMath.LMMTruncationOp` succeeds (8028 jobs).

## Aristotle bundles

Submitted five jobs after the manually closed first three theorems were
in place. Three of five completed within the 30-min wait window:

- `774d265a-cd38-4f59-abec-183c97f0a250`
  (`cycle406_iteratedDeriv_two_bounded_on_Icc`,
  `cycle406_iteratedDeriv_three_bounded_on_Icc`): COMPLETE.
  Accepted; transplanted the `iteratedDeriv 2` half as a private helper
  `iteratedDeriv_two_bounded_on_Icc` (with `max M 0` clamp). The
  `iteratedDeriv 3` variant was not needed by the residual bound and was
  not transplanted.
- `58097f0f-c0c6-4831-8e8f-b3997b8414e7`
  (`cycle406_forwardEuler_pointwise_residual_bound`): COMPLETE.
  Accepted; transplanted as the private helper
  `forwardEuler_pointwise_residual_bound`. The proof uses
  `taylor_mean_remainder_lagrange_iteratedDeriv`, `taylorWithinEval_succ`,
  `taylorWithinEval_self`, `derivWithin`, `fderivWithin_eq_fderiv`,
  `uniqueDiffOn_Icc` and a final `nlinarith`. The bound case-splits on
  `h = 0` then extracts the Lagrange residual point `x' ∈ (t, t+h)`.
- `0f08371d-008c-4d2d-9a4c-f43ead30a57a`
  (`cycle406_forwardEuler_residual_eq_localTruncation`): COMPLETE.
  Accepted as a sanity check that `forwardEuler_localTruncationError_eq`
  is in the expected direction. Not transplanted because the symmetric
  rewrite is already available.
- `39acffd3-21e8-4b43-8c00-2a59a3143a54`
  (`cycle406_forwardEuler_local_residual_bound`): IN_PROGRESS at 24% at
  the 30-min mark; canceled because the manual proof using bundle
  `774d265a` + bundle `58097f0f` was already in place.
- `34c8f322-a408-451d-82e4-0e14b42bd23c`
  (`cycle406_forwardEuler_global_error_bound`): IN_PROGRESS at 11% at
  the 30-min mark; canceled because the manual `lmm_error_bound_from_
  local_truncation` assembly was already in place.

No bundle rebuilt `LMM`, `truncationOp`, `localTruncationError`,
`forwardEuler`, `lmm_error_bound_from_local_truncation`, or
`forwardEulerIter`. No bundle introduced a tracked `sorry` in a helper
imported by the live file.

## Result
SUCCESS. All five scaffold theorems committed sorry-free; the cycle 406
target (steps 1–3) and the bonus targets (steps 4–5) are all closed.
`plan.md` §1.2 records the new chain under
"Forward-Euler scalar convergence chain".

## Dead ends
None. The original strategy worried that step (4) might require uniform-
in-`t` Taylor remainder bounds rederived from
`localTruncationError_leading_bound` (which is fixed-`t`). The cleaner
path turned out to be: prove a uniform `|y''|` bound on a compact
interval, then apply `taylor_mean_remainder_lagrange_iteratedDeriv`
pointwise and pull the constant `M/2` out of the sample range. This
avoids re-running the multi-page truncation-operator bridge with a
roving anchor.

## Discovery
- `taylor_mean_remainder_lagrange_iteratedDeriv` is the right Mathlib
  lemma for the textbook Lagrange Taylor remainder; it returns an
  intermediate point `x' ∈ Set.Ioo t (t + h)`. The proof body shipped
  by Aristotle (Job D) is short enough to drop in verbatim once the
  uniform `|y''| ≤ M` hypothesis is in scope.
- For step (5), the cleanest assembly is to align the LHS of
  `forwardEuler_one_step_error_bound`
  (`((n : ℝ) + 1) * h`) with the LMM-Gronwall form
  (`((n + 1 : ℕ) : ℝ) * h`) by a single `push_cast; ring` rewrite. The
  initial-error term cancels because `forwardEulerIter h f t₀ y₀ 0 = y₀`
  by `forwardEulerIter_zero` and `(0 : ℕ) * h = 0`.
- `add_le_add_left`/`add_le_add_right` in this Mathlib pin elaborate in
  unexpected directions for these inequalities; both fights with
  `linarith` cleanly via the `[hcomb, h_alg]` pattern. Recorded as a
  small reusable trick.

## Suggested next approach
The §1.2 LMM convergence chain now has both the forcing-side (uniform
local truncation) and consumer-side (forward-Euler scalar convergence)
endpoints. The natural cycle 407 frontier is the general
`s ≥ 2` companion-matrix Lipschitz step that the strategy explicitly
reserved: combine
`uniformly_bounded_tupleSucc_iterates` from `SpectralBound.lean` with
`localTruncationError_leading_bound` plus a Lipschitz `f` to derive
`e (n+1) ≤ (1 + h*L) * e n + C * h^(p+1)` for a general zero-stable
order-`p` LMM acting on a `C^(p+2)` solution.

A smaller, lower-risk cycle 407 alternative is to lift
`forwardEuler_global_error_bound` from scalar `f : ℝ → ℝ → ℝ` to
vector-valued `f : ℝ → E → E` with `E` a finite-dimensional normed
space, since the same Lipschitz / Lagrange ingredients work coordinate-
wise. This is a useful warm-up for the multistep companion-matrix step.
