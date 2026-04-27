# Cycle 468 Results

## Worked on
Mechanical port of AB8 residual + bridge + headline machinery to AB9 in
`OpenMath/LMMAB9Convergence.lean`. Sections A through I:
- A: `ab9_residual_alg_identity` — algebraic decomposition of the AB9 LTE
  into 2 y-Taylor remainders (order 10) plus 8 y'-Taylor remainders
  (order 9), proved by `ring`.
- B: `ab9_residual_bound_alg_identity` — sum of scaled Lagrange remainder
  bounds equals `(102509448755347 / 20575296000) * M * h^10`, proved by
  `ring`.
- C: `ab9_triangle_aux` (10 abstract args) and `ab9_residual_ten_term_triangle`
  — chained triangle inequality with 10 letters A..J.
- D: `ab9_pointwise_residual_bound` — bound `≤ 4983 * M * h^10`.
- E: `ab9_local_residual_bound` — `O(h^10)` residual bound on a finite
  horizon.
- F: `ab9GenericCoeff : Fin 9 → ℝ` plus 9 simp lemmas and
  `abLip_ab9GenericCoeff = (2231497 / 14175) * L`. Helper
  `sum_univ_nine_aux` introduced because Mathlib lacks `Fin.sum_univ_nine`.
- G: `ab9Iter_eq_abIter` — strong-induction bridge.
- H: `ab9Residual_eq_abResidual` — bridge connecting concrete AB9 residual
  to the generic scaffold residual.
- I: `ab9_global_error_bound` — headline `O(ε₀ + h^9)` global error bound.

## Approach
Mirrored AB8 verbatim, with two added derivative letters (`d8`,
`ddddddddd`) and one extra Taylor-remainder slot. Verified the key
constants (`102509448755347/20575296000` and `2231497/14175`) symbolically
before committing.

## Result
SUCCESS — file compiles cleanly with no `sorry`, no warnings, and no
heartbeat increases above the 200000 default.

## Dead ends
- The kernel was timing out at `whnf` while typechecking the proof of
  `ab9_pointwise_residual_bound` whenever any non-trivial `have`
  statement (in particular the intermediate `linarith` step combining the
  10 scaled Taylor remainders) was introduced inline. The timeout was
  reproducible even when the body was replaced with `sorry` — what
  triggered it was the *type* of any new local `have` referencing the
  10 abstract Taylor remainders in scope.
- Several attempts to keep things inline failed:
  - Big single-shot `linarith` on htri + 10 bounds: timeout.
  - Chained intermediate `have`s with abstract `bA..bJ`: timeout.
  - Pure `calc` chain (AB8 style): also timed out at AB9 scale.
  The AB8 file works because at order 9 the kernel can still whnf the
  10-summand goal; AB9 has 11 summands plus an extra `(9 * h)^10`
  remainder, which seems to push past the budget.

## Discovery
Factoring all post-`clear_value` work into a private lemma
`ab9_residual_combine_aux` taking `A,B,…,J,M,h` and the ten Taylor-bound
hypotheses as arguments, with the entire combination proof confined
inside that lemma, restored a fast kernel typecheck. The body of
`ab9_pointwise_residual_bound` then ends with a clean `exact
ab9_residual_combine_aux …`, so the kernel never sees the giant combined
proof term in the same context as the `set`/`clear_value` machinery.

This pattern is reusable for the (presumed) AB10 port.

## Suggested next approach
- AB10 will likely face the same kernel `whnf` budget issue at even
  larger scale; preempt it by structuring the combine lemma the same way
  from the start.
- Continue with BDF/AM10 truncation and convergence chains as planned.
