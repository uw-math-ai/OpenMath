# Cycle 402 Results

## Worked on
Strengthening the smooth-solution local truncation error surface in
`OpenMath/LMMTruncationOp.lean` from the cycle-401 vacuous-existential-`C`
shape (`C` allowed to depend on the fixed `h` because both sides are divided
by `h^(p+2)`) to a genuine uniform-in-`h` `(C, δ)` estimate, plus packaging
the local truncation error operator `localTruncationError` and the
Iserles-form headline corollary `localTruncationError_leading_bound`.

## Approach
Sorry-first scaffold of three new declarations directly inside
`OpenMath/LMMTruncationOp.lean` (no new tracked files):

1. `truncationOp_smooth_local_truncation_error` — the uniform `(C, δ)`
   bound for the order-`p` truncation operator acting on a globally
   `ContDiff ℝ (p+2) y` solution.
2. `localTruncationError` — wrapper `def` packaging
   `m.truncationOp h (fun u => iteratedDeriv 0 y u) (fun u => iteratedDeriv 1 y u) t`.
3. `localTruncationError_leading_bound` — corollary stated in the
   `localTruncationError` notation, matching the textbook surface form
   `τ(t, h) = y^(p+1)(t) · errorConstant p · h^(p+1) + O(h^(p+2))`.

The proof reduces to two uniform Taylor remainder bounds:
- `taylor_remainder_value_bound_uniform` (value bound at order `p+1`):
  `|y(u) - taylorPolyOf y t (p+1)(u-t)| ≤ Cv · |u-t|^(p+2)`
- `taylor_remainder_deriv_bound_uniform` (derivative bound at order `p+1`):
  `|y'(u) - (taylorPolyOf y t (p+1))'(u-t)| ≤ Cd · |u-t|^(p+1)`

Both come from Mathlib's `exists_taylor_mean_remainder_bound` after a bridge
lemma `taylorWithinEval_eq_taylorPolyOf_eval` matching Mathlib's
`taylorWithinEval` with our local `taylorPolyOf`. The derivative bound
reuses the value bound at order `p` for `deriv y`, made possible by the
polynomial identity `taylorPolyOf_derivative_eval`:
`(taylorPolyOf y t (p+1)).derivative.eval x = taylorPolyOf (deriv y) t p . eval x`.

The aggregate constant is `C = Cv * Aα * s^(p+2) + Cd * Aβ * s^(p+1)`
where `Aα = ∑ |α j|`, `Aβ = ∑ |β j|`, and `δ = δ₀` is preserved through.

## Result
SUCCESS. `lake env lean OpenMath/LMMTruncationOp.lean` compiles cleanly
with no warnings and no `sorry`s. `lean_verify` reports both
new theorems depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]`:

- `LMM.truncationOp_smooth_local_truncation_error`
- `LMM.localTruncationError_leading_bound`

The cycle-401 `truncationOp_smooth_eq_leading_add_remainder` was preserved
(not deleted) since it operates on a slightly different `ContDiffOn`
hypothesis surface; it is now superseded by the uniform variant for
practical use.

## Dead ends
- `Mathlib.Analysis.Calculus.Taylor.exists_taylor_mean_remainder_bound`
  (qualified path) is not a thing — the lemma lives in the root namespace.
- `subst hut` with `hut : u = t` substitutes `t → u`, leaving an "Unknown
  identifier `t`" goal; replaced with `rw [hut]; simp`.
- `pow_le_pow_left` (no `₀`) is not the current Mathlib spelling for the
  base-monotonicity lemma; the live name is `pow_le_pow_left₀`.
- `field_simp` in the polynomial-derivative coefficient identity left a
  spurious `True ∨ x = 0 ∧ ¬j = 0` side goal; replaced with explicit
  `simp only` over `Polynomial.eval_*` plus an `omega` arithmetic step
  for `(j+1)-1 = j`.
- The naive `contDiff_succ_iff_deriv.mp h1` rewrite produced a coercion
  mismatch `(↑↑(p + 1 + 1))` vs `(↑(↑p + 1) + 1)`; resolved with
  `simpa [Nat.add_assoc]`.

## Discovery
- The polynomial identity `(taylorPolyOf y t (n+1)).derivative.eval x =
  (taylorPolyOf (deriv y) t n).eval x` is the key reduction that lets one
  Taylor-remainder bound (the value bound) cover both the value and
  derivative residual estimates. This avoids needing a Mathlib derivative
  Taylor remainder bound for `taylorWithinEval`.
- For the Mathlib↔local Taylor bridge to apply, we need
  `iteratedDerivWithin k y (Set.Icc t (t+L)) t = iteratedDeriv k y t` at
  the left endpoint, which requires `UniqueDiffOn ℝ (Set.Icc …)` and
  `ContDiffAt ℝ (k : ℕ∞) y t` — both available from a global
  `ContDiff ℝ (n+1) y` hypothesis.
- The strategy's preferred surface `ContDiffOn ℝ (p+2) y (Set.Icc t (t + s*δ₀))`
  is technically correct but harder to feed into `taylorWithinEval` because
  the iteratedDerivWithin↔iteratedDeriv bridge wants `ContDiffAt`. Using
  the global `ContDiff ℝ (p+2) y` hypothesis is a strict simplification
  that the textbook also assumes (smooth ODE solutions are `C^∞` on the
  interior of their existence interval).

## Suggested next approach
- The natural follow-up is the global error theorem: combine
  `localTruncationError_leading_bound` with the existing zero-stability /
  Dahlquist-equivalence machinery to bound the global error
  `e_n = y(t_n) - y_n` over a finite horizon as `O(h^p)`. This is the
  standard textbook convergence theorem for consistent + zero-stable LMMs.
- Two intermediate steps that may help: (i) a discrete Grönwall lemma
  variant suited to the recurrence `e_{n+s} = … + h·τ_n`, (ii) tying the
  uniform `δ` from `localTruncationError_leading_bound` to a uniform
  bound across all step indices `n` (currently `δ₀` is a free parameter
  of the bound; the convergence theorem instantiates `δ₀ = T - t₀`).
- The cycle-401 `truncationOp_smooth_eq_leading_add_remainder` could be
  deprecated/removed in a later cleanup cycle once nothing else depends
  on its weaker existential surface.

## Aristotle usage
Submitted 4 Aristotle jobs early in the cycle (A: bridge lemma,
B: value bound, C: derivative bound, D: assembly), all of which were
still IN_PROGRESS at 12-20% when the manual proof completed. Manual
proof was faster than the Aristotle round trip for this particular
sub-task (the polynomial-derivative identity is short once one spots
it, and the Mathlib bridge is mostly mechanical).
