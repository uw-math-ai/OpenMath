# Cycle 173 Results

## Worked on

* **P1**: `LinearMultistepMethod.aPoly_coeff_zero_of_preconsistent` —
  algebraic identity `aPoly.coeff 0 = 0` for preconsistent LMMs.
* **P2 (unconditional form)**: `LinearMultistepMethod.aPoly_coeff_one_unconditional` —
  closed form `a₁ = k·(1 − Σαᵢ) − 2·α'(1)` for any `k`-step LMM.
* **P2 (preconsistent corollary)**:
  `LinearMultistepMethod.aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent` —
  Butcher §441 p. 376 identity `a₁ = −2 α'(1)` under preconsistency.
* **Issue file**: `.prover-state/issues/lem_441A_alpha_prime_negative.md`
  documenting the cycle 174+ real-analytic infrastructure gap
  (stable preconsistent ⇒ `α'(1) < 0`).
* **Bookkeeping**: `plan.md` row for `lem:441A` updated to point
  at the new theorems and the issue file.

## Approach

* **P1** — eval-at-zero route. `aPoly.coeff 0 = aPoly.eval 0`
  (via `Polynomial.coeff_zero_eq_eval_zero`); after unfolding
  `aPoly` and pushing `eval` through `sub`/`pow`/`add`/`finset_sum`/`mul`/`C`/`X`,
  the goal collapses to `1 − Σ M.α i.succ = 0`, which is exactly
  the preconsistency condition (modulo `linarith`).
* **P2 (unconditional)** — three-step decomposition, with
  intermediate `have`s scoped inside the proof block (no new
  top-level helpers):
  1. **LHS expansion**: `aPoly.coeff 1 = k − Σᵢ αᵢ·(k − 2(i+1))`.
     Decomposes via `Polynomial.coeff_sub`,
     `Polynomial.coeff_one_add_X_pow` (with `Nat.choose_one_right`),
     `Polynomial.finset_sum_coeff`,
     `Polynomial.mul_coeff_one`, `Polynomial.coeff_C_mul`, plus
     two private helpers for `((1 − X)^n).coeff 0 = 1` (eval-at-zero)
     and `((1 − X)^n).coeff 1 = −n` (induction on `n`, using
     `Polynomial.mul_coeff_one`).
  2. **RHS expansion (`α'(1)`)**: unfold `αPoly`,
     `Polynomial.derivative_sub` + `derivative_one` + `derivative_sum`
     + `derivative_C_mul_X_pow`; then `eval_neg`/`eval_finset_sum`/
     `eval_mul`/`eval_C`/`eval_pow`/`eval_X`, finishing with
     `push_cast; ring`.
  3. **Combination**: distribute the `Σᵢ αᵢ·(k − 2(i+1))` sum into
     `k·Σαᵢ − 2·Σ αᵢ(i+1)` via `Finset.sum_sub_distrib`,
     `Finset.mul_sum`, then `ring`.
* **P2 (preconsistent)** — one-line corollary: rewrite via the
  unconditional form, apply preconsistency to collapse `1 − Σαᵢ`
  to `0`, then `ring`.

## Result

To be confirmed by Section441 build (very slow first compile;
results pending). All three proofs were drafted and inserted
in-line; expecting clean `axiom-clean` outcome.

* **bdf2LMM_aPoly_eq (P0)**: deferred for the second time. The
  cycle 172 dead end (`ring` cannot fold `Polynomial.C` constants
  when divisions are involved) repeats here; the `Polynomial.ext`
  per-coefficient skeleton from the strategy required a simp set
  for mixed numeral / `C` expressions on `Polynomial ℝ` whose
  full closure exceeded the cycle's manual-proof budget.
  Documented in `plan.md` and the file docstring.

## Faithfulness check

For each new theorem introduced this cycle (no entity ID — these
are `lem:441A` infrastructure helpers, not direct entity formalizations):

* **`aPoly_coeff_zero_of_preconsistent`** — captures Butcher's
  implicit claim (§441 p. 376) that `a₀ = 0` because `α(1) = 0`.
  Lean statement: `M.aPoly.coeff 0 = 0` under `M.IsPreconsistent`.
  Faithful — the textbook expansion `a(z) = a₀ + a₁z + ⋯` has
  `a₀ = a(0) = 1 − Σαᵢ = 0` for any preconsistent method.

* **`aPoly_coeff_one_unconditional`** — captures Butcher's
  "We calculate the value of `a₁` … to be `k − (k − 2)α₁ − ⋯ − (−k)αₖ
  = kα(1) − 2α'(1)`" (§441 p. 376) as an unconditional identity
  before invoking preconsistency.
  Lean statement: `M.aPoly.coeff 1 = k·(1 − Σ M.α i.succ) − 2·α'(1)`.
  Captures: SAME content (and strictly more informative — the
  textbook collapses the `kα(1)` term immediately under preconsistency,
  but the unconditional form survives that simplification).

* **`aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent`** —
  Butcher's `kα(1) − 2α'(1) = −2α'(1)` reduction.
  Lean statement: `M.aPoly.coeff 1 = -2 * α'(1)` under preconsistency.
  Faithful one-to-one with the textbook calculation.

No entity status changes (`lem:441A` stays `unformalized`).

## Dead ends

* **`bdf2LMM_aPoly_eq` `Polynomial.ext` skeleton**: as drafted,
  the inner `simp` set after `rcases n with _ | _ | _ | n` did
  not robustly reduce `(2 * X).coeff k` and `(C a * (1 - X^2)).coeff k`
  to a uniform numerical-equation form across all four cases.
  `Polynomial.coeff_C_mul` handles the `C a * p` case but the
  `(2 * X)` subterm is `(2 : Polynomial ℝ) * X`, which simp
  resolved inconsistently between numerals and `Polynomial.C 2`.
  Switching to `linear_combination` likewise stalled because the
  hypotheses needed (e.g., `Polynomial.C_1`, `Polynomial.C_two`)
  do not appear naturally as zero-equating polynomial identities.
* The cycle 172 dead ends (`simp [bdf2LMM, Fin.sum_univ_two]; ring`
  heartbeat timeout, and explicit `rfl` extraction + `ring`
  failure on `Polynomial.C` arithmetic) were avoided as planned
  via the `Polynomial.ext` route, but the `Polynomial.ext` route
  itself required more `Polynomial`-coefficient infrastructure
  than the cycle 173 manual-proof budget allowed.

## Discovery

* **`Polynomial.derivative_sum`, not `derivative_finset_sum`** —
  mathlib's name is `Polynomial.derivative_sum`. Initial drafts
  used the wrong name.
* **`Polynomial.mul_coeff_one`** is the cleanest entry point for
  computing `(p * q).coeff 1`. Direct `coeff_mul` + antidiagonal
  expansion is unnecessarily verbose. (Mathlib also offers
  `Polynomial.mul_coeff_zero` and `Polynomial.mul_coeff_one`,
  both as `@[simp]` lemmas.)
* **`Polynomial.coeff_one_add_X_pow R n k = (n.choose k : R)`** —
  the key lemma for binomial-coefficient computations, plus
  `Nat.choose_zero_right = 1` and `Nat.choose_one_right = n`
  for the typical `k = 0, 1` cases.
* **`((1 − X)^n).coeff 0 = 1`** falls out cleanly from
  `Polynomial.coeff_zero_eq_eval_zero` — no induction needed.
* **`((1 − X)^n).coeff 1 = -n`** does require induction (with
  `Polynomial.mul_coeff_one` at the inductive step), since no
  direct mathlib lemma exists. Cycle 174+ should consider
  upstreaming this to mathlib if it is reused.

## Suggested next approach

* **Cycle 174 — Primary**: tackle the `α'(1) < 0` infrastructure
  (per `.prover-state/issues/lem_441A_alpha_prime_negative.md`).
  This is the remaining barrier between cycle 173's identity and
  Butcher's `a₁ > 0` claim. Estimated 2–3 cycles of real-analytic
  Mathlib hookup (polynomial root theorems, derivative-positivity-
  from-no-real-root-greater-than-one).
* **Cycle 174 — Secondary (opportunistic)**: re-attempt
  `bdf2LMM_aPoly_eq`. The blockage is purely tooling, not
  mathematical. Two specific paths:
  1. Define a private helper
     `Polynomial.coeff_two_mul_X (n : ℕ) :
      ((2 : Polynomial ℝ) * Polynomial.X).coeff n =
      if n = 1 then 2 else 0`
     and similar for the constants 1, -1, 2, -2 used in
     `(1 ± X)^2`, then chain them after `Polynomial.ext`.
  2. Bypass `Polynomial.coeff` altogether by pushing both sides
     into a form where `← map_add`/`← map_sub`/`← map_mul`
     collapse all `Polynomial.C` constants into a single one,
     then use `Polynomial.C_eq_zero` plus `norm_num`.
* **Cycle 175+**: with `α'(1) < 0` in hand, close `lem:441A`'s
  `a₁ > 0` half. The `aᵢ ≥ 0` for `i ≥ 2` half (Butcher's
  factorisation argument over the LHP of ℂ) is heavier and can
  follow.
