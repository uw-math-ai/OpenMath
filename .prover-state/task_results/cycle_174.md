# Cycle 174 Results

## Worked on

`lem:441A` ρ-polynomial bridge (Phase B). Added `ρPoly` definition
and structural/derivative lemmas to
`OpenMath/Chapter4/Section441.lean`, plus the headline corollary
`a₁ = 2·ρ'(1)` (under preconsistency), and a non-vacuity witness
for explicit Euler.

## Approach

Followed the cycle 174 strategy verbatim:

1. **Priority 1** — Added `LinearMultistepMethod.ρPoly` definition,
   `ρPoly_eval_one`, `ρPoly_eval_one_eq_zero_of_preconsistent`, and
   `ρPoly_natDegree_le`. Proofs follow the same tactic shapes as
   cycle 172's `aPoly_natDegree_le` (`Polynomial.natDegree_sub_le`
   + `Polynomial.natDegree_pow_le` + sum-of-monomials bound).

2. **Priority 2** — Added `ρPoly_deriv_eval_one_unconditional`,
   `ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`
   (the algebraic bridge `ρ'(1) = −α'(1)` under preconsistency),
   and the headline corollary
   `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
   (`a₁ = 2·ρ'(1)` under preconsistency). The derivative computation
   uses `Polynomial.derivative_X_pow`, `Polynomial.derivative_sum`,
   `Polynomial.derivative_C_mul_X_pow` (verified to exist by reuse
   from cycle 173) followed by `push_cast [Nat.cast_sub hile]; ring`.
   The bridge reuses the cycle 173 αPoly derivative computation
   inline (per the strategy's note that Priority 6 stretch
   extraction is "nice-to-have").

3. **Priority 3** — Added `explicitEulerLMM_ρPoly_eq` (non-vacuity
   witness `ρ = X − 1` for `k = 1`).

4. **Priority 4** — Updated `plan.md` `lem:441A` entry to reflect
   the new bridge, and appended a "Cycle 174 update" section to
   `.prover-state/issues/lem_441A_alpha_prime_negative.md` redirecting
   future cycles to the ρ-side claim.

5. **Aristotle policy** — Did NOT submit (per strategy "Aristotle
   policy" section: proofs short, mathlib chains tractable manually,
   cycle 173 already noted manual closure was faster).

## Result

SUCCESS. All seven new declarations type-check and the file compiles
clean (`lake env lean OpenMath/Chapter4/Section441.lean` exits 0,
no diagnostics). Sorry count remains 0. Tautology-scanner regex
returns no hits over the new declarations.

Two minor in-cycle adjustments to the strategy templates:

* In `ρPoly_eval_one`: the strategy's `rw [show (1 : ℝ) ^ ... = 1
  from one_pow _]; ring` step was redundant because the `simp only`
  already absorbed `one_pow`; goal at that point was `M.α i.succ *
  1 = M.α i.succ`. Replaced with `mul_one` lemma in the `simp only`
  set; the `congr 1` + `Finset.sum_congr rfl + intros + rw + ring`
  chain collapses to a single `simp only` call.

* In `explicitEulerLMM_ρPoly_eq`: the strategy template ended with
  `simp [explicitEulerLMM]; ring`, but the `simp` already closes
  the goal — the final `ring` triggered a "No goals" error. Removed
  the `ring`.

Both adjustments are simp/ring tuning; no semantic changes.

## Faithfulness check

For each new `def`/`theorem`:

### `LinearMultistepMethod.ρPoly` (def)

Entity: implicit (Butcher §441 p. 375 introduces `ρ(z) = z^k −
α₁z^{k-1} − ⋯ − αₖ` as part of the proof of `lem:441A`). Quoted
from `extraction/formalization_data/entities/lem_441A.json`
(`proof_text`):

> The polynomial ρ, which we recall is defined by
> ρ(z) = z^k − α₁ z^{k-1} − α₂ z^{k-2} − ⋯ − αₖ,

Lean statement captures: same content. The `Fin k`-indexed sum
`Σ Polynomial.C (M.α i.succ) * X^(k − (i+1))` matches Butcher's
`α₁ z^{k-1} + ⋯ + αₖ z^0` term-by-term: at `i.val = 0` we get
`α₁ · z^(k-1)`, at `i.val = k-1` we get `αₖ · z^0`. The sign
convention matches Butcher (subtraction). The `M.α 0 = -1`
normalisation factor is *not* used in `ρPoly`; only `M.α i.succ`
for `i : Fin k` enters, which is the textbook `α₁, …, αₖ` directly.

### `LinearMultistepMethod.ρPoly_eval_one` (theorem)

Sanity helper. No textbook entity. Statement: `ρ(1) = 1 − Σ αᵢ`,
which follows directly from the definition by setting `z = 1`.

### `LinearMultistepMethod.ρPoly_eval_one_eq_zero_of_preconsistent` (theorem)

Captures Butcher's "ρ(1) = 0" (p. 376):

> ... because ρ(1) = 0 and because limz→∞ ρ(z) = ∞, it is necessary
> that ρ'(1) > 0.

Lean statement captures: same content. Hypothesis is the same
preconsistency condition that Butcher implicitly uses (preconsistency
⇔ `α(1) = 0` ⇔ `ρ(1) = 0`).

### `LinearMultistepMethod.ρPoly_natDegree_le` (theorem)

Structural sanity. `ρ` has degree at most `k` since it is
`z^k − Σ αᵢ z^(k−(i+1))` with each summand having degree `k −
(i+1) ≤ k`.

### `LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional` (theorem)

Quoted (Butcher §441 p. 376, `proof_text`):

> Calculate this to be ρ'(1) = k − (k-1)α₁ − (k-2)α₂ − ⋯ − αₖ₋₁ = a₁.

The Lean statement `ρ'(1) = k − Σᵢ αᵢ · (k − (i+1))` matches
this expansion exactly: at `i.val = 0` we get `α₁ · (k−1)`, at
`i.val = k−2` we get `αₖ₋₁ · 1`, at `i.val = k−1` we get `αₖ · 0`
(consistent with Butcher's expansion ending at αₖ₋₁ — the αₖ term
formally vanishes). This is the *unconditional* form (no
preconsistency assumed).

### `LinearMultistepMethod.ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent` (theorem)

The algebraic bridge `ρ'(1) = −α'(1)` under preconsistency. Quoted
(Butcher §441 p. 376):

> We calculate the value of a₁, the coefficient of z, to be
> k − (k-2)α₁ − (k-4)α₂ − ⋯ − (-k)αₖ = kα(1) − 2α'(1) = −2α'(1)

Combined with the previous theorem's `ρ'(1) = k − Σ αᵢ(k−(i+1))`,
this gives `ρ'(1) = −α'(1)` as a corollary of `kα(1) = k − k·Σαᵢ
= 0` under preconsistency. Lean statement captures: same content
under preconsistency.

### `LinearMultistepMethod.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` (theorem)

Headline corollary `a₁ = 2·ρ'(1)`. Combines cycle 173's
`a₁ = −2·α'(1)` with cycle 174's `α'(1) = −ρ'(1)` to give
`a₁ = −2·(−ρ'(1)) = 2·ρ'(1)`. Quoted (Butcher §441 p. 376):

> ρ'(1) = k − (k-1)α₁ − (k-2)α₂ − ⋯ − αₖ₋₁ = a₁

(the textbook actually writes the identity as `a₁ = ρ'(1)`, but
that is in Butcher's normalisation where `a₁` is the *coefficient*
without the factor 2. Our `aPoly` matches Butcher's polynomial
directly, so the factor `2` appears naturally — i.e. the textbook's
"ρ'(1) = a₁" is mod a normalisation; the algebraic identity Lean
proves is `a₁ = 2·ρ'(1)`, which is consistent with Butcher's
parallel computation `a₁ = −2α'(1)` and `α'(1) = −ρ'(1)`.)

Wait — re-reading: the textbook's `a₁ = ρ'(1)` appears AFTER
"Calculate this to be ... = a₁", which is Butcher asserting
*equality*, not "up to a factor 2". The discrepancy is real and
deserves a note: Butcher's `a₁` formula is

> a₁ = k − (k-2)α₁ − (k-4)α₂ − ⋯ − (-k)αₖ

while ρ'(1) is

> ρ'(1) = k − (k-1)α₁ − (k-2)α₂ − ⋯ − αₖ₋₁

These are **different** linear combinations. Butcher's text claim
"= a₁" must be reinterpreted — the textbook's equality is unlikely
to hold verbatim. Our cycle 173 lemma proves `a₁ = −2α'(1)` under
preconsistency, and cycle 174 proves `ρ'(1) = −α'(1)` under
preconsistency, so `a₁ = 2·ρ'(1)`. Butcher's claim that "`a₁ =
ρ'(1)` directly" appears to omit the factor 2, but this is a
textbook discrepancy, not a Lean-side error: the algebraic chain
through α'(1) is unambiguous and our identity is correct under
preconsistency.

This is a discovery worth flagging for cycle 175+ planning: the
final `lem:441A` `a₁ > 0` claim follows from `ρ'(1) > 0` (factor
of 2 is positive), so the textbook's slight discrepancy doesn't
affect the final lemma — but the polynomial-root infrastructure
should target `ρ'(1) > 0`, not `a₁ = ρ'(1)`.

### `Section441.explicitEulerLMM_ρPoly_eq` (theorem)

Non-vacuity witness. For explicit Euler (`k = 1`, `α₁ = 1`):
`ρ(z) = z^1 − α₁ · z^0 = z − 1`. Lean statement captures: same
content. Sanity check that the `ρPoly` formula matches Butcher's
characteristic polynomial on the smallest non-trivial example.

## Tautology check

None of the new theorems' conclusions appear verbatim as
hypotheses. All new theorems are derivative computations or
algebraic bridges; `ρPoly_eval_one_eq_zero_of_preconsistent` and
`ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`
take `M.IsPreconsistent` (= `1 = Σ αᵢ`) as hypothesis but conclude
about `ρPoly.eval 1` and `ρPoly.derivative.eval 1` respectively,
which are different propositions.

## Identity check

None of the proofs is `exact h` alone; all chain through `rw` +
`linarith` / `ring` / nontrivial computations.

## Hypothesis strength check

All hypotheses match the textbook (`M.IsPreconsistent`,
or no hypothesis for unconditional forms).

## Definition smuggling check

`ρPoly` is defined by its *primary* mathematical formula
`X^k − Σ αᵢ X^(k−(i+1))`, NOT by any property of its derivative
or roots. The structural lemmas (`ρPoly_eval_one`, etc.) are
genuine consequences of the definition, not characterisations
disguised as definitions.

## Dead ends

* The strategy template's `rw [show (1 : ℝ) ^ ... = 1 from one_pow _]`
  in `ρPoly_eval_one` was redundant after the `simp only` set
  already absorbed `one_pow`. Replaced with `mul_one` in the simp
  set; the `congr` + `sum_congr` + `intros` + `rw` + `ring` chain
  collapses to a single `simp only` call.

* The strategy template's trailing `ring` in `explicitEulerLMM_ρPoly_eq`
  triggered "No goals" because `simp [explicitEulerLMM]` closes the
  goal directly. Removed the `ring`.

## Discovery

* The textbook's "ρ'(1) = a₁" claim (Butcher §441 p. 376, line
  "Calculate this to be ρ'(1) = ... = a₁") is *not* the literal
  algebraic identity — Butcher's `a₁` formula has coefficient
  `k − 2(i+1)` on `αᵢ` while ρ'(1) has coefficient `k − (i+1)`,
  off by a factor 2 in the linear combination. The correct
  algebraic bridge under preconsistency is `a₁ = 2·ρ'(1)`, which
  cycle 174 formalises as
  `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`.
  This factor 2 doesn't affect `lem:441A`'s `a₁ > 0` conclusion
  (still equivalent to `ρ'(1) > 0`), but is worth noting for any
  future textbook-faithful tracing.

* The `Polynomial.derivative_C_mul_X_pow` lemma works in the form
  `(C a * X^n).derivative = C (a * n) * X^(n-1)`, which collapses
  cleanly to `0` at `n = 0` (since `C 0 = 0`) — no edge case
  splitting needed in `ρPoly_deriv_eval_one_unconditional`.

* The unified `Σᵢ αᵢ · (k − (i+1))` form in
  `ρPoly_deriv_eval_one_unconditional` works because the natural-
  number subtraction `k - (i+1)` is `0` exactly when `i.val + 1 = k`,
  and after `Nat.cast_sub i.isLt` it becomes a real-valued subtraction
  that `ring` handles uniformly.

## Suggested next approach

For cycle 175:

1. **Polynomial-root infrastructure for `ρ'(1) > 0`**. The
   substantive multi-cycle work begins now. Three sub-claims:
   * `ρ` has positive leading coefficient (immediate from
     `ρPoly_natDegree_le` plus a `Polynomial.coeff M.ρPoly k = 1`
     lemma).
   * `ρ` has no real zero > 1 — requires Mathlib's
     `Polynomial.IsRoot` machinery + a stability hypothesis
     translated into "all roots in closed unit disc" (where
     `Polynomial.aroots` is a `Multiset ℂ`; the real-axis case
     is a sub-multiset).
   * `ρ(1+ε) > 0` for small ε > 0 by continuity + ρ(1) = 0 +
     no root in (1, 1+ε); hence `ρ'(1) ≥ 0` by L'Hôpital /
     limit-of-difference-quotient. Strengthen to `> 0` via
     simple-root condition.

2. **Cycle 175 should plan whether to tackle this directly or
   stage** the work via:
   a. Sorry-first scaffold: state `ρPoly_no_real_root_gt_one` and
      `ρPoly_deriv_eval_one_pos_of_isStable_of_isPreconsistent` as
      sorry, prove the headline `lem:441A_a_one_pos` from them, and
      iterate on the sorries.
   b. Direct attack via Mathlib polynomial-root tools.
   c. Chunk over 2–3 cycles, each addressing one sub-claim.

3. **Skip the BDF2 closed-form witness `bdf2LMM_aPoly_eq`** — has
   stalled twice (cycles 172, 173) on `Polynomial.C` arithmetic in
   `ring` normal form. Defer until a `Polynomial`-coefficient
   helper file is designed (probably cycle 176+).

4. **Stretch goal for cycle 175**: extract
   `αPoly_deriv_eval_one` from inside `aPoly_coeff_one_unconditional`
   (and from cycle 174's
   `ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`)
   to `Section410.lean`, removing ~25 LOC of duplication. This was
   the cycle 174 stretch goal; deferred this cycle because the
   primary work consumed time. Should be done before any further
   §441 derivative work.
