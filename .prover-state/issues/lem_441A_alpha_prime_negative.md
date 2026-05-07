# Issue: `α'(1) < 0` for stable preconsistent LMMs (cycle 174+)

## Blocker

`lem:441A`'s `a₁ > 0` claim reduces, via cycle 173's
`aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent`, to:

  for stable preconsistent M, `α'(1) < 0`.

Equivalently (Butcher §441 p. 376), `ρ'(1) > 0` where
`ρ(z) := z^k · α(1/z) = z^k - α₁z^{k-1} - ⋯ - αₖ`.

## Why this is non-trivial

The textbook argument (p. 376):
1. Stability ⇒ all roots of ρ are in the closed unit disc, with
   simple roots on |z| = 1.
2. Preconsistency ⇒ ρ(1) = 0; combined with (1), z = 1 is a simple
   root of ρ.
3. Real-axis analysis: ρ has no real zero > 1 (by stability),
   ρ(1) = 0, ρ(z) → +∞ as z → +∞ (leading coefficient 1), so
   ρ'(1) > 0 by IVT-style sign analysis.

Step (3) requires:
* The leading-coefficient-positive convention on ρ.
* A real-analytic ε-argument: ρ(1+ε) > 0 for small ε > 0 (else ρ
  would have a zero in (1, 1+ε)), so by L'Hôpital ρ'(1) ≥ 0; the
  simple-root condition strengthens to >.

## Mathlib hooks

* `Polynomial.IsRoot` and `Polynomial.derivative_eval`.
* `Polynomial.derivative_pos_of_isRoot_of_no_root_gt_one` —
  if such a lemma exists. Verify with `lean_local_search`.
* The simple-root condition may need `Polynomial.rootMultiplicity_eq_one`
  or similar.

Estimated cost: 2–3 cycles for the real-analytic infrastructure,
then 1 cycle to combine with cycle 173's identity to close
`lem:441A`'s `a₁ > 0` half.

## Cross-reference

* `OpenMath/Chapter4/Section441.lean::aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent`
  — cycle 173 algebraic identity.
* `OpenMath/Chapter4/Section441.lean::ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`
  — cycle 174 algebraic bridge (`ρ'(1) = −α'(1)` under preconsistency).
* `OpenMath/Chapter4/Section441.lean::aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
  — cycle 174 headline corollary (`a₁ = 2·ρ'(1)` under preconsistency).
* `extraction/formalization_data/entities/lem_441A.json` — textbook
  statement.
* `.prover-state/issues/lem_441B_misinterpretation.md` — sibling
  issue documenting the §441 cluster's interpretation pitfalls.

## Cycle 174 update

The algebraic bridge `α'(1) < 0 ⇔ ρ'(1) > 0` (under preconsistency)
is now formalised: cycle 174's
`aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` reduces
the `lem:441A` `a₁ > 0` half to the polynomial-root claim

  for stable preconsistent M, `M.ρPoly.derivative.eval 1 > 0`.

Future cycles should target the **ρ-side** claim, NOT the α-side.
The textbook argument (Butcher §441 p. 376) runs through ρ:

1. Leading coefficient of ρ is `1` (positive) — direct from
   `LinearMultistepMethod.ρPoly = X^k - Σᵢ C(αᵢ) X^(k-(i+1))`.
2. ρ(1) = 0 — already formalised as `ρPoly_eval_one_eq_zero_of_preconsistent`.
3. ρ has no real root > 1 — to be proved. This is the substantive
   real-analytic step: stability ⇒ closed-unit-disc roots ⇒ no real
   root > 1; combined with `ρ(z) → +∞` as `z → +∞`, gives
   `ρ(1+ε) > 0` for small ε > 0, hence `ρ'(1) ≥ 0`.
4. Simple-root strengthening: stability's "simple roots on |z| = 1"
   condition + ρ(1) = 0 ⇒ rootMultiplicity 1 = 1, hence ρ'(1) ≠ 0,
   strengthening (3) to `ρ'(1) > 0`.

This chain is cleaner than the α-side analogue (where the
leading-coefficient-positive convention is on `−α(z)`, the
"no real root > 1" becomes "no real root in (0, 1)" for α, and
the real-analytic argument is structurally identical but uses a
different sign convention). The ρ-side route is the textbook's
canonical argument and should be followed in cycles 175+.
