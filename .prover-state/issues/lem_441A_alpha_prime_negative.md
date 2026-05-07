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

## Cycle 175 update

Step (3) of the ρ-side chain above is now formalised:
`ρPoly_no_real_root_gt_one` (axiom-clean) in
`OpenMath/Chapter4/Section441.lean`. The argument went through
the strategy's primary recipe (`pow_unbounded_of_one_lt` from
Cycle 136's `Section520.lean::explicitEulerGLM_not_isAStable`),
no Bernoulli fallback needed. Auxiliary infrastructure:
`geomSeq_isHomogeneousSolution_of_ρPoly_isRoot` (private helper,
"real root z₀ ⇒ n ↦ z₀^n is a homogeneous solution"), pattern
reusable for cycle 176's simple-root claim.

Remaining chain:

* **Step 4** (cycle 176, Phase B.2): simple root at 1. Argument
  via the unbounded sequence `n ↦ (n : ℝ)` solving the homogeneous
  recurrence when `(z-1)² ∣ ρ`. Mirrors cycle 175's auxiliary
  lemma skeleton with `n` instead of `z₀^n`.
* **Step 3+4 → ρ'(1) > 0** (cycle 177, Phase B.3): IVT-style sign
  analysis: stability + preconsistency ⇒ ρ no real root in `(1, ∞)`
  + ρ(1) = 0 + ρ → +∞ ⇒ ρ > 0 on `(1, ∞)` ⇒ ρ'(1) ≥ 0. Simple-
  root strengthening from cycle 176 ⇒ ρ'(1) > 0.
* **Close `lem:441A` a₁ > 0** (cycle 178, Phase B.4): one-line
  composition of cycle 174's bridge (`a₁ = 2·ρ'(1)`) with cycle
  177's `ρ'(1) > 0`.
* **Phase C** (cycle 178+): `aᵢ ≥ 0` for `i ≥ 2` half — complex-
  root decomposition via `Re(ζ) ≤ 0` for roots ζ of `aPoly`.

BDF2 sanity witness `bdf2LMM_aPoly_coeff_one_eq` (a₁ = 4/3) added
this cycle replaces the long-stalled `bdf2LMM_aPoly_eq` closed-
form goal — single coefficient, exercises the cycle 174 bridge on
a non-trivial method.

## Cycle 176 update

Step (4) of the ρ-side chain above is now formalised:
`ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` (axiom-clean,
expected) in `OpenMath/Chapter4/Section441.lean`. Stability +
preconsistency ⇒ `ρ'(1) ≠ 0` (the simple-root-at-1 condition).

Argument: under preconsistency `Σᵢ αᵢ = 1` and `ρ'(1) = 0` (assumed
for contradiction), the unbounded sequence `y_n := (n : ℝ)` solves the
(403a) homogeneous recurrence (private aux
`idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero`).
This contradicts `IsStable`'s requirement that homogeneous solutions
are uniformly bounded — `exists_nat_gt C` gives `n > C` while
`hC : |n| ≤ C`. The full template parallels cycle 175's
`ρPoly_no_real_root_gt_one` recipe with the unbounded sequence
swapped from `n ↦ z₀^n` to `n ↦ (n : ℝ)`.

Remaining chain:

* **Step 3+4 → ρ'(1) > 0** (cycle 177, Phase B.3): IVT-style sign
  analysis combining cycle 175's `ρPoly_no_real_root_gt_one` with
  `ρ(1) = 0`, `Polynomial.continuous`, `Polynomial.tendsto_atTop_*`
  to get `ρ > 0` on `(1, ∞)`, then `ρ'(1) ≥ 0`. Strengthen to `> 0`
  via cycle 176's `ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent`.
* **Close `lem:441A` a₁ > 0** (cycle 178, Phase B.4): one-line
  composition of cycle 174's bridge (`a₁ = 2·ρ'(1)`) with cycle
  177's `ρ'(1) > 0`.
* **Phase C** (cycle 179+): `aᵢ ≥ 0` for `i ≥ 2` half — complex-
  root decomposition via `Re(ζ) ≤ 0` for roots ζ of `aPoly`.

BDF2 sanity witness `bdf2LMM_ρPoly_deriv_eval_one_eq` (`ρ'(1) = 2/3`)
added this cycle. Numerically witnesses Phase B.2 on the canonical
`k = 2` example and consolidates with cycle 175's
`bdf2LMM_aPoly_coeff_one_eq` (`a₁ = 4/3 = 2·(2/3)`) — the cycle 174
bridge `a₁ = 2·ρ'(1)` made explicit on a non-trivial method.
