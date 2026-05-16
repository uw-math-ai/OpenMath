# Cycle 323 Results

## Worked on

Phase D.3 of `thm:344A` Phase D ladder: Lobatto IIIA `s = 2` `RKTableau`
(trapezoidal rule). Direct two-stage extension of cycle 322's Radau
IIA `s = 1` ship, exercising the collocation-A-matrix machinery at
four entries for the first time.

Six new public symbols + one coincidence theorem + one `SatisfiesB 2`
non-vacuity example in `OpenMath/Chapter3/Section344.lean`:

- `butcherLobatto_collocationA_two : Fin 2 → Fin 2 → ℝ` — the four-entry
  collocation A-matrix `(i, j) ↦ ∫₀^{c_i} L_j(x) dx` over the
  two-leaf abscissae `c = (0, 1)`.
- `butcherLobatto_collocationA_two_apply_zero_zero` : `= 0`
- `butcherLobatto_collocationA_two_apply_zero_one`  : `= 0`
- `butcherLobatto_collocationA_two_apply_one_zero`  : `= 1/2`
- `butcherLobatto_collocationA_two_apply_one_one`   : `= 1/2`
- `butcherLobattoIIIA_two : RKTableau 2` — assembled tableau threading
  cycle 320's `_zeros_two`, cycle 321's `_quadratureWeights_two`, and
  this cycle's `_collocationA_two`.
- `butcherTrapezoidalRK : RKTableau 2` — direct trapezoidal form
  `c = (0, 1)`, `b = (1/2, 1/2)`, `A = !![0, 0; 1/2, 1/2]`.
- `butcherLobattoIIIA_two_eq_trapezoidal` — coincidence theorem.
- `example : butcherLobattoIIIA_two.SatisfiesB 2` — order-2 quadrature
  non-vacuity.

## Approach

Followed the planner's strategy §B.1–B.6 verbatim. The `(0, j)` entries
of the A-matrix collapse trivially via `intervalIntegral.integral_same`
since the upper limit `c_0 = 0` gives a vacuous integral. The `(1, j)`
entries reuse cycle 321's `_quadratureWeights_two_apply_zero/_one`
recipe verbatim since `c_1 = 1` exactly matches the standard `[0, 1]`
integration range: (a) `Finset.univ.erase ⟨j, _⟩` decide to a singleton,
(b) `rw [Lagrange.basis, h_erase, Finset.prod_singleton,
Lagrange.basisDivisor]`, (c) `simp [butcherLobatto_zeros_two,
Polynomial.eval_*]` to expose the closed-form integrand `1 - x` or `x`,
(d) `intervalIntegral.integral_sub` + `integral_one` + `integral_pow` at
power 1 + `norm_num`.

The coincidence theorem decomposes via `RKTableau.mk.injEq + funext +
fin_cases` per the cycle 322 template. For the b- and c-fields the
proof routes through cycle 321 weight applies and `rfl` pattern-match
reductions respectively. The `SatisfiesB 2` example unfolds via
`Fin.sum_univ_two` + the direct trapezoidal field values; the `k = 1`
case requires a trailing `norm_num` to close `2⁻¹ + 2⁻¹ = 1`.

## Result

SUCCESS — all six new public symbols compile, `lake env lean
OpenMath/Chapter3/Section344.lean` clean exit in ~5s, aggregator
`OpenMath/Chapter3.lean` clean, `grep -c sorry
OpenMath/Chapter3/Section344.lean` = 0. `lake build
OpenMath.Chapter3.Section344` clean. Axiom-cleanliness verified:

```
butcherLobatto_collocationA_two              : [propext, Classical.choice, Quot.sound]
butcherLobatto_collocationA_two_apply_zero_zero : [propext, Classical.choice, Quot.sound]
butcherLobatto_collocationA_two_apply_zero_one  : [propext, Classical.choice, Quot.sound]
butcherLobatto_collocationA_two_apply_one_zero  : [propext, Classical.choice, Quot.sound]
butcherLobatto_collocationA_two_apply_one_one   : [propext, Classical.choice, Quot.sound]
butcherLobattoIIIA_two                       : [propext, Classical.choice, Quot.sound]
butcherTrapezoidalRK                          : [propext, Classical.choice, Quot.sound]
butcherLobattoIIIA_two_eq_trapezoidal         : [propext, Classical.choice, Quot.sound]
```

Section344.lean: 1235 → 1397 LOC (+162 LOC, vs. estimate ~120 LOC —
the four `_apply` proofs ran slightly longer than estimated due to
each being a self-contained restatement of the cycle 321 recipe).

## Faithfulness check

### `butcherLobatto_collocationA_two` (def)
- Entity ID: support for `thm:344A` Phase D ladder (Lobatto IIIA
  scheme, Butcher §344 Table 344(I) row "Lobatto IIIA  Lobatto
  quadrature  C(s)"). No JSON entity owns this specific definition
  (it is infrastructure assembled from existing abscissae/weights);
  the textbook reference is Butcher §344 Table 344(III), Lobatto IIIA
  at `s = 2`:
  > Lobatto IIIA collocation A-matrix entry `(i, j) = ∫₀^{c_i} L_j(x) dx`.
- Lean statement captures: **same content**. The definition is the
  literal textbook collocation-A-matrix recipe: integrate the j-th
  Lagrange basis polynomial (over the two-leaf abscissae) from 0
  to `c_i`. No definition smuggling.

### Four `_apply` theorems (each `= 0` or `= 1/2`)
- Tautology check: hypothesis-free; conclusion is a closed-form value,
  not a hypothesis re-export.
- Identity check: `(0, j)` cases route through
  `intervalIntegral.integral_same` (vacuous-integral lemma);
  `(1, j)` cases route through substantive integration chains
  (`integral_sub`/`integral_one`/`integral_pow`/`norm_num`). Not
  vacuous `exact h`.
- Hypothesis strength check: zero hypotheses; minimal.

### `butcherLobattoIIIA_two` (def)
- Faithful to Butcher §344 Table 344(III): A := Lobatto IIIA
  collocation A-matrix; b := Lobatto quadrature weights;
  c := Lobatto abscissae.

### `butcherTrapezoidalRK` (def)
- Faithful to the textbook trapezoidal rule. Implicit stage equation
  `Y_0 = y_0`, `Y_1 = y_0 + (h/2)(f(Y_0) + f(Y_1))` recovers
  `y_1 = y_0 + (h/2)(f(y_0) + f(y_1))`. Matches Butcher §344
  Table 344(III) at `s = 2` and Hairer–Wanner Vol. II §IV.5.

### `butcherLobattoIIIA_two_eq_trapezoidal` (coincidence)
- Tautology check: structure equality across two independently-defined
  tableaux, not a hypothesis re-export.
- Identity check: proof routes through four substantive `_apply` calls,
  two cycle-321 weight applies, and four `rfl` reductions. Not a
  single `exact h`.
- Hypothesis strength check: zero hypotheses; minimal.
- Faithfulness: textbook identification of Lobatto IIIA `s = 2` with
  the trapezoidal rule.

### `SatisfiesB 2` non-vacuity example
- Tautology check: routes through the coincidence theorem +
  `Fin.sum_univ_two` reduction. Hypothesis-free.
- Identity check: closes via `simp + norm_num` reduction of two
  concrete weight-power sums; not a hypothesis re-export.

## Dead ends

- Initial naive `simp [butcherTrapezoidalRK, Fin.sum_univ_two]` for the
  `SatisfiesB 2` `k = 1` case left `2⁻¹ + 2⁻¹ = 1` unsolved; appending
  `norm_num` closed it. The `k = 2` case closed via `simp` alone since
  `(1/2)·0 + (1/2)·1` simplifies fully.

## Discovery

The cycle 321 `_quadratureWeights_two_apply_zero/_one` recipe ports
verbatim to the Lobatto collocation-A-matrix `(1, j)` entries: same
integrand `1 - x` or `x`, same integration range `[0, 1]`. This is
because `c_1 = 1` for Lobatto at `s = 2`. The `(0, j)` entries do
not require any cycle 321 machinery — they collapse immediately via
`intervalIntegral.integral_same`.

The `unfold` of `butcherLobatto_collocationA_two` produces a `show`
target that names the abscissae array via the Fin-indexed function
rather than reducing `c_0` and `c_1` to literals. Explicit
`butcherLobatto_zeros_two ⟨0, _⟩` / `⟨1, _⟩` arguments at the
`show` line + a definitional `rfl` for `c_1 = 1` (via `have h_c1 :
butcherLobatto_zeros_two ⟨1, by omega⟩ = 1 := rfl`) cleanly rewrites
the upper limit to the literal `1` before the integral-distribution
recipe fires.

## Suggested next approach

Cycle 324: Radau IIA `s = 2`. Same structural shape as cycle 323 but
with non-trivial abscissae `(1/3, 1)`. The `(0, j)` and `(1, j)`
collocation A-matrix entries now require non-vacuous integration on
`[0, 1/3]` and `[0, 1]` respectively. The `(1, j)` entries reuse the
cycle 321 `butcherRadauII_quadratureWeights_two_apply_zero/_one`
recipe (integrand `(3/2) - (3/2)x` or `(3/2)x - 1/2` on `[0, 1]`).
The `(0, j)` entries are new: integration to `1/3` on integrands of
the form `(3/2) - (3/2)x` or `(3/2)x - 1/2` produces target values
`(5/12, -1/12)` (Butcher Table 344(II)).

Alternative cycle 324 target: Radau IA `s = 1` (forward Euler analogue,
`c = 0`, `b = 1`, `A = 0` via `Lagrange.basis_singleton` + vacuous
`∫₀⁰`). This is the strict one-stage anchor for the left-endpoint
Radau family; smaller scope than Radau IIA `s = 2` but lower
mathematical novelty since the collocation collapses to backward
Euler's mirror.

Deferred (multi-cycle scope): Lobatto IIIA `s = 3` (Simpson's rule,
9-entry A-matrix); Phase B.2 polynomial-exactness clauses
(`2s − 2` Radau, `2s − 3` Lobatto) requiring polynomial-division
infrastructure.
