# Scoping: lem:342A (342g) — `P_n^*` has `n` distinct real zeros in (0, 1)

## Textbook statement (Butcher §342, p. 236)

> `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
> `n = 0, 1, 2, …`.

Quoted from `extraction/formalization_data/entities/lem_342A.json`,
clause (342g).

## Textbook proof sketch (Butcher §342, p. 236)

> The final result (342g) is proved by supposing, on the contrary,
> that `P_n^*(x) = Q(x) R(x)`, where the polynomial factors `Q` and
> `R` have degrees `m < n` and `n - m`, respectively, and where `R`
> has no zeros in `(0, 1)`. We now find that
> `∫₀¹ P_n^*(x) Q(x) dx = 0`, even though the integrand is not zero
> and has a constant sign.

The standard contradiction: let `x_1, …, x_k` (with `k < n`) be the
distinct real zeros of `P_n^*` in `(0, 1)` *at which `P_n^*` changes
sign*. Form
`Q(x) := (x − x_1)(x − x_2)…(x − x_k)` (degree `k < n`).
Then `P_n^*(x) · Q(x)` has constant sign on `(0, 1)` (the sign-change
zeros are paired off), so the integral is nonzero. But by (342a)
applied to `Q ∈ Span{P_0^*, …, P_{k}^*}` (since `deg Q = k < n`),
the integral *is* zero. Contradiction.

## Why this is a candidate for Aristotle, not manual

Sign-change combinatorics in Lean is fiddly:
- Need to extract a finite sign-change set from `P_n^*` on `(0, 1)`.
- Need to argue `P_n^*(x) · ∏ᵢ (x − xᵢ)` has constant sign on the open
  interval, formalizing the "sign-change zeros are paired off"
  argument.
- Need the orthogonality conclusion `∫₀¹ P_n^* · Q = 0` from a
  polynomial `Q` of degree `k < n` — a corollary of (342a), via
  expansion of `Q` in the `P_j^*` basis.

The §342 (342a)/(342b)/(342d)/(342e)/(342f) layer is now in place
post-cycle 282 — Aristotle has access to all of orthogonality,
norm-square, Rodrigues, parity, and (once 342f lands) the three-term
recurrence. (342g) is the natural next batch submission once (342f)
ships.

## Mathlib hooks likely needed

| Need | Mathlib candidate |
|---|---|
| Polynomial roots in an interval | `Polynomial.roots`, `Polynomial.card_roots_le_degree` |
| Counted multiplicity of real roots | `Polynomial.roots_count_le_degree` |
| Sign change → root in interval (IVT) | `intermediate_value_Ioo`, `Polynomial.continuous` |
| Polynomial factorization over ℝ | `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq` |
| Orthogonality vs polynomial of smaller degree | reduce via the basis `{P_0^*, …, P_k^*}` (cycle 282's `butcherShiftedLegendre_natDegree` provides the dim/degree match) |

## LOC budget estimate

~150 LOC. Structure:
- ~30 LOC infrastructure: extracting sign-change zeros of `P_n^*`
  in `(0, 1)` as a `Finset ℝ`.
- ~40 LOC: product polynomial `Q := ∏ᵢ (X − C xᵢ)` and its degree.
- ~40 LOC: sign-constancy of `P_n^* · Q` on `(0, 1)` (or "sign of
  the integrand is nonzero except at finitely many points").
- ~40 LOC: integral nonvanishing via positivity, contradiction with
  (342a)-derived `∫₀¹ P_n^* · Q = 0`.

## Risk assessment

| Risk | Mitigation |
|---|---|
| Sign-change formalization is fiddly in Lean | Submit to Aristotle once (342f) lands |
| Polynomial-basis expansion `Q ∈ Span{P_0^*, …, P_k^*}` requires a degree-induction lemma not in Mathlib | Provide as a helper axiom in the Aristotle submission |
| `card_roots` vs distinct real zeros in an open interval — Mathlib might count multiplicities | Use `Polynomial.roots.toFinset` to deduplicate |

## Cycle 283+ outlook

- Single-poll Aristotle (342f) project `c8b8f138-f875-4263-94ec-74533b5120d7`.
- If COMPLETE → integrate analogously to cycle 281's `d4ce527b`
  integration; then fire (342g) on Aristotle citing all of (342a)–(342f).
- If IN_PROGRESS at low % → continue ladder (n=5, 6, 7 recurrence
  witnesses) as Branch B fallback.

## Cycle 294 update

Cycle 294 executed the measured fire-and-forget pattern from this
scoping doc:

* **Aristotle submission**: project
  `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` (file
  `.prover-state/aristotle_submissions/cycle_294/342g_zeros.lean`,
  status `QUEUED` at 2026-05-15 22:11:40 UTC). Cites (342a)–(342f)
  plus the cycle-292 `butcherShiftedLegendre_orthogonal_to_lower_degree`
  lemma — the load-bearing prerequisite for the contradiction
  argument. Single-poll cycle 295.
* **Empirical anchors shipped**: three theorems in
  `OpenMath/Chapter3/Section342.lean`, all axiom-clean:
  * `butcherShiftedLegendre_one_root` — `P_1^*(1/2) = 0 ∧ 1/2 ∈ (0,1)`.
  * `butcherShiftedLegendre_two_roots` — distinct roots
    `(3 ± √3)/6 ∈ (0,1)` of `P_2^*`.
  * `butcherShiftedLegendre_card_roots_le` — upper bound
    `(P_n^*).roots.toFinset.card ≤ n` via `Polynomial.card_roots'`
    + cycle 273's `butcherShiftedLegendre_natDegree`.
* **`n = 3` zeros**: explicitly deferred (closed-form involves
  cubic-formula nested radicals). The IVT path is viable but
  belongs to the full closure infrastructure.

## Closes

This is a scoping document, not a deliverable in itself. No file
changes proposed; the actual (342g) work is deferred to cycle 283+.

Cycle 294 anchored the work and dispatched to Aristotle. Cycle 295
single-polls. Closure (Branch A / B / C) depends on Aristotle's
return.

## Cycle 295 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 16`
  at `2026-05-15T22:41:20Z` (≈30 min after cycle 294 submission).
  Growth from `QUEUED` (0%) ⇒ Branch B fired.
* **`n = 3` anchor shipped**: `butcherShiftedLegendre_three_roots`
  in `OpenMath/Chapter3/Section342.lean` — three distinct roots
  of `P_3^*` in `(0, 1)` via parity (middle, `r = 1/2`) plus IVT on
  `[0, 1/5]` (left, `r ∈ (0, 1/5)`) and `[4/5, 1]` (right,
  `r ∈ (4/5, 1)`), assembled with interval-disjointness `linarith`.
* **Reusable helper**: `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
  generalises the parity-driven middle-root argument to every odd
  `n`. Reused immediately in cycle 296's `n = 5` anchor.
* All cycle 295 work axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Cycle 296 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 25`
  at `2026-05-15T23:01:44Z` (≈50 min after cycle 294 submission;
  +9 percentage points from cycle 295's 16%). Healthy growth ⇒
  Branch B fires; leave Aristotle running.
* **`n = 5` anchor shipped**: `butcherShiftedLegendre_five_roots`
  in `OpenMath/Chapter3/Section342.lean` — five distinct roots of
  `P_5^*` in `(0, 1)`. Recipe:
  - **Middle root** `r₃ = 1/2` via cycle 295's
    `butcherShiftedLegendre_eval_half_eq_zero_of_odd 5 ⟨2, rfl⟩`
    (one-line application of the new helper).
  - **Two left roots** via IVT on the closed form
    `P_5^* = 252X^5 - 630X^4 + 560X^3 - 210X^2 + 30X - 1`
    (cycle 278's `butcherShiftedLegendre_five`):
    * `P_5^*(0) = -1`, `P_5^*(1/10) = 2497/6250` ⇒ ascending
      `intermediate_value_Ioo` on `[0, 1/10]`.
    * `P_5^*(1/10) = 2497/6250`, `P_5^*(1/4) = -23/256` ⇒ descending
      `intermediate_value_Ioo'` on `[1/10, 1/4]`.
  - **Two right roots** (parity-symmetric to the left pair):
    * `P_5^*(3/4) = 23/256`, `P_5^*(9/10) = -2497/6250` ⇒ descending
      `intermediate_value_Ioo'` on `[3/4, 9/10]`.
    * `P_5^*(9/10) = -2497/6250`, `P_5^*(1) = 1` ⇒ ascending
      `intermediate_value_Ioo` on `[9/10, 1]`.
  - **Distinctness** (10 pairs) via `linarith` on the disjoint
    intervals
    `(0, 1/10) < (1/10, 1/4) < {1/2} < (3/4, 9/10) < (9/10, 1)`.
* Axiom-clean (`[propext, Classical.choice, Quot.sound]`); zero
  sorries; well within the strategy's 200-LOC budget.
* Aristotle still in flight; no stall observation appended.
