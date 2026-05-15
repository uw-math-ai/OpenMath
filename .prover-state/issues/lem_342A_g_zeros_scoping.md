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

## Closes

This is a scoping document, not a deliverable in itself. No file
changes proposed; the actual (342g) work is deferred to cycle 283+.
