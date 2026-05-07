# Issue: Cycle 171 conflated `lem:441B`'s universal `c_{2i}` with `aPoly` coefficients

**Filed**: 2026-05-06 (cycle 172)

## Blocker

Cycle 171 introduced `OpenMath.Chapter4.Section404.LinearMultistepMethod.aPoly_even_coeff_neg`
in `OpenMath/Chapter4/Section441.lean`, deferred as `sorry`, claiming
to formalise Butcher's Lemma 441B. The statement is

```lean
theorem aPoly_even_coeff_neg
    {k : ℕ} (M : LinearMultistepMethod k) (_hStable : M.IsStable) :
    ∀ n : ℕ, 2 ≤ 2 * n → 2 * n ≤ k →
      M.aPoly.coeff (2 * n) < 0 := by
  sorry
```

This statement is **mathematically incorrect**. It conflates two
distinct sequences in Butcher §441 (p. 375–376):

* **Sequence 1 (`a_i`)** — coefficients of the LMM-dependent
  polynomial `a(z) = (1+z)^k − Σ_{i=1}^k αᵢ (1+z)^{k−i} (1−z)^i`.
* **Sequence 2 (`c_{2i}`)** — *universal* constants defined by
  the inverse-series identity (441c) for `(1/z)·log((1+z)/(1−z))`.

`lem:441A` is about Sequence 1; `lem:441B` is about Sequence 2.
Cycle 171's theorem keys off `aPoly` (Sequence 1) but claims the
sign behaviour of Sequence 2 — which is wrong on both ends.

## Context — Butcher §441 raw text

From `extraction/raw_text/ch04.txt:1947–2030`. Two distinct claims
are made consecutively:

> Lemma 441A. If the method under consideration is stable then
> a₁ > 0 and aᵢ ≥ 0, for i = 2, 3, …, k.

> Proof. ... [omitted] ...

> Lemma 441B. The coefficients c₂, c₄, … are all negative.

> Proof. Using the series for log(1+z)/(1−z)/z, we see that
> c₀, c₂, c₄, … satisfy
> (2 + (2/3)z² + (2/5)z⁴ + ⋯)(c₀ + c₂z² + c₄z⁴ + ⋯) = 1. (441c)
> It follows that c₀ = 1/2, c₂ = −1/6. ...

The (441c) identity has **no LMM dependency** — it is a pure
power-series identity for the function `log((1+z)/(1−z))/z`. So
the constants `c_{2i}` do not depend on `M`.

Sequence 1's bounds are governed by `lem:441A`, which says (for
stable `M`): `a₁ > 0` and `aᵢ ≥ 0`. Cycle 171's claim — that for
stable `M`, every even `aᵢ` (with `2 ≤ 2n ≤ k`) is *strictly
negative* — directly contradicts `lem:441A`.

## Algebraic verification — BDF2 explicit refutation

BDF2 (`k = 2`, `α₀ = -1`, `α₁ = 4/3`, `α₂ = -1/3`,
`Section451.bdf2LMM`):

```
aPoly = (1 + X)² − (4/3)·(1 + X)·(1 − X) − (−1/3)·(1 − X)²
      = (1 + X)² − (4/3)·(1 − X²) + (1/3)·(1 − X)²
      = (1 + 2X + X²) − (4/3 − (4/3)X²) + (1/3 − (2/3)X + (1/3)X²)
      = (1 − 4/3 + 1/3) + (2X − (2/3)X) + (X² + (4/3)X² + (1/3)X²)
      = 0 + (4/3)·X + (8/3)·X².
```

So `aPoly.coeff 2 = 8/3 > 0`. BDF2 is zero-stable (Butcher §451,
p. 363; cycle 169 formalised G-stability ⇒ A-stability for BDF2),
so `M.IsStable` holds. Cycle 171's theorem instantiated at `n = 1`
(`2n = 2`, with `2 ≤ 2 ≤ k = 2`) would assert `8/3 < 0`. **False.**

This counterexample is exhibited concretely in `bdf2LMM_aPoly_eq`
(cycle 172 addition).

## Resolution adopted in cycle 172

1. **Roll back** `aPoly_even_coeff_neg` (delete the theorem and
   its `sorry` from `OpenMath/Chapter4/Section441.lean`).
2. **Preserve** the correct cycle-171 work: `aPoly` definition
   and `explicitEulerLMM_aPoly_eq` non-vacuity witness.
3. **Add** Phase A enrichment around `aPoly`:
   * `aPoly_natDegree_le` — degree bound `aPoly.natDegree ≤ k`.
   * (Deferred) A BDF2 closed-form witness
     `bdf2LMM_aPoly_eq : bdf2LMM.aPoly = C(4/3) X + C(8/3) X²`
     was attempted; the algebra is straightforward (see
     "Algebraic verification — BDF2 explicit refutation" above)
     but Lean's `ring` does not fold `Polynomial.C` constants
     (e.g. `C(4/3) - C(-1/3) = C(5/3)` is outside `ring`'s
     normal form). A future cycle can close this either by
     coefficient-by-coefficient extensionality
     (`Polynomial.ext` + `Polynomial.coeff_*` rewrites) or by
     a more manual `linear_combination` setup.
4. **Revert** `lem:441B` in `extraction/formalization_data/lean_status.json`
   from `partial` back to `unformalized` (cycle 171 was
   incorrect), and revert `plan.md`'s `[~]` mark to `[ ]`.

## What was tried — `aPoly_even_coeff_neg` cannot be salvaged

* Restating with a different sign convention (`aPoly.coeff (2n) > 0`
  for `n ≥ 1`): also wrong. Explicit Euler has `aPoly = 2X`, so
  `aPoly.coeff 2 = 0`, not strictly positive.
* Restating with `M.IsConvergent` or `M.IsZeroStable` instead of
  `M.IsStable`: same BDF2 refutation applies.
* Restating in terms of `aPoly` evaluated at `0` or `1`: a₀ = 0
  for preconsistent `M` (since the constant-term condition is
  `α(1) = 0`), but that's a pointwise statement, not the
  even-coefficient-sign claim Butcher makes for `c_{2i}`.

The fundamental issue: `lem:441B`'s `c_{2i}` are constants of a
universal power series. Any statement keying off `M.aPoly` is
about Sequence 1, which is governed by `lem:441A`.

## Possible solutions — re-plan for the *correct* `lem:441B`

The correct formalisation requires a separate `cInverseLog : ℕ → ℝ`
definition (no `M` parameter):

* **Phase B (future cycle)**. Define
  `cInverseLog n := …` such that the (441c) identity holds:
  `(2 + (2/3)X² + (2/5)X⁴ + ⋯) · (c₀ + c₂X² + c₄X⁴ + ⋯) = 1`
  in `PowerSeries ℝ`. Closed form for `cInverseLog`:
  recurrence `c_{2n} = -(c₀·d_{2n} + c₂·d_{2n−2} + … + c_{2n−2}·d₂) / d₀`
  per Butcher's (441d) identity, where
  `d_{2i} := -8(n−i) / ((2i+1)(2i−1))`.
* **Phase B base cases**. `c₀ = 1/2`, `c₂ = -1/6` (Butcher
  p. 376).
* **Phase C induction**. Strong induction on `n`: assuming
  `c_{2i} < 0` for `i = 1, …, n−1`, the (441d) recurrence and
  `d_{2i} < 0` for `1 ≤ i ≤ n−1` together with `d_{2n} = 0`
  force `c_{2n} < 0`.

The definition of `cInverseLog` should be the *algebraic* inverse
of the partial-sum power series for `(1/z)·log((1+z)/(1−z))`, NOT
its negativity property — to avoid definition smuggling. The
`lem:441B` theorem then asserts negativity as a consequence.

The Mathlib infrastructure required:
* `PowerSeries.mk`, `PowerSeries.coeff`, multiplication.
* The series `Σ_{n ≥ 0} z^{2n} / (2n+1)` (or its `*2` rescaling
  matching Butcher's normalisation) as a `PowerSeries ℝ`.
* Inverse-series existence (Mathlib: `PowerSeries.inv` requires
  unit constant term — here `c₀ = 1/2 ≠ 0`, so inversion is
  well-defined).

This is a stand-alone `PowerSeries` problem with no LMM
dependency. It is suitable for a fully designed Phase B cycle, NOT
a one-shot Aristotle batch.

## Affected entity

`lem:441B` — extraction record `formalization_data/entities/lem_441B.json`,
status reverted to `unformalized` in `lean_status.json` after
cycle 172 rollback.

`lem:441A` — separate (also unformalized as of cycle 172). Cycle
172 strategy §C Priority 5 outlines the plan but defers the proof
to a future cycle, since Priority 0–4 budget consumed cycle 172.

## References

* `.prover-state/strategy.md` (cycle 172 strategy, §B "Why the
  cycle 171 sorry'd theorem is mathematically wrong").
* `.prover-state/task_results/cycle_171.md` (cycle 171 worker
  notes — the worker correctly noted the multi-cycle plan but
  did not catch the misinterpretation).
* `extraction/raw_text/ch04.txt:1947–2030` (raw Butcher §441 text).
* `extraction/formalization_data/entities/lem_441A.json`,
  `extraction/formalization_data/entities/lem_441B.json`.
* `OpenMath/Chapter4/Section441.lean::LinearMultistepMethod.aPoly_natDegree_le` —
  cycle 172 degree bound (Phase A infrastructure).
