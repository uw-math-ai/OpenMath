# Issue: Rouché's theorem missing from Mathlib

## Blocker

**Mathlib does not currently have Rouché's theorem** (the complex-analysis
result that, on a Jordan domain, two holomorphic functions `f, g` with
`|g - f| < |f|` on the boundary have the same number of zeros inside).

Verified by grep over `.lake/packages/mathlib/Mathlib/Analysis/`:

```
$ grep -ri "Rouch" .lake/packages/mathlib/Mathlib/Analysis/
# (no matches)
```

## Affected entities

* **`thm:431A` (Stability regions / Schur criterion, Butcher §431,
  p. 366)** — sufficiency direction. Specifically, the implication

  > `|a₀|² > |aₙ|² ∧ IsStronglyStable (schurReduce P) ⇒ IsStronglyStable P`

  is exactly the application of Rouché's theorem in Butcher's proof:

  > "By Rouché's theorem, `wPₙ₋₁(w)` has `n` zeros in the open unit disc
  >  if and only if the same property is true for `Pₙ(w)`."

  See `OpenMath/Chapter4/Section431.lean` for the partial formalisation
  (necessity direction + algebraic identity + predicate + witnesses).

  Status in `extraction/formalization_data/lean_status.json`: `partial`
  (cycle 170).

## What was tried

This cycle (cycle 170) shipped:

1. `IsStronglyStable` predicate (open-unit-disc characterisation).
2. Three non-vacuity witnesses (degree-2 stable, degree-3 stable,
   `X² - 1` *not* stable).
3. `schurReduce` definition (the Butcher §431 Schur reduction `Pₙ₋₁`,
   in ascending coefficient form).
4. `schur_identity_coeff` — the load-bearing algebraic identity
   `(X · schurReduce P).coeff (k+1) = a₀ · conj(P.coeff(k+1)) -
    aₙ · conj(P.coeff(n - k - 1))` (Butcher's `wPₙ₋₁(w) = a₀Pₙ(w) -
    aₙwⁿPₙ(w⁻¹)`).
5. `strongly_stable_imp_lead_gt_const` — the necessity direction of
   (431e), via Vieta on the multiset of roots.

The sufficiency direction was deliberately deferred per the cycle 170
strategy.

## Possible solutions

### Option A — wait for upstream Mathlib

Track `https://leanprover-community.github.io/mathlib4_docs/` for an
upstream Rouché formalisation. Mathlib's complex-analysis library is
actively developing; argument principle and winding number are
already in place, which are the natural prerequisites.

### Option B — formalise Rouché in `OpenMath/`

This is multi-cycle infrastructure. The standard proof goes through
the **argument principle** + a homotopy:

* Mathlib has `Complex.integral_circle_inv` and a notion of winding
  number (`Complex.cintegral` plus `Complex.argDeriv`).
* The argument principle `(1/(2πi)) ∮ f'/f = #zeros - #poles` is
  partially present (`Complex.integral_circle_pow_inv` and friends),
  but a clean self-contained statement requires defining a meromorphic
  function and counting zeros via `Polynomial.roots.card`.
* For polynomials specifically, "Rouché on the open unit disc" reduces
  to a real-coefficient inequality on `|w| = 1`.

Estimated cost: 4–8 cycles to build a usable Rouché statement
specialised to polynomials on the open unit disc, plus 1 cycle to
apply it for `thm:431A` sufficiency.

### Option C — accept the partial formalisation indefinitely

Necessity + the algebraic identity + the predicate is itself a
substantive textbook capture, and the sufficiency direction is the
classical computation that downstream theorems typically use as a
black box. Downstream §441 results (`thm:441C`, `lem:441A/B`) cite
the Schur criterion at the level of "such a polynomial is strongly
stable iff the Schur conditions hold" — they do not unfold the
sufficiency proof. The partial formalisation may be enough for those
to consume, treating the IFF as a hypothesis on the polynomial.

## Cross-links

* `extraction/formalization_data/entities/thm_431A.json` — textbook
  statement, dependencies, dependents.
* `OpenMath/Chapter4/Section431.lean` — the partial formalisation.
* Butcher (2008), 3rd ed., §431 "Stability regions", p. 366,
  Theorem 431A and (431e).

## Recommended path forward

**Option C (accept partial) for now**, revisit if/when (a) Mathlib
ships Rouché, or (b) a downstream Ch.4 §441 entity *requires* the
sufficiency direction unfolded (as opposed to assumed). Re-evaluate
at the start of Ch.4 §441 work.
