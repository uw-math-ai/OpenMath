# Issue: Butcher §406 lem:406B textbook decomposition has a typo

**Filed**: 2026-04-30 (cycle 040)

## Blocker

The cycle 040 strategy explicitly directed the worker to verify Butcher's
algebraic decomposition before encoding the bound's RHS. Verification fails:
Butcher's claim disagrees with the actual definition `def:406A` even on
explicit Euler.

## Context — Butcher's claim (lem:406B proof, p. 346)

Quoted from `extraction/formalization_data/entities/lem_406B.json`:

> Because of the consistency of the method, we have ∑_{i=1}^k α_i = 1 and
> ∑_{i=1}^k (iα_i − β_i) = β_0. We now write L(y, x, h) in the form
>
>   L(y, x, h) = ∑_{i=1}^k α_i (y(x) − y(x − ih) − ihy'(x))
>                + h ∑_{i=1}^k (iα_i − β_i)(y'(x) − y'(x − ih));

The local truncation error is (def:406A):

  L(y, x, h) = y(x) − ∑_{i=1}^k α_i y(x − ih) − h ∑_{i=0}^k β_i y'(x − ih)

## Algebraic verification

Expand Butcher's claimed RHS:

  RHS = ∑ α_i y(x) − ∑ α_i y(x−ih) − h y'(x) ∑ iα_i
        + h y'(x) ∑(iα_i − β_i) − h ∑(iα_i − β_i) y'(x−ih)
      = y(x) − ∑ α_i y(x−ih) − h y'(x) ∑ iα_i + h y'(x) β_0
        − h ∑(iα_i − β_i) y'(x−ih)             [preconsistency, (404b)]

For RHS = L we'd need (matching coefficients of `y'(x−ih)` for i ≥ 1
and the constant `y'(x)` term separately):

  c_i = β_i                                    [from y'(x−ih) coefficient]
  ∑ c_i = ∑ iα_i − β_0                         [from y'(x) coefficient]

By (404b), ∑_{i=1}^k iα_i − β_0 = ∑_{i=1}^k β_i, so both equations
collapse to **c_i = β_i**, NOT c_i = iα_i − β_i.

## Sanity check on explicit Euler (k=1, α₁=1, β₀=0, β₁=1)

- Actual L = y(x) − y(x−h) − h y'(x−h).
- Butcher's RHS = α₁(y(x) − y(x−h) − hy'(x)) + h(1·1 − 1)(y'(x) − y'(x−h))
              = y(x) − y(x−h) − h y'(x).  ❌ disagrees with actual L
- Alternative RHS (c_i = β_i) = α₁(y(x) − y(x−h) − hy'(x))
                                + h·1·(y'(x) − y'(x−h))
              = y(x) − y(x−h) − h y'(x−h).  ✓ matches actual L

## Sanity check on implicit Euler (k=1, α₁=1, β₀=1, β₁=0)

- Actual L = y(x) − y(x−h) − h y'(x).
- Butcher's RHS = α₁(y(x) − y(x−h) − hy'(x)) + h(1·1 − 1)(y'(x) − y'(x−h))
              = y(x) − y(x−h) − h y'(x) + 0
              ✓ — but only by accident: the (iα_i − β_i) = β_0 = 1
              coefficient cancels because y'(x) term cancels at this
              specific method. The general form still doesn't equal L.

Wait — recompute: (iα_i − β_i) = (1·1 − 1) = 0 for implicit Euler.
So Butcher's RHS = y(x) − y(x−h) − h y'(x). ✓ for implicit Euler too.

So the typo accidentally agrees on both Euler methods (explicit
disagreement was a calc error above — let me recheck):

- Explicit: (iα_i − β_i) = (1·1 − 1) = 0. Butcher's RHS =
  y(x) − y(x−h) − h y'(x) + 0. **But actual L = y(x) − y(x−h) − h y'(x−h)**.
  ❌ — disagrees.

So explicit Euler **is** a counterexample to Butcher's decomposition.
The correct form (c_i = β_i) gives β_1 = 1, recovering h(y'(x)−y'(x−h))
which combined with `−hy'(x)` yields `−hy'(x−h)`. ✓

## Resolution adopted in cycle 040

Use the **algebraically correct form** with c_i = β_i:

  L(y, x, h) = ∑_{i=1}^k α_i (y(x) − y(x − ih) − ihy'(x))
               + h ∑_{i=1}^k β_i (y'(x) − y'(x − ih))

The corresponding bound is

  |L| ≤ (½ ∑ i² |α_i| + ∑ i |β_i|) L M h²

(replacing `∑ i |iα_i − β_i|` with `∑ i |β_i|` in the textbook
statement).

Both forms are valid upper bounds *for the same |L|*, but only the
β_i form is an *equality* — and we want an equality decomposition for
the proof. The cycle 040 worker proceeds with the β_i form.

## What was tried

Direct algebraic expansion of both candidate decompositions, then
verification on explicit Euler. The β_i form survives the test;
the textbook (iα_i − β_i) form does not.

## Possible solutions

1. **(adopted)** Encode the algebraically correct form (β_i) with a
   comment in the Lean source explaining the textbook discrepancy.
2. **(rejected)** Encode Butcher's stated bound (i|iα_i − β_i|) — this
   would require a bound that does not come from the decomposition
   the proof actually uses. Misleading.
3. **(future cycle)** Cross-check against a second textbook (Iserles,
   Hairer-Wanner, etc.) to confirm the typo is not just our reading
   error. Tracked here for cycle 041+ if needed.

## Affected entity

`lem:406B` — encoded as `localTruncationError_bound` in
`OpenMath/Chapter4/Section404.lean` with the corrected bound. The
Lean source carries an explicit comment pointing to this issue file.
