# Issue: AN-stability component of `def:356A` deferred

## Blocker

Definition 356A in Butcher's textbook (page 268) bundles **two**
named concepts in a single entity record (the extractor combined a
multi-paragraph passage):

1. **AN-stable Runge–Kutta method** — the first sentence:
   `R(Z) = 1 + b'Z(I − AZ)⁻¹𝟏`, with `Z = diag(z₁, …, zₛ)`, is
   bounded in magnitude by 1 whenever every `zᵢ` lies in the closed
   left half-plane (componentwise).
2. **DJ-irreducibility** — the property that a tableau cannot be
   reduced in the sense of Definition 356B.

Cycle 029 formalised the **DJ-irreducibility** component of
`def:356A` (and the entirety of `def:356B`). The **AN-stability**
component is deferred.

## Why deferred

AN-stability requires the complex matrix-valued stability function

```
R(Z) = 1 + b' Z (I − A Z)⁻¹ 𝟏,    Z ∈ ℂ^{s×s} diagonal,
```

with the boundedness condition `|R(Z)| ≤ 1` whenever every
`Re(zᵢ) ≤ 0`. None of `R(Z)`, `(I − A Z)⁻¹`, or the `s`-dimensional
left-half-plane condition is currently in the codebase. This is
**independent infrastructure**: it shares no machinery with the
§356/§381-style reducibility predicates that DJ-irreducibility
uses, and a faithful formalisation deserves a dedicated cycle (or
multiple).

## Mathlib hooks for the future cycle

* `Matrix.IsUnit` and `Matrix.inv` (or `Matrix.nonsing_inv`) for the
  resolvent `(I − A Z)⁻¹`.
* `Matrix.diagonal` for `Z = diag(z₁, …, zₛ)` (with `zᵢ : ℂ`).
* `Complex.re` and the `Set.preimage` of `(· ≤ 0)` for the closed
  left half-plane condition `∀ i, (zᵢ).re ≤ 0`.
* `Complex.abs` (or `Complex.normSq`) for the magnitude bound
  `|R(Z)| ≤ 1`.
* The natural typeclass is `Matrix (Fin s) (Fin s) ℂ` and the natural
  `R(Z)` lives in `ℂ`.

## Downstream consumers

* `thm:356C` (AN-stability necessary conditions) — directly uses
  AN-stability as its hypothesis.
* `cor:356D` (positive weights for DJ-irreducible methods) — a
  corollary of `thm:356C`.
* `thm:357C` and `thm:357D` (algebraic stability ⇒ B-stability and
  related implications) — consume AN-stability via the §356C/D
  necessary conditions.

In short, pursuing AN-stability is the natural unblocker for the
remainder of §356–§357.

## Possible solutions

* A dedicated cycle (or two) building the complex matrix resolvent
  infrastructure: `(I − A Z)⁻¹` well-definedness lemmas, the
  scalar-valued `R(Z)`, and the boundedness predicate. After that,
  `def:356A`'s AN-stability component becomes a clean
  `def`-and-witness deliverable like `def:357B`.
* If the resolvent infrastructure proves heavy, an intermediate
  `R(Z)`-as-rational-function reformulation may be feasible — but
  this risks definition smuggling (the Lean definition would no
  longer obviously match the textbook formula). Prefer the direct
  formulation.

## Recommended resolution

A dedicated cycle, after the DJ-reducibility infrastructure of
cycle 029 has settled. `lean_status.json` records `def:356A` as
`partial` with this issue file as the pointer.
