# Issue: General reflexivity `equivalent_self M` for `def:381A` deferred

## Resolution (cycle 203)

**CLOSED.** Cycle 203 shipped `equivalent_self M : M.Equivalent M` in
`OpenMath/Chapter3/Section381.lean` (theorem
`OpenMath.Chapter3.Section312.RKTableau.equivalent_self`), built on the
cycle 201/202 Banach contraction foundation
(`RKStageMap`, `RKStageMap_dist_le`, `RKStageMap_lipschitz`,
`RKStageMap_contracting`).

Proof recipe (as deployed):
* Threshold `h₀ := 1 / (2 * (L * C + 1))` where
  `C := Σ_{i,j} |M.A i j|`, giving `0 < h₀` automatically and
  `|h| · L · C < 1` for `0 < h ≤ h₀` via the rearrangement
  `h * (2*(L*C+1)) ≤ 1 ⇒ 2*h*L*C ≤ 1 - 2*h < 1` (closed by `nlinarith`).
* `RKStageMap_contracting` discharges the smallness ⇒ `ContractingWith`
  link, then `Function.IsFixedPt` witnesses for the two stage tuples
  `Y, Y'` consume `hY_stage`/`hY'_stage` definitionally.
* `ContractingWith.eq_or_edist_eq_top_of_fixedPoints` gives the
  uniqueness disjunction; the `edist = ⊤` branch is closed by
  `edist_ne_top Y Y'` since `Fin s → N` is a `MetricSpace`.
* The output rewrite is mechanical: `rw [hY_out, hY'_out, hY_eq]`
  closes by reflexivity.

Verification: axiom-clean (`[propext, Classical.choice, Quot.sound]`),
warm rebuild of `Section381.lean` <7s, sorry count remains 0 across
the repo.

No `lean_status.json` / `plan.md` row change is needed: def:381A's
predicate + cycle 030 explicit-Euler witness already established the
formalisation status; the general reflexivity lemma is bonus non-vacuity
content (a stronger witness for the predicate's non-degeneracy story).

## Blocker

The general lemma

```lean
theorem equivalent_self {s : ℕ} (M : RKTableau s) :
    M.Equivalent M
```

is **mathematically trivial** in the textbook (the same algorithm
applied twice produces the same answer), but in our predicate-style
encoding (`IsRKOneStep` is a `Prop` admitting any solution of the
implicit stage system) it requires showing that for sufficiently small
`h`, the implicit stage map

```
(Y : Fin s → N) ↦ (i ↦ y₀ + h • Σⱼ aᵢⱼ • f(Yⱼ))
```

has a **unique** fixed point. With two arbitrary stage solutions
`Y, Y'`, we need a Lipschitz/contraction argument to conclude
`Y = Y'`, hence `y₁ = y₁'`.

The required tool is the Banach fixed-point theorem (already in
Mathlib as `ContractingWith.efixedPoint_unique` or
`contractingWith_iff_dist_lt`), but we still need:

1. A bound on the stage-map Lipschitz constant in terms of
   `h • ‖A‖_∞ • L` (where `L` is the Lipschitz constant of `f`).
2. A choice of `h₀` making this constant `< 1`.
3. A short Mathlib bridge from "two stage tuples both satisfy the
   fixed-point equation" to "they are equal" — most cleanly done by
   instantiating the contraction map and invoking
   `ContractingWith.fixedPoint_unique`.

## Context

Cycle 030 delivered:
- `IsRKOneStep` predicate (`OpenMath/Chapter3/Section381.lean`)
- `Equivalent` predicate (def:381A)
- `equivalent_explicitEuler_self` non-vacuity witness — explicit Euler
  is a *single-stage explicit* method, so its stage system has the
  unique trivial solution `Y 0 = y₀` for *every* `h`. No contraction
  argument needed; this is why the witness was tractable in one cycle.

The blocker only bites for **implicit** methods (where `A` has
non-zero diagonal entries) at moderate `h`.

## Cross-reference: AN-stability infrastructure gap

The AN-stability deferral (`AN_stability_deferred.md`, cycle 029) is a
related but distinct gap. AN-stability needs **complex matrix
resolvent** infrastructure `(I − A Z)⁻¹`; the present blocker needs
**real Banach contraction** infrastructure for the implicit stage
system. Both are facets of the same broader theme: implicit
Runge–Kutta methods are well-defined only at small `h` / small `Z`,
and faithful Lean encodings require us to prove that
well-definedness explicitly.

A future "implicit-method well-definedness" cycle could deliver:
- `RKTableau.implicitStageContraction M h hyp` — the contraction
  property at small `h`.
- `RKTableau.implicitStageUnique M h hyp` — uniqueness of stage
  solutions, derived from the contraction.
- `equivalent_self M` — direct corollary.
- (Bonus) the AN-stability `R(Z)` magnitude bound, which uses a
  related but complex-valued contraction.

## What was tried

Cycle 030 did not attempt `equivalent_self M` for general `M`; the
strategy explicitly scoped the cycle to the explicit-Euler witness.
No partial Lean attempts exist in the repo.

## Possible solutions

1. **Dedicated infrastructure cycle**: build the Banach contraction
   helper (`stageMap M h f y₀ : (Fin s → N) → (Fin s → N)` plus its
   contraction lemma at `h < 1 / (‖A‖_∞ • L)`), then both
   `equivalent_self` and other implicit-method theorems become short
   corollaries.
2. **Status quo**: keep `equivalent_explicitEuler_self` as the
   non-vacuity witness and defer `equivalent_self M` until needed by a
   downstream theorem (`thm:381H`, `thm:382A/B`, `lem:383A`,
   `lem:389A`, `thm:384A`, `thm:388B`). Several of these likely need
   the contraction infrastructure anyway.

Recommendation: **status quo** for now. The contraction infrastructure
is real Mathlib work and should be designed once, against a concrete
downstream consumer (likely `thm:381H`), rather than upfront against
a hypothetical reflexivity lemma.
