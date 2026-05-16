# Cycle 326 Results

## Worked on

§344 Phase D.6: planned target was `butcherRadauIA_two : RKTableau 2`
via the cycle 324 plain-collocation template. The cycle 326 strategy
§D faithfulness audit was explicitly flagged as load-bearing
("MOST IMPORTANT step of the cycle. Do it before writing any Lean.").
The audit fired — see below. The cycle shipped Branch B (modified
per audit) instead.

## Approach

### §C pre-flight verifications (all passed)

1. `butcherRadauI_zeros_two` exists at `Section344.lean:624`, gives
   `(0, 2/3)`. ✓
2. `butcherRadauI_quadratureWeights_two_apply_{zero,one}` exist at
   `Section344.lean:904` and `932`. ✓
3. `butcherRadauI` polynomial defined at `Section344.lean:71`. ✓

### §D faithfulness audit (fired — divergence confirmed)

Read `extraction/raw_text/ch03.txt:5214` (Table 344(I)) and
`:5274` (Radau IA `s = 2` printed table). Butcher Table 344(I)
specifies the Radau IA A-matrix construction as *"The reflections
of Radau II"* — explicitly **not** the plain collocation
`A_{ij} = ∫₀^{c_i} L_j(x) dx`.

Direct comparison at `s = 2`, abscissae `(0, 2/3)`:

| `(i, j)` | Plain collocation | Butcher Table 344(I) |
|----------|-------------------|----------------------|
| `(0, 0)` | `0`               | `1/4`                |
| `(0, 1)` | `0`               | `-1/4`               |
| `(1, 0)` | `1/3`             | `1/4`                |
| `(1, 1)` | `1/3`             | `5/12`               |

Plain collocation **does not match** Butcher's printed values.
The cycle 324 template therefore does not lift to Radau IA.

I also verified that the cycle 343 bare `RKTableau.reflection`
(Section343.lean:69) applied to `butcherRadauIIA_two` does not
recover Butcher's Radau IA values either (gave row `(5/12, 1/4)`
in both rows after the reflection, abscissae `(2/3, 0)`). Butcher's
"reflections of Radau II" is a refined construction beyond the
§343 reflection — investigation is multi-cycle scope.

### Branch B pivot, modified

The cycle 326 strategy's prescribed Branch B was "pivot to
Lobatto IIIB `s = 2`". However, Butcher line 5263 explicitly:
*"we note that Lobatto IIIB with s = 2 does not exist"*. The
strategy's Branch B target is unworkable.

I chose a different Branch B: ship the **direct form** of
Radau IA `s = 2` (`butcherRadauIADirect_two`) declared inline with
Butcher's printed values, plus a `SatisfiesB 3` non-vacuity
example. This is the smallest faithful deliverable consistent
with the §A/§B/§J cycle-326 constraints (one new `RKTableau` for
Radau IA `s = 2`, no axioms, no smuggling).

## Result

SUCCESS.

* New issue `.prover-state/issues/radau_ia_collocation_divergence.md`
  documents the audit, the divergence values, the failed
  `RKTableau.reflection` experiment, and the options menu for
  future cycles.
* Section344.lean: 1711 → 1760 LOC. 2 new public symbols
  (`butcherRadauIADirect_two`, plus an anonymous `example :
  SatisfiesB 3`). Sorry count remains `0`. No `axiom` /
  `constant` introduced.
* `lake env lean OpenMath/Chapter3/Section344.lean` exits `0`.
* `lake build OpenMath.Chapter3.Section344` succeeds.
* `#print axioms butcherRadauIADirect_two` returns
  `[propext, Classical.choice, Quot.sound]`.

## Faithfulness check

### `butcherRadauIADirect_two : RKTableau 2`

* **Source**: Butcher, *Numerical Methods for Ordinary Differential
  Equations* (3rd ed.), §344, Table 344(I) p. 225,
  `extraction/raw_text/ch03.txt:5274`.

  > Radau IA       (s = 2, p = 3),
  >                              0        1/4       -1/4
  >                              2/3      1/4        5/12
  >                                       1/4        3/4

* **Entity ID**: This is an *instance* of the more general
  `thm:344A` taxonomy entry (no per-instance entity exists in
  `formalization_data/entities/`). The textbook source for
  the instance is Table 344(I) directly.
* **Lean statement**: `c = ![0, 2/3]`, `b = ![1/4, 3/4]`,
  `A = !![1/4, -(1/4); 1/4, 5/12]`.
* **Captures**: **same** as Butcher's printed table values
  (verified entry-by-entry).
* **Smuggling check**: the symbol name `Direct` is deliberate — no
  claim is made that the `A`-matrix is derived from any
  construction. The values are declared inline directly from the
  textbook table, which is faithful.

### `example : butcherRadauIADirect_two.SatisfiesB 3`

* **Source**: implicit in `thm:344A` (p = 2s − 1 = 3 for Radau IA
  at s = 2; `B(η)` is the order-`η` quadrature condition from
  Section321).
* **Lean statement**:
  `∀ k, 1 ≤ k → k ≤ 3 → ∑ⱼ bⱼ · cⱼ^{k-1} = 1/k`.
* **Captures**: **same** — Butcher's `(s = 2, p = 3)` claim
  implies the `B(3)` quadrature condition holds, which is what
  this proves.
* **Identity check**: not vacuous. Each of the three arms
  computes a genuine sum (`1/4 + 3/4 = 1`,
  `(1/4)·0 + (3/4)·(2/3) = 1/2`,
  `0 + (3/4)·(4/9) = 1/3`) and the `norm_num` step closes a
  non-trivial rational equality.

### Tautology / smuggling sweep

* The `RKTableau` structure (Section312.lean:66) has only data
  fields (`A`, `b`, `c`), no `Prop` fields, so the "Prop field
  should be consequence" smuggling pattern does not apply.
* No new `theorem` re-exports a hypothesis as a conclusion.
* No `:= h_*` / `exact h_*` / `:= id` proofs in cycle 326
  additions.
* No `maxHeartbeats` raised. No `axiom` / `constant` introduced.
* New symbol matches a documented textbook source.

## Dead ends

### Plain collocation lift (cycle 324 template)

Initial cycle 326 plan was a mechanical port of cycle 324's
Radau IIA `s = 2` collocation construction. The §D audit ruled
this out at audit time — Butcher's "reflections of Radau II"
recipe for Radau IA is **not** the same as plain Lagrange
collocation. Committing the cycle 324 template values for Radau IA
would have shipped row 0 = `(0, 0)` and row 1 = `(1/3, 1/3)`,
which conflict with Butcher's printed `(1/4, -1/4)` and
`(1/4, 5/12)`. Cycle 326 §H explicitly forbids this: "STOP and
re-audit before commit — this is a smuggling failure mode".

### `RKTableau.reflection` from cycle 343

Computed `(butcherRadauIIA s = 2).reflection` per
`Section343.lean:69`:
* `b̂ = (3/4, 1/4)`
* `ĉ = (2/3, 0)`
* `Â = !![5/12, 1/4; 5/12, 1/4]`

Even with a stage permutation putting abscissae in increasing
order, this `Â` does not match Butcher's printed
`!![1/4, -1/4; 1/4, 5/12]`. So Butcher's "reflections of
Radau II" is a refined construction beyond the §343
adjoint — possibly involving the underlying collocation
matrix of Radau II rather than the Radau IIA tableau itself,
or a different sign convention. Investigating this is
multi-cycle scope and is logged as Option B in the divergence
issue.

### Strategy's Branch B target (Lobatto IIIB `s = 2`)

The cycle 326 strategy §F proposed Lobatto IIIB `s = 2` as the
fallback. Butcher line 5263 explicitly states this tableau does
not exist. Pivoted to a different Branch B (direct-form Radau IA
ship) instead.

## Discovery

1. **"Reflections of Radau II" ≠ §343 adjoint reflection**:
   Butcher's terminology in Table 344(I) for the Radau IA family
   refers to a refined reflection construction not captured by the
   bare cycle 343 `RKTableau.reflection`. Future cycles aiming at
   the canonical Radau IA collocation/reflection bridge will need
   to (a) read Butcher's nearby text more carefully to pin down
   the precise meaning of "reflections" in this context, and
   (b) likely introduce an `RKTableau.permute` operation alongside
   the §343 reflection.

2. **Lobatto IIIB `s = 2` does not exist** (Butcher line 5263):
   Future planners should NOT propose Lobatto IIIB `s = 2` as a
   target. The smallest-`s` Lobatto IIIB tableau is at `s = 3`.

3. **The direct-form ship pattern is light-weight**: just
   declaring `c`, `b`, `A` inline plus a `SatisfiesB n` example
   takes ~50 LOC and provides a useful concrete witness. This
   pattern remains available for any future textbook tableau
   whose derivation is multi-cycle scope.

4. **Pre-flight audits work**: cycle 326's §D textbook audit
   caught the divergence before any Lean was written. The
   `maxHeartbeats`/sorry-discipline pre-commit checks would not
   have caught this — it is a faithfulness issue, not a
   correctness one. Future planners should keep treating §D-style
   audits as load-bearing pre-Lean steps.

## Suggested next approach

For cycle 327, the planner has several options ranked by
expected cycle complexity:

1. **(LOW) Direct-form Lobatto IIIB `s = 3`** (or Radau I s=2,
   or Radau II s=2): mechanical ports of the cycle 326
   direct-form pattern. Each adds one `RKTableau` + one
   `SatisfiesB n` example, ~50 LOC, axiom-clean, no
   reflection-construction overhead. Lobatto IIIB `s = 3` is the
   reflection partner of Lobatto IIIA `s = 3`, and `s = 3` is
   the smallest available `s` for Lobatto IIIB per Butcher.
2. **(MEDIUM) Investigate Butcher's "reflections of Radau II"**:
   read pp. 220–230 closely, identify the precise meaning, and
   plan a future cycle that builds an `RKTableau.permute`
   operation + the refined reflection definition. This unlocks
   the canonical Radau IA collocation/reflection bridge.
3. **(MEDIUM) Phase B.2 polynomial-exactness `thm:344A`** (the
   `2s − 2` / `2s − 3` headline): still multi-cycle per cycles
   323/324/325, but the polynomial-family infrastructure is now
   sufficiently mature that a `B(2s − 2)` arm for Radau I `s = 2`
   may be feasible.
4. **(HIGH) Lobatto IIIA `s = 3` (Simpson's rule)**: multi-cycle
   per cycle 325 task results; not yet scheduled by the planner.

Recommend Option 1 (Lobatto IIIB `s = 3` direct form) as the
cycle 327 candidate — it continues the §344 small-`s` ladder
without taking on the multi-cycle reflection-construction
debt. The issue
`.prover-state/issues/radau_ia_collocation_divergence.md`
remains as the scoping anchor for whoever takes Option 2.
