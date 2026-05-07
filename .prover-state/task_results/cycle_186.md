# Cycle 186 Results

## Worked on

Priority 2 (GPFS still blocked for the 6th consecutive cycle) —
`def:381F` enrichment in `OpenMath/Chapter3/Section381.lean`:
promoted cycle-184/185 inline `example`/`have` witnesses to public,
named theorems exposing non-trivial heterogeneous-stage P-reduction
infrastructure for downstream consumers.

## Approach

### Priority 0 — GPFS health probe

Ran the strategy's mandatory probe
`time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
on HEAD (unchanged since cycle 184 reverted Phase C.2). Result:
EXIT=124 (timeout), wall 5m0.036s, user 0m0.265s, sys 0m0.510s
(≈0.16% CPU utilization). Pre-flight `ps -u $USER` D-state scan
returned no zombie processes, so this is pure cluster-side GPFS
load. Skipped Priority 1 per the decision tree, escalated via the
existing issue file (`cycle_182_gpfs_slowness.md`), and pivoted
to Priority 2.

### Priority 2 — Deliverable B1 (P-equivalence witness promotion)

Three cycle-184/185 building blocks were already in
`OpenMath/Chapter3/Section381.lean` as anonymous `example`s
(or in one case as a `have` chain inside the
`paddedEuler.PEquivalent paddedEuler` proof body):

1. `paddedEuler.IsPReducibleVia pairPartition` — the row-sum-
   constancy witness on `paddedEuler` via the trivial 2 ↦ 1
   partition (provable because `paddedEuler.A = 0`).
2. `paddedEuler.IsPReducible` — the existential-form predicate
   witness packing the partition + side condition + row-sum
   constancy.
3. `paddedEuler.PEquivalent (paddedEuler.pReduced pairPartition)`
   — the heterogeneous-stage (2 ↦ 1) non-reflexive P-equivalence
   witness, exercising cycle 185's tightened
   `PReducesTo.step` constructor (with `_hLt : sBar < s`).

All three were `example`s, hence not callable. Cycle 186 promoted
them to public theorems with descriptive names:

- `paddedEuler_isPReducibleVia_pairPartition`
- `paddedEuler_isPReducible`
- `paddedEuler_pEquivalent_pReduced`

Plus an intermediate single-step P-reduction witness factored out
to its own theorem (so the structure of the proof is exposed at
the top level rather than buried in a `RKTableau.PReducesTo.step`
application):

- `paddedEuler_pReducesTo_pReduced :
   RKTableau.PReducesTo paddedEuler (paddedEuler.pReduced pairPartition)`

The `paddedEuler_pEquivalent_pReduced` proof now reduces to a
one-line `RKTableau.PEquivalent.of_pReducesTo
paddedEuler_pReducesTo_pReduced`, mirroring the structure
documented in cycle 186 strategy step 1 deliverable B1.

### Deliverable B2 (Φ-equivalence witness) — deferred

Per the strategy's gating, B2 required the implication
`PReducesTo M M' → PhiEquivalent M M'` to already be shipped. A
grep for this implication in `OpenMath/Chapter3/Section381.lean`
returned nothing. Per the strategy: skip B2, file a brief note in
`lean_status.json` for `def:381B` indicating the gap, stop at B1.
Done.

## Result

**SUCCESS**. File compiles in 1m23s (≈baseline; cf. cycle 185's
~70s clean / ~4s warm). All four new public theorems are
axiom-clean per `lean_verify`:

| Theorem | Axioms |
|---|---|
| `paddedEuler_isPReducibleVia_pairPartition` | `[propext, Classical.choice, Quot.sound]` |
| `paddedEuler_isPReducible` | `[propext, Classical.choice, Quot.sound]` |
| `paddedEuler_pReducesTo_pReduced` | `[propext, Classical.choice, Quot.sound]` |
| `paddedEuler_pEquivalent_pReduced` | `[propext, Classical.choice, Quot.sound]` |

Tautology scanner (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`)
returned no matches. Sorry count: 0 → 0.

## Faithfulness check

### `paddedEuler_isPReducibleVia_pairPartition`

- Entity ID: helper for `def:381F` (P-equivalent), reusing
  `def:381D` (P-reducible)'s row-sum-constancy condition. Quoted
  from `def_381D.json`:
  > A Runge–Kutta method `(A, b, c)` is `P`-reducible' if the
  > stage index set can be partitioned into
  > `{1, 2, …, s} = P₁ ∪ P₂ ∪ ⋯ ∪ P_ŝ` and if, for all
  > `I, J = 1, 2, …, ŝ`, `Σ_{j ∈ P_J} a_{ij}` is constant for all
  > `i ∈ P_I`.
- Lean statement captures: **same content as the named-witness
  version** of def:381D's row-sum-constancy condition, instantiated
  on the concrete pair `(paddedEuler, pairPartition)`.

### `paddedEuler_isPReducible`

- Entity ID: instance of `def:381D`. Lean captures: **same content**
  (existential-form predicate, cycle 185's `sBar < s` non-triviality
  side condition discharged via `by decide`).

### `paddedEuler_pReducesTo_pReduced`

- Entity ID: instance of cycle 184's `PReducesTo` inductive
  constructor, on the concrete pair
  `(paddedEuler, paddedEuler.pReduced pairPartition)`. Captures
  **same content** as cycle 184's `PReducesTo` reflexive-transitive
  closure: `paddedEuler` reduces to its 1-stage P-reduction in one
  `step` followed by `refl`, with the cycle 185 `_hLt` side
  condition supplied via `by decide`.

### `paddedEuler_pEquivalent_pReduced`

- Entity ID: non-vacuity witness for `def:381F`. Quoted from
  `def_381F.json`:
  > Two Runge–Kutta methods are `$P$-equivalent' if each of them
  > reduces to the same reduced method.
- Lean statement captures: **same content as the witness form**
  of def:381F: `paddedEuler` and its P-reduction
  `paddedEuler.pReduced pairPartition` are P-equivalent, witnessed
  via the common reduct `paddedEuler.pReduced pairPartition` itself
  (both `paddedEuler` and `paddedEuler.pReduced pairPartition`
  reduce to it — the former via cycle 186's named single-step
  witness, the latter via reflexivity). Heterogeneous in stage
  count (2 ↦ 1), strictly beyond cycle 184's reflexivity-only
  witness.

No content was strengthened or weakened relative to the cycle
184/185 inline `example` versions; the cycle 186 promotion is a
**naming-and-visibility-only** refactor — proofs are unchanged,
types are identical.

## Dead ends

None this cycle. The B1 promotion was a clean refactor; the only
risk was that the inline-to-named transformation might have lost
some implicit-argument inference, but `lean_verify` confirmed all
four theorems are axiom-clean and the file compiles healthily.

The Priority 1 path (Phase C.2 of `lem:441A`) was a dead end this
cycle in the structural sense — GPFS still blocks Section441
verification — but this is the documented blocker, not a fresh
dead end.

## Discovery

1. **Section381 olean cache stays warm across cycles.** Compile
   time was 1m23s — slower than cycle 185's reported ~4s warm but
   well within the ~70s clean baseline. The 1m23s suggests partial
   cache invalidation (probably from cycle 184/185 edits to
   `Section441` namespace work touching shared infrastructure?
   Worth investigating if it persists; if so the cycle 185
   "warm cache" claim may be stale).

2. **The `paddedEuler.PEquivalent paddedEuler` example at line
   680–693 still constructs its inner reduction witness inline
   rather than calling `paddedEuler_pReducesTo_pReduced`.** A
   future cycle could refactor it to use the new named theorem
   (one-line cleanup), but this is purely cosmetic and not in
   scope for cycle 186 per the strategy's "do not modify [...]
   beyond [strategy items]" rule.

3. **Φ-equivalent / P-equivalent linkage gap.** The implication
   `PReducesTo M M' → PhiEquivalent M M'` (which would let
   P-equivalence witnesses pipe to Φ-equivalence ones, per
   Butcher's §380 motivation) is not yet a Lean theorem. Recorded
   in `lean_status.json` for `def:381B`. Provable: a P-reduction
   step preserves elementary weights stage-by-stage (this is
   essentially the content of Butcher's row-sum-constancy
   argument), and reflexivity is trivial; transitive closure is
   straightforward. Estimated ~30–60 LOC, axiom-clean expected,
   suitable for a future fallback cycle if GPFS remains blocked.

## Suggested next approach

### If GPFS recovers (Section441 smoke test completes <5 min)

Ship the cycle 182 Phase C.2 draft + cycle 184 namespace fix per
the original Priority 1 recipe (preserved verbatim in cycle 186
strategy). The draft is at
`.prover-state/cycle_182_draft_section441.lean`; the one-line
namespace fix is at draft line 1529 (documented in cycle 184's
update to `cycle_182_gpfs_slowness.md`). Three new public
theorems would land:
`ρPoly_complex_root_norm_le_one_of_stable`,
`αPoly_complex_root_norm_ge_one_of_stable`,
`aPoly_complex_root_re_nonpos_of_stable`. Sorry count: 0 → 0.

### If GPFS still blocked

Two productive Section381 follow-ups, both axiom-clean expected:

1. **Ship `RKTableau.PReducesTo.toPhiEquivalent`** (or
   `RKTableau.PhiEquivalent.of_pReducesTo`): the implication
   `PReducesTo M M' → PhiEquivalent M M'`. The proof is by
   induction on the `PReducesTo` constructor; the `step` case
   reduces to showing one P-reduction preserves elementary
   weights, which is essentially Butcher's row-sum-constancy
   argument unrolled per `RootedTree`. Once shipped, this unlocks
   B2 from cycle 186 strategy (heterogeneous-stage Φ-equivalence
   witness for `paddedEuler` ↔ `paddedEuler.pReduced pairPartition`)
   in a one-line corollary cycle.

2. **Refactor cycle 185's inline `paddedEuler.PEquivalent
   paddedEuler` example to use cycle 186's named theorems.**
   Pure cleanup: replace the inline `have hReduced` /
   `have hEquiv` block at lines 685–692 with two one-line calls
   to `paddedEuler_pReducesTo_pReduced` and
   `paddedEuler_pEquivalent_pReduced`. Trivial; could combine with
   #1 in a single cycle.

### Loop-maintainer escalation

Six consecutive Section441 smoke-test failures (cycles 182, 183,
184, 185, 186) constitute strong evidence that worker-side cycles
cannot make further Phase C.2 progress without intervention.
Recommendation block in `cycle_182_gpfs_slowness.md` lists three
remedies (cluster-admin consultation, tmpfs olean preload, smaller
smoke-test files). Cycle 186 added a formal "Cycle 186 update —
6th consecutive timeout, formal escalation" section to that file
documenting this pattern.
