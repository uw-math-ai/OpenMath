# Cycle 194 Results

## Worked on
- **Priority 0 (mandatory smoke test)**: one-shot `OpenMath/Chapter4/Section441.lean`
  compile to detect GPFS recovery; expected outcome (Branch A) = 14th consecutive
  timeout.
- **Priority 2 (substantive)**: shipped two new public theorems and one
  homogeneous-stage corollary in `OpenMath/Chapter3/Section381.lean` under
  `OpenMath.Chapter3.Section312.RKTableau` namespace, plus two non-vacuity
  examples in the outer `OpenMath.Chapter3.Section381` namespace.

## Approach

### Priority 0 — Section441 smoke test (Branch A confirmed)
1. `ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"`
   → no D-state processes.
2. `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
   → `EXIT=124`, real `5m0.029s`, user `0m0.238s`, sys `0m0.467s`
   (CPU = 0.24% of wall — identical near-zero pattern to cycles 182–193).
3. Logged the timeout in `.prover-state/issues/cycle_182_gpfs_slowness.md`
   under the new "Cycle 194 update (14th timeout)" section. No further
   Section441 work this cycle (per strategy "Branch A").

### Priority 2 — irreducible-endpoint extraction lemmas
1. Confirmed cycle 188's `eq_of_isIrreducible_of_pReducesTo` returns
   `s' = s ∧ HEq M' M` (Section381.lean:502–505), exactly the shape the
   strategy template assumed. No template direction-flip needed.
2. Inserted three new declarations immediately after cycle 193's
   `PEquivalent.eq_of_both_isIrreducible` (line 582 → new lines 584–633):
   - `PEquivalent.pReducesTo_of_left_isIrreducible`: unpacks the
     existential `PEquivalent`, applies cycle 188 to collapse the common
     reduct onto the irreducible source, then `subst`/`eq_of_heq` to
     re-type the second leg from `PReducesTo M' MMid` to `PReducesTo M' M`.
   - `PEquivalent.pReducesTo_of_right_isIrreducible`: one-line corollary
     via `h.symm.pReducesTo_of_left_isIrreducible hIrr`.
   - `PEquivalent.eq_of_both_isIrreducible_homogeneous` (Priority 3
     stretch): same-stage corollary of cycle 193's `eq_of_both_isIrreducible`,
     dropping the `HEq` packaging via `eq_of_heq` + `.symm` (the
     `HEq M' M` direction means `eq_of_heq` gives `M' = M`, so the
     `M = M'` conclusion needs `.symm`, exactly as the strategy
     anticipated).
3. Added two non-vacuity examples at the end of the outer Section381
   namespace, where the `private`
   `paddedEuler_pReduced_pairPartition_isIrreducible` witness is in
   scope:
   - `paddedEuler.PReducesTo (paddedEuler.pReduced pairPartition)` via
     `paddedEuler_pEquivalent_pReduced.pReducesTo_of_right_isIrreducible
       paddedEuler_pReduced_pairPartition_isIrreducible` — recovers
     cycle 186's `paddedEuler_pReducesTo_pReduced` through the new
     extraction lemma rather than assuming it.
   - `paddedEuler.pReduced pairPartition = paddedEuler.pReduced pairPartition`
     via `eq_of_both_isIrreducible_homogeneous` from `PEquivalent.refl`
     of the irreducible 1-stage method — exercises the homogeneous
     `HEq → Eq` collapse on a non-trivial irreducibility witness.

### Verification protocol
1. `time lake env lean OpenMath/Chapter3/Section381.lean` → `EXIT=0`,
   real `1m21.920s` (cold start; cache invalidated by the new edits, no
   warm rebuild available this cycle).
2. `grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean` → `0`.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.pReducesTo_of_left_isIrreducible`
   → axioms `[propext, Classical.choice, Quot.sound]`.
4. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.pReducesTo_of_right_isIrreducible`
   → axioms `[propext, Classical.choice, Quot.sound]`.
5. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.eq_of_both_isIrreducible_homogeneous`
   → axioms `[propext, Classical.choice, Quot.sound]`.

All three verifications axiom-clean. Two warnings reported (`unused
variable 'heq'` at lines 576 and 1352) are both pre-existing patterns
(`∃ heq : s' = s, ...` binders inside the cycle 193
`eq_of_both_isIrreducible` declaration and example), unrelated to
cycle 194 changes.

## Result

**SUCCESS** — Priority 0 confirmed Branch A (14th consecutive
GPFS-blocked timeout, logged); Priorities 2 and 3 (stretch) shipped
three theorems + two examples, all axiom-clean, sorry count remains
0.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `PEquivalent.pReducesTo_of_left_isIrreducible`
- Entity ID and textbook statement (quoted from formalization_data
  for `def:381F`):
  > Two Runge–Kutta methods are 'P-equivalent' if each of them reduces
  > to the same reduced method.
- Lean statement captures: **same content (corollary)**. The new lemma
  is a structural corollary of `def:381F` (the existential P-equivalence
  predicate) and `def:381E` (irreducibility). The conclusion
  `PReducesTo M' M` is structurally distinct from both hypotheses and
  follows from cycle 188's `eq_of_isIrreducible_of_pReducesTo` collapse.
- **Tautology check**: pass — conclusion `PReducesTo M' M` does not
  appear among hypotheses (`hIrr : M.IsIrreducible`,
  `h : PEquivalent M M'`).
- **Identity check**: pass — proof body uses `obtain`, `subst`,
  `eq_of_heq`, then `exact h₂` against a re-typed term; not a single
  `exact h`.
- **Hypothesis strength check**: pass — both `hIrr` and `h` are
  consumed; cannot weaken either.

### `PEquivalent.pReducesTo_of_right_isIrreducible`
- Same `def:381F` textbook statement applies.
- Lean statement captures: **same content (symmetric corollary)** of
  `pReducesTo_of_left_isIrreducible` via `PEquivalent.symm`.
- **Tautology check**: pass — conclusion `PReducesTo M M'` distinct
  from `hIrr : M'.IsIrreducible` and `h : PEquivalent M M'`.
- **Identity check**: pass — proof body composes
  `h.symm.pReducesTo_of_left_isIrreducible hIrr`, which inlines the
  Deliverable A proof at a swapped endpoint; not `exact h` or `id`.
- **Hypothesis strength check**: pass — both consumed.

### `PEquivalent.eq_of_both_isIrreducible_homogeneous`
- Same `def:381F` + `def:381E` textbook statement combination applies.
- Lean statement captures: **same content (homogeneous-stage corollary)**
  of cycle 193's `eq_of_both_isIrreducible`. The heterogeneous-stage
  `HEq` packaging is dropped via `eq_of_heq` because the same-stage
  case eliminates the `s' = s` cast.
- **Tautology check**: pass — conclusion `M = M'` does not appear among
  hypotheses (`hM : M.IsIrreducible`, `hM' : M'.IsIrreducible`,
  `h : PEquivalent M M'`).
- **Identity check**: pass — proof body composes `eq_of_both_isIrreducible
  hM hM' h` then `eq_of_heq` then `.symm`; real reasoning work.
- **Hypothesis strength check**: pass — homogeneous stage `s : ℕ`
  shared between `M` and `M'` is the natural specialization; cannot
  weaken either irreducibility hypothesis.

### Definition smuggling check
- N/A — this cycle introduced no new `def` or `structure`.

## Dead ends
None. The strategy template proof shape worked on the first
compile attempt; both `subst` + `eq_of_heq` and the symmetric
companion via `PEquivalent.symm` fired without modification.

## Discovery
- The `paddedEuler_pReduced_pairPartition_isIrreducible` private
  witness lives in the outer `OpenMath.Chapter3.Section381` namespace
  block (line 1264, cycle 190). The non-vacuity example consuming it
  must be placed in the same namespace block (or the witness must be
  exposed via `protected`/non-`private`); attempting reuse from a
  separate namespace block would fail with a privacy/scoping error.
  Resolution: placed both Deliverable C examples in the outer
  `Section381` namespace alongside the existing cycle 190 witnesses.
- The `last_cycle` field in `extraction/formalization_data/lean_status.json`
  is new (only the `def:381F` row carries it after this cycle). The
  cycle 194 strategy referenced it as if it were an established field;
  if other rows should adopt this pattern, that's a per-cycle followup
  worth proposing to the planner.

## Suggested next approach

Two natural follow-ups for the next cycle, in priority order:

1. **`def:381E reducedMethod` infrastructure (multi-cycle)**: the
   irreducible-endpoint extraction lemmas shipped this cycle compose
   directly with cycle 193's `eq_of_both_isIrreducible` to give
   uniqueness of the irreducible reduct *if* one exists. The remaining
   gap is **existence**: an iterated `reduce-until-irreducible` fixed
   point requires a `WellFoundedRelation` instance for either
   `PReducesTo` or the stage-count function. Cycle 194 strategy
   re-confirmed this is multi-cycle infrastructure work
   (`.prover-state/issues/reduced_method_deferred.md`).

2. **`PReducesTo`-confluence-lite via stage-count strict descent**:
   between cycles 185 (which tightened `PReducesTo.step` to require
   `sBar < s`) and cycle 188 (which added `zeroStep`), every
   non-reflexive `PReducesTo` step strictly decreases the stage count.
   This already gives a `Nat`-valued well-founded measure on the
   relation, which would let the planner state and prove
   `PReducesTo.wellFounded_of_strict` (a small, single-cycle
   deliverable) as a stepping stone toward the def:381E construction.
   Worth verifying that the `zeroStep` constructor actually decreases
   stage count too — if it does, this is genuinely
   tight (no reductions are stage-preserving), making the
   well-foundedness proof a one-liner.

3. **Optional cleanup**: extract the cycle 193 + cycle 194 examples
   in the outer Section381 namespace into named `theorem` declarations
   (currently `example`) so that downstream test files can reference
   the canonical-form recovery directly. Cosmetic, not load-bearing.
