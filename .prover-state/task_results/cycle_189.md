# Cycle 189 Results

## Worked on

* Priority 0: GPFS smoke test on `OpenMath/Chapter4/Section441.lean`
  (HEAD, unchanged since cycle 184). 9th consecutive timeout.
* Priority 2 Deliverables A–C on `OpenMath/Chapter3/Section381.lean`:
  - **A**: `RKTableau.PEquivalent.toPhiEquivalent` — the
    `def:381F → def:381B` bridge (easy direction of `thm:381H`).
  - **B**: `RKTableau.PEquivalent.of_isZeroReducibleVia` — direct
    corollary mirroring `PEquivalent.of_pReducesTo` for 0-reduction.
  - **C**: two `paddedEuler` Φ-equivalent witnesses derived via the
    bridge — `paddedEuler_phiEquivalent_self_via_PEquivalent` and
    `paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent`.

## Approach

### Priority 0 (GPFS smoke test)

`time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
on HEAD: EXIT=124, real 5m0.047s, user 0m0.291s, sys 0m0.909s.
CPU = 0.40% of wall — same near-zero pattern as cycles 182–188,
consistent with mathlib olean fetching from GPFS being the
bottleneck. Appended the 9th timeout to
`.prover-state/issues/cycle_182_gpfs_slowness.md` and pivoted to
Priority 2.

### Priority 2 (Section381 deliverables)

**Deliverable B placement — `PEquivalent.of_isZeroReducibleVia`.**
Inserted immediately after `PEquivalent.of_pReducesTo` in the
`OpenMath.Chapter3.Section312.RKTableau` namespace (file line 451 in
the post-edit file). The proof composes `PReducesTo.zeroStep` with
`PReducesTo.refl` (giving `PReducesTo M (M.zeroReduced inP1)`) and
funnels the result through `PEquivalent.of_pReducesTo`. Body is
4 lines.

**Deliverable A placement — `PEquivalent.toPhiEquivalent`.**
The cycle 189 strategy proposed placing this after
`PEquivalent.trans_of_middle_isIrreducible` (~line 497) in the
`Section312.RKTableau` namespace. That ordering does not type-check
because `PhiEquivalent.of_pReducesTo` is defined later in the file
(line 1086 in the pre-edit file, in the `Section381` namespace),
and Deliverable A's body composes `PhiEquivalent.of_pReducesTo`
twice with `PhiEquivalent.symm` and `.trans`.

Resolution: place the theorem after `PhiEquivalent.of_pReducesTo`
(file line 1118 in the post-edit file). To preserve dot notation
`(h : PEquivalent _ _).toPhiEquivalent` (used by Deliverable C),
the theorem must live in `OpenMath.Chapter3.Section312.RKTableau`
where `PEquivalent` is defined. The edit ends the `Section381`
namespace, opens `Section312.RKTableau` with
`open OpenMath.Chapter3.Section381`, declares the theorem, then
re-opens `Section381` with the original `open` directives so the
existing `paddedEuler_phiEquivalent_zeroReduced` (cycle 188) and
the new Deliverable C witnesses retain their context.

The body matches the strategy verbatim:

```lean
theorem PEquivalent.toPhiEquivalent {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} :
    PEquivalent M M' → PhiEquivalent M M'
  | ⟨_, _, hM, hM'⟩ =>
      (PhiEquivalent.of_pReducesTo hM).trans
        (PhiEquivalent.of_pReducesTo hM').symm
```

**Deliverable C placement — paddedEuler bridge witnesses.**
Inserted in the `Section381` namespace (with the `Section310` /
`Section312` opens active) immediately after the existing
`paddedEuler_phiEquivalent_zeroReduced`. Both proofs use dot
notation through Deliverable A:

```lean
theorem paddedEuler_phiEquivalent_self_via_PEquivalent : ... :=
  (RKTableau.PEquivalent.refl paddedEuler).toPhiEquivalent

theorem paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent : ... :=
  paddedEuler_pEquivalent_zeroReduced.toPhiEquivalent
```

The `RKTableau.PEquivalent.refl` qualifier is needed for the first
witness because `PEquivalent` is not in the `Section381` namespace.
The second uses the cycle 188 witness `paddedEuler_pEquivalent_zeroReduced`
(line 750 area in the post-edit file) directly, since that's a
local `Section381` declaration.

## Result

**SUCCESS.** All Priority 2 deliverables compiled and verified:

* `lake build OpenMath.Chapter3.Section381` exited 0 in 3.6 s
  (cached oleans warm).
* `time lake env lean OpenMath/Chapter3/Section381.lean` exited 0
  in 1m25s wall on the post-edit file.
* `grep -c sorry OpenMath/Chapter3/Section381.lean` → `0`.
* Tautology / identity scanner against the file → no hits.
* Axiom-cleanliness verified for all four new theorems:
  - `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.of_isZeroReducibleVia`
    → `[propext, Classical.choice, Quot.sound]`.
  - `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.toPhiEquivalent`
    → `[propext, Classical.choice, Quot.sound]`.
  - `OpenMath.Chapter3.Section381.paddedEuler_phiEquivalent_self_via_PEquivalent`
    → `[propext, Classical.choice, Quot.sound]`.
  - `OpenMath.Chapter3.Section381.paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent`
    → `[propext, Classical.choice, Quot.sound]`.

## Faithfulness check

### `PEquivalent.toPhiEquivalent` (Deliverable A)

* **Entity**: not a Butcher-numbered theorem — this is the easy
  direction of `thm:381H` ("Equivalent ↔ P-equivalent ↔
  Φ-equivalent"). Statement: P-equivalent methods are
  Φ-equivalent.
* **Lean statement captures**: same content. Hypothesis
  `PEquivalent M M'` (def:381F) and conclusion `PhiEquivalent M M'`
  (def:381B) are exactly the textbook predicates for "P-equivalent"
  and "Φ-equivalent" respectively.
* **Tautology check**: conclusion `PhiEquivalent M M'` does not
  appear as a hypothesis (the hypothesis is `PEquivalent M M'`,
  a different predicate involving `PReducesTo` to a common reduct;
  `PhiEquivalent` is pointwise equality of all elementary
  weights). No tautology.
* **Identity check**: proof composes three named lemmas
  (`PhiEquivalent.of_pReducesTo` twice, `.symm`, `.trans`) — not
  `exact h`.
* **Hypothesis strength check**: only `PEquivalent M M'` —
  matches what the textbook uses.
* **Definition smuggling check**: no new `def`/`structure`.

### `PEquivalent.of_isZeroReducibleVia` (Deliverable B)

* **Entity**: not Butcher-numbered — internal corollary of
  def:381C (0-reduction) and def:381F (P-equivalence).
* **Lean statement captures**: weaker form of the textbook claim
  that a method is equivalent to its 0-reduction. We prove it
  for *P-equivalence* (def:381F), not full equivalence (def:381A);
  the latter requires `Equivalent` which is the semantic-output
  notion. This is the "P-side" version.
* **Tautology check**: hypothesis is
  `IsZeroReducibleVia inP1 ∧ ∃ i, inP1 i = false`; conclusion is
  `PEquivalent M (M.zeroReduced inP1)`. Different predicates.
* **Identity check**: proof composes `PReducesTo.zeroStep`,
  `PReducesTo.refl`, and `PEquivalent.of_pReducesTo`.
* **Hypothesis strength check**: matches `PReducesTo.zeroStep`'s
  constructor signature (which already encodes def:381C's
  hypotheses faithfully — verified in cycle 188).
* **Definition smuggling check**: no new `def`/`structure`.

### `paddedEuler_phiEquivalent_self_via_PEquivalent` (Deliverable C₁)

* **Entity**: non-vacuity witness, not a textbook theorem.
* **Lean statement captures**: trivially true (everything is
  Φ-equivalent to itself, since `PhiEquivalent.refl` already
  exists). The point is to exercise `PEquivalent.toPhiEquivalent`
  on the canonical reflexive `PEquivalent` witness.
* **Tautology check**: not a tautology in the strict sense —
  the proof goes through `PEquivalent.refl` then `toPhiEquivalent`,
  so it's an *alternative derivation* of the trivial fact, not a
  re-export. Distinct from `PhiEquivalent.refl paddedEuler`.
* **Identity check**: proof is
  `(RKTableau.PEquivalent.refl paddedEuler).toPhiEquivalent`,
  composing two named lemmas. Not `exact h`.
* **Hypothesis strength check**: no hypotheses.

### `paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent` (Deliverable C₂)

* **Entity**: alternative derivation of cycle 188's
  `paddedEuler_phiEquivalent_zeroReduced`.
* **Lean statement captures**: identical statement as cycle 188's
  `paddedEuler_phiEquivalent_zeroReduced`, but proved via the
  P-equivalence intermediary
  (`paddedEuler_pEquivalent_zeroReduced` from cycle 188 →
  `toPhiEquivalent`) instead of the direct
  `PhiEquivalent.of_pReducesTo paddedEuler_pReducesTo_zeroReduced`
  used by cycle 188.
* **Tautology check**: conclusion does not appear in any
  hypothesis (no hypotheses). The two derivations agreeing on
  the same statement validates that the bridge is consistent
  with the direct construction.
* **Identity check**: proof composes
  `paddedEuler_pEquivalent_zeroReduced` with
  `PEquivalent.toPhiEquivalent`. Not `exact h`.
* **Hypothesis strength check**: no hypotheses.

## Dead ends

None substantive this cycle. One placement adjustment was needed
(see Approach, Deliverable A) — the strategy's proposed line 497
location for `PEquivalent.toPhiEquivalent` would have failed
because `PhiEquivalent.of_pReducesTo` (line 1086) is required and
defined later. Resolution was a clean namespace switch at the end
of the file; no proof body changes.

## Discovery

* The strategy's proposed in-file ordering for `PEquivalent.toPhiEquivalent`
  (after line 497, in `RKTableau` namespace) was incompatible with
  the existing structure of `Section381.lean`, where
  `PhiEquivalent.of_pReducesTo` lives at line 1086 in the
  `Section381` namespace and `PhiEquivalent` itself is defined at
  line 122 in `Section381`. Future cycles wanting to add bridges
  between `PEquivalent` (in `RKTableau`) and `PhiEquivalent` (in
  `Section381`) need to be placed at the very end of the file,
  after `PhiEquivalent.of_pReducesTo`, with namespace switches.

* `lake env lean OpenMath/Chapter3/Section381.lean` succeeded in
  1m25s wall — significantly faster than recent Section441
  attempts. Section381 has fewer mathlib import deps than
  Section441 (no `Polynomial`, `RatPower`, `Complex.normSq`
  machinery), which appears to keep it under the GPFS slowness
  threshold even when the broader cluster is degraded.

* `lake env lean ... ; lake env lean ...` does not refresh `.olean`
  for `#print axioms` to find new constants — `lake build
  OpenMath.Chapter3.Section381` is required to rebuild the olean
  before downstream `#print axioms` queries see the new constants.

## Suggested next approach

1. **Continue Section381 follow-up while §441 is GPFS-blocked.**
   The next-most-valuable deliverables in §380:
   - Promote the `paddedEuler_pReducesTo_zeroReduced` cycle 188
     witness to a generic `PReducesTo.of_isZeroReducibleVia` that
     mirrors a hypothetical `PReducesTo.of_isPReducibleVia`.
   - Ship `eq_of_isIrreducible_of_pEquivalent`: if the middle is
     irreducible, both endpoints reduce to it. Generalises cycle
     188's `trans_of_middle_isIrreducible` and tightens the
     irreducible-canonical-form story.
   - Deferred reverse direction of `thm:381H` (PhiEquivalent →
     PEquivalent) requires `thm:314A` (Independence of elementary
     differentials) which is unstarted in plan.md. Multi-cycle
     infrastructure scope; do not attempt as a single-cycle
     deliverable.

2. **GPFS-permitting**: The cycle 182 draft of Phase C.2 of
   `lem:441A` remains preserved at
   `.prover-state/cycle_182_draft_section441.lean` with the
   cycle 184 namespace fix already identified. If the planner
   detects GPFS health on a future cycle 0, that recipe should
   ship cleanly.

3. **No new Aristotle batch this cycle.** All three deliverables
   were 4–10 LOC of pure composition; Aristotle adds no value at
   that scale. Reserve Aristotle slots for substantive proofs
   (e.g., when Section441 reopens or when a new `thm:` requires
   non-trivial proof construction).
