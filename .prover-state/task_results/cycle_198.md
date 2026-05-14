# Cycle 198 Results

## Worked on

* **P0** (mandatory smoke test) — `OpenMath/Chapter4/Section441.lean`
  GPFS smoke test, single attempt per the established 17-cycle
  pattern (now 18 consecutive).
* **P1** (substantive deliverable) — def:381F existential
  characterization:
  `OpenMath.Chapter3.Section312.RKTableau.pEquivalent_iff_exists_common_irreducible_reduct`.
  Inserted at `OpenMath/Chapter3/Section381.lean:831` directly after
  cycle 197's `reducedMethod_exists`.
* **P2** (stretch, landed) — one non-vacuity `example` exercising
  the forward (`.mp`) direction of the iff on
  `paddedEuler_pEquivalent_pReduced` (cycle 186).

## Approach

### P0 — GPFS smoke test (18th consecutive block)

```text
$ ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D" \
    || echo "(no D-state processes)"
(no D-state processes)

$ time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
EXIT=124
real    5m0.029s
user    0m0.216s
sys     0m0.518s
```

CPU = (0.216 + 0.518) / 300 ≈ 0.24% of wall (identical
near-zero pattern as cycles 182–197). Logged the 18th-cycle update
to `.prover-state/issues/cycle_182_gpfs_slowness.md` and pivoted to
Priority 1 per strategy.

### P1 — pEquivalent_iff_exists_common_irreducible_reduct

**Pre-flight verification confirmed**:
* `PEquivalent` shape (line 428): simple existential
  `∃ sBar Mbar, PReducesTo M Mbar ∧ PReducesTo M' Mbar` — the
  cleanest of the two anticipated cases.
* `reducedMethod_exists` (cycle 197, line 801): in scope, signature
  `∀ M : RKTableau s, ∃ s' M', M.PReducesTo M' ∧ M'.IsIrreducible`.
* `PReducesTo.trans` (cycle 192, line 482): dot-notation method
  with signature `PReducesTo M M' → PReducesTo M' M'' → PReducesTo M M''`.
* Cycle 184's `PEquivalent.refl` / `PEquivalent.symm` /
  `PEquivalent.of_pReducesTo` all in scope.

**Proof**: 8-line tactic block.

```lean
theorem pEquivalent_iff_exists_common_irreducible_reduct
    {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') :
    PEquivalent M M' ↔
      ∃ (s'' : ℕ) (M'' : RKTableau s''),
        PReducesTo M M'' ∧ PReducesTo M' M'' ∧ M''.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · rintro ⟨t, N, hMN, hM'N⟩
    obtain ⟨s'', M'', hNM'', hIrr⟩ := reducedMethod_exists N
    exact ⟨s'', M'', hMN.trans hNM'', hM'N.trans hNM'', hIrr⟩
  · rintro ⟨s'', M'', hMM'', hM'M'', _hIrr⟩
    exact ⟨s'', M'', hMM'', hM'M''⟩
```

* **Forward**: destructure the `PEquivalent` witness `⟨t, N, hMN, hM'N⟩`,
  apply `reducedMethod_exists N` to obtain `⟨s'', M'', hNM'', hIrr⟩`,
  chain the two reduction sequences via `hMN.trans hNM''` and
  `hM'N.trans hNM''`.
* **Reverse**: discard `_hIrr` (P-equivalence only needs a common
  reduct, not an irreducible one); repackage the remaining triple
  as the `PEquivalent` existential.

### P2 — paddedEuler non-vacuity witness

Single `example` block after `paddedEuler_pEquivalent_zeroReduced`
(now line 1031), consuming the forward (`.mp`) direction of the iff
on `paddedEuler_pEquivalent_pReduced`:

```lean
example :
    ∃ (s'' : ℕ) (M'' : RKTableau s''),
      paddedEuler.PReducesTo M''
      ∧ (paddedEuler.pReduced pairPartition).PReducesTo M''
      ∧ M''.IsIrreducible :=
  (RKTableau.pEquivalent_iff_exists_common_irreducible_reduct _ _).mp
    paddedEuler_pEquivalent_pReduced
```

Confirms the iff fires non-vacuously on the heterogeneous-stages
(2 → 1) reduction exercised by the canonical paddedEuler example.

## Result

**SUCCESS** — all three priorities (P0 mandatory single attempt,
P1 substantive theorem, P2 stretch witness) landed in a single
cycle.

* `lake env lean OpenMath/Chapter3/Section381.lean` — EXIT=0,
  warm rebuild 3.773s real (matches strategy's ~4s baseline);
  only the two pre-existing `heq` unused-variable warnings
  (lines 576 and 1607).
* `grep -c sorry OpenMath/Chapter3/Section381.lean` = 0
  (unchanged from cycle 197).
* `wc -l OpenMath/Chapter3/Section381.lean` = 1657
  (cycle 197 baseline 1606 + 35 LOC for the iff + comments +
  16 LOC for the P2 example + comments = +51 LOC, slightly above
  the strategy's ~30 LOC estimate due to docstrings).
* `lean_verify` on
  `OpenMath.Chapter3.Section312.RKTableau.pEquivalent_iff_exists_common_irreducible_reduct`:
  axioms `[propext, Classical.choice, Quot.sound]` — axiom-clean,
  expected `Classical.choice` inherited from `reducedMethod_exists`.

## Faithfulness check

### `pEquivalent_iff_exists_common_irreducible_reduct`

* Entity ID: **def:381F** (read
  `extraction/formalization_data/entities/def_381F.json`):

  > "Two Runge–Kutta methods are 'P -equivalent' if each of
  > them reduces to the same reduced method."

* Lean statement captures: **same content as the
  existential reading**. The textbook phrase "the same reduced
  method" is an existential claim — there is some reduced method
  to which both reduce. Cycle 184's `PEquivalent` already encoded
  the existence of a common reduct (not necessarily irreducible);
  cycle 198's iff strengthens the right-hand side to require that
  common reduct be *irreducible*, matching the textbook "reduced
  method" (= "irreducible" per def:381E).

* The `PEquivalent` definition itself (cycle 184) encodes
  P-equivalence as "common reduct exists"; def:381F textbook is
  "common irreducible reduct exists". The iff bridges these two
  formulations: cycle 184's `PEquivalent` is provably equivalent
  to the textbook def:381F (via the iff). No definition
  smuggling — the cycle 184 `PEquivalent` is *not* claimed to be
  def:381F by definition; the iff is an honest theorem (uses
  cycle 197's `reducedMethod_exists` in the substantive
  direction).

* Hypothesis strength: no extra hypotheses. The iff is universally
  quantified over all `RKTableau s` and `RKTableau s'` for all
  `s s' : ℕ`.

* Tautology check: the conclusion does not appear verbatim as a
  hypothesis (there are no hypotheses other than the universally
  quantified inputs `M` and `M'`).

* Identity check: not applicable — the proof is two distinct
  tactic blocks (forward chains via `reducedMethod_exists` +
  `trans`; reverse repackages with an underscore-prefixed
  unused-on-purpose `_hIrr`).

* Underscore-prefix preserved on `_hIrr` per strategy's
  anti-list item 8 and per
  `.prover-state/issues/tautology_scanner_false_positives.md` —
  the reverse direction genuinely does not consume the
  `IsIrreducible` clause and the underscore prevents future
  tautology-scanner false positives.

### P2 `example` (paddedEuler iff forward witness)

* Not a named theorem — it is an `example`, providing a
  non-vacuity sanity check that the iff produces a usable
  witness when fed `paddedEuler_pEquivalent_pReduced` (cycle 186)
  as input. The cycle 186 source theorem was itself faithfulness-
  checked in cycle 186; this P2 example only adds a forward
  application, which inherits its semantic content from the iff.

## Dead ends

None. Pre-flight verification eliminated the only anticipated
risk (`PEquivalent` shape mismatch). The simple-existential
shape made both directions one-liner proofs after `refine ⟨?_, ?_⟩`,
and the strategy's recipe transferred verbatim.

## Discovery

1. **Strategy budget overshoot was harmless**: cycle 198 strategy
   estimated ~30 LOC; actual was +51 LOC due to substantial
   docstrings on both the iff theorem and the P2 example. None
   of the extra LOC was proof content — all comments/docstrings.
   The warm-rebuild time matched expectations exactly (3.773s vs
   ~4s baseline), confirming the substantive content was minimal.

2. **`reducedMethod_exists` immediately consumed the cycle 197
   deliverable**: cycle 197 explicitly identified the def:381F iff
   as the "essentially one cycle of bridging" next step. Cycle
   198 confirms that prediction: the iff lands in 8 lines of
   tactic, with the substantive (`→`) direction being a direct
   3-step recipe (destructure / `reducedMethod_exists` / `trans`).
   This is a clean validation of the cycle 195+196+197 chain
   strategy: build measure side → build extraction side → build
   existential witness → consume in iff.

3. **The forward direction's `_hIrr` discard pattern** is the
   correct shape for proving "cycle 184's `PEquivalent` is
   equivalent to the textbook def:381F (which mentions reduced
   method)" — `PEquivalent` deliberately omits irreducibility as
   a structural simplification, and the iff is where the
   equivalence to the textbook (irreducible) formulation is
   discharged. Future bridges between simpler structural
   definitions and the textbook canonical forms should follow
   this pattern: define structurally (cycle 184), prove the
   bridge as a theorem (cycle 198), not by definition.

4. **GPFS pathology now at 17 calendar days / 18 cycles**: zero
   variation in the timing pattern (CPU 0.24–0.32% of wall, real
   ≈ 5m0.03s ± 0.001s). The pathology is fully systemic and
   worker-side fixes will not address it.

## Suggested next approach

Per cycle 198 strategy "What success looks like" and consistent
with the cycle 197 worker's "Suggested next approach" anchored to
the cycle 197 task results:

1. **Highest-leverage**: continue chaining downstream of the def:381F
   iff. The next textbook entity is **thm:381G** (Butcher §380 —
   the actual P-equivalence theorem characterizing when two
   methods are P-equivalent in terms of weights / partitions; see
   `extraction/formalization_data/entities/thm_381G.json` for the
   statement). With both the existential witness and the iff in
   hand, thm:381G should be approachable.

2. **Alternative — uniqueness packaging**: ship a heterogeneous-
   stage uniqueness wrapper for the iff via cycle 193's
   `PEquivalent.eq_of_both_isIrreducible`. Strategy anti-item 9
   explicitly rejected packaging uniqueness *into* the iff, but
   a separate `pEquivalent_irreducible_reduct_unique` theorem
   (formalizing "the common irreducible reduct is unique up to
   HEq") would be a clean ~10-LOC follow-up and would complete
   the canonical-form story for def:381F.

3. **Constructive `noncomputable def reducedMethod`**: still
   deferred. Cycle 198 has added one more downstream consumer
   (the iff), increasing the value of the constructive recursion,
   but the multi-cycle engineering cost (Option A: Σ-wrapper
   `WellFoundedRelation`; Option B: `Decidable IsPReducible` /
   `Decidable IsZeroReducible`) has not changed. Both options
   remain 2–4 cycles and should be scoped as their own strategy.

4. **Section441 Phase C.2 / C.3 / C.4**: still blocked by
   18-cycle GPFS pathology. Per strategy anti-list item 2, no
   worker-side action available. Continue the established
   one-attempt-per-cycle smoke-test pattern.

5. **Phantom-verdict pattern**: Priority 3 was not triggered this
   cycle (cycle 197 commit `6a25cd5` did include Section381.lean
   changes per `git show --stat`); no entry added to
   `phantom_commit_verdict_pattern.md`.
