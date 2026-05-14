# Cycle 194 Strategy

## Context

Cycle 193 shipped `PEquivalent.eq_of_both_isIrreducible` (canonical-form
half of def:381E) and `PReducesTo.toPhiEquivalent` (caller-ergonomics
alias) in `OpenMath/Chapter3/Section381.lean`, both axiom-clean. Sorry
count = 0. Section441 hit its 13th consecutive GPFS-blocked timeout.

Branch HEAD is `1dc230a`. State to verify before doing any work:

```
git log -1 --format='%H %s'
# Expected: 1dc230a Cycle 193 — §380 PEquivalent.eq_of_both_isIrreducible ...
grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean
# Expected: 0
```

If those don't match, escalate (the cycle 180 phantom-verdict pattern
may have struck again — see
`.prover-state/issues/phantom_commit_verdict_pattern.md`).

## Priority 0 — Section441 smoke test (one-shot, mandatory)

Run **exactly once**:

```bash
ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"
# Expect no D-state zombies. If any, skip the smoke test entirely
# (zombies will distort the result; log the zombie state instead).

time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
# Expected: EXIT=124 or 143 after exactly 300s, near-zero CPU (~0.2-0.7%).
# If unexpectedly clean (<5 min), GPFS has recovered — see "Branch B" below.
```

**Branch A (expected: 14th consecutive timeout)**: log the timeout in
`.prover-state/issues/cycle_182_gpfs_slowness.md` under a new "Cycle
194 update" section. Continue to Priority 2 immediately. Do NOT
re-attempt the smoke test, do NOT submit Section441 work to Aristotle
(loop-maintainer escalation already in flight via
`phantom_commit_verdict_pattern.md` and `cycle_182_gpfs_slowness.md`).

**Branch B (unexpected: GPFS recovered)**: replace
`OpenMath/Chapter4/Section441.lean` with the cycle 182 draft from
`.prover-state/cycle_182_draft_section441.lean` AND apply the cycle
184 namespace fix on line 1529:

```
- M.αPoly_complex_root_norm_ge_one_of_stable hStable hψ_ne hψ_isRoot
+ LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M
+   hStable hψ_ne hψ_isRoot
```

Compile-test (`time lake env lean OpenMath/Chapter4/Section441.lean`,
budget 20 min). If clean: ship Phase C.2 (three theorems +
helpers, all axiom-clean per the cycle 184 Aristotle audit). If errors:
spend at most 30 min on simp-set ordering / naming touchups; if
unresolvable, revert and continue with Priority 2.

## Priority 2 — substantive: ship `PReducesTo`-extraction lemmas for irreducible-endpoint P-equivalences

Per cycle 193 task results §"Suggested next approach", the natural
next def:381F follow-up is extracting structural information from
`PEquivalent` when one endpoint is irreducible. The new lemma below
is provable in ≤25 LOC using cycle 188's
`eq_of_isIrreducible_of_pReducesTo` and is genuinely load-bearing for
any future def:381E `reducedMethod` work (it's the "M' reduces to its
unique irreducible reduct" half-step that downstream uniqueness
arguments will compose).

### Deliverable A (mandatory): `PEquivalent.pReducesTo_of_left_isIrreducible`

Add to `OpenMath/Chapter3/Section381.lean` in the
`OpenMath.Chapter3.Section312.RKTableau` namespace block, immediately
after cycle 193's `PEquivalent.eq_of_both_isIrreducible` (around
Section381.lean:584):

```lean
/-- If `M.IsIrreducible` and `PEquivalent M M'`, then `M'` reduces to
`M`. Direct corollary of cycle 188's `eq_of_isIrreducible_of_pReducesTo`
applied to the irreducible-source leg of the common-reduct existential. -/
theorem PEquivalent.pReducesTo_of_left_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hIrr : M.IsIrreducible)
    (h : PEquivalent M M') :
    PReducesTo M' M := by
  obtain ⟨sMid, MMid, h₁, h₂⟩ := h
  obtain ⟨h_eq, h_heq⟩ := eq_of_isIrreducible_of_pReducesTo hIrr h₁
  subst h_eq
  cases h_heq
  exact h₂
```

**Rationale for each tactic step**:
- `obtain ⟨sMid, MMid, h₁, h₂⟩ := h` — unpacks the
  `∃ sMid MMid, PReducesTo M MMid ∧ PReducesTo M' MMid` body of
  `PEquivalent`.
- `eq_of_isIrreducible_of_pReducesTo hIrr h₁` — cycle 188 result;
  verify the conclusion direction with `lean_hover_info` first
  (cycle 193 task results §"Approach Priority 2" describes it as
  returning `s' = s ∧ M' ≍ M` form, instantiated here as
  `sMid = s ∧ MMid ≍ M`). If the return is `s = sMid` instead,
  swap the `subst` direction.
- `subst h_eq` — collapses `sMid` to `s`, making `MMid` and `M` the
  same type so `h_heq : MMid ≍ M` is a `HEq` between same-type
  terms.
- `cases h_heq` (or `obtain rfl := h_heq`) — same-type HEq collapses
  to definitional equality.
- `exact h₂` — `h₂ : PReducesTo M' MMid` after `cases` becomes
  `PReducesTo M' M`.

If `cases h_heq` doesn't fire cleanly (older Lean versions sometimes
require explicit `eq_of_heq`), fall back to:
```lean
  obtain rfl := eq_of_heq h_heq
  exact h₂
```

### Deliverable B (mandatory): `PEquivalent.pReducesTo_of_right_isIrreducible`

One-line corollary via `PEquivalent.symm` (cycle 184), placed
immediately after Deliverable A:

```lean
/-- Symmetric companion of `pReducesTo_of_left_isIrreducible`: if
`M'.IsIrreducible` and `PEquivalent M M'`, then `M` reduces to `M'`. -/
theorem PEquivalent.pReducesTo_of_right_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hIrr : M'.IsIrreducible)
    (h : PEquivalent M M') :
    PReducesTo M M' :=
  h.symm.pReducesTo_of_left_isIrreducible hIrr
```

### Deliverable C (mandatory): non-vacuity witness

Cycle 188's `paddedEuler_pEquivalent_pReduced` gives `PEquivalent
paddedEuler (paddedEuler.pReduced pairPartition)`. The private witness
`paddedEuler_pReduced_pairPartition_isIrreducible` (Section381.lean
~1244, cycle 190) gives that the reduced form is irreducible. Compose:

```lean
/-- Non-vacuity exercise: `paddedEuler.pReduced pairPartition` is
irreducible (cycle 190), and `paddedEuler` is P-equivalent to it
(cycle 188), so by `pReducesTo_of_right_isIrreducible`, `paddedEuler`
reduces to it. Confirms the structural extraction theorem produces
the expected reduct on a non-trivial heterogeneous-stage example
(matches cycle 186's `paddedEuler_pReducesTo_pReduced` directly). -/
example :
    PReducesTo paddedEuler (paddedEuler.pReduced pairPartition) :=
  paddedEuler_pEquivalent_pReduced.pReducesTo_of_right_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
```

Place this in the outer `OpenMath.Chapter3.Section381` namespace
(NOT inside `RKTableau`), after the existing public theorems near
the end of the file. Confirm with `grep -n
"paddedEuler_pReduced_pairPartition_isIrreducible"
OpenMath/Chapter3/Section381.lean` that the witness is accessible
(it is `private` — if `private` blocks reuse from the outer
namespace, you may need to either (a) place the example in the
same `namespace` block where the witness lives, or (b) substitute
the public `paddedEuler_pReducesTo_pReduced` shape directly:

```lean
example : PReducesTo paddedEuler (paddedEuler.pReduced pairPartition) :=
  paddedEuler_pReducesTo_pReduced
```

— but this is trivially circular; prefer the real composition).

### Verification protocol (run all four)

1. `time lake env lean OpenMath/Chapter3/Section381.lean` — exit 0,
   warm rebuild ≤6s (cycle 193 baseline 3.7s).
2. `grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean` —
   expect 0.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.pReducesTo_of_left_isIrreducible`
   — expect axioms `[propext, Classical.choice, Quot.sound]`.
4. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.pReducesTo_of_right_isIrreducible`
   — same axiom set.

If any new identifier returns a `sorryAx`-tainted axiom set despite
no `sorry` being visible: this is the cycle-192 stale-`.olean`
gotcha (lesson from cycle 192 task results). Run `lake build
OpenMath.Chapter3.Section381` to refresh the cache before re-running
`lean_verify`.

## Priority 3 (stretch, only if Priorities 0 + 2 finish in < 2/3 of cycle)

**Do NOT** attempt full `PEquivalent.trans` (requires reduction
confluence — multi-cycle infrastructure work). Per the cycle 188
status note: "full `PEquivalent.trans` (without irreducible-middle
hypothesis) requires reduction confluence (multi-cycle work)".

**Do NOT** attempt `PEquivalent.trans_of_endpoint_isIrreducible` (the
analogue of cycle 188's `trans_of_middle_isIrreducible` with an
irreducible *end*). Analysis: from `h₁ : PEquivalent M M'` with
`M.IsIrreducible`, Deliverable A gives `PReducesTo M' M`. From
`h₂ : PEquivalent M' M''`, the witness common reduct `M_c` of M' and
M'' is *not* known to relate to M without confluence. So this is
NOT a one-cycle deliverable; mark it as deferred along with full
trans.

**If genuinely time-permitting**: add the homogeneous-stage `Eq`
corollary of cycle 193's `eq_of_both_isIrreducible`:

```lean
/-- Homogeneous-stage corollary of `eq_of_both_isIrreducible`: when the
two irreducible P-equivalent methods have the same stage count, they
are literally equal. Drops the heterogeneous `HEq` packaging for
caller convenience when the stage type is known statically. -/
theorem PEquivalent.eq_of_both_isIrreducible_homogeneous
    {s : ℕ} {M M' : RKTableau s}
    (hM : M.IsIrreducible) (hM' : M'.IsIrreducible)
    (h : PEquivalent M M') :
    M = M' := by
  obtain ⟨_, h_heq⟩ := h.eq_of_both_isIrreducible hM hM'
  exact (eq_of_heq h_heq).symm
```

Verify the `HEq` direction in cycle 193's `eq_of_both_isIrreducible`
first via `lean_hover_info`. The cycle 193 task results §"Approach
Priority 2" describes the conclusion as `HEq M' M`, so `eq_of_heq`
gives `M' = M` and the homogeneous corollary needs `.symm`. If the
actual conclusion is `HEq M M'`, drop the `.symm`.

Add a non-vacuity example (e.g. `(paddedEuler.pReduced
pairPartition)` P-equivalent with itself via `PEquivalent.refl` ⇒
`M = M`).

## What NOT to do

- **Do NOT** attempt `Section441.lean` work past the one-shot smoke
  test in Branch A. The 14-day GPFS pathology is not transient; one
  cycle's compute budget on Section441 is wasted compute.
- **Do NOT** poll any Aristotle project this cycle. No jobs are
  outstanding (cycle 193 made no submissions).
- **Do NOT** submit new Aristotle jobs for Priority 2. The proof is
  ≤10 LOC and follows the cycle 188/190/193 template; manual closure
  beats Aristotle's typical first-poll latency.
- **Do NOT** attempt full `PEquivalent.trans` or
  `trans_of_endpoint_isIrreducible` (see Priority 3 §"Do NOT").
- **Do NOT** attempt the `def:381E reducedMethod` iterated-reduction
  fixed-point construction. It requires a `WellFoundedRelation`
  instance for `PReducesTo` (or stage count) — multi-cycle
  infrastructure work, deferred per
  `.prover-state/issues/reduced_method_deferred.md`.
- **Do NOT** edit `scripts/autonomous_loop.py`. The phantom-verdict
  pattern is loop-maintainer territory.
- **Do NOT** raise `maxHeartbeats` above 200000 anywhere in the
  Lean source.
- **Do NOT** introduce `axiom` or `constant` declarations.
- **Do NOT** rename or refactor any of cycle 184–193's
  `paddedEuler_*` named witnesses without an explicit reason.
  Cycle 193's discovery (planner-strategy mismatch on
  `paddedEuler_isIrreducible`, which doesn't exist because
  `paddedEuler` is P-reducible not irreducible) suggests the
  named-witness lookup is sensitive; do a `grep -n
  "paddedEuler_pReduced_pair" OpenMath/Chapter3/Section381.lean`
  before referencing the irreducibility witness to confirm its
  current name and visibility.
- **Do NOT** use `:=` shorthand for theorems whose proofs use
  `cases` or `subst` — those tactics need `by` blocks.

## Pre-commit faithfulness checklist (apply per CLAUDE.md)

For each new theorem in Deliverables A and B:

- **Tautology check**: conclusion `PReducesTo M' M` (or `PReducesTo
  M M'`) is structurally distinct from the hypothesis `PEquivalent
  M M'` (an existential over a common reduct) and the hypothesis
  `M.IsIrreducible` (a predicate on the source). **Pass expected.**
- **Identity check**: proof body composes
  `eq_of_isIrreducible_of_pReducesTo` + `subst` + `cases` (or
  `eq_of_heq`) — not just `exact h`. Real proof work. **Pass
  expected.**
- **Hypothesis strength check**: both hypotheses are consumed
  (`hIrr` gates `eq_of_isIrreducible_of_pReducesTo`; `h` provides
  the existential to unpack). Cannot weaken. **Pass expected.**
- **Definition smuggling check**: not a `def` or `structure`. N/A.

For the Deliverable C example: not a `theorem`, no faithfulness
checks apply.

## End-of-cycle deliverables (to write)

- `.prover-state/task_results/cycle_194.md` — standard format,
  documenting Priorities 0/2/3 outcomes.
- Updates to `plan.md` def:381F row noting the new
  `pReducesTo_of_left_isIrreducible` /
  `pReducesTo_of_right_isIrreducible` deliverables (single
  paragraph appended to the existing run-on update).
- Update to `extraction/formalization_data/lean_status.json`
  def:381F row: bump `last_cycle` to 194; status remains
  `partial` (full `trans` still deferred, `def:381E` reduced
  method construction still deferred).
- `.prover-state/issues/cycle_182_gpfs_slowness.md` — append "Cycle
  194 update" with the timeout details from Branch A.

Commit message template (Branch A):

```
Cycle 194 — §380 PEquivalent.pReducesTo_of_{left,right}_isIrreducible (irreducible-endpoint extraction); §441 Phase C.2 GPFS-blocked (14th)
```

(or, if Branch B fires unexpectedly and Phase C.2 ships:)

```
Cycle 194 — §441 Phase C.2 shipped (cycle 182 draft + cycle 184 namespace fix); §380 PEquivalent irreducible-endpoint corollaries
```
