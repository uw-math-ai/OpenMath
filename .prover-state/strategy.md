# Cycle 200 Strategy

## Context inheritance

Cycle 199 shipped the **honest weaker variant**
`pEquivalent_irreducible_reduct_unique_of_sources_irreducible` (axiom-clean,
+64 LOC at `OpenMath/Chapter3/Section381.lean:866`) after pre-flight Grep
revealed that the previous strategy's primary recipe misread cycle 188's
signature direction (irreducible **source** vs irreducible **target**). The
full uniqueness theorem requires confluence of `PReducesTo` (Newman's
lemma); the multi-cycle plan is documented in
`.prover-state/issues/p_reduction_confluence_gap.md`.

Cycle 199 also produced a recon on **thm:381G**:
- Requires unformalized **thm:314A** (Independence of elementary
  differentials) — itself a 2–3 cycle deep result.
- Plus substantial subalgebra-in-ℝ^s infrastructure.
- **NOT single-cycle.** Cycle 198's "highest-leverage next" suggestion
  underestimated complexity.

Sorry count at HEAD: **0**. Axiom-clean. `Section381.lean` is 1721 LOC.

Cycle 200's job is to pick the **next concrete, single-cycle deliverable**
from the post-cycle-199 options:

* **Pivot A** (cycle 199 worker's #1 suggestion): thm:381H statement-only
  with `sorry`-tracked proof. Spec-level deliverable; proof closure waits
  on thm:381G.
* **Pivot B**: Confluence Phase 1 — first lattice-closure lemma toward
  full uniqueness. Multi-cycle plan, but each step ships meaningful
  infrastructure.
* **Pivot C**: Tackle thm:314A as thm:381G prerequisite — 2–3 cycle deep
  dive.

## Decision

**Priority 1: Ship `thm:381H` (Equivalence of equivalences) as a
sorry-first scaffold.** Single-cycle deliverable; statement is fully
faithful to Butcher §380; proof body uses cycle-199's lemma chain
modulo one tracked sorry that closes once thm:381G is shipped.

This is preferred over **Pivot B** (confluence Phase 1) because:

1. The cycle 199 issue file explicitly notes "**thm:381H is likely
   unblocked by cycle 198 alone**" — the proof of thm:381H references
   thm:381G as a black-box hypothesis, not as a uniqueness fact.
   Re-reading Butcher §380.8627–8667 confirms this.
2. The Section381 cluster has now had eight consecutive cycles of
   `PEquivalent`-flavoured work (cycles 192–199). Shipping the
   textbook landmark theorem **thm:381H** caps that arc and provides
   a clean stopping point before pivoting to thm:381G's prerequisite
   infrastructure.
3. Confluence Phase 1 (`IsPReducibleVia_join`) has unknown LOC
   profile — `PPartition` may or may not admit clean lattice structure,
   and the cycle 199 issue file's Option A is sketched at the spec
   level only. Higher risk for a single cycle.

## Mandatory pre-flight steps

### P0 — GPFS smoke test on Section441.lean (one attempt only)

Per the established 19-cycle pattern, run a single 5-min smoke test
on `OpenMath/Chapter4/Section441.lean` to confirm GPFS state:

```bash
ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D" \
  || echo "(no D-state processes)"
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

**Decision tree**:

* If EXIT=0 in <60s ⇒ GPFS healthy. Pivot: ship the cycle 182 draft
  + cycle 184 namespace fix per `lem_441A_phase_C_scoping.md`. Phase
  C.2 closure is then the cycle 200 deliverable instead of thm:381H.
* If EXIT=124 with near-zero CPU ⇒ GPFS still pathological. Append a
  "Cycle 200 update" row to `.prover-state/issues/cycle_182_gpfs_slowness.md`
  (20th consecutive timeout). Proceed to Priority 1.
* If EXIT=0 in 60–300s ⇒ partial recovery; still treat as blocked for
  cycle 200 (the cycle 182 draft compile takes >5 min even when GPFS
  is healthy). Continue to Priority 1.

**DO NOT** retry the smoke test after the first attempt. **DO NOT**
re-attempt Phase C.2 manually (4th attempt failed in cycle 184).

### P0.5 — Verify the file state

```bash
git log -1 --format='%H %s'
wc -l OpenMath/Chapter3/Section381.lean
grep -c sorry OpenMath/Chapter3/Section381.lean
```

Expected: cycle 199 commit `3ac0841`, 1721 LOC, 0 sorries. If any
disagree, escalate to consultant rather than proceeding.

## Priority 1 — `thm:381H` statement-only

### Step 1: Read the textbook statement (MANDATORY)

Read `extraction/raw_text/ch03.txt` lines ~8627–8700 directly before
writing the Lean statement. Per the cycle 199 P2 recon, thm:381H
lives in this range (after thm:381G at line 8579). **Quote the
textbook statement verbatim in the Lean docstring.**

Also read `extraction/formalization_data/entities/thm_381H.json` for
the extracted statement and dependency list. If the extracted
statement disagrees with the raw text, **trust the raw text** and
note the discrepancy in the cycle results.

The expected form (subject to textbook verification — do NOT type
the Lean statement before reading the source):

> Two Runge–Kutta methods M, M' are equivalent (def:381A) iff they
> are P-equivalent (def:381F) iff they are Φ-equivalent (def:381B).

### Step 2: Pre-flight Grep (MANDATORY — cycle 199 lesson)

Cycle 199 was burned by misreading a signature direction. Before
typing any Lean, use Grep on `OpenMath/Chapter3/Section381.lean` to
verify each cited name and its signature:

* `Equivalent` (def:381A) — what are its hypotheses?
* `PEquivalent` (def:381F) — confirmed at line 1657-ish.
* `PhiEquivalent` (def:381B) — confirmed in Section381.
* `pEquivalent_iff_exists_common_irreducible_reduct` (cycle 198) —
  the existential characterization.
* `PEquivalent.toPhiEquivalent` (cycle 187) — `PEquivalent → PhiEquivalent`
  bridge.
* `PEquivalent.of_pReducesTo` (cycle 187 alias) — alternative bridge
  name; check both.
* `reducedMethod_exists` (cycle 197) — existential irreducible reduct.

For each, record (a) the namespace, (b) the argument order, (c)
which arguments are hypotheses vs conclusions. Cycle 199's failure
was assuming target-irreducibility when cycle 188 actually requires
source-irreducibility.

### Step 3: Lean signature

```lean
/-- **Theorem 381H** (Butcher §380, p. ~287).
Two Runge–Kutta methods are equivalent iff they are P-equivalent iff
they are Φ-equivalent. -/
theorem equivalent_iff_pEquivalent_iff_phiEquivalent
    {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') :
    (M.Equivalent M' ↔ M.PEquivalent M') ∧
    (M.PEquivalent M' ↔ M.PhiEquivalent M') := by
  refine ⟨?_, ?_⟩
  · -- (def:381A ↔ def:381F) — likely needs thm:381G
    sorry
  · -- (def:381F ↔ def:381B)
    -- forward: PEquivalent.toPhiEquivalent (cycle 187)
    -- reverse: may close via cycle 197 + cycle 198 + cycle 188
    sorry
```

Adjust names to whatever Grep reveals. If thm:381H's textbook
statement is shaped differently (e.g. 3-way TFAE rather than two
iffs), reshape accordingly.

### Step 4: Attempt to close the easier half first

**The `(def:381F ↔ def:381B)` half is likely closable axiom-clean
with existing cycle 184–198 infrastructure**:

* **Forward (`PEquivalent → PhiEquivalent`)**: one-line via cycle 187's
  `PEquivalent.toPhiEquivalent`.
* **Reverse (`PhiEquivalent → PEquivalent`)**: harder. The textbook
  argument uses thm:381G-style elementary-weight independence. But
  there may be a shorter path: PhiEquivalent says
  `derivativeWeight M t = derivativeWeight M' t` for every rooted
  tree `t`; this needs to imply existence of a common irreducible
  reduct. If thm:381G is genuinely required here, defer this
  direction.

**Attempt order**:

1. Try the forward direction via `PEquivalent.toPhiEquivalent` —
   should close in 1 line.
2. Attempt the reverse direction. If you find yourself needing
   "elementary weights distinguish stages of irreducible methods",
   that IS thm:381G — defer with a `sorry` and document the
   blocker.

### Step 5: Attempt the `(def:381A ↔ def:381F)` half

This is likely the harder iff. Butcher's proof typically goes:

* **Forward (`Equivalent → PEquivalent`)**: two equivalent methods
  produce the same output for every IVP; by the trivial-IVP / linear
  argument, they have the same Φ-equivalence class; combined with
  thm:381G's distinguishability, they have the same P-reducibility
  pattern.
* **Reverse (`PEquivalent → Equivalent`)**: P-equivalent methods share
  a reduced form (cycle 198), which is canonical; the reduced form
  uniquely determines numerical output up to stage permutation.

Both directions plausibly need thm:381G or its consequences. If
neither closes in 30 minutes of manual work, defer with a `sorry`.

### Step 6: Document remaining sorries

For each `sorry` that remains, write a precise blocker comment AND
add an entry to a new issue file
`.prover-state/issues/thm_381H_deferred.md`:

* Which direction is blocked.
* What infrastructure would close it (thm:381G with its specific
  prerequisites, OR a more direct route if one is visible).
* Cross-link to `p_reduction_confluence_gap.md` and
  `lem_441A_phase_C_scoping.md` style multi-cycle plans.

### Risk assessment

* **Mathematical risk: medium**. One of the four iff-halves should
  close cleanly with existing infrastructure (`PEquivalent.toPhiEquivalent`).
  The remaining three are uncertain — could all close, or all
  defer, or mixed.
* **LOC risk: low**. Statement + docstring ≈ 40 LOC. Closed halves
  add ~10–30 LOC each. Total cycle delta likely 40–120 LOC.
* **Verification risk: low**. Section381.lean compiles in ~44s at
  HEAD (cycle 199 measurement); incremental edits should be fast.
* **Tautology risk**: if PhiEquivalent's definition is too weak, the
  `(def:381F ↔ def:381B)` half might be vacuously true. **Sanity
  check**: ensure cycle 187's `PEquivalent.toPhiEquivalent` does
  real work — if PhiEquivalent unfolds to "same `RKTableau`" then
  this whole exercise is definition smuggling. Verify before
  shipping.

### Acceptance criteria

* `OpenMath/Chapter3/Section381.lean` contains
  `equivalent_iff_pEquivalent_iff_phiEquivalent` (or the actual
  shape from the entity JSON if it differs from two-iff form).
* File compiles via `lake env lean OpenMath/Chapter3/Section381.lean`.
* Sorry count is **at most 4** (statement-only with four sorries —
  one per iff direction) or ideally **1–2** (with 1–3 directions
  closed) or **0** (all four closed if existing infrastructure
  suffices — unlikely but possible).
* `lean_status.json` row for `thm:381H` updated to `partial` (if
  sorries remain) or `formalized` (if all closed).
* Faithfulness check in cycle results: quote textbook statement
  from `raw_text/ch03.txt`, confirm Lean statement matches.

## Priority 2 (stretch, only if Priority 1 closes axiom-clean — unlikely)

If all four iff directions of thm:381H close in <2 hours and the
file recompiles clean, attempt one of:

**Option 2A — Confluence Phase 1.1**: ship `IsPReducibleVia_join` per
the cycle 199 issue file. Prerequisite verification (Grep for
existing `PPartition` lattice instance) before committing.

**Option 2B — Promote underused cycle 198/199 results**: identify any
`example` blocks in Section381.lean (cycles 184–199) that should be
promoted to named theorems. Cosmetic but low-risk.

**Option 2C — Update plan.md** to reflect thm:381H closure status
and refine the priority order of remaining §380 entities (thm:382A,
thm:386A, etc.) given the new understanding.

**Time-box: 60 minutes**. If not closing cleanly, abort. Do NOT
introduce stretched sorries for Priority 2.

## Anti-priorities (DO NOT do these)

1. **Do NOT re-attempt the cycle 199 strategy's
   `pEquivalent_irreducible_reduct_unique`** (full uniqueness without
   sources-irreducibility). Per cycle 199's analysis, this requires
   confluence reasoning that is 4–5 cycles of infrastructure. The
   weak variant shipped in cycle 199 is the right ergonomic API for
   now.

2. **Do NOT attempt thm:381G in this cycle.** Per cycle 199's recon,
   it requires thm:314A (currently unformalized) plus substantial
   linear-algebra-in-ℝ^s infrastructure (subalgebra generated by
   elementary weights). Multi-cycle, deep.

3. **Do NOT attempt thm:314A in this cycle.** Itself 2–3 cycles of
   work; not the right level for cycle 200's deliverable.

4. **Do NOT introduce `axiom` or `constant` declarations** for the
   thm:381H proof body. Sorry-first with tracked-issue is the
   approved pattern; per CLAUDE.md, `axiom`/`constant` are forbidden.

5. **Do NOT manually re-attempt Phase C.2 of `lem:441A`** (cycle 182
   draft). The local-compile path is blocked by 19-cycle GPFS
   pathology. Only the smoke test in P0 is permitted.

6. **Do NOT modify `scripts/autonomous_loop.py`** to fix the
   phantom-commit verdict pattern. Worker-side rule per CLAUDE.md;
   issue already escalated via
   `.prover-state/issues/phantom_commit_verdict_pattern.md`.

7. **Do NOT poll Aristotle** unless you submit a new job this cycle.
   No pending jobs are tracked at strategy-write time. If you submit
   one for the thm:381H proof body, single-poll discipline applies
   (do not re-poll within the same cycle).

8. **Do NOT rename hypothesis variables with `h_<name>`** patterns
   that trigger the tautology scanner. Use `h<name>` (no underscore)
   from the start. Issue `tautology_scanner_false_positives.md` is
   open but worker-side workaround stands.

9. **Do NOT skip the textbook-prose read in Step 1.** Cycle 199's
   confluence-gap issue was found precisely because the prior
   planner cited cycle 188 lemmas without verifying their direction.
   Writing thm:381H's statement without quoting the textbook is the
   same class of failure.

## Aristotle batch (optional, low priority)

If the `(def:381B → def:381F)` reverse half or either
`(def:381A ↔ def:381F)` direction doesn't close within 30 minutes of
manual attempts, **consider** submitting it as a single Aristotle job
with:
- The cycle 198 iff theorem as in-context template.
- Cycle 187/188/197 named lemmas as available citations.
- Strong induction skeleton or direct construction via
  `reducedMethod_exists`.

**Single-poll discipline**: after submission, do not re-poll within
this cycle. Continue with the other halves / Priority 2 work.
Aristotle results will be incorporated in cycle 201.

## Faithfulness reminders

Per CLAUDE.md pre-commit checklist (apply to thm:381H):

* **Definition smuggling check**: confirm Lean's `Equivalent`,
  `PEquivalent`, `PhiEquivalent` match the textbook definitions
  faithfully. Cycle 184 promoted def:381F; cycle 199's weak variant
  is documented as `_of_sources_irreducible`. The textbook
  thm:381H quantifies over ALL methods, not just irreducible ones —
  if your formalization adds an irreducibility hypothesis, that's a
  red flag.
* **Tautology check**: the conclusion of thm:381H is two iffs;
  neither side appears verbatim as a hypothesis. Good. Also: if
  `PhiEquivalent` unfolds *too easily* to `PEquivalent`, the
  `(def:381F ↔ def:381B)` half is vacuous — sanity-check by reading
  the cycle 187 `PEquivalent.toPhiEquivalent` proof and confirming
  it does real work (computes derivative weights, applies
  `Finset.sum_bij`, etc.).
* **Identity check**: the proof body must do real work. A
  `:= rfl` or `:= Iff.rfl` for any half would be a red flag.
* **Hypothesis strength check**: thm:381H's textbook statement takes
  no hypotheses beyond the two RK methods themselves. **Do not add
  irreducibility, preconsistency, or stability hypotheses** unless
  the Butcher prose explicitly requires them — if you find yourself
  needing extras, that's a signal the proof is closing the wrong way.
* **Absent theorem check**: if you defer a half with `sorry`,
  verify the issue file `thm_381H_deferred.md` is actually written
  (not just promised in a comment).

## Verification commands at end of cycle

```bash
# Compile and confirm sorry count
time lake env lean OpenMath/Chapter3/Section381.lean
grep -c sorry OpenMath/Chapter3/Section381.lean

# File size
wc -l OpenMath/Chapter3/Section381.lean

# Axiom check on new theorem
echo '#print axioms OpenMath.Chapter3.Section312.RKTableau.equivalent_iff_pEquivalent_iff_phiEquivalent' \
  | lake env lean --stdin OpenMath/Chapter3/Section381.lean
```

(Adjust namespace and theorem name to match what was actually shipped.)

Expected (best case): EXIT=0, sorry count 0, axioms
`[propext, Classical.choice, Quot.sound]`.

Expected (acceptable): EXIT=0, sorry count 1–4 (tracked in issue
file), axioms `[propext, Classical.choice, Quot.sound, sorryAx]`.

## Bookkeeping checklist

End-of-cycle updates:

1. **`extraction/formalization_data/lean_status.json`**: thm:381H row
   to `partial` or `formalized` based on outcome.
2. **`plan.md`**: thm:381H row from `[ ]` to `[~]` or `[x]`.
3. **`.prover-state/task_results/cycle_200.md`**: full result document
   per CLAUDE.md template.
4. **`.prover-state/issues/thm_381H_deferred.md`** (if any sorries
   remain): document what's blocked and on what.
5. **`.prover-state/issues/cycle_182_gpfs_slowness.md`**: append 20th
   timeout entry.
6. **Git commit** with descriptive message referencing the textbook
   theorem; push.

Cycle 200 is a clean landmark — the 200th cycle of the project. Ship
something solid.
