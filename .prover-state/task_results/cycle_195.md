# Cycle 195 Results

## Worked on

- **Priority 0 (mandatory smoke test)**: 15th-attempt GPFS smoke test on
  `OpenMath/Chapter4/Section441.lean` — followed Branch A (still
  degraded, EXIT=124).
- **Priority 1 (substantive)**: Stage-count-descent infrastructure for
  `PReducesTo` in `OpenMath/Chapter3/Section381.lean` — shipped three
  axiom-clean theorems plus one `private` helper, all in the
  `OpenMath.Chapter3.Section312.RKTableau` namespace:
  - `card_filter_true_lt_of_exists_false` (private helper, shared
    between `size_le` and `size_lt_of_zeroStep`)
  - `PReducesTo.size_le`
  - `PReducesTo.size_lt_of_step`
  - `PReducesTo.size_lt_of_zeroStep`
- **Priority 2 (stretch)**: Skipped — Priority 1 plus the bookkeeping
  consumed the cycle budget on the post-edit cold compile (Section381
  cold compile measured 1m12s after the new edits invalidated the
  cached `.olean`).

## Approach

### Priority 0 (smoke test, 15th attempt)

Pre-flight `ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[
]*[0-9]+ +D"` returned no D-state processes. Single-shot
`time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
produced:

```
real    5m0.031s
user    0m0.238s
sys     0m0.722s
EXIT=124
```

CPU utilisation 0.32% of wall time — identical near-zero signature to
the prior 14 timeouts. No retry. Logged the 15th-timeout row to
`.prover-state/issues/cycle_182_gpfs_slowness.md` under a new
"Cycle 195 update (15th timeout)" section. Pivoted to Priority 1 per
strategy.

### Priority 1 (P-reduction stage-count descent)

Followed the cycle 195 strategy's three-theorem deliverable list
verbatim, with one structural refinement (factoring out the shared
card-filter argument as a `private` helper rather than duplicating it
inline). The placement decision: immediately after cycle 194's
`PEquivalent.eq_of_both_isIrreducible_homogeneous` (line 626 in the
pre-edit file), before the `### Definition 381A` comment, keeping the
new lemmas inside `namespace OpenMath.Chapter3.Section312.RKTableau`.

The helper `card_filter_true_lt_of_exists_false` derives
`(Finset.univ.filter (fun i : Fin s => inP1 i = true)).card < s` from
`hP0 : ∃ i, inP1 i = false` via `Finset.filter_ssubset` (gives `⊂
Finset.univ`) followed by `Finset.card_lt_card` and a `simpa
[Finset.card_univ, Fintype.card_fin]` cleanup. Pre-implementation
verified the lemma names against `.lake/packages/mathlib/Mathlib/Data/
Finset/{Card,Filter}.lean`:

- `Finset.filter_ssubset` (`Mathlib/Data/Finset/Filter.lean:133`):
  `s.filter p ⊂ s ↔ ∃ x ∈ s, ¬p x`.
- `Finset.card_lt_card` (`Mathlib/Data/Finset/Card.lean:298`):
  `s ⊂ t → #s < #t`.

The strategy also flagged `Finset.card_filter_add_card_filter_not`
(formerly `filter_card_add_filter_neg_card_eq_card`) as an
alternative; the `filter_ssubset` path is more direct (no
two-step `omega` chase) and was preferred.

For `PReducesTo.size_le`, the proof inducts on the three
`PReducesTo` constructors:

- `refl _` → `le_refl _` (homogeneous case, `s' = s`).
- `step _ hLt _ _ ih` → `ih.trans hLt.le` (the `step` constructor's
  `_hLt : sBar < s` combined with `ih : s'' ≤ sBar`).
- `zeroStep inP1 hP0 _ _ ih` → `ih.trans
  (card_filter_true_lt_of_exists_false hP0).le` (the helper supplies
  `|P₁| < s`).

The two strict-descent corollaries are one-liners on top of `size_le`:

- `size_lt_of_step` ⇒ `lt_of_le_of_lt hRest.size_le hLt`.
- `size_lt_of_zeroStep` ⇒ `lt_of_le_of_lt hRest.size_le
  (card_filter_true_lt_of_exists_false hP0)`.

### Bookkeeping

1. Updated `extraction/formalization_data/lean_status.json` def:381F
   row's narrative with a cycle 195 paragraph and bumped `last_cycle`
   from 194 to 195.
2. Updated `plan.md` Chapter 3 def:381F row's narrative with a
   matching cycle 195 paragraph (followed the existing cycle-by-cycle
   bullet style).
3. Wrote this task results file.

## Result

**SUCCESS** — all three theorems compile axiom-clean.

### Compile verification

```
$ time lake env lean OpenMath/Chapter3/Section381.lean
[no errors]
real    1m11.867s
user    0m2.662s
sys     0m3.225s
EXIT=0
```

Two unused-variable warnings on lines 576 and 1415 are pre-existing
(cycle 191 / cycle 193 `heq` parameters); none in cycle 195 code.

### Sorry count

```
$ grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean
0
```

### Axiom-cleanness (via `lean_verify` MCP tool — not `#print axioms`)

| Theorem | Axioms |
|---|---|
| `OpenMath.Chapter3.Section312.RKTableau.PReducesTo.size_le` | `[propext, Classical.choice, Quot.sound]` |
| `OpenMath.Chapter3.Section312.RKTableau.PReducesTo.size_lt_of_step` | `[propext, Classical.choice, Quot.sound]` |
| `OpenMath.Chapter3.Section312.RKTableau.PReducesTo.size_lt_of_zeroStep` | `[propext, Classical.choice, Quot.sound]` |

All three on the standard Mathlib trio — no `sorry`, no `axiom`,
no `Classical.choice`-beyond-the-baseline. Verified against the
in-process `.olean`, sidestepping the stale-`.olean` trap.

## Faithfulness check

The three theorems are *helper lemmas about an inductive predicate*,
not textbook-named entities — `PReducesTo` itself encodes Butcher
§380's P-reduction relation (def:381D + def:381C combined into a
single reflexive-transitive closure), and the stage-count-descent
lemmas are Lean-side scaffolding for the deferred def:381E
`reducedMethod` construction.

The textbook does not give these lemmas explicit names, but the
content is implicit in Butcher §380:

- **`PReducesTo.size_le`** — the entire textbook discussion of
  "reducing" a Runge–Kutta method to its irreducible form presupposes
  that each reduction step does not enlarge the stage count. Butcher
  §380, paragraph after def:381D, observes "the number of stages of
  the reduced method is at most that of the original" (paraphrased);
  this lemma is the Lean statement of that observation iterated over
  arbitrary reduction sequences.

- **`PReducesTo.size_lt_of_step`** — likewise implicit in def:381D's
  side condition `ŝ < s` (Butcher §380, "with the number of blocks
  strictly less than the number of stages"); the Lean constructor
  `PReducesTo.step` already requires `_hLt : sBar < s` to faithfully
  encode this side condition (cycle 185 closure of the original
  cycle-184 soundness gap), so this lemma is the immediate downstream
  consequence at the reflexive-transitive-closure level.

- **`PReducesTo.size_lt_of_zeroStep`** — similarly implicit in
  def:381C's "non-empty P₀" requirement: deleting a non-empty P₀
  strictly decreases the stage count. The Lean constructor
  `PReducesTo.zeroStep` already requires `_hP0 : ∃ i, inP1 i = false`
  (cycle 188 introduction); this lemma exposes the strict-descent
  consequence.

The Lean statements match textbook intent: each cite the constructor
hypothesis as input and produce the strict-descent conclusion on the
underlying `ℕ` stage-count parameter. No definition smuggling — the
lemmas are genuinely doing work (they require induction on
`PReducesTo` for `size_le`, then combine with constructor
hypotheses for the strict-descent siblings).

### Tautology / identity / hypothesis-strength checks

- **Tautology check**: none of the three conclusions appear verbatim
  as a hypothesis. `size_le`'s `s' ≤ s` is not given; it is derived
  from the structure of the `PReducesTo` proof. Same for the strict
  siblings.
- **Identity check**: `size_lt_of_step` is `lt_of_le_of_lt
  hRest.size_le hLt`; this is *not* `exact h` — it consumes
  `hRest.size_le` (a genuine theorem-call) plus `hLt` (a constructor
  hypothesis). `size_lt_of_zeroStep` likewise. `size_le` requires a
  three-case induction. None are vacuous.
- **Hypothesis strength**: `size_lt_of_step` takes `(P : PPartition
  s sBar)`, `(hLt : sBar < s)`, `(_hRed : M.IsPReducibleVia P)`,
  `(hRest : PReducesTo (M.pReduced P) M'')` — exactly the four
  arguments the `PReducesTo.step` constructor consumes. None are
  stronger than the constructor itself. Likewise `size_lt_of_zeroStep`.
- **Absent theorem check**: no in-file comments promise theorems not
  present.

## Dead ends

None this cycle — the proofs landed first-try, no rework. The
strategy's pre-flight name verification against vendored Mathlib
(`Finset.filter_ssubset`, `Finset.card_lt_card`) was confirmed
before writing; the alternative
`Finset.card_filter_add_card_filter_not` was identified as
applicable but unnecessary since `filter_ssubset` gives the
strict-subset → strict-card jump directly.

The pre-emptive `private` helper extraction (factoring out
`card_filter_true_lt_of_exists_false`) avoided duplicating the
4-line `filter_ssubset` + `card_lt_card` argument between `size_le`'s
`zeroStep` case and `size_lt_of_zeroStep` — a small style win the
strategy flagged as optional ("factor into a `have` shared between
the two if convenient — or expose as a separate `private` lemma").

## Discovery

- **Heterogeneous-stage induction principle for `PReducesTo`**: the
  `induction h with` tactic on a `PReducesTo` proof gives access to
  the inductive hypothesis `ih` whose form follows the motive (in
  this case `s' ≤ s`). The three-case pattern (`refl` / `step` /
  `zeroStep`) is now confirmed-working not just for transitivity
  (cycle 192) and the Φ-equivalence bridge (cycles 187–188) but also
  for *stage-count metric* arguments. This generalises to any
  ℕ-valued descent-with-equality argument and may be useful for
  other reductions in the §380 / §381 family.

- **Mathlib's `Finset.filter_ssubset` is a clean entry point**: when
  the goal is "filter card < universe card", `filter_ssubset` +
  `card_lt_card` is one step shorter than the alternative
  `card_filter_add_card_filter_not` + `omega` path. The trade-off:
  `filter_ssubset` requires constructing a *single* witness in the
  iff; `card_filter_add_card_filter_not` requires the additive
  partition. For "exists a counter-example" hypotheses,
  `filter_ssubset` wins.

- **`simp [hi]` closes Boolean disequality after substitution**:
  given `hi : inP1 i = false`, the goal `¬ (inP1 i = true)` reduces
  to `¬ (false = true)` after `simp [hi]`, which is decided by
  `Bool` reflection lemmas in the default simp set. No need for an
  explicit `Bool.false_ne_true`.

## Suggested next approach

1. **Priority 0** remains the §441 GPFS smoke test (16th attempt) —
   one-shot 300s timeout. If Branch A fires again, proceed to
   Priority 1.

2. **Priority 1 (substantive, Branch A path) — next infrastructure
   step for def:381E `reducedMethod`**: with the cycle 195 descent
   lemmas in hand, the next single-cycle deliverable is one of:

   **Option A — `IsPReducible` / `IsZeroReducible` choice destructor**:
   ship `Classical.choose`-style destructor functions that, given
   `M.IsPReducible`, expose the partition witness `P : PPartition s
   sBar` plus its `sBar < s` hypothesis and the
   `IsPReducibleVia` proof. Likewise for `IsZeroReducible`. These
   are needed to *call* the cycle 195 descent lemmas inside the
   eventual `reducedMethod` definition (which must extract the
   partition from the existential `IsReducible` predicate at each
   step). Should be ~4–6 short definitions; axiom-clean. Estimated
   scope: one cycle.

   **Option B — Σ-wrapper packaging for heterogeneous-stage
   `PReducesTo`**: define `RKTableauSig := Σ s, RKTableau s` and
   lift `PReducesTo` to a homogeneous relation on `RKTableauSig`
   (carry the stage count along). This is the *packaging* step
   referenced in the cycle 195 strategy's "What NOT to try" section
   — flagged as multi-cycle, but the *definition* + *lift lemma*
   alone (without the full `WellFoundedRelation` instance) might
   fit in a single cycle. The `WellFoundedRelation` discharge would
   then be a follow-up cycle consuming the cycle 195 descent lemmas
   directly.

   **Option C — well-foundedness of stage count alone**: state and
   prove `WellFounded (PReducesToOnSig)` *without* the Σ-wrapper,
   using `WellFounded.onFun` with a stage-count projection (much
   cleaner than building a separate Σ structure). This is the
   minimal-engineering path; it requires Option B-style packaging
   only at the projection level, and may close in a single cycle if
   the projection lemma is straightforward.

   The planner should pick between these based on which leads most
   directly to the eventual `reducedMethod` definition. Cycle 195
   recommends **Option A** as the safest single-cycle deliverable
   (no new infrastructure types, just destructor functions
   consuming `Classical.choose` against the existential predicates;
   the well-foundedness packaging questions can wait).

3. **Priority 2 (stretch)**: the cycle 195 strategy's deferred
   Priority 2 (promoting cycle 194's `example`s at lines 1351,
   1368, 1379 to named theorems) remains available; cycle 196 can
   pick this up if Priority 1 closes early.
