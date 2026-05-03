# Cycle 078 strategy — recover from cycle 077 revert

## Context

Cycle 077 was **REVERTED with score −2**. It attempted `thm:410D`
(Butcher §410 log-form order condition) and left **two unresolved
sorries**, triggering the supervisor's "sorry count increased 0→2"
revert. The two sorries are documented in
`.prover-state/issues/thm_410D_substitution.md`:

1. `coeff_eq_zero_of_coeff_subst_eq_zero` — reverse direction of
   "substitution by a unit-leading series preserves vanishing of low
   coefficients".
2. `subst_logOnePlusPS_expNegPS` — load-bearing identity
   `subst logOnePlusPS expNegPS = oneOverOnePlusPS`, equivalent to
   `exp(-log(1+w)) = (1+w)^{-1}`. Mathlib has no `PowerSeries.log`,
   so route (a) (direct coefficient computation) is required.

Cycle 077 also submitted an Aristotle batch on these two sub-lemmas
(project ID `18504be5-2481-4d60-9d7b-12b8a5cd2b47`, file
`.prover-state/aristotle_submissions/cycle_077/section410d_helpers.lean`).
At cycle 077's last check it was at 13% with ≈80 minutes elapsed.
By now (cycle 078), it may have completed.

**The cycle 077 worker's Lean infrastructure (`oneOverOnePlusPS`,
`logOnePlusPS`, `genFnLog`, the *forward* substitution lemma, and
the substitution decomposition `genFnLog M = subst logOnePlusPS
(genFn M)`) was committed in the reverted cycle and is therefore
NOT in the current `OpenMath/Chapter4/Section410.lean`.** Verify
this with `git log --oneline -5` — current HEAD must be `9dab007`
(cycle 076). If a §410D rebuild is undertaken, **all** of that
infrastructure must be reproduced; the only artifact preserved is
the Aristotle submission file `section410d_helpers.lean`.

## Top priority — DO NOT REPEAT cycle 077's failure mode

**Absolute rule: do NOT commit any new sorry to the repository this
cycle.** If you cannot fully close a theorem, either decompose it
into closable parts, or revert to a smaller target. The supervisor
reverts any cycle that increases sorry count.

If you write a sorry-first scaffold to plan a proof, that is fine
— but it MUST be either fully closed by end of cycle, or rolled
back via `git restore` before commit. Do not commit partial scaffolds.

## Priority 0 — Check Aristotle status (5 minutes, MANDATORY)

Run:

```
mcp__aristotle__get_status with project_id = "18504be5-2481-4d60-9d7b-12b8a5cd2b47"
```

Then `mcp__aristotle__download_result` if status is `COMPLETED`.

The submission file is preserved at
`.prover-state/aristotle_submissions/cycle_077/section410d_helpers.lean`
(3.3KB) — read it to see exactly which 5 sub-lemmas were submitted.
Inspect each returned proof: which of these did Aristotle close?

* `coeff_eq_zero_of_coeff_subst_eq_zero` — the reverse direction.
* `subst_logOnePlusPS_expPS` (= `1 + X` if present) — the
  load-bearing identity.
* (Plus three smaller helpers.)

**Decision rule based on Aristotle results:**

* **Both sorries closed by Aristotle** → take Path A (rebuild §410D
  fully).
* **One sorry closed, one open** → take Path B (pivot away from
  §410D — partial closure of a single direction is not worth the
  rebuild risk).
* **Neither closed** → take Path B.
* **Aristotle still IN_PROGRESS or FAILED** → take Path B.

Document the Aristotle result in `.prover-state/task_results/cycle_078.md`
regardless of which path you take.

---

## Path A — Aristotle delivered both proofs: rebuild and close §410D

This path applies **only** if Aristotle returned proofs for **both**
of the two cycle-077 sorries. Otherwise skip to Path B.

### Step 1 — Reproduce the cycle-077 infrastructure

Re-derive in `OpenMath/Chapter4/Section410.lean` (after the existing
§410C cluster from commit `9dab007`):

1. `oneOverOnePlusPS : PowerSeries ℝ` — the formal `1/(1+X)` series
   with coefficients `(-1)^n`. Define via
   `PowerSeries.mk (fun n => (-1)^n)` or analogous.
2. `logOnePlusPS : PowerSeries ℝ` — formal `log(1+X)` with
   coefficients `(-1)^(n+1) / n` for `n ≥ 1`, `0` at `n=0`.
   Use `PowerSeries.mk` and prove constant term = 0,
   `coeff 1 logOnePlusPS = 1` (the unit-leading conditions needed
   for `PowerSeries.subst`).
3. `genFnLog (M : LinearMultistepMethod k) : PowerSeries ℝ` — the
   log-form generating function. By the textbook, this equals
   `subst logOnePlusPS (genFn M)` (substitution decomposition);
   prove the decomposition lemma `genFnLog_eq_subst_genFn`.
4. `(1 + X) * oneOverOnePlusPS = 1` — algebraic identity.
5. **Forward direction** of substitution-preserves-vanishing
   (cycle 077 closed this manually; reproduce):
   `∀ p, ∀ f g, constantCoeff g = 0 → coeff 1 g = 1 →
   (∀ j ≤ p, coeff j f = 0) → ∀ j ≤ p,
   coeff j (PowerSeries.subst g f) = 0`.

Stay within the cycle 077 manual proof shapes — those compiled.

### Step 2 — Incorporate Aristotle's two proofs verbatim

Copy Aristotle's returned proofs for the two reverse-direction
sub-lemmas into the file. Verify each compiles
(`lake env lean OpenMath/Chapter4/Section410.lean`) and has clean
axioms.

### Step 3 — State and close `thm:410D`

The textbook statement (Butcher §410):

> A linear multistep formula `[α, β]` has order `p` if and only if
> `coeff j (genFnLog M) = 0` for all `0 ≤ j ≤ p`.

Bridging via the substitution decomposition + forward direction +
Aristotle's reverse direction gives the iff.

### Step 4 — Pre-commit gates

* `lake build` clean.
* `#print axioms thm_410D` shows only `[propext, Classical.choice,
  Quot.sound]`.
* Faithfulness check: `genFnLog` matches Butcher's
  `log(α(1+z)/...)` formula (or document the formal-power-series
  reformulation as an equivalence lemma).
* Update `lean_status.json::thm:410D` to `formalized`.
* Update `plan.md` to mark `thm:410D` `[x]`.
* Move `.prover-state/issues/thm_410D_substitution.md` to a
  resolution note in `task_results/cycle_078.md` (or delete it).

### Path A budget warning

If by ~70% of the cycle-time budget you have NOT completed Steps
1–3 cleanly, **STOP, restore to HEAD (`git restore .`), switch to
Path B**. Do not commit a partial Path A. The cycle 077 worker
spent the whole cycle on §410D and ended with sorries — that is
precisely the failure mode to avoid.

---

## Path B (default for most outcomes) — pivot to `lem:383A`

Take this path if Aristotle did not return both proofs, OR if
Path A's budget warning fires.

### Target: `lem:383A` — multiplicativity of forest mappings

Textbook statement (Butcher §383):

> Let α and β be multiplicative mappings from the forests to the
> real numbers. Then αβ is multiplicative.

Entity:
`extraction/formalization_data/entities/lem_383A.json`. Dependencies:
`def:381A` (already formalized as
`OpenMath.Chapter3.Section381.Equivalent`).

### Why this target is right for cycle 078

* Status: unformalized, all dependencies done, no infrastructure
  blocker.
* Risk: low. The proof is essentially "ring algebra after unfolding
  the multiplicativity equation", a few lines.
* Faithfulness: clean — Butcher's "forest" is a multiset of rooted
  trees; we already have `RootedTree`
  (`OpenMath/Chapter3/Section310.lean`, inductive
  `RootedTree | mk : List RootedTree → RootedTree`).
* Non-vacuity: trivially provided by the constant function
  `α : Forest → ℝ` with `α _ := 1`.

### Step 1 — Add `Forest` infrastructure in a new file

Create `OpenMath/Chapter3/Section383.lean`. **Do NOT** modify
`Section381.lean` or `Section310.lean` beyond the import line of
the new file.

```lean
import OpenMath.Chapter3.Section310
import Mathlib.Data.Multiset.Basic

namespace OpenMath.Chapter3.Section383

open OpenMath.Chapter3.Section310

/-- A *forest* of rooted trees — Butcher §383's underlying object
for multiplicative mappings. Encoded as a `Multiset RootedTree`
(unordered, with multiplicities). The empty forest is the unit
of the multiplicative monoid. -/
abbrev Forest : Type := Multiset RootedTree

/-- Multiplicative mapping (Butcher §383): a function from the
forest monoid to ℝ that sends the empty forest to 1 and preserves
multiset addition (i.e. forest concatenation). -/
def IsMultiplicative (α : Forest → ℝ) : Prop :=
  α 0 = 1 ∧ ∀ s t : Forest, α (s + t) = α s * α t
```

**Faithfulness note**: Butcher's "forest" is a multiset of rooted
trees, so `Multiset RootedTree` is the literal encoding. The
`α 0 = 1` clause is the standard normalization (the empty product
is 1) implicit in Butcher's exposition. If on inspection of the
surrounding §383 prose you find Butcher does NOT include the
empty-forest normalization, drop `α 0 = 1` and adjust the lemma
proof accordingly — but document the divergence in the cycle 078
faithfulness check.

### Step 2 — Prove `lem:383A`

```lean
/-- Butcher §383 Lemma 383A — pointwise product of multiplicative
mappings is multiplicative. -/
theorem multiplicative_mul {α β : Forest → ℝ}
    (hα : IsMultiplicative α) (hβ : IsMultiplicative β) :
    IsMultiplicative (fun f => α f * β f) := by
  refine ⟨?_, ?_⟩
  · simp [hα.1, hβ.1]
  · intro s t
    rw [hα.2 s t, hβ.2 s t]
    ring
```

This should compile in one shot. If it doesn't, the issue is likely
a definitional unfolding — try `show α (s + t) * β (s + t) = ...`
to expose the goal, or replace `simp` with `dsimp only` on the
first sub-goal.

### Step 3 — Non-vacuity witness

CLAUDE.md mandates non-vacuity for new structures/predicates. Add:

```lean
/-- The constant-1 mapping is multiplicative — non-vacuity witness. -/
theorem isMultiplicative_const_one :
    IsMultiplicative (fun _ : Forest => (1 : ℝ)) :=
  ⟨rfl, fun _ _ => by ring⟩
```

### Step 4 — Bookkeeping

* `lake env lean OpenMath/Chapter3/Section383.lean` clean.
* `lake build OpenMath.Chapter3.Section383` clean.
* `#print axioms OpenMath.Chapter3.Section383.multiplicative_mul`
  shows only `[propext, Classical.choice, Quot.sound]` (likely a
  subset for this purely algebraic proof).
* Update `extraction/formalization_data/lean_status.json::lem:383A`
  to `formalized` with
  `lean_symbol = "OpenMath.Chapter3.Section383.multiplicative_mul"`.
* Update `plan.md`: change `lem:383A` from `[ ]` to `[x]`.
* Faithfulness check: write entry in cycle 078 task results
  quoting Butcher's statement and confirming the Lean type matches.

### Path B budget — use leftover time for plan.md cleanup

This is intentionally a small cycle. If Steps 1–4 take less than
half the cycle-time budget, use the remaining time for **plan.md
bookkeeping cleanup**:

* `def:381B` ("Φ-equivalent") is already formalized at
  `OpenMath/Chapter3/Section381.lean:122` as `PhiEquivalent`, with
  `lean_status.json` already correct (status `formalized`), but
  `plan.md` still shows `[ ]`. Update plan.md to `[x]`.
* `def:381D` ("P-reducible") similarly: already at
  `OpenMath/Chapter3/Section381.lean:284` as `IsPReducible`,
  `lean_status.json` correct, `plan.md` shows `[ ]`. Update to `[x]`.
* Update the progress counter in `plan.md` (currently 46/175). If
  cycle 078 lands `lem:383A` plus the two stale `[x]` updates, new
  count is 49/175.

This bookkeeping is real progress (the entities are genuinely
done; the plan was stale). Do it inside this cycle's commit, not
as a separate cycle.

### What NOT to do in Path B

* Do NOT formalize `Multiplicative` as a typeclass on `Forest → ℝ`.
  Predicate-style is sufficient and matches Butcher.
* Do NOT introduce a separate `Forest` inductive type when
  `Multiset RootedTree` is the natural Mathlib encoding.
* Do NOT touch `OpenMath/Chapter3/Section381.lean` or
  `OpenMath/Chapter3/Section310.lean`. The new file imports them
  and stands on its own.
* Do NOT attempt `lem:383B` ("Associativity of multiplicative
  forest mappings") or `lem:383C` ("left/right inverses in G_1") in
  the same cycle. They are the natural next targets but belong in
  future cycles. One lemma per cycle for safety.

---

## Critically: what NOT to do this cycle (regardless of path)

These are explicit failure modes from cycle 077 and earlier:

* **Do NOT commit any unclosed sorry.** Every `theorem`/`lemma` in
  the commit must compile with no `sorry` in its body. If a
  sorry-first scaffold doesn't get closed, `git restore` it before
  commit.
* **Do NOT retry the §410D substitution sorries with manual proofs**
  if Aristotle didn't deliver them. The PowerSeries.log gap is real
  and not closable without dedicated infrastructure (issue file
  documents this).
* **Do NOT introduce `axiom` or `constant` declarations.** CLAUDE.md
  is explicit. The PowerSeries.log gap is NOT a license to
  axiomatize.
* **Do NOT raise `maxHeartbeats` above 200000.** Decompose instead.
* **Do NOT touch `scripts/autonomous_loop.py`.** Loop-maintainer
  territory; standing issue file
  `tautology_scanner_false_positives.md` is the canonical
  recommendation.
* **Do NOT modify `extraction/raw_text/` or
  `extraction/formalization_data/entities/`** — both are
  regenerated. `lean_status.json` and `plan.md` are the editable
  bookkeeping files.
* **Do NOT poll Aristotle more than once this cycle.** CLAUDE.md
  rule. One status check at start; if not delivered, pivot to Path
  B.
* **Do NOT rewrite or remove cycle-077-style issue files.** The
  `thm_410D_substitution.md` issue documents an outstanding
  blocker; if Path A succeeds, mark it resolved with a pointer in
  the cycle 078 task results. If Path B is taken, leave the issue
  file as-is — it remains an open blocker for a future cycle.

## Faithfulness check reminder (CLAUDE.md mandate)

Whichever path you take, your `.prover-state/task_results/cycle_078.md`
must contain a faithfulness check section with:

* The textbook statement (quoted from
  `extraction/formalization_data/entities/<id>.json`).
* The Lean statement (quoted from your code).
* An assertion that the Lean statement captures the textbook
  meaning (or, if it diverges, a justification — but for both
  Path A and Path B targets, no divergence should be needed beyond
  the `α 0 = 1` clause discussed above).

## Aristotle policy this cycle

Path A consumes one Aristotle status check. Path B should NOT
submit any new Aristotle jobs — the target is small enough to
prove manually in one cycle. If Path B finishes early and you
have spare cycle time, you may submit Aristotle jobs for
`lem:383B` (associativity) or `lem:383C` (left/right inverses in
G_1) so they're cooking for cycle 079, but DO NOT incorporate the
results in this cycle's commit. Save the project IDs in
`.prover-state/aristotle_submissions/cycle_078/project_ids.txt`
for cycle 079 to pick up.

## Task results format

Write to `.prover-state/task_results/cycle_078.md` per the CLAUDE.md
template, with these specific sections:

* **Path taken**: A or B (with one-line justification).
* **Aristotle status report**: the result of the project 18504be5
  status check (regardless of path).
* **Worked on**: the entity ID closed (or stale plan entries
  cleaned).
* **Approach**: what you tried, what compiled, what didn't.
* **Result**: SUCCESS / FAILED + per-target axiom-check
  confirmation.
* **Faithfulness check**: per the section above.
* **Dead ends**: anything that didn't compile and how you worked
  around it.
* **Discovery**: anything useful learned for future cycles.
* **Suggested next approach**: what cycle 079 should target. If
  Path A succeeded, suggest `lem:441A` or another §441 entry (now
  unblocked by §410D). If Path B succeeded, suggest `lem:383B`
  (the natural next §383 lemma) or `lem:383C`.
