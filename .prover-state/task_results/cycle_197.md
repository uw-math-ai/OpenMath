# Cycle 197 Results

## Worked on

- **Priority 0 (mandatory verification)** — Cycle 196 supervisor
  verdict (score=0) claimed `OpenMath/Chapter3/Section381.lean` was
  absent from commit `2feee1d`. Verified the claim against git.
- **Priority 1 (substantive)** — `RKTableau.reducedMethod_exists` in
  `OpenMath/Chapter3/Section381.lean`: the **existential-witness
  half** of the deferred def:381E `reducedMethod` construction
  (`∀ M : RKTableau s, ∃ s' M', M.PReducesTo M' ∧ M'.IsIrreducible`).
  Consumes the cycle 195 measure side + cycle 196 extraction side +
  cycle 192 transitivity in a single packaging theorem.
- **Priority 2 (low-cost mandatory)** — §441 GPFS smoke test, 17th
  attempt.

## Approach

### Priority 0

Ran the strategy's verification command set verbatim against commit
`2feee1d`:

```bash
$ git show --stat 2feee1d -- OpenMath/Chapter3/Section381.lean
 OpenMath/Chapter3/Section381.lean | 99 ++++++++++++++++++++++++++++++++++++++-
 1 file changed, 97 insertions(+), 2 deletions(-)

$ git rev-parse HEAD ; git rev-parse origin/butcher-experiments
2feee1d7af41682be39a6b92f64e9ae8ba321a95
2feee1d7af41682be39a6b92f64e9ae8ba321a95
```

Landmark `grep -n` confirmed all 6 promised cycle-196 theorems
present at HEAD:

| Symbol                                                                           | Line |
| -------------------------------------------------------------------------------- | ---- |
| `IsPReducible.sBar`                                                              | 692  |
| `IsPReducible.sBar_lt`                                                           | 701  |
| `IsPReducible.partition`                                                         | 708  |
| `IsPReducible.partition_isPReducibleVia`                                         | 716  |
| `IsZeroReducible.inP1`                                                           | 723  |
| `IsZeroReducible.exists_inP1_false`                                              | 733  |
| `paddedEuler_pReduced_pairPartition_eq_of_both_isIrreducible` (P2)               | 1493 |
| `paddedEuler_pReducesTo_pReduced_via_pEquivalent_extraction` (P2)                | 1510 |

Total: 1544 LOC, 0 sorrys at start of cycle 197. **Branch P0.A
(phantom verdict) confirmed.** This is the 9th occurrence in the
established false-alarm pattern documented in
`.prover-state/issues/phantom_commit_verdict_pattern.md` (cycles
008 / 035 / 073 / 170 / 176 / 177 / 178 / 179 / 196). The pattern
now spans two distinct Lean files (`Section441.lean` and
`Section381.lean`), refuting the earlier "path-matching bug
specific to §441" hypothesis.

Recorded the false-alarm in `.prover-state/attempts.md` ("Cycle 197
confirmation" entry under the cycle 196 row) and appended a "Cycle
197 update" section to `phantom_commit_verdict_pattern.md`. Took no
worker-side action to fix the supervisor's diff-detection logic —
per CLAUDE.md and the strategy, that is loop-maintainer territory.

### Priority 1

Verified `IsIrreducible`'s definitional shape and the `PReducesTo`
constructor argument orders by reading the source directly
(`Section381.lean:353` for `IsIrreducible`, `:393` for the
`PReducesTo` inductive). Key shapes:

* `IsIrreducible M := ¬ M.IsZeroReducible ∧ ¬ M.IsPReducible`
  (0-reducible **first**, P-reducible **second** — important for
  the disjunction's variable order in the case split).
* `PReducesTo.step (P : PPartition s sBar) (_hLt : sBar < s)
   (_h : M.IsPReducibleVia P) : PReducesTo (M.pReduced P) M'' →
   PReducesTo M M''` — argument order (P, hLt, h_via, continuation).
* `PReducesTo.zeroStep (inP1 : Fin s → Bool)
   (_hP0 : ∃ i, inP1 i = false) (_h : M.IsZeroReducibleVia inP1) :
   PReducesTo (M.zeroReduced inP1) M'' → PReducesTo M M''` —
  argument order (inP1, hP0, h_via, continuation).
* `PReducesTo.trans : PReducesTo M M' → PReducesTo M' M'' →
   PReducesTo M M''` — cycle 192 deliverable, dot-notation method.

Wrote the theorem at line 769 in `Section381.lean`, just before the
"Definition 381A" comment header (inside the inner
`OpenMath.Chapter3.Section312.RKTableau` namespace block):

```lean
theorem reducedMethod_exists {s : ℕ} (M : RKTableau s) :
    ∃ (s' : ℕ) (M' : RKTableau s'),
      M.PReducesTo M' ∧ M'.IsIrreducible := by
  suffices h : ∀ s : ℕ, ∀ M : RKTableau s,
      ∃ (s' : ℕ) (M' : RKTableau s'),
        M.PReducesTo M' ∧ M'.IsIrreducible from h s M
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro M
    by_cases hIrr : M.IsIrreducible
    · exact ⟨s, M, .refl M, hIrr⟩
    · rw [IsIrreducible, not_and_or, not_not, not_not] at hIrr
      rcases hIrr with hZ | hP
      · have hStep : M.PReducesTo (M.zeroReduced hZ.inP1) :=
          .zeroStep hZ.inP1 hZ.exists_inP1_false
            hZ.inP1_isZeroReducibleVia (.refl _)
        obtain ⟨s', M', hRed, hIrr'⟩ :=
          ih _ hZ.zeroReduced_size_lt (M.zeroReduced hZ.inP1)
        exact ⟨s', M', hStep.trans hRed, hIrr'⟩
      · have hStep : M.PReducesTo (M.pReduced hP.partition) :=
          .step hP.partition hP.sBar_lt
            hP.partition_isPReducibleVia (.refl _)
        obtain ⟨s', M', hRed, hIrr'⟩ :=
          ih hP.sBar hP.sBar_lt (M.pReduced hP.partition)
        exact ⟨s', M', hStep.trans hRed, hIrr'⟩
```

Strong-induction packaging: the `suffices h : ∀ s : ℕ, ∀ M : RKTableau s, …`
move lifts the implicit `s` to an explicit-`∀` form so
`Nat.strong_induction_on` can supply `ih : ∀ m, m < s → ∀ M : RKTableau m, …`
with the right universal-quantifier structure.

Case-split: the strategy's "Tactic-shape risks" pre-flight
correctly predicted that `IsIrreducible := ¬ A ∧ ¬ B`, so `¬ IsIrreducible`
needs `not_and_or` (gives `¬¬A ∨ ¬¬B`) followed by `not_not` twice
to recover `M.IsZeroReducible ∨ M.IsPReducible`. Worked on the first
try.

### Priority 2

```
$ ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"
(empty — no D-state processes)

$ time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
real  5m0.028s
user  0m0.242s
sys   0m0.726s
EXIT=124  (timeout exit code from `timeout 300`)
EXIT=143 (downstream `tail` SIGTERM)
```

CPU = (0.242 + 0.726) / 300 = **0.32 % of wall-clock** — identical
near-zero pattern to cycles 182–196. 17th consecutive timeout
spanning 16 calendar days. Logged to
`.prover-state/issues/cycle_182_gpfs_slowness.md`.

## Result

- **Priority 0**: ✅ SUCCESS — Branch P0.A (phantom verdict)
  confirmed; cycle 196 work is at HEAD as reported. False-alarm
  entries appended to `attempts.md` and
  `phantom_commit_verdict_pattern.md`. Loop-maintainer escalation
  remains in force.
- **Priority 1**: ✅ SUCCESS — `RKTableau.reducedMethod_exists`
  shipped axiom-clean:
  - File compiles in **3.793s** (`time lake env lean
    OpenMath/Chapter3/Section381.lean` → EXIT=0, only pre-existing
    `heq` unused-variable warnings at lines 576 and 1556).
  - Sorry count: **0 → 0**.
  - File size: **1544 → 1606 LOC** (+62 LOC).
  - `lean_verify`:
    `OpenMath.Chapter3.Section312.RKTableau.reducedMethod_exists`
    → axioms = `[propext, Classical.choice, Quot.sound]` (the
    expected clean trio — `Classical.choice` is necessary because
    the cycle-196 destructors are `noncomputable def`s built on
    `Classical.choose`, and the `not_and_or` / `not_not` rewrites
    are classical-flavoured).
- **Priority 2**: ✅ EXPECTED FAILURE — 17th GPFS timeout per the
  established 16-day pattern. Single attempt only, no retry per
  strategy.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `RKTableau.reducedMethod_exists`

- **Entity ID**: closest match is **def:381E** (Butcher §380, page
  303, second sentence: *"The method formed from a method by first
  carrying out a P-reduction and then carrying out a 0-reduction is
  said to be the 'reduced method'"*) — but this cycle ships the
  *existential* witness only, not the textbook's constructive
  recipe. See `.prover-state/issues/reduced_method_deferred.md`
  for the standing scoping decision (Q1 / Q2 unchanged from cycles
  022 / 196).

  The full textbook statement of def:381E introduces **two** items:
  the predicate `IsIrreducible` (already shipped cycle 022) and
  the **constructive** reduced-method recipe. Cycle 197 ships
  neither — it ships a **lemma** asserting that *some* irreducible
  reduct exists for every method, which is the existential closure
  of the textbook's constructive intent.

- **Lean statement captures**: **same content (existential form),
  weaker than textbook constructive recipe**. The textbook asserts
  the *existence and uniqueness* of *the* reduced method via a
  concrete recipe (P-reduce, then 0-reduce, then — by thm:381H
  context — iterate to fixed point); cycle 197 asserts only the
  *existence* of an irreducible reduct, leaving uniqueness to
  cycle 193's `eq_of_both_isIrreducible` (already shipped) and
  constructibility to a future cycle.

- **Justification for divergence**: The cycle 196 task results
  explicitly scoped the constructive `noncomputable def reducedMethod`
  as multi-cycle (Σ-wrapper `WellFoundedRelation` instance, Option A,
  or `Decidable IsPReducible / IsZeroReducible` instances, Option
  B). The cycle 197 strategy instructed shipping the existential
  witness instead, on the grounds that (a) it is a single-cycle
  deliverable; (b) it directly consumes the cycle 195 + 196
  infrastructure end-to-end, justifying those cycles; (c) it
  unblocks def:381F (P-equivalent) phrased existentially, which is
  the immediate downstream consumer; (d) it does not introduce any
  new mathematical content beyond the existing predicates, so the
  faithfulness audit reduces to a packaging-correctness check
  rather than a definitional one.

  No new `def`, no new `structure`, no new `class` introduced. The
  only new declaration is a `theorem`. Therefore the "definition
  smuggling" check is **vacuous** for this cycle — there is no
  definition that could be smuggled.

- **Tautology check**: ❌ NOT TAUTOLOGICAL. The conclusion
  `∃ s' M', M.PReducesTo M' ∧ M'.IsIrreducible` does not appear
  verbatim or even shape-equivalently as a hypothesis; the only
  hypothesis is `(M : RKTableau s)` (universally quantified). The
  proof is a 50-line strong induction.

- **Identity check**: ❌ NOT VACUOUS. The proof is a non-trivial
  strong induction with three cases (refl-irreducible / zeroStep /
  step), each chaining a single-step reduction with an
  IH-supplied tail via `PReducesTo.trans`. Real mathematical work,
  not `exact h`.

- **Hypothesis strength check**: ❌ HYPOTHESES MATCH TEXTBOOK
  EXACTLY. The theorem takes only `(M : RKTableau s)`, which is
  exactly what Butcher's def:381E requires. No extra hypotheses
  (no decidability, no constructibility, no
  `WellFoundedRelation` — all the technical machinery is buried in
  the proof via the cycle 196 destructors' `Classical.choose`).

- **Absent theorem check**: N/A — no comments promising future
  content.

## Dead ends

None. The proof worked first try with the strategy's recipe; the
"Tactic-shape risks" pre-flight in the strategy file correctly
anticipated all three potential pitfalls (`IsIrreducible` shape,
constructor argument orders, `Nat.strong_induction_on` motive).

In particular:

- The strategy's draft constructor invocations had the argument
  order **wrong** in the `step` branch
  (`.step hP.sBar_lt hP.partition …` was reversed). I caught this
  during the "Tactic-shape risks" verification by reading
  `Section381.lean:404–408` directly: the correct order is
  `.step (P : PPartition s sBar) (_hLt : sBar < s)
   (_h : M.IsPReducibleVia P) (continuation)`. Fixed before writing
  the proof.

- The strategy suggested `Nat.strongRecOn` or hand-rolled strong
  recursion as a fallback if `Nat.strong_induction_on` produced
  unexpected motive-shape goals. The `suffices h : ∀ s, ∀ M, …`
  packaging worked first try with `Nat.strong_induction_on`, so
  no fallback needed.

## Discovery

1. **The phantom-verdict pattern has spread to a second Lean file.**
   Cycles 176–179 (4 false alarms) and 196 (5th — but the 9th
   cumulative across all files including pre-§441 history) all
   involve "supervisor claims file absent, git says file is +N
   LOC". The cycle 196 occurrence is the first in `Section381.lean`
   rather than `Section441.lean`, refuting the
   "path-matching bug specific to §441" hypothesis in the issue
   file. Loop-maintainer escalation remains in force; no
   worker-side fix is possible per CLAUDE.md.

2. **`not_and_or` + double `not_not` is the cleanest way to negate
   `IsIrreducible`** under the current
   `IsIrreducible M := ¬ M.IsZeroReducible ∧ ¬ M.IsPReducible`
   definition. `push_neg` would work too, but the explicit
   rewrite chain is more debuggable when the case-split breaks. The
   strategy's "fallback plan" to introduce an auxiliary
   `not_isIrreducible_iff` lemma was not needed — the in-line
   `rw [IsIrreducible, not_and_or, not_not, not_not] at hIrr` is
   one line and discharges cleanly.

3. **`Nat.strong_induction_on with | _ s ih => intro M`** is the
   idiomatic way to do strong induction with a parameterised
   motive. Requires `suffices h : ∀ s, ∀ M : RKTableau s, …` to
   abstract the implicit `s` first; then the `intro M` after the
   `induction` packs `M` back into the IH scope. Worked first try
   without any `revert`/`generalize` plumbing.

4. **`PReducesTo.trans` (cycle 192) was the load-bearing piece**
   for the cycle-197 packaging. Without it, the recursive case
   would have had to inline the multi-step reduction by induction
   on the IH's witness shape, which would not factor cleanly
   through the cycle-196 destructors. The cycle 192 deliverable
   (which at the time only had two `paddedEuler` non-vacuity
   examples to its name) turns out to be the structural prerequisite
   that makes cycle 197's existential witness fit in 50 LOC.

5. **`Classical.choice` is the only non-`propext`/`Quot.sound`
   axiom needed.** Despite the proof using `by_cases`, `not_and_or`,
   `not_not`, and three cycle-196 destructors all built on
   `Classical.choose`, the only resulting non-standard axiom is
   `Classical.choice` (which subsumes `Classical.em` and
   `Classical.choose`). `Decidable IsPReducible` / `Decidable
   IsZeroReducible` are **not** needed for the existential witness;
   they only become necessary for a *constructive*
   `noncomputable def reducedMethod` recursion (the still-deferred
   Option B from cycle 196 task results).

## Suggested next approach

Three candidates for the planner, in rough order of cycle 198
priority:

### Option 1 (recommended — single-cycle, directly downstream)

**def:381F existential phrasing** — Combine
`reducedMethod_exists` (cycle 197) with cycle 188's
`eq_of_isIrreducible_of_pReducesTo` and cycle 193's
`PEquivalent.eq_of_both_isIrreducible` to produce the canonical
existential form of def:381F:

```lean
theorem PEquivalent_iff_exists_common_irreducible_reduct
    {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') :
    PEquivalent M M' ↔
      ∃ (s'' : ℕ) (M'' : RKTableau s''),
        M.PReducesTo M'' ∧ M'.PReducesTo M'' ∧ M''.IsIrreducible
```

This is essentially what Butcher's def:381F asserts under the
existential reading of "the reduced method" (cycle 197's
`reducedMethod_exists` makes both sides of `PEquivalent` produce
*some* irreducible reduct; cycle 193's `eq_of_both_isIrreducible`
makes them coincide up to `HEq`). Single-cycle deliverable, ~20-30
LOC.

### Option 2 (medium-cycle — `Decidable` instances)

**`Decidable (M.IsPReducible)` / `Decidable (M.IsZeroReducible)`
instances** — would unblock the *constructive* `noncomputable def
reducedMethod` recursion (Option B from cycle 196 task results).
Decidability for `IsZeroReducible` is the easier one: it reduces
to a finite scan over `Fin s → Bool` (`Fintype.decidableExists`).
`IsPReducible` is harder: requires deciding the existence of a
non-trivial partition `P : PPartition s sBar` with
`sBar < s` and `IsPReducibleVia M P` — a finite scan but with a
nested existential and `Decidable` for `IsPReducibleVia`. Likely
2–3 cycles.

### Option 3 (multi-cycle — Σ-wrapper)

**Σ-wrapper `WellFoundedRelation` instance** — Option A from
cycle 196 task results. Would also unblock the constructive
recursion. More principled (no `Decidable` plumbing required, no
`Classical.byCases` branching at every step), but more engineering
upfront. Likely 3–4 cycles for the full instance + the
`reducedMethod` definition + a `reducedMethod_spec` lemma proving
the constructive function realises cycle 197's existential.

The §441 Phase C.2 GPFS block remains a parallel concern; nothing
this cycle could do about it.
