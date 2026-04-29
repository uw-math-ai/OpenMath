# Cycle 029 Strategy

## Status

* No pending Aristotle results.
* No sorry's anywhere in `OpenMath/`.
* 29 / 175 entities formalized; cycle 028 closed `def:357B` (algebraic
  stability) cleanly. The §357 stability stack has now hit a
  prerequisite wall: every remaining §357 entity (`def:357A`,
  `thm:357C`, `thm:357D`) consumes the §356 dissipativity setup
  (DJ-irreducibility, AN-stability, reduced methods).

The cycle 028 task results explicitly recommended **"option 3:
§356 dissipativity infrastructure (`def:356A`, `def:356B`, `cor:356D`,
`thm:356C`)"** as the natural unblocker. We follow that recommendation.

## Cycle 029 target — `def:356B` and the DJ-irreducibility component of `def:356A`

`def:356B` is the foundational reducibility predicate of §356:
**DJ-reducibility** (Dahlquist–Jeltsch). `def:356A` introduces two
separate concepts in one entity record (the extractor combined a
multi-paragraph passage):

1. **AN-stable Runge–Kutta method** — first sentence,
   `R(Z) = 1 + b'Z(I − AZ)⁻¹𝟏` with `Z = diag(z₁,…,zₛ)` bounded ≤ 1
   on the closed left half-plane (componentwise). Substantial: needs
   complex matrix-valued resolvent infrastructure.
2. **DJ-irreducibility** — the *named* concept of the entity record,
   defined as the negation of `def:356B` (DJ-reducibility).

This cycle formalises **`def:356B` (DJ-reducibility) and the
DJ-irreducibility part of `def:356A` only**. The AN-stability part of
`def:356A` is deferred to a separate cycle (it is independent
infrastructure: `R(Z)` is a complex-analytic boundedness condition,
unrelated to the §381-style reducibility predicates that define
DJ-irreducibility). Document the deferral in an issue file; do **not**
silently weaken `def:356A` to "DJ-irreducibility only" without an
explicit note.

## Quoted textbook content

### `def:356B` (Butcher §356, p. 268, quoted from `entities/def_356B.json`)

> A Runge–Kutta method is 'DJ-reducible' if there exists a partition
> of the stages `{1, 2, …, s} = S ∪ S₀`, with `S₀` non-empty, such
> that if `i ∈ S` and `j ∈ S₀`,
>
>     b_j = 0   and   a_{ij} = 0.
>
> The 'reduced method' is the method formed by deleting all stages
> numbered by members of the set `S₀`.

### `def:356A` second-named-concept (Butcher §356, p. 268, quoted from `entities/def_356A.json`)

> we identify 'irreducibility in the sense of Dahlquist and Jeltsch',
> or 'DJ-irreducibility', (Dahlquist and Jeltsch, 1979) as the
> property that a tableau cannot be reduced in the sense of
> Definition 356B.

## Interpretation note (settle before writing code)

The textbook says "with `S₀` non-empty" but is silent on whether `S`
must be non-empty. Two readings:

* **Literal reading.** `S₀ ≠ ∅`, `S` may be empty. Then taking
  `S = ∅, S₀ = {1,…,s}` makes the conjunction "`if i ∈ S and j ∈ S₀`"
  vacuously true for every method. **Every tableau is DJ-reducible**,
  so DJ-irreducibility has no models. This degenerates the entire §356
  development.
* **Spirit-of-the-theorem reading.** Both `S` and `S₀` non-empty —
  i.e. the partition is genuinely "non-trivial on both sides". This
  matches Butcher's §357 usage where DJ-irreducibility is treated as a
  non-vacuous strengthening of irreducibility (e.g. `cor:356D`
  asserts `b_i > 0` *under* DJ-irreducibility, which would be vacuous
  on the literal reading).

**Adopt the spirit-of-the-theorem reading.** The Lean predicate
requires both `(∃ i, inS i = true)` and `(∃ i, inS i = false)` to
witness DJ-reducibility. Document this in the file docstring next to
the textbook quote, and explicitly justify the addition (the existing
`def:381C`/`IsZeroReducible` already adopts the analogous `P₀ ≠ ∅`
strengthening; we mirror that convention).

## File and namespace layout

Create a new file `OpenMath/Chapter3/Section356.lean`. Add its import to
`OpenMath/Chapter3.lean` (insert between `Section355` and `Section357`
to keep the alphabetical ordering already established in cycle 028).

Imports needed:

```lean
import OpenMath.Chapter3.Section312   -- RKTableau, RKTableau.explicitEuler
```

Do **not** import `OpenMath.Chapter3.Section381` even though
`Section381` already has `IsZeroReducibleVia`/`IsZeroReducible`. The
DJ-reducibility predicate is mathematically a special case of
0-reducibility (with both partition sides non-empty), but the
textbook positions DJ-reducibility *before* the §381 unified
treatment. Keeping `Section356` independent of `Section381` matches
the textbook order and avoids a forward-importing tangle if a future
cycle wants to refactor §381 into a function of §356.

If you choose to write a cross-reference equivalence lemma (see
"Optional: relationship lemma" below), put it in `Section381.lean`
(which already imports `Section312`) — not in `Section356.lean`.

Namespace: `OpenMath.Chapter3.Section356`. Predicates on `RKTableau`
go in the `OpenMath.Chapter3.Section312.RKTableau` namespace, mirroring
the pattern in `Section381` (so users can write `M.IsDJReducible` for
`M : RKTableau s`).

## Concrete plan — what to write

Follow the sorry-first rule. Step 1 below establishes a compiling
skeleton; steps 2–5 fill in proofs.

### Step 1. Define the predicates.

```lean
namespace OpenMath.Chapter3.Section312.RKTableau

open OpenMath.Chapter3.Section356

/-- Boolean encoding of a 2-block partition `{1,…,s} = S ∪ S₀`:
`inS i = true` ↔ `i ∈ S`, `inS i = false` ↔ `i ∈ S₀`. -/
def IsDJReducibleVia {s : ℕ}
    (M : RKTableau s) (inS : Fin s → Bool) : Prop :=
  ∀ j : Fin s, inS j = false →
      M.b j = 0 ∧ ∀ i : Fin s, inS i = true → M.A i j = 0

/-- Butcher §356 Definition 356B — a Runge–Kutta method is
*DJ-reducible* if there is a 2-block partition with **both** `S` and
`S₀` non-empty satisfying the zero conditions. The both-sides-non-empty
strengthening is justified in the file docstring. -/
def IsDJReducible {s : ℕ} (M : RKTableau s) : Prop :=
  ∃ inS : Fin s → Bool,
    (∃ i, inS i = true) ∧ (∃ i, inS i = false) ∧ M.IsDJReducibleVia inS

/-- Butcher §356 Definition 356A (DJ-irreducibility component) — a
Runge–Kutta method is *DJ-irreducible* if it is not DJ-reducible. -/
def IsDJIrreducible {s : ℕ} (M : RKTableau s) : Prop :=
  ¬ M.IsDJReducible

end OpenMath.Chapter3.Section312.RKTableau
```

(Adjust the `IsDJReducibleVia` shape if you find an alternative
formulation
`(∀ i j, inS i = true → inS j = false → M.b j = 0 ∧ M.A i j = 0)`
shorter — both encode the same condition. The chosen shape should
make the witness proof short. If you switch shapes, update the
`paddedEuler` proof below accordingly.)

Note that `IsDJReducibleVia` factors out only the "if i ∈ S and
j ∈ S₀ then b_j = 0 ∧ a_ij = 0" conjunction; the both-non-empty
condition is in `IsDJReducible`. This mirrors the
`IsZeroReducibleVia` / `IsZeroReducible` split in `Section381.lean:170`
and lets you re-use `IsDJReducibleVia` for any future "reduced
method" construction.

### Step 2. Verify it compiles.

```bash
lake env lean OpenMath/Chapter3/Section356.lean
```

Expect zero errors at this point. If `Mathlib.Data.Matrix.Basic` /
`Section312`'s exposure of `RKTableau` doesn't carry through cleanly,
add the missing imports — but do not import `Section381`.

### Step 3. Prove `RKTableau.explicitEuler.IsDJIrreducible`.

Concrete witness, parallel to
`Section381.lean:398-407`'s `explicitEuler_isIrreducible`. The proof
is short:

* `explicitEuler.IsDJReducible` would supply
  `inS : Fin 1 → Bool` with both `(∃ i, inS i = true)` and
  `(∃ i, inS i = false)`. Both witnesses are `0 : Fin 1`, so we have
  `inS 0 = true ∧ inS 0 = false`, contradicting `Bool.true ≠ false`.

```lean
theorem explicitEuler_isDJIrreducible :
    RKTableau.explicitEuler.IsDJIrreducible := by
  rintro ⟨inS, ⟨i, hi⟩, ⟨j, hj⟩, _⟩
  fin_cases i; fin_cases j
  exact Bool.true_ne_false (hi.symm.trans hj)
```

If the exact incantation fails, try `lean_multi_attempt` with:

```text
exact absurd (hi.symm.trans hj) Bool.true_ne_false
fin_cases i; fin_cases j; simp_all
fin_cases i; fin_cases j; omega
```

### Step 4. Provide a non-vacuous DJ-reducible witness.

Define a 2-stage `paddedEuler` analogue inline in `Section356.lean`
(do **not** import `Section381`). The same `A=0, b=![1,0], c=0`
shape works: choose `inS = ![true, false]`, so `S = {0}` (non-empty)
and `S₀ = {1}` (non-empty). The zero conditions hold because
`paddedEuler.b 1 = 0` and `paddedEuler.A 0 1 = 0`.

Proof shape mirrors `Section381.lean:370-384`:

```lean
def paddedEuler : RKTableau 2 where
  A := 0
  b := ![1, 0]
  c := 0

example : paddedEuler.IsDJReducible := by
  refine ⟨![true, false], ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
  intro j hj
  fin_cases j
  · simp_all
  · refine ⟨rfl, ?_⟩
    intro i _
    simp [paddedEuler]
```

(Tune the case analysis based on which `inS i = false` arm fires.
The first arm — `j = 0` — is impossible because `inS 0 = true`, so
`hj : true = false` is a contradiction; the second arm — `j = 1` —
is the productive one where you discharge `b 1 = 0` and the
inner-row-zero condition.)

A standalone `paddedEuler` here is fine; it duplicates the
`Section381.lean:126` definition but keeps `Section356` imports
minimal. Add a comment cross-referencing the `Section381` version
and noting that a future refactor could share the witness via a
dedicated helpers file.

### Step 5. (Optional) Relationship to `IsZeroReducible`.

If time allows, add an explicit equivalence theorem in
`Section381.lean` (NOT `Section356.lean`):

```lean
theorem IsDJReducible_iff {s : ℕ} (M : RKTableau s) :
    M.IsDJReducible ↔ ∃ inP1 : Fin s → Bool,
      (∃ i, inP1 i = true) ∧ (∃ i, inP1 i = false) ∧
        M.IsZeroReducibleVia inP1 := ...
```

(With `inP1 := !inS` — the partitions are isomorphic via Boolean
negation, with `S ↔ P₁`, `S₀ ↔ P₀`.) This is a faithfulness bonus,
not required this cycle. **Skip it if step 4 takes longer than
expected** — better to land a clean `def:356B` than to bundle and
rush.

## Faithfulness checklist for the commit

For both new definitions and theorems, verify:

* **Definition smuggling check.** `IsDJReducible` is a `Prop`, not a
  `class`/`structure` with derived-conclusion fields. The
  both-sides-non-empty strengthening of the textbook is documented
  inline at the definition site, with the textbook quote and the
  justification (vacuity argument).
* **Hypothesis strength check.** `IsDJReducibleVia` does not assume
  any consistency / row-sum / weight-positivity conditions on `M`.
* **Tautology check.** `explicitEuler_isDJIrreducible` does real
  work — it constructs a contradiction from the partition data; it
  does not collapse to `exact h_…` or `:= id`.
* **Identity check.** `IsDJIrreducible := ¬ IsDJReducible` is
  intentionally trivial (negation), but its non-vacuity is witnessed
  by `explicitEuler_isDJIrreducible` and the `paddedEuler`
  reducibility example. This is the same pattern as `IsIrreducible`
  in `Section381.lean:324`.
* **Absent theorem check.** Verify there are no comments promising
  proofs that aren't written. The AN-stability deferral note must
  point to a real issue file (see "Issue file to write" below).

## Issue file to write — AN-stability deferral

After committing the DJ-irreducibility deliverable, write
`.prover-state/issues/AN_stability_deferred.md`:

* **Blocker.** `def:356A` introduces both DJ-irreducibility and
  AN-stability. Cycle 029 formalised the DJ-irreducibility component;
  AN-stability is deferred.
* **Why deferred.** AN-stability requires the complex matrix
  stability function `R(Z) = 1 + b'Z(I − AZ)⁻¹𝟏` for
  `Z = diag(z₁,…,zₛ) ∈ ℂ^{s×s}`, with the boundedness condition
  `|R(Z)| ≤ 1` whenever every `Re(zᵢ) ≤ 0`. None of `R(Z)`,
  `(I − AZ)⁻¹`, or the `s`-dimensional left-half-plane condition is
  currently in the codebase. This is independent infrastructure (it
  shares no machinery with the §381-style reducibility predicates),
  and a faithful formalisation deserves a dedicated cycle.
* **Mathlib hooks for the future cycle.** `Matrix.IsUnit` and
  `Matrix.inv` for `(I − AZ)⁻¹`; `Complex.re` and `Set.preimage` for
  the half-plane; `Matrix.toLin'` and `‖·‖` for the magnitude bound.
  The natural typeclass is `Matrix (Fin s) (Fin s) ℂ`.
* **Downstream consumers.** `thm:356C` (AN-stability necessary
  conditions) and `thm:357C/D` (algebraic stability ⇒ B/BN-stability)
  cite AN-stability directly. Pursuing AN-stability is the natural
  unblocker for the rest of §356–§357.
* **Recommended resolution.** A dedicated cycle, after the
  DJ-reducibility infrastructure of this cycle has settled.

This issue file is the bookkeeping deliverable required by CLAUDE.md
for any partial-formalization commit ("a cycle with zero changes is
unacceptable; at minimum, decompose a sorry or write an issue").

## Verification before commit

1. `lake env lean OpenMath/Chapter3/Section356.lean` — clean.
2. `lake env lean OpenMath/Chapter3.lean` — clean (re-verifies the
   chapter aggregator).
3. `lake build` — clean.
4. `#print axioms` for both `IsDJReducible` and
   `explicitEuler_isDJIrreducible` — must show only
   `[propext, Classical.choice, Quot.sound]`.
5. Tautology scanner: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
   should return zero hits. (If you reuse a name like `h_inP1` from
   `Section381`, drop the underscore — see the cycle-014/015
   consultant notes for the standing rename convention.)
6. Sorry count: `rg --pcre2 '(?<!--\s)sorry' OpenMath/` returns zero.

## Status-file updates required

After the Lean commit lands:

* `extraction/formalization_data/lean_status.json` — flip
  `def:356B`'s `formalization_status` to `formalized`. Mark
  `def:356A` as **`partial`** (or whatever the closest schema value
  is — read `extraction/formalization_data/README.md` if unsure)
  with a `notes` field pointing at `AN_stability_deferred.md`. Do
  **not** mark `def:356A` as fully formalized; the AN-stability
  component is a faithfulness gap.
* `plan.md` — update `def:356B` to `[x]` and `def:356A` to `[~]`
  (in-progress). Update the progress counter (29 → 30 if `def:356A`
  partial counts toward the total; otherwise 29 → 31 once
  AN-stability lands). Pick one accounting and be consistent.

## What NOT to do

* **Do NOT** attempt AN-stability this cycle. It is a multi-cycle
  infrastructure investment (complex matrix resolvents); attempting
  it as a side-quest will blow up the cycle. Defer with the issue
  file.
* **Do NOT** import `Section381` from `Section356`. Mathematically
  DJ-reducibility is a refinement of 0-reducibility, but textbook
  order says §356 comes first. If you want a relationship lemma,
  put it in `Section381.lean` instead.
* **Do NOT** define DJ-reducibility as
  `IsDJReducible := M.IsZeroReducible ∧ ∃ i, inP1 i = true`
  (forwarding to `Section381`'s machinery). The textbook gives an
  independent definition; an independent Lean encoding is more
  faithful and avoids surprising the reader who reaches §356 before
  §381.
* **Do NOT** drop the both-sides-non-empty strengthening. Without
  it, every method is trivially DJ-reducible (take `S = ∅`) and
  DJ-irreducibility is vacuous. The strengthening is the universally
  understood reading; document it inline.
* **Do NOT** raise `maxHeartbeats`. If `fin_cases`-based proofs
  drag, decompose into named sub-lemmas instead.
* **Do NOT** introduce `axiom` or `constant`. The DJ predicate is a
  pure first-order condition on `RKTableau` — no axioms required.
* **Do NOT** try to fix `scripts/autonomous_loop.py` from the
  worker. Per cycle-014/015 strategy: scanner bugs go in
  `tautology_scanner_false_positives.md` for the loop maintainer.
* **Do NOT** start §142 Schur work or
  `picard_lindelof_bound_strengthening` infrastructure. Both remain
  off the critical path; cycle-009 / cycle-015 consultant notes
  classify them as non-blocking until §142 / §319 enter the active
  plan.
* **Do NOT** hand-edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/` (per
  `extraction/CLAUDE.md`). Only `lean_status.json` is editable
  among the formalization-data files.

## Aristotle (optional, low priority this cycle)

The `def:356B` proof load is small enough that direct hand-proof is
faster than batch-submitting to Aristotle. **Skip Aristotle this
cycle** unless step 4 (the `paddedEuler` reducibility witness) hits
an unexpected blocker that survives 3 `lean_multi_attempt` rounds. If
that happens, batch the witness sub-goal and continue with step 3
(the irreducibility theorem) while Aristotle works.

## Suggested fall-back targets if `def:356B` is unexpectedly tractable

If the cycle finishes with budget remaining (>60% of cycle budget
remaining after step 5):

1. **`def:381A` (equivalent)** — `Section381` infrastructure already
   gives Φ-equivalent and the reducibility predicates; defining
   "equivalent" is the next §381 leaf. Read `entities/def_381A.json`
   first to confirm the textbook formulation.
2. **`def:323A` (internal order q)** — pure scalar definition, no
   stability infrastructure needed.

Do **not** chain into `thm:356C` (AN-stability necessary conditions)
or `cor:356D` — both depend on the AN-stability machinery that this
cycle is explicitly deferring.

## Summary

* **Primary deliverable.** `IsDJReducible`, `IsDJReducibleVia`,
  `IsDJIrreducible` in a new `OpenMath/Chapter3/Section356.lean`,
  plus an `explicitEuler_isDJIrreducible` witness and a
  `paddedEuler`-style DJ-reducibility witness.
* **Issue deliverable.**
  `.prover-state/issues/AN_stability_deferred.md` documenting the
  AN-stability gap in `def:356A`.
* **Status updates.** `lean_status.json` and `plan.md` reflecting
  `def:356B` formalised and `def:356A` partial.
* **Faithfulness disclosure.** Both-sides-non-empty strengthening of
  `def:356B`, documented inline; AN-stability deferral, documented
  in the issue file and in `lean_status.json`.
