# Cycle 188 Results

## Worked on

* Priority 0: GPFS smoke test on `OpenMath/Chapter4/Section441.lean`
  (HEAD, unchanged since cycle 184). 8th consecutive timeout.
* Priority 2 deliverables on `OpenMath/Chapter3/Section381.lean`:
  Deliverables A–D from the cycle 188 strategy — extending
  `RKTableau.PReducesTo` with a `zeroStep` constructor, shipping
  `zeroReduced_phiEquivalent`, extending `PhiEquivalent.of_pReducesTo`,
  and adding `paddedEuler` non-vacuity witnesses for `zeroStep`.

## Approach

### Priority 0 (GPFS smoke test)

`time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
on HEAD: EXIT=124, real 5m0.036s, user 0m0.253s, sys 0m0.535s.
CPU = 0.26% of wall — same near-zero pattern as cycles 182–187,
consistent with mathlib olean fetching from GPFS being the
bottleneck. Appended the 8th timeout to
`.prover-state/issues/cycle_182_gpfs_slowness.md` and pivoted to
Priority 2.

### Priority 2 (Section381 deliverables)

**Deliverable A — extend `RKTableau.PReducesTo` with `zeroStep`.**
Added a third constructor between `step` and the closing `end`
matching the strategy verbatim:

```lean
| zeroStep {s s'' : ℕ}
    {M : RKTableau s} {M'' : RKTableau s''}
    (inP1 : Fin s → Bool) (_hP0 : ∃ i, inP1 i = false)
    (_h : M.IsZeroReducibleVia inP1) :
    PReducesTo (M.zeroReduced inP1) M'' → PReducesTo M M''
```

The `_hP0` non-emptiness side condition mirrors cycle 185's `_hLt :
sBar < s` strengthening on `step`: without it, the trivial
all-stages-in-P₁ partition would admit vacuous "0-reductions" that
do not decrease the stage count.

**Strengthening `eq_of_not_isPReducible_of_pReducesTo` and
`PEquivalent.trans_of_middle_not_pReducible`.** Adding `zeroStep`
broke the existing `cases h with | refl | step` patterns (now
non-exhaustive), and the original lemma's conclusion is genuinely
false with the weaker hypothesis: `¬ M.IsPReducible` does not
preclude 0-reduction out of `M`. Renamed both lemmas with
strengthened hypothesis `M.IsIrreducible` (i.e. both negations).
Updated the cycle-185 trans-through-irreducible-middle example
(line 716) to construct the full `IsIrreducible` for
`paddedEuler.pReduced pairPartition` — required computing
`(paddedEuler.pReduced pairPartition).b 0 = 1` via a filter-equals-
univ rewrite + `Fin.sum_univ_two`.

**Deliverable B — `zeroReduced_phiEquivalent`.** Shipped the
0-reduction analogue of cycle-187's `pReduced_phiEquivalent` via:

* Helper lemma `zeroReducedEmb_inP1_eq_true`: every embedded
  index lies in P₁.
* Two private mutual theorems `derivativeWeight_zeroReduced` /
  `derivativeWeightProd_zeroReduced` proving stage-by-stage
  derivative-weight agreement.
* Main theorem `zeroReduced_phiEquivalent`: discards
  `inP1 i = false` summands (their `b i` factor is 0 by clause 1
  of `IsZeroReducibleVia`), then reindexes the surviving sum.

The reindexing uses `Finset.sum_bij` rather than the natural
`rw [← image_orderEmbOfFin_univ, Finset.sum_image]` because the RHS
sum is over `Fin (filter.card)`, and rewriting the filter
expression hits the dependent type and breaks the motive
type-checker. `Finset.sum_bij` sidesteps this entirely. The
surjectivity case is closed by `hImg.symm ▸ hb` where
`hImg : Finset.image (zeroReducedEmb inP1) Finset.univ = filter`
(via `Finset.image_orderEmbOfFin_univ` after a `show` to unfold
the `zeroReducedEmb` alias).

**Deliverable C — extend `PhiEquivalent.of_pReducesTo`.** Added the
new induction case:

```lean
| zeroStep inP1 _hP0 hVia _hRest IH =>
    exact PhiEquivalent.trans (zeroReduced_phiEquivalent _ hVia) IH
```

**Deliverable D — non-vacuity witnesses.** Promoted two cycle-184
inline `example` witnesses to named theorems
`paddedEuler_isZeroReducibleVia_split` and
`paddedEuler_isZeroReducible`. Added `paddedEuler_pReducesTo_zeroReduced`
exercising the new `zeroStep` constructor on `paddedEuler` with
the partition `![true, false]`. Added downstream consumers
`paddedEuler_pEquivalent_zeroReduced` (via `PEquivalent.of_pReducesTo`)
and `paddedEuler_phiEquivalent_zeroReduced` (via
`PhiEquivalent.of_pReducesTo`, demonstrating the `zeroStep` case
of the latter's induction). The Φ-equivalent companion had to be
placed AFTER `PhiEquivalent.of_pReducesTo`'s definition (line 1086)
to avoid forward-reference; the P-equivalent companion stays in
the witness block.

## Result

**SUCCESS.**

Build: `time timeout 1200 lake env lean OpenMath/Chapter3/Section381.lean`
exited 0 in real 3m5.248s (user 2.594s, sys 3.033s — most of the
wall was GPFS olean loading; the lean elaboration was fast).
Sorry count: 0 project-wide and 0 in `Section381.lean`. Tautology
scanner: no new entries (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`
found nothing). All eight new public theorems verified axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

* `paddedEuler_isZeroReducibleVia_split` (promoted from example)
* `paddedEuler_isZeroReducible` (promoted from example)
* `paddedEuler_pReducesTo_zeroReduced` (NEW, exercises `zeroStep`)
* `paddedEuler_pEquivalent_zeroReduced` (NEW)
* `paddedEuler_phiEquivalent_zeroReduced` (NEW, exercises
  `PhiEquivalent.of_pReducesTo`'s `zeroStep` case)
* `zeroReduced_phiEquivalent` (NEW, headline)
* `eq_of_isIrreducible_of_pReducesTo` (strengthened from cycle 185)
* `PEquivalent.trans_of_middle_isIrreducible` (strengthened from
  cycle 185)

Regression checks:
* `pReduced_phiEquivalent` (cycle 187 headline) — still axiom-clean.
* `PhiEquivalent.of_pReducesTo` — still axiom-clean after the
  `zeroStep` extension.

## Faithfulness check

### `RKTableau.PReducesTo.zeroStep` (new constructor)

Textbook reference: Butcher §380 `def:381C` (page 303) — quoted in
`extraction/formalization_data/entities/def_381C.json`:

> A Runge–Kutta method `(A, b , c)` is `0-reducible' if the stage
> index set can be partitioned into two subsets
> `{1, 2, …, s} = P0 ∪ P1` such that `bᵢ = 0` for all `i ∈ P0` and
> such that `aᵢⱼ = 0` if `i ∈ P1` and `j ∈ P0`. The method formed
> by deleting all stages indexed by members of `P0` is known as
> the `0-reduced method'.

Lean encoding captures: same content. `inP1 : Fin s → Bool`
encodes the 2-block partition (P₀ = {i | ¬ inP1 i}, P₁ =
{i | inP1 i}); `IsZeroReducibleVia` (already in the file) encodes
the two zero conditions; `_hP0 : ∃ i, inP1 i = false` encodes
non-trivial P₀. The `zeroStep` constructor adds 0-reduction as a
single step in the reduction relation; the recursive `PReducesTo
(M.zeroReduced inP1) M''` allows further reductions. Faithful to
def:381C.

### `zeroReduced_phiEquivalent` (new public theorem)

Textbook reference: Butcher §380 narrative (p. 302) treats
Φ-preservation under 0-reduction as obvious — deleted stages
(those in P₀) have weight `bᵢ = 0` and so do not contribute to
elementary weights `Φ(t) = Σᵢ bᵢ Φᵢ(t)`. This is not a numbered
result in the textbook but is the implicit basis for the entire
"reduced method" / "P-equivalent" infrastructure of `def:381F`.

Lean encoding captures: same content.
`PhiEquivalent M (M.zeroReduced inP1)` says
`∀ t, M.elementaryWeight t = (M.zeroReduced inP1).elementaryWeight t`.
The proof shows the LHS sum over `Fin s` collapses to the surviving
P₁ summands (clause 1 of `IsZeroReducibleVia` kills the P₀ ones),
which reindex through `zeroReducedEmb` to the RHS sum over
`Fin (#P₁)`. Faithful.

### `PhiEquivalent.of_pReducesTo` (extended)

Cycle 187 docstring identified the `zeroStep` extension as a
deferred follow-up. Cycle 188 closes that gap. The textbook
implicitly treats both P-reduction and 0-reduction as preserving
elementary weights; the extended induction now handles arbitrary
mixed reduction sequences. Same content as cycle 187, with the
0-reduction case folded in cleanly.

### `eq_of_isIrreducible_of_pReducesTo` and
### `PEquivalent.trans_of_middle_isIrreducible` (strengthened)

Hypothesis-strength change: cycle 185's lemmas required only
`¬ M.IsPReducible`; cycle 188 strengthens to `M.IsIrreducible`
(both negations). The textbook does not state these lemmas as
numbered results — they are auxiliaries. The strengthening is
necessary, not arbitrary: with only `¬ M.IsPReducible`, the
`zeroStep` case (which produces a non-reflexive reduction out of
a possibly-non-P-reducible source) makes the lemma genuinely
false. Documented in the lemma docstrings.

### Hypothesis discipline (CLAUDE.md checklist)

* TAUTOLOGY CHECK: ran the full tautology-scanner regex on
  `Section381.lean` — no new entries.
* IDENTITY CHECK: no new theorem proves itself by `:= h` /
  `exact h_*` / `:= id`. All new theorems do real work
  (constructor extensions, mutual induction, sum reindexing).
* DEFINITION SMUGGLING CHECK: no new `structure` introduced.
  `RKTableau.PReducesTo`'s new `zeroStep` constructor adds a
  hypothesis (the IsZeroReducibleVia witness + non-empty P₀),
  not a conclusion — analogous to `step`'s existing
  `IsPReducibleVia` + `sBar < s`.
* HYPOTHESIS STRENGTH CHECK: the strengthened
  `eq_of_isIrreducible_of_pReducesTo` is exactly as strong as the
  inductive structure permits — anything weaker would break the
  conclusion. The `_hP0` and `_hLt` side conditions in
  `PReducesTo`'s constructors are minimum-necessary to keep the
  relation faithful to Butcher's "non-trivial reduction"
  language.
* ABSENT THEOREM CHECK: every promised theorem is present.
  `paddedEuler_phiEquivalent_zeroReduced` referenced from the
  `paddedEuler_pEquivalent_zeroReduced` docstring is positioned
  at line 1097 (after `PhiEquivalent.of_pReducesTo`).

## Dead ends

* **`rw [Finset.image_orderEmbOfFin_univ.symm]` for the reindexing
  step.** First attempt; the rewrite tactic failed with "motive is
  not type correct" because the LHS pattern
  `Finset.univ.filter (fun j => inP1 j = true)` appears both as
  a Finset (in the LHS sum domain) AND inside the dependent-type
  cardinality expression `Fin (filter.card)` (in the RHS sum
  domain). Rewriting it would change the sum index type, which
  Lean cannot validate through the motive. Fixed by switching
  to `Finset.sum_bij` (no rewrite of the filter expression).

* **`cases hh : inP1 j with | true => Finset.mem_filter.mpr ⟨_, hh⟩`
  fails to elaborate.** The expected type of the membership proof
  involved `(Eq (inP1 j))` partially applied as the filter
  predicate, and Lean unified the `_` placeholder to `true`
  instead of `j`, producing nonsensical "true ∉ filter" error.
  Fixed by extracting the negation as a separate `have hjNotTrue
  : inP1 j ≠ true := fun hjT => hj_notin (Finset.mem_filter.mpr
  ⟨Finset.mem_univ j, hjT⟩)` BEFORE the `cases`, then closing the
  `true` branch with `absurd hh hjNotTrue`. This avoids the
  premature unification.

* **`hImg ▸ hb` (forward direction) in surjectivity proof.**
  The `▸` rewrite acts on the type of the term, replacing the LHS
  of the equality with the RHS. For `hImg : Image = Filter` and
  `hb : b ∈ Filter`, we want to reach `b ∈ Image`, so we need to
  rewrite the RHS pattern in `hb`'s type — i.e. `hImg.symm ▸ hb`.
  The forward direction silently produced a type mismatch.

## Discovery

* **`Finset.sum_bij` is the right tool when sum reindexing
  involves `OrderEmbedding`-induced `Fin n` index types on the
  RHS.** The natural `rw [image_orderEmbOfFin_univ.symm,
  Finset.sum_image]` recipe is sabotaged by Lean's motive-type
  checker because the cardinality expression inside `Fin (s.card)`
  also gets rewritten. `Finset.sum_bij` takes the bijection
  explicitly without any rewriting of finsets, neatly bypassing
  the issue. Save this for any future "reindex via order
  embedding" sum-equality step.

* **Definitional equality of `RKTableau.zeroReducedEmb` to its
  underlying `orderEmbOfFin`.** The alias `RKTableau.zeroReducedEmb
  inP1 := (filter ...).orderEmbOfFin rfl` is by definition. To
  apply Mathlib lemmas that pattern-match on
  `Finset.orderEmbOfFin _`, use `show` to unfold the alias —
  e.g. `show Finset.image ⇑((filter).orderEmbOfFin rfl) Finset.univ
  = _` — then the lemma fires. Direct `rw` doesn't unfold the
  alias.

* **`hImg.symm ▸ hb` rewriting direction.** When you have
  `hImg : a = b` and `hb : x ∈ b` and want `x ∈ a`, use
  `hImg.symm ▸ hb` (replace `b` with `a` in `hb`'s type). The
  forward `hImg ▸ hb` looks for `a` in `hb`'s type and finds
  nothing.

## Suggested next approach

1. **GPFS recovery for Section441.** The 8th consecutive timeout
   suggests the GPFS regression on `/mmfs1/gscratch/amath/...` is
   semi-permanent at this point. Loop-maintainer escalation in
   `cycle_182_gpfs_slowness.md` remains the canonical path
   forward; cycle 189 should retry the smoke test in case
   anything changed.

2. **§380 follow-ups now unlocked by `zeroStep`.** With both
   reduction constructors landed, future cycles can ship:
   * `PEquivalent.of_zeroReducible` (P-equivalence under
     0-reduction directly, mirroring cycle 187's
     `PEquivalent.of_pReducesTo`-based pattern but specialized).
   * A non-trivial `paddedEuler.PEquivalent paddedEuler.someTwoStepReduct`
     witness exercising both `step` and `zeroStep` in a chain
     (currently the chains are pure-P or pure-0).
   * `thm:381G` (irreducible methods are stage-distinguishable) —
     a `def:381E`-only result (no `def:381F` infrastructure
     needed). See backup Plan C in cycle 188 strategy.

3. **`def:381E`'s `reducedMethod` fixed-point construction.**
   Still deferred per `.prover-state/issues/reduced_method_deferred.md`.
   Needs strong induction on stage count + termination argument;
   multi-cycle work. Cycle 188's `zeroStep` constructor extension
   is one of the building blocks.

4. **Confluence of `PReducesTo` for full `PEquivalent.trans`.**
   Cycle 188's `trans_of_middle_isIrreducible` covers the easy
   case (irreducible middle). Full transitivity over arbitrary
   middles requires confluence: any two reduction sequences from
   a common source can be completed to a common target. This is
   meaningful work; mathematically corresponds to the
   well-definedness of "the" reduced method up to equivalence.

5. **Aristotle re-engagement.** No pending jobs from cycle 187.
   Future cycles could submit `def:381E`'s reduced-method
   construction (when scoping done) or `thm:381G`'s
   stage-distinguishability proof to Aristotle for partial
   discharge; both have textbook proofs that translate well.
