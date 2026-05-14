# Issue: Deferred — second sentence of def:381E ("reduced method")

## Blocker

Definition 381E of Butcher §380 introduces **two** concepts:

1. The predicate "irreducible" — a Runge–Kutta method is irreducible
   if it is neither 0-reducible nor P-reducible.
2. The "reduced method" construction — *"The method formed from a
   method by first carrying out a P-reduction and then carrying out
   a 0-reduction is said to be the 'reduced method'."*

Cycle 022 formalises (1) as
`OpenMath.Chapter3.Section312.RKTableau.IsIrreducible`, witnessed by
`explicitEuler_isIrreducible`. The construction (2) is **deferred**
to a later cycle for the reasons documented below.

## Textbook quote (def:381E, second sentence)

> The method formed from a method by first carrying out a P-reduction
> and then carrying out a 0-reduction is said to be the 'reduced
> method'.

## Open interpretation questions

The textbook is silent on two points that materially affect the Lean
encoding:

### Q1. What is the "reduced method" when neither reduction applies?

If `M` is irreducible, no P-reduction or 0-reduction step is
available, so the textbook formulation does not produce a value.
Convention to adopt (consistent with §380's later use of "the
reduced method" as a uniqueness landmark — cf. thm:381H):
`reducedMethod M = ⟨s, M⟩` if `M.IsIrreducible`.

### Q2. Single P-reduction or iterate to a fixed point?

Butcher writes "first carrying out a P-reduction", suggesting one
step. But thm:381H ("two methods are equivalent iff P-equivalent
iff Φ-equivalent") only makes sense if "the reduced method" is a
canonical normal form, which requires iterating P-reduction (and
0-reduction) until no further reduction is possible. The
discriminating step is checking whether `pReduced M P` is itself
P-reducible — if yes, iterate.

This question must be settled before def:381F (P-equivalent) can be
formalised, because "each of them reduces to the same reduced
method" is exactly the equality of the (unique) normal forms.

## Lean implementation sketch (do NOT implement this cycle)

```lean
noncomputable def reducedMethod {s : ℕ} (M : RKTableau s) :
    Σ s', RKTableau s' :=
  if hP : M.IsPReducible then
    let ⟨sBar, _, partition, _⟩ := Classical.choose hP …
    let M₁ := pReduced M partition
    if hZ : M₁.IsZeroReducible then
      let ⟨inP1, _, _⟩ := Classical.choose hZ …
      ⟨_, zeroReduced M₁ inP1⟩
    else ⟨_, M₁⟩
  else if hZ : M.IsZeroReducible then
    let ⟨inP1, _, _⟩ := Classical.choose hZ …
    ⟨_, zeroReduced M inP1⟩
  else ⟨s, M⟩
```

Difficulties:

* `Classical.choose` on `IsPReducible` and `IsZeroReducible` needs
  appropriate destructors that expose the partition witness.
* The dependent pair `Σ s', RKTableau s'` is needed because the
  reduced method's stage count is not a function of `s` alone.
* If Q2 says "iterate", the recursion's well-foundedness must be
  proved by strong induction on `s` (each genuine reduction strictly
  decreases the stage count, since `IsPReducible` requires `sBar < s`
  and `IsZeroReducible` requires `P₀ ≠ ∅`).

## Downstream consumer audit

Searched all five entities listed under `def:381E.dependents` for
references to "reduced":

| Entity     | Mentions "reduced method" / depends on construction (2)? |
|------------|----------------------------------------------------------|
| def:370A   | mentions "0-reduced method" (variable definition only)   |
| def:381A   | mentions "0-reduced method" (variable definition only)   |
| def:381C   | already formalised in cycle 020                          |
| def:381F   | **YES** — "each of them reduces to the same reduced method" |
| thm:381G   | name only ("Reduced Runge–Kutta methods are…")           |

Conclusion: `IsIrreducible` (the cycle 022 deliverable) is sufficient
for `thm:381G` and for the variable-definition references in
def:370A and def:381A. The first downstream consumer that
**genuinely requires** the construction (2) is `def:381F` (the next
candidate after thm:381G in the §380 topo order). Therefore
construction (2) becomes blocking when def:381F is queued.

## What was tried this cycle

Nothing — the deferral was decided up-front by cycle 022 strategy
on the grounds that the construction is non-trivial and the
predicate alone unblocks all immediate downstream work (thm:381G,
def:370A, def:381A).

## Possible solutions / recommended resolution cycle

* **Resolve Q1 and Q2** (consult the immediately surrounding §380
  paragraphs in `extraction/raw_text/ch03.txt` — do *not* edit
  `raw_text/`).
* Recommended cycle: when `def:381F` is queued (currently planned
  for cycle 024 or thereabouts).
* If iteration is required (Q2 → "iterate"), the recursion
  termination proof should reuse the strict stage-count decrease
  already implicit in `IsPReducible` (`sBar < s`) and the
  similarly-strict 0-reduction decrease (`#P₁ < s` whenever
  `P₀ ≠ ∅`, which is the side condition on `IsZeroReducible`).

## Cycle 196 update — destructor infrastructure landed

The `Classical.choose` plumbing that the implementation sketch above
relies on (the
`let ⟨sBar, _, partition, _⟩ := Classical.choose hP …` /
`let ⟨inP1, _, _⟩ := Classical.choose hZ …` lines) is now available
as named API in `OpenMath/Chapter3/Section381.lean` (cycle 196):

* `IsPReducible.sBar` (`Classical.choose`-extracted reduced stage
  count) and companion spec `IsPReducible.sBar_lt` (`ŝ < s`).
* `IsPReducible.partition` (extracted `PPartition s h.sBar`) and
  companion spec `IsPReducible.partition_isPReducibleVia`.
* `IsZeroReducible.inP1` (extracted `Fin s → Bool` partition
  predicate) with specs `IsZeroReducible.exists_inP1_false`
  (`∃ i, inP1 i = false`, i.e. `P₀ ≠ ∅`) and
  `IsZeroReducible.inP1_isZeroReducibleVia`.
* Stage-count-descent corollaries `IsPReducible.pReduced_size_lt`
  and `IsZeroReducible.zeroReduced_size_lt` thread the cycle 195
  descent infrastructure through the destructors.

These are all axiom-clean (standard
`[propext, Classical.choice, Quot.sound]` trio) and exercised
end-to-end by two non-vacuity examples on `paddedEuler`. Together
with the cycle 195 descent lemmas (`PReducesTo.size_le`,
`size_lt_of_step`, `size_lt_of_zeroStep`), the future `reducedMethod`
recursion now has both the *measure* side (descent on stage count)
and the *extraction* side (named destructors) of the
well-foundedness story in place.

Status remains `partial`: this is a prerequisite step, not a
closure. The remaining open work before `reducedMethod` itself can
be defined is

* a decidability or `Classical.byCases` plumbing decision for
  branching on `M.IsPReducible ∨ M.IsZeroReducible`, **and**
* a Σ-wrapper (`Σ s, RKTableau s`) packaging together with a
  `WellFoundedRelation` instance derived from the cycle 195
  descent lemmas via `WellFounded.onFun` with a stage-count
  projection.

Both remain multi-cycle engineering and are explicitly out of scope
for cycle 196. Q1 / Q2 above are unchanged.

## Cycle 197 update — `reducedMethod_exists` shipped (existential half)

The **existential** half of the deferred def:381E construction is now
landed at HEAD as
`OpenMath.Chapter3.Section312.RKTableau.reducedMethod_exists`:

```lean
theorem reducedMethod_exists {s : ℕ} (M : RKTableau s) :
    ∃ (s' : ℕ) (M' : RKTableau s'),
      M.PReducesTo M' ∧ M'.IsIrreducible
```

Axiom-clean (standard `[propext, Classical.choice, Quot.sound]`
trio — `Classical.choice` is expected: both the destructors and the
strong-induction case-split on `IsIrreducible` are
classical-flavoured). Proof recipe: strong induction on the stage
count `s` (`Nat.strong_induction_on` with the universally quantified
motive `∀ M : RKTableau s, ∃ s' M', M.PReducesTo M' ∧ M'.IsIrreducible`).
The inductive step case-splits via `by_cases hIrr : M.IsIrreducible`:

* `hIrr : M.IsIrreducible` case: `⟨s, M, .refl M, hIrr⟩` directly.
* `¬ M.IsIrreducible` case: unfold the def
  `IsIrreducible := ¬ M.IsZeroReducible ∧ ¬ M.IsPReducible` and
  apply `not_and_or` + `not_not` twice to recover
  `M.IsZeroReducible ∨ M.IsPReducible`. Each branch chains the
  appropriate single-step constructor (`PReducesTo.zeroStep` /
  `PReducesTo.step`) with the IH-supplied tail via cycle 192's
  `PReducesTo.trans`. The IH-arity argument is the strict descent
  witness from cycle 195 / 196
  (`hZ.zeroReduced_size_lt` / `hP.sBar_lt`).

End-to-end, the proof consumes:

* cycle 195's measure side (`size_le`, `size_lt_of_step`,
  `size_lt_of_zeroStep` — though `reducedMethod_exists` only
  invokes the strict-descent forms via the cycle 196 destructor
  spec lemmas);
* cycle 196's extraction side (`IsPReducible.partition`,
  `IsPReducible.sBar_lt`, `IsPReducible.partition_isPReducibleVia`,
  `IsZeroReducible.inP1`, `IsZeroReducible.exists_inP1_false`,
  `IsZeroReducible.inP1_isZeroReducibleVia`,
  `IsZeroReducible.zeroReduced_size_lt`);
* cycle 192's transitivity `PReducesTo.trans`.

### What this unblocks for def:381F

Combined with cycle 188's `eq_of_isIrreducible_of_pReducesTo`
(reduction sequences out of an irreducible source are reflexive)
and cycle 193's `PEquivalent.eq_of_both_isIrreducible` (two
irreducible P-equivalent methods coincide up to heterogeneous-stage
`HEq`), `reducedMethod_exists` lets us phrase def:381F existentially
without the multi-cycle constructive `reducedMethod` recursion:

> *(def:381F existential form)* Two methods `M`, `M'` are
> P-equivalent iff there exists a common irreducible reduct: i.e.
> `∃ s'' (M'' : RKTableau s''), M.PReducesTo M'' ∧ M'.PReducesTo M''
>   ∧ M''.IsIrreducible`.

This packaging is essentially one cycle of bridging away: extract
witnesses `(s₁, M₁, …)` and `(s₂, M₂, …)` from
`reducedMethod_exists` applied to `M` and `M'` respectively, then
use cycle-193 / cycle-194 lemmas to identify them when the original
`PEquivalent M M'` hypothesis is supplied. Cycle 198 candidate.

### What still remains for the constructive `reducedMethod`

The cycle 197 existential witness does **not** subsume the full
def:381E construction. The remaining work is:

* a `noncomputable def reducedMethod : RKTableau s → Σ s', RKTableau s'`
  recursive function obtained via either
  - **Option A** (Σ-wrapper `WellFoundedRelation`): derive
    `WellFoundedRelation (Σ s, RKTableau s)` from cycle 195's
    `size_lt_of_step`/`size_lt_of_zeroStep` via `WellFounded.onFun`
    with the first-projection map `(⟨s, M⟩ : Σ s, RKTableau s) ↦ s`,
    then use `WellFounded.fix` for the recursion;
  - **Option B** (`Decidable` instances): supply
    `Decidable (M.IsPReducible)` and `Decidable (M.IsZeroReducible)`
    so a structural `if … then … else` can be written, terminating
    by `decreasing_by` annotations citing the cycle 195 strict
    descent lemmas;
* a `reducedMethod_spec` lemma showing the constructive reduct
  satisfies `M.PReducesTo (reducedMethod M).2 ∧
  (reducedMethod M).2.IsIrreducible` — i.e. that the constructive
  function realises the cycle 197 existential.

Both options remain multi-cycle engineering. The cycle 197
existential witness is sufficient for *uniqueness*-flavoured
downstream applications (def:381F existential phrasing, thm:381H
canonical-normal-form arguments via cycle 193's
`eq_of_both_isIrreducible`), so the multi-cycle constructive
recursion can be deferred until a downstream theorem strictly
requires computing the reduct rather than asserting its existence.
Q1 / Q2 above are unchanged.
