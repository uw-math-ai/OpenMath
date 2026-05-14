# Issue: P-reduction confluence gap blocks `pEquivalent_irreducible_reduct_unique`

## Blocker

Cycle 199's strategy proposed shipping a heterogeneous-stage uniqueness
companion to cycle 198's `pEquivalent_iff_exists_common_irreducible_reduct`:

```lean
theorem pEquivalent_irreducible_reduct_unique
    {s s' s₁ s₂ : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    {M₁ : RKTableau s₁} {M₂ : RKTableau s₂}
    (h₁ : PReducesTo M M₁) (h₁irr : M₁.IsIrreducible)
    (h₂ : PReducesTo M' M₂) (h₂irr : M₂.IsIrreducible)
    (hEquiv : PEquivalent M M') :
    s₁ = s₂ ∧ HEq M₁ M₂
```

The strategy claimed this is a clean ~10-LOC follow-up that consumes
cycle 188's `eq_of_isIrreducible_of_pReducesTo` + cycle 193's
`PEquivalent.eq_of_both_isIrreducible` + cycle 198's iff.

**This claim is incorrect.** Cycle 188's lemma requires an irreducible
**source** of a `PReducesTo` chain; the cycle 199 target's hypotheses
`h₁irr` and `h₂irr` instead supply irreducible **targets** (M₁ and M₂
are the reducts, not the starting methods). The substantive content of
the target is precisely the missing converse: uniqueness of an
irreducible normal form across distinct reduction paths.

## Context

### The two ingredient lemmas, restated

`eq_of_isIrreducible_of_pReducesTo` (cycle 188, line 502 in
`OpenMath/Chapter3/Section381.lean`):

```lean
theorem eq_of_isIrreducible_of_pReducesTo {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (hIrr : M.IsIrreducible) (h : PReducesTo M M') :
    s' = s ∧ HEq M' M
```

Hypothesis: `M.IsIrreducible` — source-side irreducibility.

`PEquivalent.eq_of_both_isIrreducible` (cycle 193, line 572):

```lean
theorem PEquivalent.eq_of_both_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hM : M.IsIrreducible) (hM' : M'.IsIrreducible)
    (h : PEquivalent M M') :
    ∃ heq : s' = s, HEq M' M
```

Hypotheses: both `PEquivalent` endpoints irreducible.

### What's actually missing

Setting `M = M'` in the cycle 199 target collapses it to:

> If `M` has two irreducible reducts `M₁` and `M₂`, then `M₁ ≃ M₂` (up to `HEq`).

This is uniqueness of normal forms under the abstract rewriting system
defined by `PReducesTo`. By Newman's lemma, this is implied by
**termination + local confluence**:

* **Termination** is already proved (cycle 195's `PReducesTo.size_le`
  + `size_lt_of_step` + `size_lt_of_zeroStep` give strict stage-count
  descent on every non-reflexive single step).
* **Local confluence** — i.e. that any two single-step reductions
  M → N₁ and M → N₂ have a common reduct N — is the missing piece.

Local confluence for `PReducesTo` has four cases (per the
`step` / `zeroStep` constructor combinations):

1. **P/P**: `M.IsPReducibleVia P₁` and `M.IsPReducibleVia P₂` —
   reductions to `M.pReduced P₁` and `M.pReduced P₂` via two distinct
   partitions. The natural candidate for a common reduct is
   `M.pReduced (P₁ ⊔ P₂)` (the join in the partition lattice), but
   this requires:
   * Proving the lattice join of two `IsPReducibleVia`-witnessing
     partitions is itself `IsPReducibleVia` for `M` — i.e. the
     P-reducing-partition predicate is closed under joins.
   * Constructing the secondary reductions
     `M.pReduced P₁ → M.pReduced (P₁ ⊔ P₂)` and symmetrically for
     P₂ — i.e. that the further-refined partition factors through
     each.
2. **P/0**: `M.IsPReducibleVia P` and `M.IsZeroReducibleVia inP1` —
   mixed reduction. The interaction between P-partitions and
   0-partitions (boolean predicates) needs analysis; in particular,
   `M.pReduced P` may or may not be 0-reducible at the pushed-forward
   boolean predicate, and vice versa.
3. **0/P**: symmetric to P/0.
4. **0/0**: `M.IsZeroReducibleVia inP1` and `M.IsZeroReducibleVia inP2`
   — two boolean-predicate 0-reductions. The natural common reduct
   would be `M.zeroReduced (inP1 ∧ inP2)` (componentwise conjunction),
   but again the lattice-meet of `IsZeroReducibleVia`-witnessing
   predicates needs to be shown to itself witness 0-reducibility, and
   the factoring reductions need to be constructed.

Each case requires both:
* **Lattice closure**: the relevant lattice operation on partitions /
  boolean predicates preserves the reducibility witness.
* **Functoriality of reduction**: the reduction operation respects the
  refinement order, producing the secondary `PReducesTo` arrows that
  complete the diamond.

## What was tried

Cycle 199 explored four proof attempts during pre-flight analysis,
each of which transparently reduced to the missing confluence lemma:

1. **Iff-then-cycle-188** (strategy's primary recipe): apply
   `pEquivalent_iff_exists_common_irreducible_reduct.mp hEquiv` to
   obtain a common irreducible reduct `M₃` of `M` and `M'`. Then
   attempt to identify `M₁` with `M₃` via cycle 188 applied to the two
   reduction paths from `M`. Fails because cycle 188 requires the
   **source** `M` to be irreducible (not the target).

2. **Cycle 193 route via transitivity**: build
   `PEquivalent M₁ M₂` from `(PEquivalent.of_pReducesTo h₁).symm`,
   `hEquiv`, and `PEquivalent.of_pReducesTo h₂`, then apply
   `eq_of_both_isIrreducible`. Fails because composing three
   `PEquivalent` witnesses requires `trans` with middle endpoints
   `M` and `M'`, neither of which is hypothesised to be irreducible.
   The only transitivity available
   (`PEquivalent.trans_of_middle_isIrreducible`, line 528) requires an
   irreducible middle — its docstring explicitly notes that "the
   general `PEquivalent.trans` over arbitrary middle methods would
   require confluence of P-reduction".

3. **Direct construction of `PEquivalent M₁ M₂`**: by definition this
   requires `∃ N. PReducesTo M₁ N ∧ PReducesTo M₂ N`. With both `M₁`
   and `M₂` irreducible, cycle 188 forces `N = M₁ = M₂` up to `HEq`,
   making `PEquivalent M₁ M₂` equivalent to `s₁ = s₂ ∧ HEq M₁ M₂` —
   the very goal. Circular.

4. **Derive `PReducesTo M' M₁` (or symmetric)**: would allow
   constructing `PEquivalent M₁ M₂` as `⟨M₁, refl, h_M'M₁ via h₁⟩`.
   But deriving `PReducesTo M' M₁` requires choosing a path through
   the PEquivalent witness `hEquiv = ⟨N, hMN, hM'N⟩` that lands on
   `M₁`: specifically, `PReducesTo N M₁` must be constructible from
   `hMN : PReducesTo M N`, `h₁ : PReducesTo M M₁`, and `M₁` irreducible.
   This is exactly the local-confluence diamond for the source `M`.

## Possible solutions

### Option A — full confluence (multi-cycle, recommended for cycle 200+)

Prove local confluence by case analysis on the two reduction steps:

* **Cycle N+1**: lattice-closure lemmas
  * `IsPReducibleVia_join`: if `M.IsPReducibleVia P₁` and
    `M.IsPReducibleVia P₂`, then `M.IsPReducibleVia (P₁ ⊔ P₂)` (with
    appropriate handling of trivial joins where one partition refines
    the other).
  * `IsZeroReducibleVia_meet`: if `M.IsZeroReducibleVia inP1` and
    `M.IsZeroReducibleVia inP2`, then
    `M.IsZeroReducibleVia (inP1 ∧ inP2)` (with non-emptiness
    side-conditions).
* **Cycle N+2**: factoring reductions
  * `pReduced_pReducesTo_pReduced_of_refines`: if `P` refines `Q`,
    then `M.pReduced P → M.pReduced Q`.
  * `zeroReduced_pReducesTo_zeroReduced_of_implies`: if `inP1 → inP2`,
    then `M.zeroReduced inP1 → M.zeroReduced inP2`.
* **Cycle N+3**: cross-step confluence (P/0 and 0/P cases) — requires
  understanding how P-reductions interact with 0-reductions on the
  same source.
* **Cycle N+4**: package as `PReducesTo.confluent` (single-step
  diamond) and lift to `PReducesTo.normal_form_unique` via Newman's
  lemma using cycle 195's termination.
* **Cycle N+5**: ship `pEquivalent_irreducible_reduct_unique` as a
  ~5-LOC corollary of `normal_form_unique` + cycle 198's iff.

Total: ~5 cycles of substantive infrastructure work. Each cycle is
self-contained and produces axiom-clean theorems matching the project
rules.

### Option B — weaker variant shipped in cycle 199

Cycle 199 ships
`pEquivalent_irreducible_reduct_unique_of_sources_irreducible`
(see `OpenMath/Chapter3/Section381.lean`), which adds the auxiliary
hypothesis that the *sources* `M` and `M'` are themselves irreducible.
Under that hypothesis cycle 188 forces both `h₁` and `h₂` to be
reflexive, reducing the goal to cycle 193's `eq_of_both_isIrreducible`
with HEq plumbing. This is a strictly weaker statement (the cycle 198
iff witness is not consumed) but it is axiom-clean and gives downstream
callers an ergonomic API for the special case where they already know
their inputs are reduced.

### Option C — defer indefinitely

The cycle 198 iff already provides the existential half of def:381F.
Many downstream consumers (`thm:381G`, `thm:381H`) only need
existence, not uniqueness. If confluence proves too costly, the
uniqueness theorem can be left unproved without blocking the textbook
progression.

## What downstream consumers need

* **thm:381H** (def:381F ⇔ def:381A ⇔ def:381B): per the cycle 198
  task results' "highest-leverage" suggestion, this is the natural
  next textbook target after def:381F. Reading the Butcher prose at
  `extraction/raw_text/ch03.txt:8627–8667`, the proof of thm:381H
  uses thm:381G but does not explicitly invoke uniqueness of the
  irreducible reduct — only existence (which we have via cycle 198's
  iff). **thm:381H is likely unblocked by cycle 198 alone.**
* **thm:381G** (cycle 199 P2 recon target): per its `dependencies`
  list in
  `extraction/formalization_data/entities/thm_381G.json`, only
  def:381E and thm:314A are listed; uniqueness of the reduced method
  is not required. **thm:381G is also unblocked by cycle 198 alone.**
* Downstream of the equivalence-class theory (§382 — composition
  group of equivalence classes), uniqueness of the canonical
  representative does become load-bearing. That subsection is the
  natural pressure point for Option A confluence work.

## Recommendation

For cycle 200's planner: pivot to thm:381G or thm:381H rather than
attempting the full uniqueness proof. The confluence infrastructure
(Option A) is best scoped as a 4–5 cycle effort *after* the textbook
prose target shifts to §382 and uniqueness becomes a hard
dependency.
