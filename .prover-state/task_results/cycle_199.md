# Cycle 199 Results

## Worked on

* **P0** (mandatory smoke test) — `OpenMath/Chapter4/Section441.lean`
  GPFS smoke test, single attempt per the established 18-cycle
  pattern (now 19 consecutive).
* **P1** (substantive deliverable — *pivoted*) — shipped a weaker
  variant of the strategy's `pEquivalent_irreducible_reduct_unique`
  target: `pEquivalent_irreducible_reduct_unique_of_sources_irreducible`,
  inserted at `OpenMath/Chapter3/Section381.lean:866`, immediately
  after cycle 198's iff. The strategy's full target requires
  confluence of `PReducesTo` (Newman's lemma), which is not currently
  in scope; the gap is documented in a new issue file.
* **P1 stretch** — non-vacuity `example` exercising the weak variant
  on the reflexive `paddedEuler.pReduced pairPartition` case.
* **P2** (read-only recon) — read
  `extraction/formalization_data/entities/thm_381G.json` and the
  surrounding Butcher §380 prose at
  `extraction/raw_text/ch03.txt:8579–8623`. Summary below.

## Approach

### P0 — GPFS smoke test (19th consecutive block)

```text
$ ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D" \
    || echo "(no D-state processes)"
(no D-state processes)

$ time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
EXIT=124
real    5m0.032s
user    0m0.233s
sys     0m0.732s
```

CPU = (0.233 + 0.732) / 300 ≈ 0.32% of wall — identical near-zero
pattern as cycles 182–198. Logged the 19th-cycle update to
`.prover-state/issues/cycle_182_gpfs_slowness.md` and pivoted to
Priority 1.

### P1 — confluence-gap analysis and weak-variant pivot

**Pre-flight `Grep` verification of cycle 188/193/198 names**:

* `eq_of_isIrreducible_of_pReducesTo` — confirmed at
  `OpenMath/Chapter3/Section381.lean:502`. Signature
  `(hIrr : M.IsIrreducible) (h : PReducesTo M M') : s' = s ∧ HEq M' M`
  — **hypothesis is on the SOURCE `M`, not the target `M'`**.
* `PEquivalent.eq_of_both_isIrreducible` — confirmed at line 572.
  Signature
  `(hM : M.IsIrreducible) (hM' : M'.IsIrreducible) (h : PEquivalent M M')`
  → `∃ heq : s' = s, HEq M' M`. Both `PEquivalent` endpoints
  irreducible.
* `paddedEuler_pReduced_pairPartition_isIrreducible` — confirmed at
  line 1562.

**Critical finding**: The strategy's P1 target

```lean
theorem pEquivalent_irreducible_reduct_unique
    (h₁ : PReducesTo M M₁) (h₁irr : M₁.IsIrreducible)
    (h₂ : PReducesTo M' M₂) (h₂irr : M₂.IsIrreducible)
    (hEquiv : PEquivalent M M') :
    s₁ = s₂ ∧ HEq M₁ M₂
```

requires **confluence of `PReducesTo`** (uniqueness of normal forms),
which is not provable from cycle 188 / 193 / 198. The strategy's
recipe was based on the misreading that cycle 188's
`eq_of_isIrreducible_of_pReducesTo` extracts an irreducible
*target*; in fact it consumes an irreducible *source*. With only
target-irreducibility (the cycle 199 hypotheses `h₁irr`, `h₂irr`), no
extraction or transitivity argument in the current Section381
infrastructure produces the goal.

Four proof paths were tried and ruled out:

1. **Iff-then-cycle-188**: `pEquivalent_iff_exists_common_irreducible_reduct.mp`
   produces a third irreducible reduct `M₃`, leaving the goal as
   "identify `M₁` with `M₃` given that both are irreducible reducts
   of `M`". This is the local confluence diamond for `M`.
2. **Cycle 193 + transitivity**: composing
   `(PEquivalent.of_pReducesTo h₁).symm`, `hEquiv`, and
   `PEquivalent.of_pReducesTo h₂` to get `PEquivalent M₁ M₂` requires
   `PEquivalent.trans` with middles `M` and `M'`, neither of which is
   irreducible. Only `trans_of_middle_isIrreducible` is available,
   which explicitly notes (line 515) that general transitivity
   "would require confluence of P-reduction".
3. **Direct construction of `PEquivalent M₁ M₂`**: equivalent to the
   goal (since both endpoints are irreducible).
4. **Derive `PReducesTo M' M₁`**: equivalent to local confluence at
   `M` (need `PReducesTo N M₁` for some `N` in `hEquiv`'s
   destructuring).

The four-case local-confluence analysis (P/P, P/0, 0/P, 0/0 single
steps) is documented in
`.prover-state/issues/p_reduction_confluence_gap.md` along with a
multi-cycle plan toward the full uniqueness statement.

**Weak-variant shipped (cycle 199 P1)**:

```lean
theorem pEquivalent_irreducible_reduct_unique_of_sources_irreducible
    {s s' s₁ s₂ : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    {M₁ : RKTableau s₁} {M₂ : RKTableau s₂}
    (hMirr : M.IsIrreducible) (hM'irr : M'.IsIrreducible)
    (h₁ : PReducesTo M M₁) (h₂ : PReducesTo M' M₂)
    (hEquiv : PEquivalent M M') :
    s₁ = s₂ ∧ HEq M₁ M₂ := by
  obtain ⟨h₁eq, h₁heq⟩ := eq_of_isIrreducible_of_pReducesTo hMirr h₁
  obtain ⟨h₂eq, h₂heq⟩ := eq_of_isIrreducible_of_pReducesTo hM'irr h₂
  obtain ⟨h₃eq, h₃heq⟩ :=
    PEquivalent.eq_of_both_isIrreducible hMirr hM'irr hEquiv
  subst h₁eq
  subst h₂eq
  subst h₃eq
  exact ⟨rfl, (h₁heq.trans h₃heq.symm).trans h₂heq.symm⟩
```

Adds the hypotheses `M.IsIrreducible` and `M'.IsIrreducible`. Under
those hypotheses cycle 188 forces `h₁` and `h₂` to be reflexive
(`M₁ ≃ M` and `M₂ ≃ M'` up to `HEq`), and cycle 193 closes the
remaining `M ≃ M'` gap. The target-irreducibility hypotheses
`M₁.IsIrreducible`, `M₂.IsIrreducible` from the strategy's target
are dropped because cycle 188 forces them to be derivable from the
sources.

**Non-vacuity witness (P1 stretch, shipped)**:

```lean
example :
    (1 : ℕ) = 1 ∧
    HEq (paddedEuler.pReduced pairPartition)
        (paddedEuler.pReduced pairPartition) :=
  RKTableau.pEquivalent_irreducible_reduct_unique_of_sources_irreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    (RKTableau.PReducesTo.refl _)
    (RKTableau.PReducesTo.refl _)
    (RKTableau.PEquivalent.refl _)
```

Reflexive case on the canonical 1-stage irreducible witness.

### P2 — thm:381G recon (read-only)

**Textbook statement** (verbatim from
`extraction/formalization_data/entities/thm_381G.json`):

> Let (A, b, c) be an irreducible s-stage Runge–Kutta method.
> Then, for any two stage indices i, j ∈ {1, 2, . . . , s}, there
> exists a Lipschitz-continuous differential equation system such
> that Yi ≠ Yj. Furthermore, there exists t ∈ T, such that
> Φi(t) ≠ Φj(t).

**Location in Butcher prose**: `extraction/raw_text/ch03.txt:8579`
(immediately after def:381F at 8576, immediately before thm:381H at
8627).

**Dependency status** (from
`extraction/formalization_data/lean_status.json`):

| Dependency | Status | Notes |
|---|---|---|
| def:381E (IsIrreducible) | ✅ formalized | cycle 188 `IsIrreducible` |
| def:381D (IsPReducible) | ✅ formalized | cycle 186 `IsPReducible` |
| def:381B (PhiEquivalent) | ✅ formalized | cycle 184 `PhiEquivalent` |
| def:310A (elementaryDiff) | ✅ formalized | `elementaryDiff` |
| thm:301A (rooted-tree recursions) | ✅ formalized | `r_recursion`, etc. |
| **thm:314A** (Independence of elementary differentials) | **🛑 unformalized** | **load-bearing** |

**Estimated complexity: LARGE / multi-cycle**.

Reasons:

1. **thm:314A is unformalized.** The proof of thm:381G in Butcher
   explicitly uses "Theorem 314A (Independence of the elementary
   differentials)" to construct the contradicting differential
   equation system in the second half. thm:314A is itself a deep
   result about the linear independence of elementary differentials
   over R-vector-space spans. Formalizing it is plausibly its own
   multi-cycle project.
2. **The proof uses substantial linear algebra in `ℝ^s`**: an algebra
   `A` of partition-respecting vectors, a subalgebra `Ã` generated by
   elementary-weight vectors over all trees, and the argument
   `Ã = A` via construction of basis vectors (characteristic
   functions of partition blocks). This requires Mathlib subalgebra
   infrastructure and the trees-→-vector machinery from §310.
3. **Two-part contradiction structure**: the first part contradicts
   irreducibility from `Φi = Φj` for all `t`; the second part
   contradicts the assumption that there is no `t` with
   `Φi(t) ≠ Φj(t)` via the Lipschitz IVP construction. Both halves
   require subsections of §314.

**Single-cycle vs multi-cycle**: definitively **multi-cycle**. A
reasonable scoping is:

* Cycle N+1: formalize thm:314A (or a sufficient sub-lemma) —
  potentially itself a 2–3 cycle effort.
* Cycle N+2: subalgebra-generated-by-elementary-weights infrastructure.
* Cycle N+3: Lipschitz-IVP construction connecting `Φi(t) ≠ Φj(t)` to
  `Yi ≠ Yj` (the second-half contradiction).
* Cycle N+4: package as thm:381G.

**Recommendation for cycle 200's planner**: thm:381G is *not* a
viable single-cycle target. The cycle 198 worker's "highest-leverage"
suggestion of thm:381G as the next textbook target was based on the
existential characterization (cycle 198's iff) being a sufficient
ingredient; on closer inspection, the proof's linear-algebra content
is far heavier than the equivalence-class infrastructure. **Suggest
either**:

* **Pivot A**: target thm:381H directly. Per cycle 198's discovery #3
  and re-reading Butcher §380.8627–8667, thm:381H's proof references
  thm:381G only as a black-box hypothesis ("by Theorem 381G, there
  exists ..."); formalizing thm:381H with thm:381G *as a hypothesis*
  is single-cycle. Statement formalization first, proof can use
  `sorry` or take thm:381G axiom-style as an assumption to be
  discharged later.
* **Pivot B**: start the confluence infrastructure for the cycle 199
  P1 target. Per the confluence-gap issue, this is a 4–5 cycle
  effort but each cycle ships meaningful infrastructure.
* **Pivot C**: tackle thm:314A as the prerequisite, scoping it as
  its own multi-cycle subtree.

## Result

**SUCCESS** (partial, intentional pivot). Cycle 199 ships:

* P0 smoke-test log (19th cycle, matches established pattern).
* `.prover-state/issues/p_reduction_confluence_gap.md` — new issue
  documenting the confluence gap with 4 proof attempts and a 4–5
  cycle plan toward the full uniqueness statement.
* `pEquivalent_irreducible_reduct_unique_of_sources_irreducible`
  + non-vacuity witness — an honest weaker variant of the strategy
  target, axiom-clean.
* P2 thm:381G recon establishing it as a multi-cycle target with
  pivot recommendations.

Verification:

* `lake env lean OpenMath/Chapter3/Section381.lean` — EXIT=0, real
  43.876s, only the two pre-existing `heq` unused-variable warnings
  (lines 576 and 1651).
* `grep -c sorry OpenMath/Chapter3/Section381.lean` = 0 (unchanged
  from cycle 198).
* `wc -l OpenMath/Chapter3/Section381.lean` — file grew from 1657 to
  1721 (+64 LOC: theorem body + docstring + non-vacuity example +
  docstring), within the strategy's "+15 to +40 LOC" range plus
  ~25 LOC for the explanatory docstring linking to the issue file.
* `lean_verify` on
  `OpenMath.Chapter3.Section312.RKTableau.pEquivalent_irreducible_reduct_unique_of_sources_irreducible`:
  axioms `[propext, Classical.choice, Quot.sound]` — axiom-clean,
  expected `Classical.choice` inherited from cycle 193's
  `eq_of_both_isIrreducible` (which itself inherits from
  `reducedMethod_exists` consumed via cycle 198's iff).

## Faithfulness check

### `pEquivalent_irreducible_reduct_unique_of_sources_irreducible`

* Entity ID: **def:381F** (read
  `extraction/formalization_data/entities/def_381F.json` in cycle 198):

  > "Two Runge–Kutta methods are 'P-equivalent' if each of them
  > reduces to the same reduced method."

* The Lean statement captures: **strictly weaker than def:381F's
  natural canonical-form reading**. The textbook "reduces to the same
  reduced method" claim is uniqueness without the
  sources-irreducibility hypothesis; cycle 199 ships only the special
  case where the sources are already irreducible. Under that
  hypothesis the targets are forced to be reflexive collapses of the
  sources, so the lemma is mechanically a corollary of cycle 193's
  `eq_of_both_isIrreducible`. The full general statement remains open;
  see `.prover-state/issues/p_reduction_confluence_gap.md` for the
  multi-cycle plan.

* **No definition smuggling**: the lemma is named with the explicit
  `_of_sources_irreducible` suffix, the docstring leads with "*special
  case where both sources are already irreducible*", and explicitly
  links to the confluence-gap issue. No claim is made that this lemma
  closes def:381F's canonical-form story; it is shipped as an
  ergonomic API for callers who already know their inputs are
  irreducible.

* **Hypothesis strength**: the lemma adds two hypotheses (`hMirr`,
  `hM'irr`) beyond the strategy target's signature and drops two
  hypotheses (`h₁irr`, `h₂irr`) that become redundant under the new
  hypotheses. This is a strictly weaker statement (fewer conclusions
  derivable, more hypotheses required), documented in the docstring.

* **Tautology check**: the conclusion `s₁ = s₂ ∧ HEq M₁ M₂` does not
  appear verbatim among the hypotheses. The proof actively consumes
  all five hypotheses: `hMirr` and `h₁` go into the first cycle 188
  application; `hM'irr` and `h₂` into the second; both go into the
  cycle 193 application; `hEquiv` is the substantive input to cycle
  193.

* **Identity check**: not applicable — the proof is a 7-line tactic
  block with three `obtain ⟨_, _⟩`, three `subst`, and a closing
  `exact` involving an `HEq.trans` chain.

### Non-vacuity `example`

* Not a named theorem — exercises the new lemma on the canonical
  1-stage `paddedEuler.pReduced pairPartition` (cycle 190 witness for
  `IsIrreducible`). Trivial reflexive case in all five hypothesis
  slots, but confirms the lemma fires non-vacuously.

## Dead ends

1. **Strategy's primary recipe** (Step A + Step B with cycle 188 to
   identify M₁ with M₃): cycle 188 takes an irreducible source, not
   target. Recipe ruled out at pre-flight `Grep` stage.

2. **Strategy's fallback recipe** (Step B' via direct cycle 188 on
   h₁ + h₁irr): same source-vs-target confusion. Ruled out.

3. **Strategy's alternative cycle 193 route** (build `PEquivalent M₁
   M₂` and apply `eq_of_both_isIrreducible`): blocks on general
   transitivity of `PEquivalent` with non-irreducible middles, which
   is exactly what `trans_of_middle_isIrreducible`'s line-515
   docstring says "would require confluence of P-reduction".

4. **Direct construction of `PReducesTo M' M₁`**: reduces to the
   local-confluence diamond for source `M`. Same confluence gap.

All four dead ends are documented in
`.prover-state/issues/p_reduction_confluence_gap.md` for future
reference.

## Discovery

1. **Strategy planner misread cycle 188's signature**. The cycle 199
   strategy claimed cycle 188's `eq_of_isIrreducible_of_pReducesTo`
   would extract an irreducible target from a `PReducesTo` chain; in
   fact it requires the *source* to be irreducible. This is the
   only failure mode the strategy's risk analysis didn't anticipate.
   Future planner cycles should `Grep`-verify signature *directions*
   (which argument is the hypothesis vs conclusion side), not just
   lemma names. Specifically: for each cited lemma, the strategy
   should record (hyp_var, conclusion_var) pairs.

2. **Cycle 198's discovery #2 underestimated the cost**. The cycle
   198 worker described a "clean ~10-LOC follow-up" for the
   uniqueness theorem, but the actual uniqueness statement requires
   confluence reasoning that is 4–5 cycles of infrastructure. The
   discrepancy traces to the cycle 198 worker not running the
   signature-direction analysis at the time of writing the "next
   approach" notes. Both cycle 198 and cycle 199 strategy notes
   propagated the underestimate.

3. **The `Section381.lean` `PEquivalent` API already contains the
   docstring-level hint about confluence**:
   `trans_of_middle_isIrreducible` at line 511 documents that
   "general `PEquivalent.trans` over arbitrary middle methods would
   require confluence of P-reduction". This text was added in cycle
   185 (per the docstring's own attribution) and has been visible
   for 14+ cycles. Cycle 198's strategy did not surface this
   constraint. Recommendation for future planners: when proposing
   uniqueness-flavored lemmas, search Section381 for "confluence" /
   "would require" to detect known infrastructure gaps before
   estimating LOC.

4. **GPFS pathology now at 18 calendar days / 19 cycles**: no
   variation. Pre-flight `ps` check showed no D-state processes;
   smoke test timed out at exactly 300s with 0.32% CPU. Pattern
   exactly matches cycles 182–198.

5. **thm:381G recon: not single-cycle**. Per the P2 recon above,
   thm:381G requires thm:314A (currently unformalized) plus
   substantial linear-algebra-in-ℝ^s infrastructure. The cycle 198
   suggestion to target thm:381G next is correct in priority
   ordering (it is the next textbook entity) but underestimates
   complexity by ~3 cycles.

## Suggested next approach

For cycle 200's planner:

1. **Highest-leverage low-cost**: ship `thm:381H` *as a statement
   only*, with the proof using thm:381G + thm:381A + thm:381B
   axioms-style (or `sorry`-with-tracking). This formalizes the
   key equivalence-of-equivalences theorem at the spec level
   without requiring thm:381G's full proof. Single-cycle ETA.

2. **Confluence track**: per the new issue
   `p_reduction_confluence_gap.md`, start with the lattice-closure
   lemmas (Option A, cycle N+1). The first piece is
   `IsPReducibleVia_join` for two partitions on the same method.
   This unblocks the full `pEquivalent_irreducible_reduct_unique` in
   ~4 more cycles.

3. **Heavy textbook track**: target thm:314A as the prerequisite for
   thm:381G. Itself likely 2–3 cycles. Only viable if cycles 200–204
   are budgeted for a single deep arc.

4. **Constructive `noncomputable def reducedMethod`**: still deferred
   per cycle 197/198 strategy. Cycle 199's weak variant
   `pEquivalent_irreducible_reduct_unique_of_sources_irreducible` is
   a strictly weaker theorem and does not increase the value of the
   constructive recursion. Strategy anti-item 7 from cycle 199
   remains the right call.

5. **Section441 Phase C.2 / C.3 / C.4**: still blocked by 19-cycle
   GPFS pathology. Continue the established one-attempt-per-cycle
   smoke-test pattern.
