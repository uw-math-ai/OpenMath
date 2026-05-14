# Cycle 229 Results

## Worked on
- §383 group-homomorphism path Phase 3 follow-up — right-identity
  counterpart of cycle 228's left-identity laws.
- Two new symbols in `OpenMath/Chapter3/Section381.lean`:
  `RKTableau.compose_id_phiEquivalent` and
  `RKTableau.composeQ_phi_left_act_id_right`.
- One P2 non-vacuity `example`.
- Single Aristotle poll on right-action job
  `176aa964-db7b-40f8-a01c-05247c186ec5` (IN_PROGRESS at 17 %, up from
  cycle 228's 11 %).

## Approach
1. Polled Aristotle exactly once per CLAUDE.md discipline. Status:
   IN_PROGRESS at 17 %. Branched to strategy §D (path B).
2. Inserted three new declarations between cycle 228's
   `composeQ_phi_left_act_id_left` (line 3402) and the §382 `Inverse
   method` section block (now line 3454):
   - `compose_id_phiEquivalent {s} (M : RKTableau s) : @PhiEquivalent
     (s + 0) s (M.compose RKTableau.id) M`
   - `composeQ_phi_left_act_id_right (q : Quotient
     PhiEquivalent.setoidSigma) : composeQ_phi_left_act q ⟨0,
     RKTableau.id⟩ = q`
3. Proof of `compose_id_phiEquivalent`: a single rewrite with cycle
   225's `compose_elementaryWeight_decomp M RKTableau.id t` puts the
   goal in the form
   `M.elementaryWeight t + ∑ i : Fin 0, RKTableau.id.b i *
     RKTableau.id.derivativeWeightWithSrc M i t = M.elementaryWeight t`,
   which `simp` closes by collapsing the empty `Fin 0` sum to `0` and
   simplifying `_ + 0`.
4. Proof of `composeQ_phi_left_act_id_right`: `Quotient.inductionOn q`
   + `rintro ⟨s, M⟩` reduces the goal to
   `Quotient.mk _ _ ⟨s + 0, M.compose RKTableau.id⟩ = Quotient.mk _ _
   ⟨s, M⟩`, then `Quotient.sound (compose_id_phiEquivalent M)` closes
   (using `s + 0 = s` definitional equality).
5. P2 non-vacuity at file's end exercises the right-identity on
   `⟨2, paddedEuler⟩` — symmetric counterpart of cycle 228's
   `composeQ_phi_left_act_id_left_paddedEuler` example.

## Result
**SUCCESS** — both new theorems compile, are axiom-clean, and the file
sorry count remains 0.

Axiom set for both new symbols:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no new
well-founded recursion axioms.

Section381.lean warm rebuild: **6.228 s** (substantial improvement
over cycle 228's ~14 s; well under §F.5 30 s red-flag threshold).

Regression spot-checks all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):
- `compose_phiEquivalent_compose_left` (cycle 226)
- `composeQ_phi_left_act` (cycle 227)
- `composeQ_phi_left_act_id_left` (cycle 228)
- `id_compose_phiEquivalent` (cycle 228)
- `composeQ_eq_of_equivalent` (cycle 218 §382 landmark)
- `instGroup` (cycle 222 §382 group instance)

Sorry count: **0** (43rd consecutive clean cycle since cycle 201
rollback).

## Faithfulness check

### `compose_id_phiEquivalent`
- Entity ID: associated with `thm:384A` (Butcher §384 group
  homomorphism Φ).
- Textbook statement (quoted from
  `extraction/formalization_data/entities/thm_384A.json`'s
  `statement_latex`):
  > "Let G be the set of all RK methods (as a group under composition).
  > Let G ̃ be the quotient of G by Φ-equivalence. Then the canonical
  > projection π : G → G ̃ is a homomorphism."
- The right-identity `PhiEquivalent (M.compose RKTableau.id) M` is a
  *helper lemma* underwriting the eventual homomorphism statement
  (the identity element preserves under Φ). The Lean statement
  captures the **right-symmetric counterpart of cycle 228's
  `id_compose_phiEquivalent`** at the same level of fidelity: a
  helper at the `PhiEquivalent` level proving the §383 group's
  identity acts trivially on the right.
- Status: same content as the textbook expectation for the §383
  identity law (right side). Not a standalone Butcher theorem; the
  fully synthesised `MonoidHom` will subsume it.

### `composeQ_phi_left_act_id_right`
- Entity ID: same `thm:384A` cluster.
- Textbook coverage: the quotient-level analog of the right-identity
  law. Captures the §384 statement at the partial-action
  (one-sided) level for the §383 Φ-quotient.
- Same content level as cycle 228's `composeQ_phi_left_act_id_left`;
  symmetric counterpart.

### Tautology / identity / definition-smuggling / hypothesis-strength
- Tautology check: neither conclusion appears verbatim as a
  hypothesis. PASS.
- Identity check: proofs are not single `exact h`. Both proofs
  perform genuine work via `Quotient.sound` and
  `compose_elementaryWeight_decomp`. PASS.
- Definition smuggling: no new `def`/`structure` — only `theorem`s.
  PASS.
- Hypothesis strength: both theorems take only the minimal hypotheses
  (a stage count and a tableau, or a quotient class). PASS.

## Dead ends
None — the proof recipe in strategy §D.2 worked first attempt
(`intro t ; rw [...] ; simp` closed `compose_id_phiEquivalent`
directly; the longhand fallback recipe was not needed).

## Discovery
1. **`Fin 0` sum collapse via `simp`** — `simp` is sufficient to
   close `M.elementaryWeight t + ∑ i : Fin 0, ... = M.elementaryWeight
   t` in this codebase. `Finset.sum_empty` fires automatically as a
   default simp lemma when the index type reduces to an empty
   `Finset` (here `Finset.univ : Finset (Fin 0)`). This is much
   cheaper than the longhand `Fin.sum_univ_zero`/`Finset.sum_empty`
   recipe and avoids needing explicit `rw [add_zero]`.
2. **Right-identity is structurally cheaper than left-identity** in
   the §383 `PhiEquivalent` setting: cycle 228 needed mutual induction
   on `RootedTree` to collapse `derivativeWeightWithSrc M id` to
   `derivativeWeight M` (two private mutual theorems
   `derivativeWeightWithSrc_id`/`derivativeWeightWithSrcProd_id`),
   whereas cycle 229's right-identity is closed by a single `simp` on
   the post-rewrite goal because the bottom-block sum ranges over
   `Fin 0` and the *whole* sum vanishes, eliminating the need for any
   tree-induction infrastructure.
3. **Aristotle progress signal**: 11 % → 17 % across ~24 hours
   suggests several-day ETA (linearly extrapolated) on the M₂-side
   sum equality. Cycle 230's outlook is identical to cycle 229's:
   single re-poll + branch.

## Suggested next approach
Cycle 230 should:

1. **Single Aristotle poll** on `176aa964-db7b-40f8-a01c-05247c186ec5`.
   If `COMPLETE` → execute strategy §C (full `composeQ_phi` ship). If
   `IN_PROGRESS`/`FAILED` → continue accreting partial-action
   infrastructure.

2. **If still gated** (path B again):
   - Prove `compose_assoc_phiEquivalent {s₁ s₂ s₃}` (associativity at
     the PhiEquivalent level — three-way associativity should follow
     from the Connes-Kreimer-free `compose_elementaryWeight_decomp`
     applied twice, recursively threading
     `derivativeWeightWithSrc_subst_M₁`).
   - Or prove `composeQ_phi_left_act_assoc` (associativity on the
     partial action — `composeQ_phi_left_act
     (composeQ_phi_left_act p q.1) q.2.1 = composeQ_phi_left_act p
     ⟨q.1 + q.2.1, ...⟩`).
   - Or pivot to inverse-method right-action: prove `PhiEquivalent
     (M.compose M.inverse) RKTableau.id` (right inverse at the §383
     level) — but this is the same Connes-Kreimer territory as the
     Aristotle job, so likely also requires Aristotle compute.

3. **Path A bookkeeping prep**: if Aristotle returns, the bracketed-
   form corollary `composeQ_phi_eq_of_phiEquivalent` and full binary
   `composeQ_phi` ship in one cycle (strategy §C.3–C.7). After path
   A, cycle 231 can target the §383 `Group (Quotient
   PhiEquivalent.setoidSigma)` instance via `Group.ofLeftAxioms`
   (porting cycle 222's §382 `instGroup` recipe to the Φ-quotient).

4. **§441 Phase C.2**: SKIP for the 45th consecutive cycle. GPFS-
   blocked since cycle 182.
