# Cycle 231 Strategy

## §A. Pre-flight: §441 Phase C.2 status

**SKIP §441 Phase C.2 entirely this cycle.** GPFS slowness on
`Section441.lean` has timed out 45+ consecutive smoke tests
(cycles 182–230). The cycle 182 draft + cycle 184 namespace fix
remain preserved at `.prover-state/cycle_182_draft_section441.lean`,
awaiting cluster-admin recovery. Do NOT attempt a smoke test this
cycle — it will burn ~5 min of wall time with zero CPU progress.
Continue on the §383 group-homomorphism path.

## §B. Priority 0 — Single Aristotle poll (one call only)

Run **exactly one** poll on the right-action job:

```
mcp__aristotle__get_status project_id="176aa964-db7b-40f8-a01c-05247c186ec5"
```

Growth trajectory across cycles 227 → 228 → 229 → 230:
9 % → 11 % → 17 % → 24 %. At the current rate (≈ 2–7 %/cycle),
expect 26–31 % this cycle. **Do NOT re-poll** mid-cycle per
CLAUDE.md single-poll discipline. Decision tree:

* **COMPLETE_SUCCESS** → branch to §C (Path A: incorporate the
  right-action proof, ship the full binary `composeQ_phi`).
* **COMPLETE_WITH_ERRORS** → download the result, audit for any
  one-line fixes (cf. cycle 184's namespace fix), apply locally,
  attempt incorporation; if errors are structural, fall through to §D.
* **IN_PROGRESS** (any %) or **FAILED** → branch to §D (Path B:
  ship the bottom-block partner `derivativeWeightWithSrc_compose_natAdd`).
* **CANCELLED** → log + branch to §D.

## §C. Path A — Aristotle COMPLETE branch (preferred outcome)

Only execute if Aristotle returned a usable proof of the M₂-side
sum equality (the right-action half of
`compose_phiEquivalent_compose`). If unsure whether Path A is
viable, default to §D.

1. **Download** the result via `mcp__aristotle__download_result`
   and **extract** via `mcp__aristotle__extract_result`.
2. **Inspect** the proof body for surprises: external axioms,
   unexpected hypotheses on `M₂` (e.g. preconsistency, irreducibility),
   new helper lemmas. If any surface, document them in the
   docstring as faithfulness divergences before incorporating.
3. **Insert** the right-action theorem at
   `OpenMath/Chapter3/Section381.lean`, immediately after cycle 226's
   `compose_phiEquivalent_compose_left` (which ends near line 2860
   in HEAD; insertion location shifts slightly due to cycle 230's
   ~50-LOC insertion at lines ~2862–2920).
4. **Assemble** the full `compose_phiEquivalent_compose` as the
   conjunction `compose_phiEquivalent_compose_left + right_action`,
   then build the full
   `composeQ_phi : Quotient PhiEquivalent.setoidSigma →
                   Quotient PhiEquivalent.setoidSigma →
                   Quotient PhiEquivalent.setoidSigma`
   via `Quotient.lift₂`, with the respect obligation discharged by
   the new full theorem.
5. **Promote** `composeQ_phi_left_act` (cycle 227) to a corollary
   of `composeQ_phi` by lifting the right argument:
   `composeQ_phi_left_act p q = composeQ_phi p ⟦q⟧`.
6. **Axiom check** every new symbol via `lean_verify`. Each must
   return `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
   no external axioms introduced by Aristotle).
7. **Update** `lean_status.json` `thm:384A` row from `partial` to
   `formalized` if and only if the full Φ homomorphism statement
   lands. Otherwise keep `partial` with a cycle 231 note.

If §C lands cleanly, the cycle's deliverable target is met.
Do NOT additionally attempt §D — that path is now superseded.

## §D. Path B — Bottom-block partner (primary plan if Aristotle still IN_PROGRESS)

Ship `derivativeWeightWithSrc_compose_natAdd` plus its list-helper
companion, mirroring cycle 230's top-block deliverable.

### D.1 Signatures

Add at `OpenMath/Chapter3/Section381.lean` immediately after cycle
230's top-block mutual block (current location: just before cycle
227's `composeQ_phi_left_act` doc block). Wrap in a fresh
`section ... open OpenMath.Chapter3.Section310 ... end` block inside
`namespace OpenMath.Chapter3.Section312.RKTableau` per the
established cycle 224/225/226/230 pattern.

```lean
mutual

  private theorem derivativeWeightWithSrc_compose_natAdd
      {s₁ s₂ s₃ : ℕ}
      (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
      ∀ (t : RootedTree) (k : Fin s₃),
        (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t
          = M₃.derivativeWeightWithSrc (M₁.compose M₂) k t

  private theorem derivativeWeightWithSrcProd_compose_natAdd
      {s₁ s₂ s₃ : ℕ}
      (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
      ∀ (children : List RootedTree) (k : Fin s₃),
        (M₂.compose M₃).derivativeWeightWithSrcProd M₁ (Fin.natAdd s₂ k) children
          = M₃.derivativeWeightWithSrcProd (M₁.compose M₂) k children

end
```

### D.2 Proof recipe (per-tree branch)

For `t = RootedTree.mk children`, the per-tree branch is a
delegation: `show ...derivativeWeightWithSrcProd... ; exact
derivativeWeightWithSrcProd_compose_natAdd M₁ M₂ M₃ children k`.
Identical to cycle 230's per-tree branch.

### D.3 Proof recipe (list-helper branch) — the substantive case

Case `children = []`: both sides reduce to `1` by definition; close
by `rfl`.

Case `children = t :: ts`:

1. **Unfold cons cell**. `show` rewrites both sides to expose
   `(elementaryWeight + ∑_{k' : Fin (s₂+s₃)} A_compose · weight) *
   tail` on LHS and
   `(elementaryWeight + ∑_{k' : Fin s₃} M₃.A · weight) * tail`
   on RHS. The `elementaryWeight` factor is `M₁.elementaryWeight t`
   on the LHS (because the source method threaded into
   `derivativeWeightWithSrc` is `M₁`) and `(M₁.compose
   M₂).elementaryWeight t` on the RHS (because the source method
   for the RHS is `M₁.compose M₂`).
2. **Apply IH on the tail**:
   `rw [derivativeWeightWithSrcProd_compose_natAdd M₁ M₂ M₃ ts k]`
   to push the IH through the trailing list.
3. **Two `congr 1`**: per cycle 230 discovery #1, the cons cell is
   `(elementaryWeight + sum) * tail` shape, so peel two layers
   (outer `_ * _`, then inner `_ + _`). After these, the goal
   reduces to BOTH (a) the `elementaryWeight` equality and (b) the
   per-summand sum equality. But because the elementaryWeights
   differ (LHS has `M₁.elementaryWeight t`, RHS has
   `(M₁.compose M₂).elementaryWeight t`), the first `congr 1`
   reduces to a single big equality of sums-with-elementaryWeight-
   prefixes, NOT cleanly to per-summand. See step 4.
4. **Combine the elementaryWeight + sum on the RHS via
   `compose_elementaryWeight_decomp` (cycle 225)**: the RHS
   `(M₁.compose M₂).elementaryWeight t + ∑ k' : Fin s₃, M₃.A k k' *
   M₃.derivativeWeightWithSrc (M₁.compose M₂) k' t` should be
   reachable from the LHS form via a rearrangement that uses cycle
   225's decomposition `(M₁.compose M₂).elementaryWeight t =
   M₁.elementaryWeight t + ∑ j : Fin s₁, M₁.b j *
   M₁.derivativeWeight j t` (verify the exact statement at the
   `compose_elementaryWeight_decomp` definition; if the cycle 225
   form differs in argument order or sign, adjust accordingly).

   Strategy: rewrite RHS's `(M₁.compose M₂).elementaryWeight t`
   to the decomposed form, so RHS becomes
   `M₁.elementaryWeight t + (decomposition-sum + M₃-sum)`. Then
   the elementaryWeights on LHS and RHS both become
   `M₁.elementaryWeight t`, and the remaining sum equality is
   `∑ k' : Fin (s₂+s₃), A_compose · weight = decomposition-sum +
   M₃-sum`.

   If `compose_elementaryWeight_decomp` does NOT cleanly fire on
   the RHS, this is the abort threshold — see §E.
5. **Block-split the LHS sum** via `Fin.sum_univ_add` on
   `Fin (s₂ + s₃)`. The split produces top-block (`castAdd s₃`-
   indexed) + bottom-block (`natAdd s₂`-indexed) summands.
6. **Simp the A blocks**: `simp only [compose_A_botLeft,
   compose_A_botRight]`. Per cycle 209's lemmas,
   `compose_A_botLeft (natAdd s₂ k) (castAdd s₃ j₁) = M₂.b j₁` and
   `compose_A_botRight (natAdd s₂ k) (natAdd s₂ j₂) = M₃.A k j₂`.
   Unlike cycle 230 (top-block), neither half vanishes — both
   contribute.
7. **Route the top half** (now of the form `∑ j₁ : Fin s₂, M₂.b j₁
   * (M₂.compose M₃).derivativeWeightWithSrc M₁ (castAdd s₃ j₁) t`)
   through **cycle 230's top-block lemma**
   `derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j₁` to
   collapse the composite's source-method-threaded weight to
   `M₂.derivativeWeightWithSrc M₁ j₁ t`. Result:
   `∑ j₁, M₂.b j₁ * M₂.derivativeWeightWithSrc M₁ j₁ t` — which is
   the decomposition expansion of `(M₁.compose M₂).elementaryWeight t
   - M₁.elementaryWeight t` (and, after rewriting in step 4, equals
   the decomposition-sum on the RHS).

   **Wait — verify decomposition shape**: cycle 225's
   `compose_elementaryWeight_decomp` likely uses `M₂`'s
   `derivativeWeight` not `derivativeWeightWithSrc`. The top-half
   collapse from cycle 230 gives
   `M₂.derivativeWeightWithSrc M₁ j₁ t`, which is in general
   DIFFERENT from `M₂.derivativeWeight j₁ t` (the former threads
   `M₁`'s `elementaryWeight` into the recursion). If
   `compose_elementaryWeight_decomp`'s RHS-sum is `∑ j : Fin s₁,
   M₁.b j * M₁.derivativeWeight j t` (cycle 225 form per its
   commit message), then the matching is NOT direct — the top
   half here produces `M₂`-indexed terms, not `M₁`-indexed terms.

   This is a **CRITICAL CHECK** before committing to the recipe.
   Open `OpenMath/Chapter3/Section381.lean`, find
   `compose_elementaryWeight_decomp`, and verify its exact RHS
   shape. If the cycle 225 lemma is shaped for `M₁`-decomposition
   only, then the LHS-side `M₂.derivativeWeightWithSrc M₁ j₁ t`
   produced by cycle 230 + the LHS top-block does NOT match the
   RHS-side decomposition-sum. In that case, the proof needs a
   different combinatorial route — most likely a separate auxiliary
   lemma "`(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight
   t + ∑ j : Fin s₂, M₂.b j * M₂.derivativeWeightWithSrc M₁ j t`"
   (the M₂-side decomposition through `derivativeWeightWithSrc`,
   not through `derivativeWeight`).

   If this auxiliary is missing, ship IT as the cycle 231
   deliverable instead, and defer the bottom-block partner to
   cycle 232. This is acceptable per §F fallback (1).
8. **Route the bottom half** (now of the form `∑ j₂ : Fin s₃,
   M₃.A k j₂ * (M₂.compose M₃).derivativeWeightWithSrc M₁ (natAdd s₂
   j₂) t`) through the **IH** (cycle 231's own per-summand recursion
   `derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t j₂`) to
   collapse to `∑ j₂, M₃.A k j₂ * M₃.derivativeWeightWithSrc
   (M₁.compose M₂) j₂ t` — which is exactly the RHS's
   `derivativeWeightWithSrc`-style sum.
9. **Close** via `Finset.sum_congr rfl (fun j _ => ...)` if there
   is any residual rearrangement.

### D.4 Non-vacuity (P2)

Add an `example` immediately after cycle 230's three-factor
`paddedEuler` witness (at the end of `namespace
OpenMath.Chapter3.Section381` near the file's bottom):

```lean
example : ∀ (t : RootedTree) (k : Fin 2),
    (paddedEuler.compose paddedEuler).derivativeWeightWithSrc
      paddedEuler (Fin.natAdd 2 k) t
      = paddedEuler.derivativeWeightWithSrc (paddedEuler.compose paddedEuler) k t :=
  fun t k => derivativeWeightWithSrc_compose_natAdd
    paddedEuler paddedEuler paddedEuler t k
```

This exercises the cycle 231 mutual pair at `(M₁, M₂, M₃) =
(paddedEuler, paddedEuler, paddedEuler)`.

### D.5 LOC estimate

~70–100 LOC for the mutual block + ~10 LOC for the P2 witness.
This is larger than cycle 230's ~50 LOC because the bottom-block
proof consumes BOTH cycle 230's top-block lemma AND cycle 225's
`compose_elementaryWeight_decomp` (or its `derivativeWeightWithSrc`-
analogue) — Step D.3.7 alone is ~25 LOC of careful sum-rearrangement.

## §E. ABORT THRESHOLDS

Abort §D and ship a smaller deliverable if any of the following
triggers:

1. **Step D.3.4 (elementaryWeight rewrite) fails**: if
   `compose_elementaryWeight_decomp` does NOT cleanly rewrite the
   RHS `(M₁.compose M₂).elementaryWeight t` to a form matching the
   decomposition-plus-sum structure, this is a real structural
   mismatch. Do NOT try to brute-force it. Document the gap and
   ship a smaller deliverable per §F below.
2. **Step D.3.7 cycle 225 lemma audit reveals mismatch**: if
   `compose_elementaryWeight_decomp`'s decomposition uses
   `M₁.derivativeWeight` instead of `M₂.derivativeWeightWithSrc`,
   the LHS top-half collapse (via cycle 230) and the RHS
   decomposition-sum don't match shape. Ship the missing auxiliary
   `compose_elementaryWeight_decomp_via_M₂_src` as the cycle 231
   deliverable; defer the bottom-block partner to cycle 232.
3. **Warm rebuild > 30s**: if `Section381.lean` warm rebuild (third
   compile after edit) exceeds 30s (well above cycle 230's 6s
   baseline), step back and split the bottom-block lemma into
   sub-lemmas. Do NOT raise `maxHeartbeats`.
4. **Step D.3.8 (IH application) requires `decreasing_by`**: cycle
   230 confirmed Lean's structural-recursion checker handles the
   mutual pair without explicit measure. If cycle 231 ever needs
   `decreasing_by`, that is a sign the recursion shape is wrong
   — revisit the IH structure rather than hacking termination.

## §F. Fallback deliverable (if §D aborts)

Ship ONE of the following, in order of preference:

1. **Auxiliary M₂-side decomposition** (best fit if §E.2 triggers):
   `compose_elementaryWeight_decomp_via_M₂_src` of shape
   `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t +
   ∑ j : Fin s₂, M₂.b j * M₂.derivativeWeightWithSrc M₁ j t`.
   This is structurally analogous to cycle 225's decomposition but
   uses the source-threaded variant and is provable via a similar
   `compose_b_castAdd`/`compose_b_natAdd` block split. ~30–40 LOC.
   Unblocks cycle 232's bottom-block partner cleanly.
2. **Split bottom-block into per-summand sub-lemmas**: prove
   `(M₂.compose M₃).derivativeWeightWithSrc M₁ (natAdd s₂ k) t =
   X + Y` for explicit closed forms `X` (top contribution), `Y`
   (bottom contribution), as a stand-alone helper without
   identifying it with the RHS. ~30 LOC.
3. **A non-vacuity witness exercise**: prove the `paddedEuler`
   instance of the bottom-block identity at `s₁ = s₂ = s₃ = 2`
   by direct computation (no general theorem). ~20 LOC. Lowest
   value but axiom-clean and unblocks cycle 232 to reverse-engineer
   the general proof from a worked example.

Any of (1)–(3) is acceptable as a fallback. Do NOT introduce a
`sorry`-first scaffold — sorry count must remain 0 (45+ consecutive
clean cycles is a meaningful streak per the cycle 226 / 230 trend).

## §G. What NOT to try (do not repeat these dead ends)

1. **Do NOT attempt §441 Phase C.2 smoke test.** 45 consecutive GPFS
   timeouts; cluster-admin recovery is loop-maintainer territory.
2. **Do NOT raise `maxHeartbeats` above 200 000** per CLAUDE.md.
   If the bottom-block mutual block exceeds default heartbeats,
   decompose into sub-lemmas (cycle 150 precedent).
3. **Do NOT add `decreasing_by` annotations to the mutual block.**
   Cycle 224/225/230 confirmed Lean's structural-recursion checker
   handles `RootedTree` + `List RootedTree` mutuals without explicit
   measure.
4. **Do NOT use a single `congr 1`** before `Fin.sum_univ_add` on
   the `(elementaryWeight + sum) * tail` cons-cell shape. Cycle 230
   discovery #1: need TWO `congr 1` calls (one for outer `_ * _`,
   one for inner `_ + _`). Cycle 231's bottom-block lemma uses the
   same shape and needs the same depth.
5. **Do NOT attempt to derive `PhiEquivalent → Equivalent` to
   reduce to cycle 217's `compose_equivalent_compose`.** Per
   `.prover-state/issues/cycle_226_compose_phi_right_action.md`,
   this requires Taylor expansion / B-series machinery not in the
   project.
6. **Do NOT re-poll Aristotle mid-cycle.** Single poll per CLAUDE.md;
   the next status check is cycle 232.
7. **Do NOT use the first `lake env lean` reading as the warm-rebuild
   gauge.** Per cycle 230 discovery #2, the first compile after an
   edit takes 2m+ even for sole-modified files (LSP-side full
   transitive olean walk); the steady-state warm baseline is ~6s
   (third compile onward).
8. **Do NOT introduce `axiom` or `constant` declarations** per
   CLAUDE.md.
9. **Do NOT shop for a quotient route to avoid the right-action.**
   The right-action is genuinely the hard half of `thm:384A`; the
   left-action quotient-lift (cycle 227's `composeQ_phi_left_act`)
   already finesses everything that can be finessed. The remaining
   work is the M₂-side sum equality.
10. **Do NOT modify cycle 224/225/226/227/228/229/230's deliverables.**
    All axiom-clean and load-bearing. Insertions go between cycle
    230's top-block end and cycle 227's `composeQ_phi_left_act`
    `noncomputable def` doc block.

## §H. Verification checklist (mandatory before commit)

Before commit, run in order:

1. `lake env lean OpenMath/Chapter3/Section381.lean` (three times
   — the first will be cold-cache ≈ 2m, the second ≈ 30s, the third
   ≈ 6s; use the third as the warm-rebuild gauge).
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` → expect 0.
3. `lean_verify` on each new symbol → expect
   `[propext, Classical.choice, Quot.sound]` only.
4. Regression spot-check `lean_verify` on:
   - `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc_compose_castAdd`
     (cycle 230)
   - `OpenMath.Chapter3.Section312.RKTableau.compose_phiEquivalent_compose_left`
     (cycle 226)
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_left_act_id_left`
     (cycle 228)
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_left_act_id_right`
     (cycle 229)
   All must remain axiom-clean.
5. Update `plan.md` `thm:384A` row with cycle 231 outcome.
6. Update `.prover-state/issues/cycle_226_compose_phi_right_action.md`
   with cycle 231 outcome + cycle 232 outlook.
7. Write `.prover-state/task_results/cycle_231.md` per CLAUDE.md
   format.

## §I. Cycle 232 outlook (not this cycle's work)

After cycle 231's bottom-block partner lands, cycle 232 should
assemble `compose_assoc_phiEquivalent` — the three-factor
associativity at the PhiEquivalent level, mirroring cycle 221's
`compose_equivalent_compose_assoc` at the §382 level. This is a
prerequisite for the eventual §383 `Group` instance on
`Quotient PhiEquivalent.setoidSigma`, which would package
`thm:384A`'s homomorphism in typeclass form.

If Aristotle returns COMPLETE before cycle 232, branch instead to
the full binary `composeQ_phi` lift (§C above).

## §J. Summary

**Primary plan (if Aristotle still IN_PROGRESS)**: ship
`derivativeWeightWithSrc_compose_natAdd` + list-helper companion
+ `paddedEuler` non-vacuity witness, ~70–110 LOC, axiom-clean.
If §E.2 triggers, fall back to §F.1 (auxiliary M₂-side
decomposition).

**Bonus plan (if Aristotle COMPLETE)**: incorporate the
right-action proof, assemble full `compose_phiEquivalent_compose`
+ `composeQ_phi`, promote cycle 227's left-act lemma to a
corollary, flip `thm:384A` to `formalized`.

**Constraint**: sorry count remains 0. 45th consecutive clean cycle
since cycle 201 rollback (and counting).

**Skip**: §441 Phase C.2 smoke test (46th consecutive cycle).
