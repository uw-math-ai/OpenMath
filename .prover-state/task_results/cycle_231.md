# Cycle 231 Results

## Worked on

§383 group-homomorphism path Phase 3 follow-up: built the
bottom-block `derivativeWeightWithSrc_compose_natAdd` mutual block
(path B per cycle 231 strategy §B decision tree). This is the
companion to cycle 230's top-block `_compose_castAdd` and the
final per-stage infrastructure lemma needed before cycle 232's
`compose_assoc_phiEquivalent`. NOT the right-action deferred in
`.prover-state/issues/cycle_226_compose_phi_right_action.md`.

## Approach

1. **Aristotle single poll**: project
   `176aa964-db7b-40f8-a01c-05247c186ec5` (right-action M₂-side
   sum equality) returned `IN_PROGRESS` at **29 %** on the single
   permitted poll. Growth pattern: 9 % → 11 % → 17 % → 24 % → 29 %
   across cycles 227 / 228 / 229 / 230 / 231 (≈ 2–7 % per cycle,
   slightly slowing). Several-day ETA at current rate. **Path B**
   taken per §B.
2. **Critical pre-flight audit (§D.3.7)**: confirmed cycle 225's
   `compose_elementaryWeight_decomp` (Section381.lean lines
   2819–2833) already has the M₂-side `derivativeWeightWithSrc`-
   form decomposition:
   `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t
       + ∑ i : Fin s₂, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t`
   This matches the shape required by the cycle 231 bottom-block
   proof — the strategy's "if cycle 225 uses `derivativeWeight`
   not `derivativeWeightWithSrc` then fallback to §F.1" branch
   was NOT triggered. The original cycle 225 commit author
   anticipated cycle 231 and shaped the decomp accordingly
   (M₂-side, source-method-threaded).
3. **Insertion site**: lines 2933–3025 of `Section381.lean`,
   inserted between cycle 230's top-block `end` (now at line
   ~2931 in HEAD) and cycle 227's `composeQ_phi_left_act` doc
   block (starting at line ~3025 after the insertion).
4. **Mutual block** (per cycle 231 strategy §D.1, ~95 LOC inside
   `section ... open OpenMath.Chapter3.Section310 ... end`
   wrapper, identical pattern to cycles 224 / 225 / 226 / 230):

   - **D.1 per-tree branch** `derivativeWeightWithSrc_compose_natAdd`
     (`private` mutual `theorem`): `∀ (t : RootedTree) (k : Fin s₃),
     (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t
       = M₃.derivativeWeightWithSrc (M₁.compose M₂) k t`.
     Proof recipe: pattern-match on `RootedTree.mk children`,
     `show` rewrites goal to list-helper form, `exact` delegates
     to companion. Identical to cycle 230's pattern.

   - **D.1 list-helper branch** `derivativeWeightWithSrcProd_compose_natAdd`
     (`private` mutual `theorem`): `∀ (children : List RootedTree)
     (k : Fin s₃), (M₂.compose M₃).derivativeWeightWithSrcProd M₁
         (Fin.natAdd s₂ k) children
       = M₃.derivativeWeightWithSrcProd (M₁.compose M₂) k children`.
     Proof for `t :: ts`:
     ```
     show (M₁.elementaryWeight t + ∑ k' : Fin (s₂+s₃), ...) * tail
         = ((M₁.compose M₂).elementaryWeight t + ∑ k' : Fin s₃, ...) * tail
     rw [derivativeWeightWithSrcProd_compose_natAdd M₁ M₂ M₃ ts k]  -- IH on tail
     rw [compose_elementaryWeight_decomp M₁ M₂ t]                     -- expand RHS elementaryWeight
     congr 1                                                          -- peel _ * tail (one layer since brackets disagree in shape)
     rw [Fin.sum_univ_add]                                            -- split LHS sum into top/bottom blocks
     simp only [compose_A_botLeft, compose_A_botRight]                -- compose.A → M₂.b j₁ (top) / M₃.A k j₂ (bottom)
     rw [show ... from Finset.sum_congr rfl (fun j₁ _ => by rw [derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j₁])]  -- cycle 230 routes top
     rw [show ... from Finset.sum_congr rfl (fun j₂ _ => by rw [derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t j₂])]    -- IH routes bottom
     ring                                                             -- close residual associativity A + (B + C) = (A + B) + C
     ```

5. **D.2 P2 non-vacuity** at `Section381.lean` (after cycle 230's
   three-factor `paddedEuler` witness): ~12 LOC `example` for
   `(paddedEuler.compose paddedEuler).derivativeWeightWithSrc
       paddedEuler (Fin.natAdd 2 k) t
     = paddedEuler.derivativeWeightWithSrc
         (paddedEuler.compose paddedEuler) k t` exercising
   `(M₁, M₂, M₃) = (paddedEuler, paddedEuler, paddedEuler)`.

## Result

**SUCCESS** — both new symbols ship axiom-clean:
- `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc_compose_natAdd`:
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrcProd_compose_natAdd`:
  `[propext, Classical.choice, Quot.sound]`

`Section381.lean` warm rebuild: 6.35s (third compile after edit;
first 1m27s cold, second 7.7s; well within §F.3 30s red-flag
threshold; comparable to cycle 230's 6.0s baseline).
Sorry count: 0 (44th consecutive clean cycle since the cycle 201
rollback, plus cycle 230 = 45th). Regression spot-checks all
axiom-clean: cycle 230 `derivativeWeightWithSrc_compose_castAdd`,
cycle 226 `compose_phiEquivalent_compose_left`, cycle 228
`composeQ_phi_left_act_id_left`, cycle 229
`composeQ_phi_left_act_id_right`.

## Faithfulness check

Both new symbols are *helper lemmas* for the §383 group-
homomorphism path, not direct formalizations of a textbook
entity. `thm:384A` remains `partial` in `lean_status.json`.

- **`derivativeWeightWithSrc_compose_natAdd`** (cycle 231 mutual
  pair, per-tree branch): no entity ID. This is a structural
  helper for `compose_assoc_phiEquivalent` (cycle 232 target,
  prerequisite for `thm:384A`'s full homomorphism statement).
  The lemma's statement is derivable mechanically from the
  definitions of `derivativeWeightWithSrc` (cycle 225 def at
  Section381.lean:2680–2694) and `compose` (cycle 209): the
  `natAdd s₂ k` index lands in the bottom block of `M₂.compose
  M₃`'s `A` matrix, so the composite's derivative-weight-with-
  source decomposes into M₂-side and M₃-side contributions
  through the `compose_A_bot*` simp set. The RHS specifically
  threads `M₁.compose M₂` (not just `M₁`) because the bottom
  block of `M₂.compose M₃` advances M₃'s stages from a state
  already evolved through `M₁` and `M₂`. The pattern is the
  structural extension of cycle 225's M₂-side decomp to
  three-factor composites at the `derivativeWeightWithSrc`
  level.

- **`derivativeWeightWithSrcProd_compose_natAdd`** (cycle 231
  mutual pair, list-helper branch): no entity ID. Bookkeeping
  companion that handles the recursion over the children list of
  a `RootedTree`. Substantive structural content lives here; the
  per-tree branch is a one-step delegation.

- **`example` P2 non-vacuity witness**: no entity ID. Exercises
  the cycle 231 mutual pair on the three-factor `paddedEuler`
  trio (`M₁ = M₂ = M₃ = paddedEuler`, `s₁ = s₂ = s₃ = 2`)
  mirroring cycle 230's top-block witness with the bottom-block
  mutual identity. Trivially axiom-clean (direct application of
  the new theorem).

No tautology, identity, definition-smuggling, or hypothesis-
strength issues; the new lemmas are genuine intermediate steps
between cycle 225's elementary-weight decomposition and cycle
232's associativity at the PhiEquivalent level.

## Dead ends

No dead ends this cycle — the proof recipe followed the strategy
§D.3 plan verbatim with no surprises. The §E abort thresholds
(§E.1 elementary-weight rewrite mismatch, §E.2 cycle 225
decomp-shape mismatch, §E.3 warm-rebuild > 30s, §E.4 missing
`decreasing_by`) all failed to fire.

The only structural risk that materialized: my initial draft
applied a *single* `congr 1` after the elementaryWeight rewrite
(matching cycle 225's pattern at line 2729). This works here
because the brackets immediately differ in shape after the
rewrite — the LHS bracket is `M₁.elementaryWeight t + bigSum`
and the RHS bracket (after the rewrite) is
`(M₁.elementaryWeight t + ∑ M₂.b · M₂.derivativeWeightWithSrc M₁)
+ ∑ M₃.A · M₃.derivativeWeightWithSrc (M₁.compose M₂)`. A second
`congr 1` would NOT peel cleanly because of the associativity
asymmetry; instead, one `congr 1` plus a closing `ring` handles
the residual `A + (B + C) = (A + B) + C` directly.

(Cycle 230 discovery #1's "two `congr 1` rule" applies when both
LHS and RHS have the cons-cell shape `(elementaryWeight + sum)
* tail` with the *same* elementaryWeight on each side. Cycle
231's case is asymmetric — LHS has `M₁.elementaryWeight t`, RHS
has `(M₁.compose M₂).elementaryWeight t` — so the rewrite step
breaks the symmetry before the `congr 1` and the second peel is
neither possible nor needed.)

## Discovery

1. **`compose_elementaryWeight_decomp` is M₂-side, not M₁-side**:
   the cycle 225 lemma's decomposition uses
   `M₂.derivativeWeightWithSrc M₁ i t` (NOT `M₁.derivativeWeight`)
   — confirmed by reading lines 2819–2833. This means the cycle
   231 strategy's "§E.2 CRITICAL CHECK" abort branch (fallback
   to §F.1 auxiliary lemma) was unnecessary: cycle 225 already
   shipped the right form. Future cycles building on cycle 225
   should treat its decomp as the canonical M₂-side, source-
   threaded form.

2. **`congr 1` depth: count layers in the GOAL, not the show**:
   cycle 230's discovery #1 said "two `congr 1`" because both
   sides had `(elementaryWeight + sum) * tail` with the same
   `elementaryWeight`. Cycle 231 only needs one `congr 1`
   because the `rw [compose_elementaryWeight_decomp]` step
   breaks the bracket-shape symmetry — after the rewrite, the
   LHS bracket has one `+` layer (single elementaryWeight +
   single big sum) and the RHS bracket has two `+` layers (an
   expanded elementaryWeight that already includes the M₂-side
   sum, plus the M₃-side sum). General rule: *after* every
   rewrite, count layers in the current goal; don't pre-plan
   `congr` depth based on the `show` form.

3. **`ring` is robust to large opaque atoms**: the final `ring`
   step closed an equation containing four large opaque atoms
   (`M₁.elementaryWeight t`, two big sums, a third big sum)
   plus standard real-number arithmetic. No special handling
   needed; `ring` treats opaque terms as atoms and resolves
   pure `+`/`*`/associativity goals over the reals.

4. **First-compile-cost vs warm-rebuild gap (cycle 230 D2
   replicated)**: first `lake env lean` after the edit took
   1m27s, second 7.7s, third 6.35s. The 1m27s reading reflects
   LSP-side full transitive olean walk on the cold cache and is
   NOT representative of the steady-state cost. The warm-
   rebuild baseline is the THIRD compile onward. This matches
   cycle 230's pattern (2m10s / 29s / 6.1s).

5. **Mutual structural recursion still handles
   `RootedTree` + `List RootedTree` without explicit measure**:
   no `decreasing_by` annotation needed (§G.3 confirmed for the
   fifth consecutive cycle: 224 / 225 / 226 / 230 / 231). Lean's
   structural-recursion checker handles the mutual pair via the
   `RootedTree.mk children` ↔ `t :: ts` shape correspondence.

## Suggested next approach

Cycle 232 — `compose_assoc_phiEquivalent` (three-factor
associativity at the PhiEquivalent level), the prerequisite for
the eventual §383 `Group` instance on `Quotient
PhiEquivalent.setoidSigma`. Recipe (sketch):

1. Apply `compose_elementaryWeight_decomp` to BOTH sides of the
   target `PhiEquivalent ((M₁.compose M₂).compose M₃) (M₁.compose
   (M₂.compose M₃))` to expose all three elementary-weight
   contributions.
2. Route each composite's `derivativeWeightWithSrc` factor
   through cycles 230 (top-block) and 231 (bottom-block) plus
   the appropriate `Fin.castAdd` / `Fin.natAdd` index plumbing.
3. The residual goal should reduce to a `Fin (s₁+s₂+s₃)` versus
   `Fin (s₁+(s₂+s₃))` block-rearrangement identity, closed via
   `Fin.cast_natAdd` / `Fin.natAdd_castAdd` and `Finset.sum_*`
   reindexing lemmas.

Estimated 50–80 LOC. If §441 GPFS recovery has not happened
(46th consecutive cycle as of cycle 231), continue skipping that
smoke test.

Aristotle (project `176aa964-db7b-40f8-a01c-05247c186ec5`) will
be polled exactly once at cycle 232 start; growth trajectory
9 % → 11 % → 17 % → 24 % → 29 % suggests 32–36 % at next poll.
If COMPLETE before cycle 232, branch to §C (full
`composeQ_phi` via `Quotient.lift₂`); if still IN_PROGRESS,
ship the associativity lemma.
