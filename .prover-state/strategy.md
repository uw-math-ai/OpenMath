# Cycle 225 Strategy

## Headline

Ship the **bottom-block `derivativeWeight` analog for `compose`** in
`OpenMath/Chapter3/Section381.lean`, complementing cycle 224's
top-block pair (`derivativeWeight_compose_castAdd` /
`derivativeWeightProd_compose_castAdd`). This is the cycle 224
"Suggested next approach §225" — Option A (auxiliary function
`derivativeWeightWithSrc`) is mandatory; Option B (direct mutual
induction without a new function) is not viable because the
bottom-block formula has a genuinely recursive term that needs a
name.

Sorry count must remain 0 (cycle 224 was the 38th consecutive clean
cycle since the cycle 201 rollback; do not break the streak).

## A. §441 Phase C.2 — SKIP

Do **not** run the §441 GPFS smoke test. We are at 41 consecutive
timeouts spanning cycles 182–224 (43 calendar days). The pattern is
fully entrenched and re-attempting wastes 5 minutes for no signal.
Per the standing escalation in
`.prover-state/issues/cycle_182_gpfs_slowness.md`, cluster recovery
is loop-maintainer territory. Go straight to §B work.

## B. Priority 1 deliverables — bottom-block `derivativeWeight`

### B.0 Where the work lands

Insert immediately **after** cycle 224's `end ... end` block at
`OpenMath/Chapter3/Section381.lean:2654`, before the
`compose_isExplicit_iff` theorem at line 2656.

The new declarations live inside the existing
`namespace OpenMath.Chapter3.Section312.RKTableau` block. The
`RootedTree` namespace clash from cycle 224's "Dead end #1" still
applies — wrap the new `mutual ... end` block (and the auxiliary
`mutual` def block) in:

```lean
section
open OpenMath.Chapter3.Section310

mutual ... end  -- defs

mutual ... end  -- proofs

end
```

This is documented in cycle 224 results as a "reusable trick"; reuse
it verbatim. Use ONE wrapper around BOTH `mutual` blocks (they share
the namespace scope; defs come first so the proof block can name
them).

### B.1 (P1) — Auxiliary function `derivativeWeightWithSrc`

Define a mutual pair of `noncomputable def`s in the
`OpenMath.Chapter3.Section312.RKTableau` namespace. The name
`derivativeWeightWithSrc M₂ M₁` reads as "M₂'s derivative weight,
with M₁ as the *source* method providing initial-value contributions
at each leaf-attachment point":

```lean
mutual
  /-- *Derivative weight relative to a source method.* For the bottom-
  block stages of `M₁.compose M₂`, the per-tree derivative weight
  recursively accumulates `M₁`'s elementary weight at each
  leaf-attachment point (representing M₁'s contribution to the
  starting value used by M₂'s stage `i`). Cycle 225 closed-form
  partner of `derivativeWeight_compose_natAdd`. -/
  noncomputable def derivativeWeightWithSrc {s₁ s₂ : ℕ}
      (M₂ : RKTableau s₂) (M₁ : RKTableau s₁) :
      Fin s₂ → RootedTree → ℝ
    | i, RootedTree.mk children =>
        M₂.derivativeWeightWithSrcProd M₁ i children

  /-- List-helper companion to `derivativeWeightWithSrc`. -/
  noncomputable def derivativeWeightWithSrcProd {s₁ s₂ : ℕ}
      (M₂ : RKTableau s₂) (M₁ : RKTableau s₁) :
      Fin s₂ → List RootedTree → ℝ
    | _, [] => 1
    | i, t :: ts =>
        (M₁.elementaryWeight t
          + ∑ j : Fin s₂, M₂.A i j * M₂.derivativeWeightWithSrc M₁ j t)
        * M₂.derivativeWeightWithSrcProd M₁ i ts
end
```

**Termination**: Lean should infer well-foundedness from the
`children`/`t :: ts` structural recursion (same template as cycle
187's `derivativeWeight` definition in Section312). If
`decreasing_by` complains, find Section312's `derivativeWeight`
definition with `lean_local_search "derivativeWeight"`, copy
whatever `decreasing_by` block it uses.

**Why this shape?** The bottom-block A-row is `(M₁.b j₁, M₂.A i j₂)`
(cycle 209's `compose_A_botLeft = M₁.b j` and
`compose_A_botRight = M₂.A i j`). Splitting the `Fin (s₁+s₂)` sum
via `Fin.sum_univ_add`:

* Top half: `∑ j₁, M₁.b j₁ * (compose).derivativeWeight (castAdd s₂ j₁) t`
  collapses via cycle 224's `derivativeWeight_compose_castAdd` to
  `∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t = M₁.elementaryWeight t`.
* Bottom half: `∑ j₂, M₂.A i j₂ * (compose).derivativeWeight (natAdd s₁ j₂) t`
  retains the recursive `(compose).derivativeWeight (natAdd s₁ j₂) t`
  factor — exactly what the mutual partner picks up via
  `M₂.derivativeWeightWithSrc M₁ j₂ t`.

So the `t :: ts` body
`(M₁.elementaryWeight t + ∑ j, M₂.A i j * derivativeWeightWithSrc M₁ j t) * ...prod ts`
is the closed-form analog of the recursive sum.

### B.2 (P1) — Mutual identity `derivativeWeight_compose_natAdd`

In a second `mutual` block (still inside the
`section ... open Section310 ... end` wrapper), prove:

```lean
mutual
  /-- *Bottom-block derivative-weight reduction.* For a stage
  `natAdd s₁ i` in the bottom block of `M₁.compose M₂`, the composite
  derivative weight equals `M₂`'s derivative-weight-with-source on
  tree `t`. Companion to `derivativeWeightProd_compose_natAdd`. -/
  private theorem derivativeWeight_compose_natAdd {s₁ s₂ : ℕ}
      (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) :
      ∀ (t : RootedTree) (i : Fin s₂),
        (M₁.compose M₂).derivativeWeight (Fin.natAdd s₁ i) t
          = M₂.derivativeWeightWithSrc M₁ i t
    | RootedTree.mk children, i => by
        show (M₁.compose M₂).derivativeWeightProd (Fin.natAdd s₁ i) children
            = M₂.derivativeWeightWithSrcProd M₁ i children
        exact derivativeWeightProd_compose_natAdd M₁ M₂ children i

  /-- List-helper companion to `derivativeWeight_compose_natAdd`. -/
  private theorem derivativeWeightProd_compose_natAdd {s₁ s₂ : ℕ}
      (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) :
      ∀ (children : List RootedTree) (i : Fin s₂),
        (M₁.compose M₂).derivativeWeightProd (Fin.natAdd s₁ i) children
          = M₂.derivativeWeightWithSrcProd M₁ i children
    | [], _ => rfl
    | t :: ts, i => by
        -- Mirrors cycle 224's derivativeWeightProd_compose_castAdd
        -- recipe at lines 2638–2651, with two differences:
        --   (a) compose_A_botLeft / compose_A_botRight in place of
        --       compose_A_topLeft / compose_A_topRight
        --   (b) NEITHER half is zero, so we route the top half
        --       through cycle 224 and the bottom half through the
        --       mutual partner.
        show (∑ j : Fin (s₁ + s₂),
                (M₁.compose M₂).A (Fin.natAdd s₁ i) j
                  * (M₁.compose M₂).derivativeWeight j t)
              * (M₁.compose M₂).derivativeWeightProd (Fin.natAdd s₁ i) ts
            = (M₁.elementaryWeight t
                + ∑ j₂ : Fin s₂,
                    M₂.A i j₂ * M₂.derivativeWeightWithSrc M₁ j₂ t)
              * M₂.derivativeWeightWithSrcProd M₁ i ts
        rw [derivativeWeightProd_compose_natAdd M₁ M₂ ts i]
        congr 1
        rw [Fin.sum_univ_add]
        simp only [compose_A_botLeft, compose_A_botRight]
        -- Top half: rewrite via cycle 224's per-tree mutual partner.
        rw [show
              (∑ j₁ : Fin s₁,
                  M₁.b j₁ * (M₁.compose M₂).derivativeWeight (Fin.castAdd s₂ j₁) t)
                = ∑ j₁ : Fin s₁, M₁.b j₁ * M₁.derivativeWeight j₁ t
            from Finset.sum_congr rfl (fun j₁ _ => by
              rw [derivativeWeight_compose_castAdd M₁ M₂ t j₁])]
        -- Bottom half: rewrite via the mutual partner just below.
        rw [show
              (∑ j₂ : Fin s₂,
                  M₂.A i j₂ * (M₁.compose M₂).derivativeWeight (Fin.natAdd s₁ j₂) t)
                = ∑ j₂ : Fin s₂, M₂.A i j₂ * M₂.derivativeWeightWithSrc M₁ j₂ t
            from Finset.sum_congr rfl (fun j₂ _ => by
              rw [derivativeWeight_compose_natAdd M₁ M₂ t j₂])]
        -- Now the goal is:
        --   (∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t)
        --   + (∑ j₂, M₂.A i j₂ * M₂.derivativeWeightWithSrc M₁ j₂ t)
        --     = M₁.elementaryWeight t
        --       + (∑ j₂, M₂.A i j₂ * M₂.derivativeWeightWithSrc M₁ j₂ t)
        -- Close by rewriting ∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t
        -- to M₁.elementaryWeight t via the elementaryWeight unfold.
        rfl  -- if elementaryWeight is definitionally the sum;
             -- otherwise see R1 below for the recovery.
end
```

### B.3 (P2) — `paddedEuler` non-vacuity witness

Outside the namespace block (in `namespace OpenMath.Chapter3.Section381`,
after cycle 224's P2 example at the end of the file), add:

```lean
/-- Cycle 225 P2 non-vacuity: `derivativeWeight_compose_natAdd` lifted
to the concrete pair `(paddedEuler, paddedEuler)`. -/
example (t : OpenMath.Chapter3.Section310.RootedTree) (i : Fin 2) :
    (paddedEuler.compose paddedEuler).derivativeWeight (Fin.natAdd 2 i) t
      = paddedEuler.derivativeWeightWithSrc paddedEuler i t :=
  RKTableau.derivativeWeight_compose_natAdd paddedEuler paddedEuler t i
```

The `Fin.natAdd 2 i` arity should match (paddedEuler is `RKTableau 2`,
so `s₁ = 2`). If Lean balks at implicit-argument inference, pass
`(s₁ := 2) (s₂ := 2)` explicitly.

## C. Verification (mandatory before commit)

1. `lake env lean OpenMath/Chapter3/Section381.lean` — must exit 0.
   Time budget: ≤2 minutes warm rebuild (cycle 223 baseline 8.276s,
   cycle 224 6.088s; small additions should stay similar). If
   compile exceeds 2 minutes, abort and roll back per §G.
2. `mcp__lean-lsp__lean_verify` on each new symbol:
   * `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc`
   * `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrcProd`
   * `OpenMath.Chapter3.Section312.RKTableau.derivativeWeight_compose_natAdd`
   * `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightProd_compose_natAdd`

   The two `noncomputable def`s in B.1 may include an additional
   `WellFounded.fix` or similar axiom from well-founded-recursion
   machinery — that's expected. The two private theorems in B.2
   must report axioms `[propext, Classical.choice, Quot.sound]`
   only. `sorryAx` must not appear in any of the four.
3. Spot-check regressions on cycle 224 + landmarks via `lean_verify`:
   * `OpenMath.Chapter3.Section312.RKTableau.derivativeWeight_compose_castAdd`
     (cycle 224)
   * `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent`
     (cycle 218)
   * `OpenMath.Chapter3.Section312.RKTableau.instGroup` (cycle 222)

   All must remain at the same axiom triple; no regressions.
4. Sorry count: `grep -c sorry OpenMath/Chapter3/Section381.lean`
   must remain 0 (39th consecutive clean cycle since cycle 201).

## D. What NOT to try

1. **Do not attempt P3 (`compose_phiEquivalent_compose`) this cycle.**
   Per cycle 224 task results "Suggested next approach", the bottom-
   block formula is the prerequisite; assembling
   `compose_phiEquivalent_compose` from cycle 224 (top) + cycle 225
   (bottom) is itself a substantive cycle. Cycle 226+ work.
2. **Do not attempt Option B (direct mutual induction without
   auxiliary function).** Per cycle 224 task results "Suggested next
   approach", the bottom-block formula contains a genuinely recursive
   `(compose).derivativeWeight (natAdd s₁ j) t` term that does not
   eliminate cleanly. Without a name (the auxiliary function
   `derivativeWeightWithSrc`), the closed form cannot be stated.
   Option A is the only viable path.
3. **Do not redefine `compose`, `compose_A_botLeft`, `compose_A_botRight`,
   or any cycle 209 simp lemmas.** They are correct as-is (cycle 224
   confirmed the `compose_A_topLeft`/`topRight` analogs work for the
   top-block recipe; the same simp set drives the bottom block).
4. **Do not omit the `section ... open Section310 ... end` wrapper.**
   Cycle 224's "Dead end #1" documents that unqualified `RootedTree`
   inside `Section312.RKTableau` resolves to a different type. The
   wrapper is mandatory for both the def block and the proof block.
   Use ONE wrapper around BOTH `mutual` blocks.
5. **Do not run the §441 smoke test.** 41 consecutive timeouts. Per
   §A above.
6. **Do not raise `maxHeartbeats`.** Per CLAUDE.md. If the second
   `mutual` block times out at 200000 heartbeats, decompose the
   `t :: ts` proof into a private `Fin.sum_univ_add` + simp-set
   helper that handles the four-block split in isolation, separate
   from the per-summand mutual recursion. Cycle 150's pattern at
   `matrix7_oneMinusZSmul_det` is the precedent — if a single proof
   blows past heartbeats, factor the structural part from the
   per-summand recursion.
7. **Do not change the `compose` definition** (Section381.lean line
   ~2410). Cycle 209's encoding is consumed by 30+ downstream
   theorems; refactoring would cascade.
8. **Do not introduce `axiom` or `constant` declarations.** Per
   CLAUDE.md.
9. **Do not commit `sorry`-scaffolded versions of B.1 or B.2.**
   Sorry count must stay 0. If B.1 or B.2 cannot be closed within
   §F budget, abort per §G — do NOT ship a sorry-first scaffold.
   Cycle 200's thm:381H scaffold (sorry count 0 → 3) was rolled
   back in cycle 201 with score −2; same precedent applies.

## E. Risk register (pre-flagged, recovery plans inline)

* **R1 — `M₁.elementaryWeight` definitional shape.** `rfl` at the
  end of B.2's proof closes only if `elementaryWeight M t = ∑ i,
  M.b i * M.derivativeWeight i t` definitionally. **Recovery**: if
  not, run `lean_local_search "elementaryWeight"` for the unfold
  lemma (likely `RKTableau.elementaryWeight_eq` or similar — cycle
  187's `pReduced_phiEquivalent` proof at `Section381.lean:1322`
  unfolds elementaryWeight via `show ∑ i, ...`, so the same trick
  works here). Apply via
  `show (∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t) + _ = M₁.elementaryWeight t + _`
  followed by `rfl`, OR insert `rw [← elementaryWeight_eq]` /
  `unfold elementaryWeight`. Estimated 5-minute recovery.

* **R2 — `Fin.sum_univ_add` rewrites both halves the wrong way.** The
  rewrite produces `∑ j₁ : Fin s₁, ... + ∑ j₂ : Fin s₂, ...` from
  `∑ j : Fin (s₁ + s₂), ...`. Cycle 224's recipe used this exact
  step at line 2647 — it's already validated. **Recovery**: not
  expected to fire.

* **R3 — `compose_A_botLeft` / `compose_A_botRight` simp lemma
  names.** Cycle 209's task results name them as stated; cycle 213's
  `compose_of_isRKOneStep` proof uses the same names. **Recovery**:
  if names have drifted, `lean_local_search "compose_A_bot"` finds
  them.

* **R4 — Auxiliary function termination.** The mutual recursion
  pattern in B.1 mirrors cycle 187's `derivativeWeight` /
  `derivativeWeightProd` mutual definition (in Section312, find via
  `lean_local_search "derivativeWeight"`). Lean's well-foundedness
  inference handled cycle 187 cleanly; same template should work
  here. **Recovery**: if termination fails, copy the `decreasing_by`
  block (if any) from Section312's `derivativeWeight` definition.

* **R5 — `paddedEuler.derivativeWeightWithSrc paddedEuler i t`
  arity in P2.** `paddedEuler : RKTableau 2`, so
  `derivativeWeightWithSrc` expects `s₂ = 2`, `s₁ = 2`. Should
  infer cleanly. **Recovery**: if Lean balks, pass
  `(s₁ := 2) (s₂ := 2)` explicitly to both
  `derivativeWeightWithSrc` and `derivativeWeight_compose_natAdd`
  in the example.

* **R6 — Heartbeats on the `t :: ts` proof.** The single-shot proof
  has two large rewrites (top + bottom half). If it exceeds 200000
  heartbeats, factor as in §D point 6 above. **Recovery**: introduce
  `private theorem fin_sum_univ_add_split_natAdd_block` proving the
  four-block split numerically:
  ```
  ∀ (X : Fin (s₁+s₂) → ℝ),
    ∑ j : Fin (s₁+s₂), (M₁.compose M₂).A (Fin.natAdd s₁ i) j * X j
    = (∑ j₁ : Fin s₁, M₁.b j₁ * X (Fin.castAdd s₂ j₁))
      + (∑ j₂ : Fin s₂, M₂.A i j₂ * X (Fin.natAdd s₁ j₂))
  ```
  Then the `t :: ts` proof becomes a one-line `rw` against this
  helper. Each of the two parts (helper + main proof) fits within
  heartbeats independently.

* **R7 — Cycle 224 `derivativeWeight_compose_castAdd` is `private`.**
  It's marked `private` in cycle 224 (per the task results), but it
  lives in the same namespace block as B.2's mutual partners, so
  visibility is preserved. **Recovery**: not expected to fire; if
  it does, either drop the `private` modifier on cycle 224's
  declarations (one-line edit, no semantic change) or move B.2 to
  the same `section` scope.

## F. Time budget and abort criteria

* B.1 (def block): ≤30 minutes. If the `noncomputable def` does not
  type-check after 30 minutes, abort to §G.
* B.2 (proof block): ≤60 minutes. If either mutual partner stalls
  past 60 minutes, attempt R6 decomposition; if that also stalls
  another 30 minutes, abort to §G.
* B.3 (P2 example): ≤10 minutes. If it does not type-check
  immediately, drop to a weaker form (e.g. concrete `i := 0` or a
  fully numerical RHS).
* Total cycle budget: ≤2.5 hours. After 2.5 hours, save partial
  work to `.prover-state/cycle_225_draft_section381.lean` and abort.

## G. Abort and rollback policy

If B.1 or B.2 cannot be closed within budget:

1. **Do not commit `sorry`-scaffolded versions.** Cycle 200's
   thm:381H scaffold (sorry count 0 → 3) was supervisor-rolled back
   in cycle 201 (score −2). Same precedent applies here.
2. Save the partial work to
   `.prover-state/cycle_225_draft_section381.lean` (a new untracked
   file). Do NOT modify `OpenMath/Chapter3/Section381.lean`.
3. Write `.prover-state/issues/cycle_225_partial.md` documenting:
   what was attempted, what compiled, what didn't, and the specific
   stall point (def termination? proof tactic? heartbeats? mutual
   partner unification?).
4. Cycle 226 strategy can resume from the draft.
5. The cycle still satisfies CLAUDE.md "minimum: decompose a sorry
   or write an issue" via the issue file.

## H. Faithfulness check (pre-commit, mandatory)

* `derivativeWeightWithSrc` and `derivativeWeightWithSrcProd` are
  internal helper definitions — no textbook entity ID applies. They
  are pure mathematical bookkeeping for the bottom-block recursion of
  `compose`'s derivative weight. The docstring in B.1 makes this
  explicit ("Cycle 225 closed-form partner of
  `derivativeWeight_compose_natAdd`"). ✓
* `derivativeWeight_compose_natAdd` and
  `derivativeWeightProd_compose_natAdd` are private mutual partners
  for the (forthcoming) `compose_phiEquivalent_compose`. Same status
  as cycle 224's `derivativeWeight_compose_castAdd` pair. No
  textbook entity ID applies. ✓
* Tautology check: the conclusions of both new mutual identities are
  genuine *equalities* between two different recursive expressions
  (`(M₁.compose M₂).derivativeWeight (natAdd s₁ i) t` vs
  `M₂.derivativeWeightWithSrc M₁ i t`). Not hypothesis re-exports. ✓
* Identity check: B.2's `t :: ts` proof performs real rewriting
  (Fin.sum_univ_add + four-block simp + per-summand mutual recursion
  via cycle 224 + per-summand mutual recursion via the new partner +
  elementaryWeight unfold). Not `exact h`-style. ✓
* Hypothesis strength: only `M₁ M₂` (no extra hypotheses). Minimal. ✓
* Absent theorem check: B.2's mutual partners exist as written; no
  `sorry`-promised theorems introduced. ✓
* Definition smuggling: `derivativeWeightWithSrc`'s body uses
  `M₁.elementaryWeight` (an existing concept) at the leaf-attachment
  point. This is the correct mathematical content (M₁'s contribution
  to the starting value for M₂'s stage), not a smuggled
  characterization. ✓

## I. After successful close

Update:

* `lean_status.json` — no row to flip; cycle 225 ships infrastructure
  helpers, not a textbook entity.
* `plan.md` — no row to flip for the same reason.
* `.prover-state/task_results/cycle_225.md` — document the
  deliverables (B.1, B.2, B.3), the verification outcomes, any risk
  triggers (R1–R7) that fired, and the cycle 226+ outlook.

The cycle 226 outlook should propose:

* **Cycle 226**: ship `compose_phiEquivalent_compose` (the
  `PhiEquivalent`-respect lemma for `compose`) by composing cycle
  224's `derivativeWeight_compose_castAdd` (top half) with cycle
  225's `derivativeWeight_compose_natAdd` (bottom half), threaded
  through `Fin.sum_univ_add` on the `(compose).b`-sum. The `b`
  vector is `Fin.append M₁.b M₂.b` (cycle 209), so the sum splits
  cleanly into top-block (collapses to `M₁.elementaryWeight t` via
  cycle 224) + bottom-block (uses cycle 225's
  `derivativeWeightWithSrc`). Then `PhiEquivalent.elementaryWeight`
  of `M₁` vs `M₁'` (and `M₂` vs `M₂'`) closes the per-tree equality.
  Estimated ~80 LOC.
* **Cycle 227**: ship `composeQ_phi : Quotient PhiEquivalent.setoidSigma →
  Quotient PhiEquivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma`
  via `Quotient.lift₂` consuming cycle 226's lemma. Mirror of cycle
  218's `composeQ`.
* **Cycle 228**: ship `composeQ_phi_id_left` / `composeQ_phi_id_right`
  identity laws on the new quotient (mirror of cycle 219).
* **Cycle 229+**: assemble `instance : Group (Quotient
  PhiEquivalent.setoidSigma)` via `Group.ofLeftAxioms` (mirror of
  cycle 222's `instGroup`).
* **Cycle 230**: ship `thm:384A` (Φ as a group homomorphism between
  the §382 `Quotient Equivalent.setoidSigma` group and the §383
  `Quotient PhiEquivalent.setoidSigma` group).

Cycle 225 is the structural prerequisite for the entire §383+
group-homomorphism path. Land it cleanly.
