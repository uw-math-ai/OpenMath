# Cycle 225 Results

## Worked on

§383 group-homomorphism path **Phase 2 (bottom block)**: closed-form
unfolding of `(M₁.compose M₂).derivativeWeight (Fin.natAdd s₁ i) t`
in terms of a new auxiliary helper `derivativeWeightWithSrc`.
Complements cycle 224's top-block pair
(`derivativeWeight_compose_castAdd` /
`derivativeWeightProd_compose_castAdd`).

Four new symbols + one P2 non-vacuity witness shipped at
`OpenMath/Chapter3/Section381.lean` (inserted immediately after cycle
224's `end ... end` block at line 2654, before
`compose_isExplicit_iff` at the new line 2756):

- **B.1 — auxiliary mutual `def`s** (`Section381.lean:2670–2697`):
  - `RKTableau.derivativeWeightWithSrc` —
    `Fin s₂ → RootedTree → ℝ`, the mutual partner threading
    `M₁.elementaryWeight` into each leaf-attachment point.
  - `RKTableau.derivativeWeightWithSrcProd` —
    `Fin s₂ → List RootedTree → ℝ`, the list helper.
- **B.2 — mutual identities** (`Section381.lean:2699–2748`):
  - `RKTableau.derivativeWeight_compose_natAdd` (private) —
    `(M₁.compose M₂).derivativeWeight (Fin.natAdd s₁ i) t
       = M₂.derivativeWeightWithSrc M₁ i t`.
  - `RKTableau.derivativeWeightProd_compose_natAdd` (private) —
    list-helper version.
- **B.3 — P2 non-vacuity** (`Section381.lean:3434–3443`, new
  `example` at the file's `paddedEuler` non-vacuity block):
  - Concrete `(paddedEuler.compose paddedEuler).derivativeWeight
      (Fin.natAdd 2 i) t = paddedEuler.derivativeWeightWithSrc
      paddedEuler i t`.

Sorry count remains **0** (39th consecutive clean cycle since the
cycle 201 rollback).

## Approach

Followed cycle 225 strategy §B verbatim:

1. Wrapped both `mutual` blocks (defs + proofs) in **one**
   `section\nopen OpenMath.Chapter3.Section310\n...\nend` to resolve
   unqualified `RootedTree` inside `namespace
   OpenMath.Chapter3.Section312.RKTableau` (cycle 224's "Dead end
   #1" reusable trick).
2. Defined the auxiliary pair via structural recursion through
   `RootedTree` (mk constructor) and `List RootedTree` (cons), with
   the inner sum recursing on `derivativeWeightWithSrc`. Lean's
   structural-recursion checker accepted the mutual pair without
   `decreasing_by`, mirroring cycle 187's template at
   `Section312.lean:91–106`.
3. Proved the mutual identities by induction on the tree
   (per-tree partner unfolds to the list helper via `show`; list
   helper recurses on `t :: ts`). The `t :: ts` body:
   - `rw [derivativeWeightProd_compose_natAdd M₁ M₂ ts i]` —
     mutual partner on the trailing list.
   - `congr 1` — reduces to the per-summand inner-sum equality.
   - `rw [Fin.sum_univ_add]` — splits `Fin (s₁+s₂)` into top
     (`Fin.castAdd`) + bottom (`Fin.natAdd`) halves.
   - `simp only [compose_A_botLeft, compose_A_botRight]` —
     bottom-block A-row collapses to `M₁.b j₁` (top half) and
     `M₂.A i j₂` (bottom half).
   - `rw [show ...]` (top half via cycle 224) — rewrites
     `∑ j₁, M₁.b j₁ * (M₁.compose M₂).derivativeWeight (castAdd s₂ j₁) t`
     into `∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t` using
     cycle 224's `derivativeWeight_compose_castAdd`.
   - `rw [show ...]` (bottom half via mutual partner) —
     rewrites `∑ j₂, M₂.A i j₂ * (M₁.compose M₂).derivativeWeight (natAdd s₁ j₂) t`
     into `∑ j₂, M₂.A i j₂ * M₂.derivativeWeightWithSrc M₁ j₂ t`
     using the new mutual partner.
   - Final `rfl` closes the goal: `M₁.elementaryWeight t` is
     definitionally `∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t`
     (Section312's `elementaryWeight_eq` is `:= rfl`), so the goal
     `(∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t) + (∑ j₂, ...)
       = M₁.elementaryWeight t + (∑ j₂, ...)` is reflexivity.

4. B.3 non-vacuity example: `Fin.natAdd 2 i` matches `paddedEuler :
   RKTableau 2`, so `(s₁ := 2) (s₂ := 2)` is inferred cleanly.

## Result

**SUCCESS** — all four new symbols compile clean, sorry count
remains 0, and warm-rebuild time is 6.310s (well under the cycle
225 strategy §C.1 budget of 2 minutes; comparable to cycle 224's
6.088s).

### Verification outcomes (strategy §C)

1. `lake env lean OpenMath/Chapter3/Section381.lean` — `EXIT=0`.
   Warm rebuild **6.310s**.
2. `lean_verify` on all four new symbols:
   - `derivativeWeightWithSrc` — axioms `[propext, Classical.choice,
     Quot.sound]`. **No `sorryAx`**, no additional well-founded-
     recursion axioms (R4 did not fire — Lean's structural-
     recursion inference handled this cleanly, same as cycle 187).
   - `derivativeWeightWithSrcProd` — same.
   - `derivativeWeight_compose_natAdd` — same.
   - `derivativeWeightProd_compose_natAdd` — same.
3. Regression spot-checks all axiom-clean:
   - Cycle 224 `derivativeWeight_compose_castAdd` —
     `[propext, Classical.choice, Quot.sound]`. ✓
   - Cycle 218 `composeQ_eq_of_equivalent` —
     `[propext, Classical.choice, Quot.sound]`. ✓
   - Cycle 222 `instGroup` —
     `[propext, Classical.choice, Quot.sound]`. ✓
4. Sorry count: `grep sorry` returns the lone docstring hit at
   line 2884 (cycle 216 prose, not an actual proof). Genuine
   sorry count remains **0**.

### Risk register firings

- **R1 (elementaryWeight definitional shape)** — *did not fire*.
  Because Section312 defines `elementaryWeight` as the raw sum
  body (no `match` / no helper layer), `elementaryWeight_eq` is
  literally `:= rfl`. The final `rfl` in B.2 closed the goal
  without needing the recovery (`show` + `elementaryWeight_eq`
  rewrite).
- **R2 (Fin.sum_univ_add direction)** — *did not fire*. The
  rewrite produced the expected top + bottom split.
- **R3 (compose_A_bot* names)** — *did not fire*. Names matched
  the strategy exactly (`Section381.lean:2590–2598`).
- **R4 (auxiliary def termination)** — *did not fire*. Lean's
  structural-recursion inference handled the mutual `def` pair
  with no `decreasing_by` clause, exactly mirroring cycle 187's
  template.
- **R5 (paddedEuler arity in P2)** — *did not fire*. Implicit
  inference is clean for `Fin.natAdd 2 i`.
- **R6 (heartbeats on `t :: ts` proof)** — *did not fire*. The
  proof closed in well under 200000 heartbeats; no decomposition
  helper needed.
- **R7 (cycle 224 `derivativeWeight_compose_castAdd` is private)**
  — *did not fire*. Both cycle 224 and cycle 225's mutual blocks
  live in the same `namespace OpenMath.Chapter3.Section312.RKTableau`
  block (spans lines 2508–3394), so the private declaration is
  visible.

### LOC ledger

- B.1 (defs): ~28 LOC (`Section381.lean:2670–2697`, including
  docstrings).
- B.2 (proofs): ~50 LOC (`Section381.lean:2699–2748`, including
  docstrings).
- Outer `section`/`end` wrapper + intro comment: ~17 LOC
  (`Section381.lean:2656–2668` + `Section381.lean:2750`).
- B.3 (P2 example): ~10 LOC (`Section381.lean:3434–3443`).
- **Total added**: ~105 LOC across the file (file grew from
  3712 → 3812 lines).

## Faithfulness check

For each new `def` and `theorem` introduced this cycle:

### `RKTableau.derivativeWeightWithSrc` (`def`)
- **Entity ID**: none — this is an internal helper, not a
  textbook entity.
- **Lean statement captures**: pure mathematical bookkeeping for
  the bottom-block recursion of `compose`'s derivative weight.
  The docstring makes this explicit: "Cycle 225 closed-form
  partner of `derivativeWeight_compose_natAdd`".
- **Definition smuggling check**: the body uses
  `M₁.elementaryWeight` (an existing concept from Section312) at
  the leaf-attachment point. This is the correct mathematical
  content — `M₁`'s contribution to the starting value for `M₂`'s
  stage — not a smuggled characterization. ✓
- **Justification**: same status as cycle 224's
  `derivativeWeight_compose_castAdd` / `derivativeWeightProd_*`
  pair (no entity ID; internal infrastructure for the §383
  group-homomorphism path).

### `RKTableau.derivativeWeightWithSrcProd` (`def`)
- **Entity ID**: none — list-helper companion.
- Same status as above.

### `RKTableau.derivativeWeight_compose_natAdd` (`theorem`, private)
- **Entity ID**: none — private mutual partner for the
  (forthcoming) `compose_phiEquivalent_compose` (cycle 226).
- **Tautology check**: conclusion is a genuine equality between
  two different recursive expressions
  (`(M₁.compose M₂).derivativeWeight (natAdd s₁ i) t` vs
  `M₂.derivativeWeightWithSrc M₁ i t`). Not a hypothesis
  re-export. ✓
- **Identity check**: proof recurses through the mutual partner
  via `show ... ; exact derivativeWeightProd_compose_natAdd
  M₁ M₂ children i` — real work. ✓
- **Hypothesis strength**: only `M₁ M₂` (no extra constraints).
  Minimal. ✓

### `RKTableau.derivativeWeightProd_compose_natAdd` (`theorem`, private)
- **Entity ID**: none — list-helper companion.
- **Tautology check**: ✓ (same as above).
- **Identity check**: `t :: ts` body performs real rewriting
  (`Fin.sum_univ_add` + 2-block `simp` + two `Finset.sum_congr`
  rewrites via the two mutual partners + `elementaryWeight`
  unfold via `rfl`). Not `exact h`-style. ✓
- **Hypothesis strength**: only `M₁ M₂`. Minimal. ✓

### P2 non-vacuity example
- Pure application of the new mutual identity to `paddedEuler`.
  No textbook claim. ✓

## Dead ends

None — strategy §B recipe worked verbatim, no recoveries
triggered. All seven pre-flagged risks (R1–R7) failed to fire.

## Discovery

- **Cycle 187's mutual-recursion template is fully reusable**.
  When you need a `Fin s → RootedTree → ℝ` helper that recurses
  through a list helper on `mk children`, the cleanest path is
  the same template Section312 uses for `derivativeWeight`
  itself: `mutual ... def f : ... | RootedTree.mk children =>
  fProd ... | f' : List RootedTree → ℝ | [] => 1 | t :: ts =>
  (... inner ... f j t ...) * f' ts end`. No `decreasing_by`
  needed — Lean infers structural recursion automatically.
- **`elementaryWeight_eq` is `:= rfl`**, so `M₁.elementaryWeight
  t` unfolds definitionally to `∑ i : Fin s, M₁.b i *
  M₁.derivativeWeight i t`. Final `rfl` closes goals that mix
  `elementaryWeight` and its raw sum form, even with renamed
  bound variables (binder names don't affect definitional
  equality). R1's recovery (using `show` + `unfold` + rewrite)
  was unnecessary for this cycle.
- **One `section\nopen Section310\n...\nend` wrapper around
  BOTH `mutual` blocks works correctly**. The wrapper scope
  spans defs + proofs cleanly; no need to nest. (Verified by
  successful compile.)
- **`@[simp]` lemmas `compose_A_botLeft` / `compose_A_botRight`
  drive the bottom-block split via `simp only`** with no other
  arithmetic helpers needed — both halves' coefficient is
  exactly `M₁.b j₁` / `M₂.A i j₂`. No `zero_mul`/`add_zero`
  cleanup needed (unlike cycle 224's top-block recipe which
  used those because `compose_A_topRight = 0`).

## Suggested next approach

Per cycle 225 strategy §I, the next several cycles are:

- **Cycle 226**: ship `compose_phiEquivalent_compose` by
  composing cycle 224's `derivativeWeight_compose_castAdd` (top
  half) with cycle 225's `derivativeWeight_compose_natAdd`
  (bottom half), threaded through `Fin.sum_univ_add` on the
  `(compose).b`-sum:
  - `(M₁.compose M₂).elementaryWeight t = ∑ j : Fin (s₁+s₂),
      (M₁.compose M₂).b j * (M₁.compose M₂).derivativeWeight j t`
    (by `elementaryWeight_eq`).
  - `Fin.sum_univ_add` + `compose_b_castAdd` /
    `compose_b_natAdd` (`Section381.lean:2560–2568`) gives:
    - Top half: `∑ j₁, M₁.b j₁ * M₁.derivativeWeight j₁ t
        = M₁.elementaryWeight t` (cycle 224 + `elementaryWeight_eq`).
    - Bottom half: `∑ j₂, M₂.b j₂ * M₂.derivativeWeightWithSrc
        M₁ j₂ t` (cycle 225).
  - **Key insight for cycle 226**: prove an auxiliary lemma
    `derivativeWeightWithSrc_respects_phiEquivalent` saying that
    `M₂.derivativeWeightWithSrc M₁ i t` is invariant under
    `PhiEquivalent M₁ M₁'` *and* `PhiEquivalent M₂ M₂'`. The
    second part is the new bit (the first part follows from the
    fact that `derivativeWeightWithSrc` consumes `M₁` only
    through `M₁.elementaryWeight`). Then
    `compose_phiEquivalent_compose` follows by combining the top
    half (which uses cycle 224 + the M₁ side of the auxiliary
    lemma) with the bottom half (which uses cycle 225 + both
    sides of the auxiliary lemma).
  - Estimated 80–120 LOC including the auxiliary respect lemma.
  - **Risk for cycle 226**: the bottom-half sum `∑ j₂, M₂.b j₂
    * M₂.derivativeWeightWithSrc M₁ j₂ t` doesn't collapse to
    `M₂.elementaryWeight t` directly (the `derivativeWeightWithSrc`
    differs from `derivativeWeight` at every recursion step
    because it threads `M₁.elementaryWeight` at each leaf). The
    `PhiEquivalent`-respect path is the only viable one.
- **Cycle 227**: `composeQ_phi` via `Quotient.lift₂` consuming
  cycle 226 (mirror of cycle 218's `composeQ`).
- **Cycle 228**: identity laws `composeQ_phi_id_left` /
  `composeQ_phi_id_right` (mirror of cycle 219).
- **Cycle 229+**: assemble `instance : Group (Quotient
  PhiEquivalent.setoidSigma)` via `Group.ofLeftAxioms` (mirror
  of cycle 222's `instGroup`).
- **Cycle 230**: ship `thm:384A` (Φ as a group homomorphism
  between the §382 and §383 quotient groups).

### Additional housekeeping for cycle 226+

- Consider exposing `derivativeWeightWithSrc` (drop the implicit
  `private` if any added) and adding a `simp` lemma
  `derivativeWeightWithSrc_mk` / `_vertex` for downstream
  convenience. Currently the only consumer is cycle 225's
  mutual identity, so no API smoothing is urgent.
- §441 Phase C.2 remains GPFS-blocked (42 consecutive timeouts
  through cycle 225). Per cycle 225 strategy §A, this is
  cluster-recovery territory and should be left alone by the
  worker. The standing escalation at
  `.prover-state/issues/cycle_182_gpfs_slowness.md` remains the
  authoritative record.
