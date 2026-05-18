# Cycle 377 — Strategy

## Context recap

Cycle 376 shipped **Phase γ** axiom-clean: `inversePolynomial_eq_of_subtree_agreement` at end of `OpenMath/Chapter4/Section422.lean`. The §422 axiom-clean streak now stands at **41 substantive + 1 doc** cycles (336–376).

The cycle 373 scoping doc `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` decomposes the Sub-lemma A closure into Phases α, β, γ, δ, ε:

| Phase | Status | Cycle |
|-------|--------|-------|
| α.1 (4-tree `inversePolynomial`) | ✓ shipped | 374 |
| β.1 (4 per-tree bridges + aggregator) | ✓ shipped | 375 |
| γ (closed-subtree agreement, 4 trees) | ✓ shipped | 376 |
| **α.2 + β.2 (extend to 7 trees)** | **← cycle 377 target** | — |
| δ (general `m` via `powRep`) | TODO | 378+ |
| ε (close cycle 365 grandfathered sorry) | TODO | 379+ |
| α' (well-founded recursion on all trees) | open research | — |

The cycle 376 worker's "Option C" (Phase ε feasibility audit) is premature — the grandfathered sorry at `Section422.lean:2279` is quantified over arbitrary `t`, but Phase α.1 covers only 4 trees. Closing Phase ε requires Phase α coverage to expand first.

## Cycle 377 deliverable

**Ship Phase α.2 + β.2: extend the ladder from 4 trees to 7 trees** by adding pattern-match branches for the cycle 370/371/372 closed forms (`bushy`, `mk [broom₃]`, `mk [vertex, cherry]`) and the matching Phase β.2 bridges + a refreshed 7-tree aggregator.

**LOC budget**: ~110 LOC. Mechanical ladder extension. Should ship axiom-clean.

### Deliverables (in this order)

**Step 1 — Phase α.2: extend `inversePolynomial` to 7 trees** (~25 LOC).

Edit the body of `inversePolynomial` at `Section422.lean:4234–4248`. Append three new `else if` branches **before** the `else 0` fallback, using the closed forms from cycles 370/371/372 (visible in the file at lines 3011, 3397, 3798):

```lean
noncomputable def inversePolynomial (t : RT) (f : RT → ℝ) : ℝ :=
  if t = RootedTree.vertex then
    -(f RootedTree.vertex)
  else if t = RootedTree.cherry then
    (f RootedTree.vertex) ^ 2 - f RootedTree.cherry
  else if t = RootedTree.broom₃ then
    -(f RootedTree.vertex) ^ 3
      + 2 * f RootedTree.vertex * f RootedTree.cherry
      - f RootedTree.broom₃
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry] then
    -(f RootedTree.vertex) ^ 3
      + 2 * f RootedTree.vertex * f RootedTree.cherry
      - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
  else if t = RootedTree.bushy then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + 3 * f RootedTree.vertex * f RootedTree.broom₃
      - f RootedTree.bushy
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃] then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + f RootedTree.vertex * f RootedTree.broom₃
      + 2 * f RootedTree.vertex
          * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry] then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + (f RootedTree.cherry) ^ 2
      + f RootedTree.vertex * f RootedTree.broom₃
      + f RootedTree.vertex
          * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
  else
    0
```

**Critical: match the closed forms exactly.** Cross-check each new branch against the source theorem:

- `bushy` ↦ cycle 370's `elementaryWeightQ_phi_inv_bushy` at lines 3011–3019 (RHS: `v⁴ − 3v²·c + 3v·b' − Φ_η(bushy)`).
- `mk [broom₃]` ↦ cycle 371's `elementaryWeightQ_phi_inv_mkBroom₃` at lines 3397–3410 (RHS: `v⁴ − 3v²·c + v·b' + 2v·m − M`).
- `mk [vertex, cherry]` ↦ cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry` at lines 3798–3814 (RHS: `v⁴ − 3v²·c + c² + v·b' + v·m − V`).

**Step 2 — Phase α.2 calibration witnesses** (~30 LOC).

Ship three `example` non-vacuity witnesses for the new branches, mirroring the cycle 374 pattern (Section422.lean:4255–4308). Each requires four or five `if_neg (by decide : ...)` discharges (one per earlier tree in the chain) followed by `if_pos rfl`. Insert these after the existing `mk [cherry]` calibration witness (after line 4308).

Example for `bushy` (the simplest of the three — only needs 4 `if_neg`s, since `bushy` is the 5th branch):
```lean
example (f : RT → ℝ) :
    inversePolynomial RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          RootedTree.bushy
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_pos rfl]
```

For `mk [broom₃]` and `mk [vertex, cherry]`, each needs **5** or **6** `if_neg`s respectively (since they come later in the chain).

**Step 3 — Phase β.2: three per-tree bridges** (~50 LOC).

Append three bridge theorems after `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry` (after line 4401), each following the cycle 375 recipe verbatim. Pattern:

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.bushy
      = inversePolynomial RootedTree.bushy (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          RootedTree.bushy
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_pos rfl]
  exact elementaryWeightQ_phi_inv_bushy η_q
```

Same shape for `_mkBroom₃` and `_mkVertexCherry`, but with **5** and **6** `if_neg`s each respectively (additional ones for `bushy` and (in the case of `_mkVertexCherry`) for `mk [broom₃]`).

**Step 4 — Refresh the aggregator** (~10 LOC).

Update `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` at lines 4410–4422 to take a 7-way disjunction and chain the new bridges. **Do not delete the existing 4-tree aggregator** — extend it in place:

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht : t = RootedTree.vertex ∨ t = RootedTree.cherry
        ∨ t = RootedTree.broom₃
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
        ∨ t = RootedTree.bushy
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) :
    elementaryWeightQ_phi η_q⁻¹ t
      = inversePolynomial t (elementaryWeightQ_phi η_q) := by
  rcases ht with h | h | h | h | h | h | h <;> subst h
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃ η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkBroom₃ η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry η_q
```

### Phase γ proof — likely needs minor patch to handle 7 branches

Cycle 376's Phase γ proof at `inversePolynomial_eq_of_subtree_agreement` does a 4-way `by_cases` over `{vertex, cherry, broom₃, mk [cherry]}` plus a "default" branch which unfolds via `unfold inversePolynomial`. **The default branch's `if_neg` chain may need to be extended** when `inversePolynomial` grows three new `else if` branches.

**Pre-flight check before extending Phase α.2:** run `lake build OpenMath.Chapter4.Section422` immediately after Step 1's `inversePolynomial` redefinition. If Phase γ's default branch breaks (some `if_neg`/`if_pos` rewrite no longer fires), there are two paths:

1. **Patch the existing default branch** (recommended, minimal effort): add three more `if_neg (h_<tree>)` discharges to the default-branch `rw` chain, using the cycle 376 `h_bushy`/`h_mkBroom₃`/`h_mkVertexCherry`-style negation tags from the case split. This is mechanical (≤10 LOC patch).
2. **Add three more `by_cases` blocks for the new trees** (full Phase γ extension): defers cleanly to cycle 378. If pre-flight shows this is needed, **revert the cycle 377 Phase α.2 ship to a smaller scope**: ship only α.2 + β.2 (Steps 1–3) without the aggregator, and defer the aggregator + Phase γ extension to cycle 378.

**Recommended approach**: try Step 1 first, recompile, check what fails. If only the default-branch `if_neg` chain needs more entries, patch it (~10 LOC). If three new `by_cases` blocks are needed for full Phase γ coverage, **defer all Phase γ work to cycle 378** and ship only Steps 1–3 in this cycle, leaving the cycle 376 aggregator with its 4-tree disjunction untouched (it still type-checks even if `inversePolynomial` grows).

## Verification protocol

1. After editing the file, run `lake build OpenMath.Chapter4.Section422` to refresh `.olean`. Expect ~4 min cold rebuild.
2. Run `lake env lean OpenMath/Chapter4/Section422.lean` to check the file diagnostics. Expect **ONE** pre-existing sorry warning at line ~2279 (the cycle 365 grandfathered sorry, code-level count 1) — do **not** introduce any new sorries.
3. Confirm sorry count: `grep -c sorry OpenMath/Chapter4/Section422.lean` should return **5** (4 docstring mentions + 1 actual code sorry), unchanged from HEAD.
4. Axiom-check the new theorems via a temporary file:
   ```lean
   import OpenMath.Chapter4.Section422
   #print axioms OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy
   #print axioms OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolynomial_mkBroom₃
   #print axioms OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry
   #print axioms OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder
   ```
   Each should output `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`. Per cycle 376 Discovery #1, you **must** run `lake build` first; `lake env lean` alone does NOT refresh the `.olean` cache used by downstream `import`.

## Faithfulness check (for the pre-commit list)

The three new bridges replicate cycles 370/371/372's closed forms verbatim (file lines 3011–3019, 3397–3410, 3798–3814). The Phase α.2 pattern-match branches are direct one-to-one transcriptions of those closed forms. No definitions are being smuggled — these are infrastructure bridges between two equal-by-construction representations.

Update `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` §10 with a cycle 377 update block (after the cycle 376 §10.5 block) documenting Phase α.2 + β.2 ship and the Phase γ extension deferral (if any).

## What NOT to try

Do **NOT** attempt these in cycle 377:

- **Closing the cycle 365 grandfathered sorry at line 2279.** Phase ε requires Phase δ + Phase α coverage of arbitrary `t`. Premature. Even a Phase ε "feasibility audit" on the 7-tree ladder would not produce a meaningful closure of a fully-general sorry.
- **Phase α' / well-founded recursion on all trees.** Multi-cycle research per `def_422B_subLemmaA_inductive_plan.md` §A. The cycle 374 strategy explicitly deferred it; the cycle 376 task results re-flag it. Needs its own scoping doc before any worker attempt.
- **Phase δ (general `m` via `powRep`).** Even if shipped in cycle 377, it would only cover 4 trees (the current Phase α.1 coverage before this cycle's ship). Wait for cycle 378+ after the ladder extension is verified.
- **Full Phase γ extension to 7 trees in this cycle.** Defer to cycle 378. The pre-flight check above will reveal whether the existing Phase γ proof needs a minimal patch (≤10 LOC, ship in cycle 377) or a full three-case extension (~150 LOC, defer to cycle 378).
- **Compiling `OpenMath/Chapter4/Section441.lean`.** 43+ consecutive GPFS timeouts; skip per `.prover-state/issues/cycle_182_gpfs_slowness.md`.
- **Introducing any new sorries.** Per cycle 365 rollback precedent. The cycle 365 grandfathered sorry stays; nothing else may be sorry'd.
- **Redefining `inversePolynomial`'s base 4-tree shape.** The 4-tree definition is fixed (cycle 374); only append new `else if` branches between the `mk [cherry]` branch and the `else 0` fallback. Don't reorder, don't rename. Reordering would break cycle 375's β.1 bridges (each chain of `if_neg`s assumes the 4-tree order).
- **Using `simp` instead of explicit `rw [if_neg, ..., if_pos rfl]`.** Cycle 374 task results documented that `by decide` discharges the `RootedTree` inequality side-goals via the cycle 343 structurally-recursive `RootedTree.order`; `simp` may not fire cleanly through nested `if`-then-`else`.
- **Using `Equiv.swap` / `RootedTree.symmetry` machinery.** Phase α.2 is pure pattern-match extension; no tree-automorphism reasoning needed.
- **Modifying `scripts/autonomous_loop.py` or any supervisor infrastructure.** Per CLAUDE.md.

## Bookkeeping

After the cycle 377 ship lands axiom-clean:

- `lean_status.json`: row for `def:422B` stays `partial`. No status promotion. The Sub-lemma A → Sub-lemma B → `def:422B` chain is still multi-phase; cycle 377 closes one further step.
- `plan.md`: row for `def:422B` stays `[~]`. No status change.
- Update `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` §10 with the cycle 377 update.
- Write `task_results/cycle_377.md` documenting Phase α.2 + β.2 ship + cycle 378 entry point (Phase γ extension to 7 trees, if not already shipped this cycle).

## Cycle 378 entry point

If Phase γ shipped (the existing proof needed only a small default-branch patch), cycle 378 should pursue **Phase δ.B** (general `m` via `powRep` induction at the theorem level) per the scoping doc §6.4. Use cycle 361's `linearResidualAt_succ_mk_eq` as the inductive bridge and the cycle 377 Phase β.2 bridges as the m=0 base case.

If Phase γ extension was deferred (the existing proof needed a full three-case extension), cycle 378 should ship that extension first: add three more `by_cases` blocks to `inversePolynomial_eq_of_subtree_agreement` covering the new `bushy`, `mk [broom₃]`, `mk [vertex, cherry]` cases. Each block follows the cycle 376 recipe (~50 LOC each, ~150 LOC total). Phase δ then targets cycle 379.

Phase ε (closing the cycle 365 sorry) remains blocked on Phase α' (recursive `inversePolynomial` covering arbitrary `t`). That gap requires its own multi-cycle scoping doc — defer until at least cycle 380+.
