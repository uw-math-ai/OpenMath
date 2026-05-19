# Cycle 389 Results

## Worked on
§422 Phase α'.4.1 P3 `(broom₃, cherry)` cross-term + calibration witnesses:
- **P1** `inversePolyTree_broom₃` — new theorem at `Section422.lean:6392`.
- **P2** `bichildCrossTerm` refinement — `(broom₃, cherry)` `else if` branch
  added to the if-then-else dispatch at `Section422.lean:6253+`.
- **P3** `inversePolyTree_mkBroomCherry` — new theorem at `Section422.lean:6481`,
  matching cycle 386's `elementaryWeightQ_phi_inv_mkBroomCherry` 14-term
  closed form verbatim under `f = elementaryWeightQ_phi η_q`.

## Approach
Followed strategy §K order:

1. **§A status verification**: `git log --oneline -1` confirmed cycle 388
   HEAD `ce128f4`. `grep -c sorry` confirmed 5 (4 docstring refs +
   1 grandfathered code sorry at line 2272).
2. **§D paper algebra**: verified the 9-term cross-term value
   matches the strategy by computing
   `(Target − Backbone)` term-by-term:
   - Backbone of `bichildPolynomial broom₃ cherry (-v³+2vc-b') (v²-c) f`
     = `v⁶ − 3v⁴c + 2v²c² + v³b' − vb'c + v³m − 2vcm + b'm
        + c·M_broom − v²·M_broom − bc`.
   - Target = cycle 386 RHS (14 terms).
   - Difference = `-2v⁴c + 3v²c² + v³b' − vb'c + 2v³m − 2vcm
                   − 3v²·vc + 2v·cc + v·vb'` ✓ matches §C P2.
3. **P2**: extended `bichildCrossTerm` def with second `else if` branch,
   updated docstring to mention cycle 389 alongside cycle 388.
4. **P1**: wrote `inversePolyTree_broom₃` using `show` to expose
   `broom₃ = mk [vertex, vertex]`, `rw [inversePolyTree,
   inversePolyTree_vertex]`, `unfold bichildPolynomial`, then proved
   `bichildCrossTerm vertex vertex f = 0` via two `if_neg (by decide)`
   (neither `(cherry, cherry)` nor `(broom₃, cherry)` matches), then
   two explicit `show` steps to fold `mk [vertex] = cherry` and
   `mk [vertex, vertex] = broom₃` definitionally, then `ring`.
5. **P3**: wrote `inversePolyTree_mkBroomCherry` exactly per strategy
   skeleton — `rw [inversePolyTree, inversePolyTree_broom₃,
   inversePolyTree_cherry]`, `unfold bichildPolynomial`, then a single
   `rw [show bichildCrossTerm broom₃ cherry f = <9-term value> by ...]`
   reducing the cross-term via `if_neg (by decide); if_pos ⟨rfl, rfl⟩`,
   then `ring` closed the degree-6 9-indeterminate identity well
   within heartbeat budget (no `maxHeartbeats` bump, no Fallback A
   decomposition needed).
6. **Compile + axiom check**: `lake build OpenMath.Chapter4.Section422`
   succeeded (309s); `#print axioms` on all three new symbols
   (`inversePolyTree_broom₃`, `bichildCrossTerm`, `inversePolyTree_mkBroomCherry`)
   and the cycle 388 regression target `inversePolyTree_mkCherryCherry`
   all reported `[propext, Classical.choice, Quot.sound]` — fully
   axiom-clean.

## Result
SUCCESS — all three sub-deliverables (P1, P2, P3) shipped axiom-clean.

- `ring` closed the P3 9-indeterminate degree-6 identity without
  Fallback A decomposition.
- Sorry count unchanged at 5 (4 docstring refs + 1 grandfathered code
  sorry at line 2272).
- §422 streak: 51 → **52** substantive + 2 doc cycles (336–389).
- Cycle 389 score target: 2 (substantive ship, no faithfulness divergence).

## Faithfulness check

For each new symbol introduced this cycle:

### `inversePolyTree_broom₃` (theorem, P1)

- **Entity ID**: none (internal infrastructure for the unified
  recursive `inversePolyTree` Family C handler).
- **Quoted reference**: matches cycle 368's
  `elementaryWeightQ_phi_inv_broom₃` closed form (Butcher §382)
  `Φ_{η_q⁻¹}(broom₃) = -v³ + 2vc - b'` under `f = Φ_η`.
- **Lean statement captures**: same content (verified by paper
  algebra: `broom₃ = mk [vertex, vertex]` ⇒ `inv₁ = inv₂ = -v` ⇒
  backbone yields `-v³ + 2vc - b'` after collapsing `mk [vertex] →
  cherry` and `mk [vertex, vertex] → broom₃` definitionally;
  cross-term contribution is `0` since `(vertex, vertex)` matches
  neither if-branch).
- **Tautology check**: conclusion is a 3-term polynomial in `f vertex`,
  `f cherry`, `f broom₃`; no hypothesis equals the conclusion.
- **Identity check**: proof body is
  `rw + unfold + rw [show ... = 0] + show + show + ring`;
  real algebraic work, not a hypothesis re-export.
- **Hypothesis strength**: universal in `f : RT → ℝ`, no extra
  hypotheses beyond cycle 368's textbook statement.

### `bichildCrossTerm` (def, P2 extension)

- **Entity ID**: none (internal infrastructure helper for binary-
  children polynomial dispatch).
- **Definition smuggling check**: `(broom₃, cherry)` value is
  **back-computed** from cycle 386's
  `elementaryWeightQ_phi_inv_mkBroomCherry` (axiom-clean ship from
  cycle 386, **independent** of any cycle 389 theorem) by
  subtracting the cycle 387 `bichildPolynomial` backbone at
  `(inv_b, inv_c) = (-v³+2vc-b', v²-c)`. The value is pinned by
  empirical data shipped 3 cycles before P3's calibration witness,
  so the calibration is **NOT** definition smuggling — see strategy
  §E for the full argument.
- **Lean statement captures**: 9-term value matching the paper
  algebra in strategy §D (verified term-by-term).

### `inversePolyTree_mkBroomCherry` (theorem, P3)

- **Entity ID**: none (internal calibration witness connecting the
  recursive `inversePolyTree` evaluation at `mk [broom₃, cherry]`
  to cycle 386's hand-derived closed form).
- **Quoted reference**: matches cycle 386's
  `elementaryWeightQ_phi_inv_mkBroomCherry` 14-term RHS verbatim
  under `f = elementaryWeightQ_phi η_q` (copy-paste verified from
  `Section422.lean:5176-5216`).
- **Lean statement captures**: same content as cycle 386's
  quotient-level theorem (universal in `f` here, specialised to
  `f = Φ_η` there).
- **Tautology check**: 14-term degree-6 polynomial RHS; no
  hypothesis equals the RHS.
- **Identity check**: proof body is `rw + unfold + rw [show ...] + ring`;
  `ring` performs genuine algebraic cancellation reducing
  `backbone + cross-term` to the 14-term target.
- **Hypothesis strength**: universal in `f : RT → ℝ`, no extra
  hypotheses (parametric in `f` so no requirement on `vb'` either).

## Dead ends
None this cycle — all three sub-deliverables landed on first compile.
Worth noting: the strategy's §F Fallback A (decomposing the P3 proof
into a backbone-only lemma + cross-term residue lemma) was **NOT**
needed; `ring` closed the 9-indeterminate degree-6 identity directly
without timing out. If future cycles add larger cross-term branches
(e.g. `(broom₃, broom₃)`), the Fallback A pattern remains a viable
plan-B.

## Discovery
- **`(vertex, vertex)` falls through both if-branches in
  `bichildCrossTerm` cleanly via `by decide`**: the `if_neg (by decide)`
  pair fires axiom-cleanly (just `[propext, Classical.choice,
  Quot.sound]`, no new `Decidable` infrastructure required). This
  means P1's proof for `inversePolyTree_broom₃` is **future-proof
  against further `bichildCrossTerm` extensions**: as long as the
  new branches don't add an `(vertex, vertex)` case (and they
  shouldn't — `broom₃` is the canonical `mk [vertex, vertex]`
  representative), P1's `if_neg; if_neg` cascade remains valid.

- **Definitional fold `mk [vertex] = cherry` works in `show`**:
  after `rw [inversePolyTree, inversePolyTree_vertex]` and
  `unfold bichildPolynomial`, the LHS has `f (mk [vertex])` and
  `f (mk [vertex, vertex])` literally; a sequence of two `show`
  reductions folds them back to `f cherry` and `f broom₃` before
  `ring` is called. This avoids needing an explicit `rfl` rewrite
  step and keeps the proof body short.

- **`ring` budget for P3**: the 9-indeterminate degree-6
  bichild-broom-cherry identity (15-monomial backbone + 9-monomial
  cross-term ↦ 14-monomial target) closes under default
  `maxHeartbeats = 200000`. This validates the strategy's
  expectation (§C P3 "ring should close in under 200000 heartbeats")
  and provides a benchmark for sizing future bichild cross-term
  refinements: even with 9 indeterminates and degree 6, `ring`'s
  Buchberger-style normalisation finishes well within budget on
  this cluster.

## Suggested next approach
Cycle 390 has three viable directions:

1. **(broom₃, broom₃)** cross-term: requires shipping a
   `mk [broom₃, broom₃]` quotient-level closed form first
   (`elementaryWeightQ_phi_inv_mkBroomBroom`). This is a substantive
   2-cycle deliverable — cycle 390 ships the quotient closed form,
   cycle 391 back-computes the cross-term and ships the calibration
   witness. The new kernels likely surfaced: `mk [vertex, broom₃]`
   (already in `bichildCrossTerm broom₃ cherry`) plus possibly
   `mk [broom₃, broom₃]` itself. Order-7 tree.

2. **Phase α'.4.2** migration: dispatch `inversePolynomial`'s
   Family C branches (currently pattern-match for the small ladder)
   through the recursive `inversePolyTree`. Parallel to cycles
   381/383 for Families A/B. Requires no new quotient-level theorems
   — just rewiring the existing pattern-match calls. ~80–150 LOC,
   low risk.

3. **Phase β bridges** for existing Family C trees: each cycles
   371, 372, 384, 386 quotient theorem needs an analog of cycle
   375's bridge `elementaryWeightQ_phi (η_q⁻¹) t =
   inversePolynomial t (elementaryWeightQ_phi η_q)`. This is the
   "make use of the calibration witnesses" cycle, converting them
   from internal recursion-evaluators to fully-fledged quotient-level
   alternative-form theorems.

**Recommendation**: option **2** (Phase α'.4.2 migration) for cycle
390. It unblocks the most downstream work (any future client of
`inversePolynomial` that wants to use the Family C closed forms gets
them for free via the recursion), has no quotient-level dependencies
(everything needed is already on disk after cycle 389), and matches
the cycle 385 scoping doc §6 ladder progression. Options 1 and 3
are also viable, but option 1 is multi-cycle and option 3 is broad
(4 separate bridge theorems) — option 2 is single-cycle, focused, and
low-risk.

**Strict NO** for cycle 390: continuing to expand `bichildCrossTerm`
without first migrating `inversePolynomial`. The cross-term ladder
is currently 2 entries deep (cherry-cherry, broom₃-cherry); adding
more without consuming them via the migration creates a "lots of
infrastructure, no clients" anti-pattern.
