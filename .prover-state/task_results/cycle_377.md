# Cycle 377 Results

## Worked on

§422 Sub-lemma A Phase α.2 + β.2 + γ extension (7-tree ladder closure):

- **Phase α.2**: extended `inversePolynomial` pattern-match from 4
  trees (`vertex`, `cherry`, `broom₃`, `mk [cherry]`) to 7 trees by
  appending three new `else if` branches (`bushy`, `mk [broom₃]`,
  `mk [vertex, cherry]`) with closed forms from cycles 370/371/372.
- **Phase α.2 calibration**: three new `example` non-vacuity
  witnesses confirming `inversePolynomial` evaluates as the closed-form
  table prescribes on the three new trees.
- **Phase β.2 bridges**: three new theorems
  (`elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy`,
  `_mkBroom₃`, `_mkVertexCherry`) discharging the
  `unfold inversePolynomial` → `if_neg* + if_pos rfl` → cycle 370/371/372
  closed-form recipe.
- **Phase β aggregator refresh**:
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` upgraded
  from a 4-way to a 7-way disjunction.
- **Phase γ extension**: in-place extension of
  `inversePolynomial_eq_of_subtree_agreement` with three new `by_cases`
  blocks for the new trees and a 3-`if_neg`-each extension of the
  final default branch.

## Approach

1. **Step 1 — Phase α.2**: edited the body of `inversePolynomial` at
   `Section422.lean:4234–4248`. Appended three new `else if` branches
   between `mk [cherry]` and the `else 0` fallback. Closed forms
   transcribed verbatim from cycle 370/371/372 theorem statements.
2. **Pre-flight `lake build`**: as the strategy prescribed,
   immediately ran `lake build OpenMath.Chapter4.Section422` after
   Step 1. Phase γ's default branch broke (3 unresolved
   `if t = <new tree> then ... else 0`-shaped goals remained on each
   side of the equality), exactly as the strategy's option-2
   contingency predicted.
3. **Phase γ patch** (forced by pre-flight): inserted three new
   `by_cases` blocks between the existing `mk [cherry]` block and
   the final default branch in
   `inversePolynomial_eq_of_subtree_agreement`. Each new block
   followed the cycle 376 `mk [cherry]` recipe verbatim: `subst`,
   then `have h_<subtree>` × N from `h_closed`, then a chain of
   `if_neg (by decide : ...)` discharges followed by `if_pos rfl`
   (twice, once per side of the equation), then the `h_<subtree>`
   rewrites. Final default branch extended with 3 more `if_neg
   h_<new tree>` entries per side.
4. **Step 2 — Phase α.2 calibration**: appended three `example`
   theorems after the cycle 374 `mk [cherry]` calibration witness.
   The `bushy` witness requires 4 `if_neg`s + `if_pos rfl`;
   `mk [broom₃]` needs 5; `mk [vertex, cherry]` needs 6 (matching
   each tree's position in the chain).
5. **Step 3 — Phase β.2 bridges**: appended three theorems after
   cycle 375's `_mkCherry` bridge. Same `unfold inversePolynomial`
   → `if_neg* + if_pos rfl` → `exact` recipe, with `exact` quoting
   the cycle 370/371/372 closed-form theorems.
6. **Step 4 — aggregator refresh**: in-place upgrade of
   `_on_ladder` from `rcases ht with h | h | h | h` to `rcases ht
   with h | h | h | h | h | h | h`, with three new `exact`
   dispatches chained to the three new bridges.
7. **Build + axiom check**: `lake build OpenMath.Chapter4.Section422`
   succeeded (~3:33 → ~4:06 cold rebuild times across the two passes).
   `lake env lean` axiom-check on all 4 new public theorems plus the
   in-place-extended Phase γ theorem each returned `[propext,
   Classical.choice, Quot.sound]` — no `sorryAx`.

## Result

**SUCCESS** — all of Phase α.2, β.2, the aggregator refresh, and the
Phase γ extension to 7 trees ship axiom-clean. The §422 axiom-clean
streak advances from **41 substantive + 1 doc** (cycles 336–376) to
**42 substantive + 1 doc** (cycles 336–377).

The 7-tree closed-form ladder is now **fully bridged** in both
directions: forward via Phase β.1 + β.2 bridges (taking
`elementaryWeightQ_phi η_q⁻¹ t` to `inversePolynomial t
(elementaryWeightQ_phi η_q)`), and agreement-stable via Phase γ
(taking closed-subtree agreement of `f` and `g` to equality of
`inversePolynomial t f` and `inversePolynomial t g`).

Sorry count unchanged: still 5 lines / 1 code sorry (the cycle 365
grandfathered Sub-lemma A body at `Section422.lean:2272`).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

- **`inversePolynomial` (extended)** — *entity*: helper definition,
  not a Butcher-named concept, so no `formalization_data/entities`
  JSON. The three new pattern-match branches transcribe cycles 370/371/372's
  closed forms verbatim:
  - `bushy` branch RHS = `v⁴ − 3v²·c + 3v·b' − f bushy` matches
    `elementaryWeightQ_phi_inv_bushy` (Section422.lean:3011–3019).
  - `mk [broom₃]` branch RHS = `v⁴ − 3v²·c + v·b' + 2v·m − f (mk [broom₃])`
    matches `elementaryWeightQ_phi_inv_mkBroom₃` (Section422.lean:3397–3410).
  - `mk [vertex, cherry]` branch RHS = `v⁴ − 3v²·c + c² + v·b' + v·m
    − f (mk [vertex, cherry])` matches
    `elementaryWeightQ_phi_inv_mkVertexCherry` (Section422.lean:3798–3814).
  - Lean statement captures: **same content** as the three closed-form
    theorems' RHSs (modulo `f` ↔ `elementaryWeightQ_phi η_q`
    instantiation).

- **`_bushy`, `_mkBroom₃`, `_mkVertexCherry` Phase β.2 bridges** —
  *entity*: infrastructure theorems linking `Φ_{η⁻¹}` to
  `inversePolynomial`. Not Butcher-named concepts; no JSON. Each
  statement is the obvious bridge `elementaryWeightQ_phi η_q⁻¹ t =
  inversePolynomial t (elementaryWeightQ_phi η_q)` for the named
  tree, with proof being `unfold inversePolynomial` + a chain of
  `if_neg`/`if_pos rfl` rewrites and `exact <cycle 370/371/372
  closed-form theorem>`. **Tautology check passes**: the conclusion
  is an equality whose LHS is not a hypothesis; the proof is
  non-trivial in the sense that it requires `unfold`, multiple
  `if_neg`s, and the cycle 370/371/372 base lemmas. **Identity check
  passes**: the proof is not `exact h` for some pre-existing `h`;
  it requires `unfold` and a chain of `if_neg`s before the final
  `exact`. **Hypothesis strength check passes**: only the quotient
  argument `η_q` is taken; no extra hypotheses.

- **`_on_ladder` (refreshed)** — *entity*: aggregated 7-way bridge.
  The 4-way version (cycle 375) is in-place replaced with a 7-way
  version. No new definition; the theorem name and conclusion are
  unchanged, only the disjunction hypothesis grows from 4 to 7
  cases. **Tautology check passes** (the conclusion is a
  non-trivial equality). **Identity check passes** (the proof is a
  7-way `rcases` chained to 7 `exact` dispatches; non-trivial work
  per case). **Hypothesis strength check passes** (the 7-way
  disjunction is weaker than any individual tree-specific hypothesis,
  not stronger; it is the natural aggregator form).

- **`inversePolynomial_eq_of_subtree_agreement` (extended)** —
  *entity*: Phase γ closed-subtree agreement. Theorem name and
  signature unchanged from cycle 376 (`(t : RT) (f g : RT → ℝ)
  (h_closed : ∀ s, s.order ≤ t.order → f s = g s) :
  inversePolynomial t f = inversePolynomial t g`). The proof body
  is extended with three new `by_cases` blocks plus a 3-`if_neg`-
  per-side extension of the final default branch. **Tautology check
  passes**, **Identity check passes**, **Hypothesis strength check
  passes** (the hypothesis is the closed-subtree form per the §6.3
  scoping doc — exactly what downstream Phase D.3.d will need).

## Dead ends

- **Strategy's "defer Phase γ extension to cycle 378" path was
  infeasible**: the cycle 377 strategy's recommended approach (option 1)
  said to patch the default branch with `≤10 LOC` of `if_neg
  h_<tree>` discharges. But this requires hypotheses `h_bushy`,
  `h_mkBroom`, `h_mkVertexCherry` which don't exist in the cycle 376
  proof — they would need to come from new `by_cases` blocks. So
  option 1 (small patch) and option 2 (full extension) are
  effectively the same: both require the 3 new `by_cases` blocks.
  The "defer to cycle 378" path described in the strategy would
  have left the file with a build error, so was not a viable choice.

## Discovery

- **Discovery #1 — `unfold inversePolynomial` exposes the full
  chain**: a single `unfold inversePolynomial` at the start of
  `inversePolynomial_eq_of_subtree_agreement`'s proof reveals all
  7 nested `if-then-else` expressions on each side of the equation.
  Each subsequent `by_cases h_<tree>` + `subst` + `if_neg`-chain
  + `if_pos rfl` block discharges one case. The default branch's
  `if_neg h_<existing tree>`-chain only works for the **first 4**
  trees; if `inversePolynomial` grows new branches, the default
  branch must either grow new `if_neg`s (requiring the new
  hypotheses from new `by_cases` blocks) or be matched by new
  `by_cases` blocks before the final default. There's no way to
  patch the default branch alone.

- **Discovery #2 — `(by decide : RootedTree.X ≠ <larger tree>)`
  works in both directions**: the new Phase γ blocks needed
  disequalities like `RootedTree.bushy ≠
  OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]`
  (i.e., a smaller tree on the LHS, a larger tree on the RHS).
  All such side conditions discharge via `by decide` thanks to the
  cycle 343 structurally-recursive `RootedTree.order`-based
  decidability instance, regardless of which tree is on which side.

- **Discovery #3 — proof-block ordering is load-bearing in the
  extended Phase γ**: the new `by_cases` blocks must be inserted in
  the same order as the new `else if` branches in
  `inversePolynomial`. Specifically: `h_bushy`, then `h_mkBroom`,
  then `h_mkVertexCherry`. Each block's `if_pos rfl` triggers at
  the position corresponding to that tree's branch in the chain;
  reordering would shuffle the count of `if_neg` discharges per
  block.

- **Discovery #4 — Phase α.2 calibration witnesses' `if_neg`
  count grows linearly with branch position**: the `bushy`
  calibration witness needs 4 `if_neg`s; `mk [broom₃]` needs 5;
  `mk [vertex, cherry]` needs 6. This is just the chain length
  before the matched branch fires. Same applies to the Phase β.2
  bridges (4/5/6 `if_neg`s respectively).

## Suggested next approach

**Cycle 378 — Phase δ.B (general `m` via `powRep` induction)** is now
unblocked across the entire 7-tree ladder. With Phases α.1+α.2
(`inversePolynomial` definitionally 7 trees), β.1+β.2 (forward
bridges for all 7 trees), and γ (closed-subtree agreement for all 7
trees) all axiom-clean, cycle 378 can attack the general-`m`
extension using cycle 361's `linearResidualAt_succ_mk_eq` as the
inductive bridge and the cycle 377 Phase β bridges as the m=0 base
case.

Specifically, the cycle 378 worker should:
1. State a `powRep_inversePolynomial_eq` theorem capturing the
   m+1-step `powRep` action on `Φ_{η^(−(m+1))}` in terms of
   `inversePolynomial` and the m-step `Φ_{η^(−m)}` action.
2. Use `Nat.rec` or `induction m` to perform the induction; the m=0
   base case is the Phase β bridge (`_on_ladder`), and the m+1 step
   reduces to a `Finset.sum` rewrite over the `powRep` definition.
3. Verify axiom-clean via `#print axioms`.

If cycle 378 succeeds, cycle 379 can begin Phase ε (closing the cycle
365 grandfathered sorry at `Section422.lean:2272`). However, Phase ε
remains gated on Phase α' (recursive `inversePolynomial` covering
arbitrary `t`, not just the 7-tree ladder), since the sorry's
quantifier is `∀ t : RT`. A multi-cycle scoping doc for Phase α' is
recommended before any cycle 380+ attempt at Phase ε.

**Cycle 378 entry point (alternative)**: if Phase δ is judged
too ambitious for a single cycle, an intermediate cycle could ship
a "Phase γ' — open-subtree agreement" variant taking
`∀ s, s.order < t.order → f s = g s` (strict-subtree, instead of
closed-subtree), which would be useful for downstream `induction t`
arguments where the inductive hypothesis is given for strict
subtrees. The cycle 376 `closed-subtree` form is sufficient for
Phase D.3.d but not necessarily for all consumers.
