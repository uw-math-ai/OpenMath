# Cycle 374 Results

## Worked on

Phase α.1 of `def_422B_subLemmaA_inductive_plan.md` (cycle 373 scoping
doc). Shipped a new `noncomputable def` and 4 non-vacuity witnesses
in `OpenMath/Chapter4/Section422.lean`:

- `inversePolynomial : RT → (RT → ℝ) → ℝ` — explicit pattern-match
  closed-form polynomial on the four small trees `vertex`, `cherry`,
  `broom₃`, `mk [cherry]`, with `0` for all other trees.
- 4 calibration `example`s confirming the definition evaluates to
  the cycle 341/367/368/369 closed forms on each of the four trees.

Target file: `OpenMath/Chapter4/Section422.lean`, appended just
before the closing `end OpenMath.Chapter4.Section422` (lines
4187–4309). The cycle 365 grandfathered sorry at line 2279 is
untouched.

## Approach

Per the cycle 374 strategy's **Recommended Approach A** (explicit
pattern match on small trees + `0` default), shipped Phase α.1 — the
strictly-easier deliverable — rather than the original §7 spec
(well-founded recursion on `RootedTree.order` matching all 7
witnesses). The strategy was explicit that pattern-matching is the
correct cycle 374 choice and that the recursive form is Phase α'
(cycle 375+ work).

Implementation steps:

1. Read cycle 367/368/369 closed forms at lines 2376, 2538, 2772 to
   pin down the exact polynomial expression on each tree.
2. Wrote the `noncomputable def` using `if t = vertex then … else
   if t = cherry then … else if t = broom₃ then … else if
   t = mk [cherry] then … else 0`. The `DecidableEq RootedTree`
   instance at `Section301.lean:92` makes the `if` branches fire.
3. Wrote 4 `example`s, each closed by `unfold inversePolynomial`
   followed by `rw [if_neg (by decide), …, if_pos rfl]` chains.
4. `lake env lean OpenMath/Chapter4/Section422.lean` — clean exit.
5. `lake build OpenMath.Chapter4.Section422` — clean rebuild
   (282 s including downstream dependencies).
6. `#print axioms` on `inversePolynomial` and on each of the 4
   witness statements (via a temporary check file with `RT` alias) —
   all returned `[propext, Classical.choice, Quot.sound]`.

Name resolution gotcha: `RootedTree.mk [cherry]` written at the top
level of `Section422.lean` resolves to *Mathlib's* `_root_.RootedTree`
(a graph-theoretic rooted tree from `Mathlib.Combinatorics`), not
our `OpenMath.Chapter3.Section310.RootedTree`. Fix is to fully
qualify: `OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]`.
This matches the convention already used at lines 2774–2875.

## Result

**SUCCESS** —

- `lake env lean OpenMath/Chapter4/Section422.lean` exits clean
  (only the cycle 365 grandfathered sorry warning at line 2272).
- `lake build OpenMath.Chapter4.Section422` rebuilds clean
  (no errors, 8037/8037 jobs).
- `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged
  from HEAD; same 1 code sorry + 4 docstring mentions).
- `#print axioms OpenMath.Chapter4.Section422.inversePolynomial`
  → `[propext, Classical.choice, Quot.sound]` (standard only).
- `#print axioms` on each of the 4 witnesses (via temporary RT-aliased
  test file) → `[propext, Classical.choice, Quot.sound]`.

The §422 axiom-clean streak (cycles 336–372 substantive, 373
doc-only) advances to 38 substantive + 1 doc + 1 substantive
(cycle 374). The streak is preserved.

## Faithfulness check

### New `def` — `inversePolynomial`

This is **not** a textbook-named concept. It is a helper definition
introduced internally by the cycle 373 scoping doc (§4.5,
"inversePolynomial t f") to bridge Sub-lemma A's quotient-level
equality to a `RootedTree → ℝ`-polynomial form. No `formalization_data`
entity exists.

The cycle 373 scoping doc §4.5 defines its purpose as: "the
closed-form polynomial in `{f s : s.order ≤ t.order}` such that
`elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t
(elementaryWeightQ_phi η_q)`". The cycle 374 ship realizes this
*partially* — on the four trees `vertex`, `cherry`, `broom₃`,
`mk [cherry]` the definition agrees with the cycle 341/367/368/369
closed forms; for all other trees it returns `0` (a Phase α'
placeholder).

**Definition smuggling check**: this is a `def`, not a `class` /
`structure`. There is no Prop field to smuggle. The four matched
cases are stated, verified, and explicitly listed in the doc-comment.

**Hypothesis strength check**: not applicable (no hypotheses).

### Four new `example`s — calibration witnesses

Each example is a non-vacuity check: `inversePolynomial <tree> f =
<closed-form polynomial>` for `<tree>` ∈ `{vertex, cherry, broom₃,
mk [cherry]}`. The closed forms are:

- `vertex`: `-(f RootedTree.vertex)` — matches cycle 341 P3
  (`Φ_{η⁻¹}(τ) = -Φ_η(τ)`, `Section422.lean:433`).
- `cherry`: `(f vertex)^2 - f cherry` — matches cycle 367
  (`elementaryWeightQ_phi_inv_cherry`, `Section422.lean:2376`).
- `broom₃`: `-(f vertex)^3 + 2·f vertex·f cherry - f broom₃` —
  matches cycle 368 (`elementaryWeightQ_phi_inv_broom₃`,
  `Section422.lean:2538`).
- `mk [cherry]`: `-(f vertex)^3 + 2·f vertex·f cherry -
  f (mk [cherry])` — matches cycle 369
  (`elementaryWeightQ_phi_inv_mkCherry`, `Section422.lean:2772`).

**Tautology check**: none of the examples have the conclusion
appearing as a hypothesis. The only hypothesis is `f : RT → ℝ`.

**Identity check**: each proof is `unfold + rw chain of if_neg/if_pos`,
non-trivial computational work driving `inversePolynomial`'s
`if-then-else` cascade to the chosen branch.

**Hypothesis strength check**: no hypotheses beyond `f`. The
witnesses are universal in `f`.

## Dead ends

- **Initial attempt with `RootedTree.mk [RootedTree.cherry]`**
  (without the `OpenMath.Chapter3.Section310.` prefix) failed with
  "Application type mismatch: `[RootedTree.cherry]` has type
  `List Chapter3.Section310.RootedTree` but expected `Type _`".
  Root cause: at the top level of `Section422.lean`, the bare name
  `RootedTree.mk` resolves to *Mathlib's* `_root_.RootedTree.mk`
  (constructor of `Mathlib.Combinatorics.RootedTree`, expecting a
  type argument), not our `OpenMath.Chapter3.Section310.RootedTree.mk`
  (which expects `List RootedTree`). Fix: full qualification.

- **Initial axiom check via test file with `open ...RootedTree`**
  failed because the local namespace clash inserted `sorry` for
  unresolved identifiers, contaminating the `#print axioms` output
  with `sorryAx`. Fix: use a `private abbrev RT := ...RootedTree`
  inside the test file, exactly matching the convention in
  `Section422.lean`.

## Discovery

1. **`by decide` is robust on `RootedTree` inequalities** at the
   four small trees of order ≤ 3 — no fallback to `injection` or
   `cases h` was needed. The cycle 367 worker had hit some
   `decide` failures on `Vertex`-typed equalities (memory
   `feedback_indexed_inductive_cases_disjoint.md`), but at the
   `RootedTree` level the constructor stack `mk` / `List.cons` /
   `List.nil` is shallow enough for `decide` to fire.

2. **The `RT` private abbrev is NOT sufficient for top-level
   `RootedTree.mk [...]` writing** — dot notation `RT.mk` still
   resolves to the ambient `RootedTree.mk` Lean elaborates, which
   when there's a Mathlib `_root_.RootedTree` in scope picks the
   wrong one. The robust fix is to write the fully qualified path
   `OpenMath.Chapter3.Section310.RootedTree.mk [...]` directly,
   matching the convention at `Section422.lean:2774`.

3. **The pattern-match form is Phase β-ready**. When cycle 375
   attempts the Phase β bridge lemma
   `elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t
   (elementaryWeightQ_phi η_q)` for `t` in the four-tree ladder,
   each case will reduce by `unfold inversePolynomial; rw [if_*];
   exact elementaryWeightQ_phi_inv_<tree>`. No additional `simp`
   normalization is anticipated.

4. **Cycles 370–372 closed forms are NOT yet pattern-matched** —
   `bushy`, `mk [broom₃]`, `mk [vertex, cherry]` all currently
   map to `0` under `inversePolynomial`. Extending the
   pattern-match to those 3 cases is trivial (Phase α.2 = 3
   additional `else if` clauses + 3 additional `example`s) and is
   a natural cycle 375 stretch option.

## Suggested next approach

For the cycle 375 planner:

**Option A — Phase β.1 on the four-tree ladder (RECOMMENDED first
target)**: prove the Phase β bridge lemma
`elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t
(elementaryWeightQ_phi η_q)` on the four trees `vertex`, `cherry`,
`broom₃`, `mk [cherry]`. Each case unfolds to the corresponding
cycle 341/367/368/369 theorem. This is the strict cycle 374 → 375
continuation that the scoping doc anticipated.

**Option B — Phase α.2 (pattern-match expansion)**: extend
`inversePolynomial` to the three additional witnesses (`bushy`,
`mk [broom₃]`, `mk [vertex, cherry]`) per cycles 370–372. Three
additional `else if` clauses plus three additional `example`s.
Strictly easier than Option A but provides less Phase β progress.

**Option C — Phase α' (well-founded recursion refinement)**: design
the recursive shape mirroring cycle 358's `_inv_mk` so that
`inversePolynomial` agrees with the full Phase β bridge on *all*
trees. This is multi-cycle research and risks introducing a partial
scaffold under a single-cycle budget. Recommended only if Options
A and B are both judged exhausted.

**Recommended cycle 375 plan**: Option A. The four-tree ladder
Phase β.1 closes a complete Sub-lemma A sub-strand and unblocks
incremental Sub-lemma A body progress. The non-matched trees in
`inversePolynomial` (currently returning `0`) are irrelevant
to Phase β.1 — they're a future cycle's concern.

**Do NOT** in cycle 375:

- Discharge the cycle 365 grandfathered sorry at line 2279 (still
  Phase ε, projected cycle 378+).
- Pivot to a fresh entity (`def:422B` is still the active
  multi-cycle target; pivoting now wastes both cycle 373 and
  cycle 374 investment).
- Add new sorries beyond the cycle 365 grandfathered one.
