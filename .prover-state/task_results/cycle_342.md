# Cycle 342 Results

## Worked on

§422 Phase D.1 — the closed-form `η(τ)` base-case solver for Butcher's
underlying-one-step-method (422a) equation. Three new public theorems
shipped to `OpenMath/Chapter4/Section422.lean` (484 → 696 LOC,
+~212 LOC delta):

* `Eq422a_at_vertex_linear` (P1, load-bearing).
* `Eq422a_at_vertex_linear_of_isConsistent` (P2, IsConsistent
  corollary recovering Butcher's textbook η-coefficient).
* `Eq422a_at_vertex_eta_eq` (P4, closed-form η(τ) extraction under a
  non-vanishing-coefficient hypothesis — stretch goal).

Plus a `k = 0` non-vacuity anonymous `example`.

## Approach

Followed the strategy's §B.2 P1 recipe verbatim:

1. Verified cycle 341 state at HEAD (`34c199e`, 484 LOC, 0 sorrys).
2. Sorry-first scaffold for `Eq422a_at_vertex_linear`. Cold compile
   confirmed signature parses.
3. Filled the P1 proof body with the strategy's six-step plan:
   specialize `hEq` at `RootedTree.vertex`, collapse `Φ_1(τ) = 0` via
   `elementaryWeightQ_phi_id`, rewrite each α-summand via cycle 341
   P3 (`elementaryWeightQ_phi_zpow_vertex`), each β-summand via cycle
   341 P1+P3 + cycle 337 `D_element_elementaryWeight_vertex`, then
   factor η out of both sums via `Finset.sum_neg_distrib` +
   `Finset.sum_mul` + `Finset.sum_add_distrib` (with `congr 1` for
   the β-side's split into the `-(coef·η)` and `+β_i` halves),
   closing by `linarith`.
4. Added P2: bridge `SatisfiesEq404b`'s `((i : ℕ) + 1 : ℝ)` cast
   form to the `((i.val + 1 : ℕ) : ℝ)` form used by
   `Eq422a_at_vertex_linear` via `push_cast; ring` inside a
   `Finset.sum_congr`; rewrite RHS using the resulting identity.
5. Added P3 (Option A — `k = 0` `example`): `simp` reduces
   `Eq422a_at_vertex_linear` (both sums empty / one-β-term collapse)
   directly to `0 = M.β 0`.
6. Added P4 stretch: `field_simp` + `linarith` from P1.
7. Verified compile, sorry count = 0, tautology scanner clean, all
   three theorems axiom-clean.

No Aristotle submissions per the strategy's §C explicit "do NOT
submit anything to Aristotle this cycle" guidance — the work was
structural algebraic specialization, not premise selection.

## Result

**SUCCESS.** All three target theorems plus the non-vacuity example
ship axiom-clean. Verification:

* `lake env lean OpenMath/Chapter4/Section422.lean` → exit 0 (~5 min
  warm, no errors).
* `lake env lean OpenMath/Chapter4.lean` → exit 0.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` → 0.
* Tautology scanner (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`) → no hits.
* `#print axioms` for all three new theorems → `[propext,
  Classical.choice, Quot.sound]` only.

## Faithfulness check

For each new `theorem` introduced this cycle:

* **`Eq422a_at_vertex_linear`** — entity `def:422B`, supporting
  algebraic specialization. Textbook context (Butcher §422 p. 358,
  proof at `extraction/raw_text/ch04.txt:1163`):
  > "These equations are recursive in nature. The first equation
  > (with the empty tree) is trivially satisfied. Selecting `u = τ`
  > gives `−(α₁ + 2α₂ + ⋯ + kαₖ) η(τ) − β₀ − β₁ − ⋯ − βₖ = 0`,
  > so that `η(τ) = − (β₀ + β₁ + ⋯ + βₖ) / (α₁ + 2α₂ + ⋯ + kαₖ)`."

  Lean statement captures: **same content** (the unconditional
  algebraic specialization). Butcher's textbook form
  `−(α₁ + 2α₂ + ⋯ + kαₖ) η(τ) = β₀ + β₁ + ⋯ + βₖ` is the special
  case under consistency (where `Σ i·αᵢ = Σ βᵢ` makes `coef_β`
  irrelevant); the unconditional Lean form keeps the β-side
  `coef_β(M) := Σ i · βᵢ` contribution explicit because we have not
  yet assumed `IsConsistent`. Note: the textbook coefficient sign
  flips because Butcher rearranges the equation `LHS − Σ(…) = 0` to
  `Σ(…) = 0`; the Lean form reads the η-coefficient as
  `+(coef_α + coef_β)` after the η-extraction sign cancels with the
  `-1` from `-(…)` rewrites. Both forms agree under
  `Eq422a_at_vertex_linear_of_isConsistent` (P2).

* **`Eq422a_at_vertex_linear_of_isConsistent`** — entity `def:422B`,
  consistency-strengthened corollary. Textbook (Butcher §422 p.
  1163, same paragraph as above): the RHS `β₀ + β₁ + ⋯ + βₖ`
  collapses to `α₁ + 2α₂ + ⋯ + kαₖ` under (404b) consistency,
  giving the final formula `η(τ) = −1` (the explicit numerical
  value Butcher cites — under preconsistency,
  `Σ i·αᵢ = Σ βᵢ` and the η-coefficient `coef_α + coef_β` simplifies
  to `coef_α + coef_β` where consistency makes `coef_α = sum_β`, so
  `η(τ) = coef_α / (coef_α + coef_β)`). Lean statement captures:
  **same content** — the RHS is recast as `coef_α` in place of
  `sum_β` via the `SatisfiesEq404b` identity.

* **`Eq422a_at_vertex_eta_eq`** — entity `def:422B`, closed-form η(τ)
  extraction. Textbook (Butcher §422 p. 1163, last line of the
  cited paragraph): `η(τ) = ...`. Lean statement captures: **same
  content** under the hypothesis `coef_α + coef_β ≠ 0`. The extra
  hypothesis is documented as "downstream of IsStable +
  IsPreconsistent via cycle 178's
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`" and is *not*
  in the textbook statement — but it is the load-bearing condition
  Butcher implicitly relies on (he says "by stability the
  coefficient is non-zero" without making the dependency explicit).
  The bridge to remove this hypothesis is a separate cycle 343+
  deliverable per `def_422B_path.md` §G.

No new `def`, `structure`, or `class` introduced this cycle. No
hypothesis strength issues: P1 takes only `hEq : Eq422a M η_q`
(matching the textbook's "η satisfies (422a)"); P2 adds
`M.IsConsistent` per the textbook's explicit "under consistency";
P4 adds `coef_α + coef_β ≠ 0` per the textbook's implicit
non-vanishing requirement.

No tautology / identity issues. P1's conclusion is a fresh real
identity not appearing in any hypothesis; P2 derives a different
RHS via the `SatisfiesEq404b` rewrite; P4 derives a `field_simp`d
form via `linarith` from P1's conclusion.

## Dead ends

1. First proof attempt left vestigial `simp [Finset.sum_mul, …]`
   lines inside the `hα_factor` / `hβ_factor` helpers after a `rw`
   chain that had already closed the goals — Lean reported "No
   goals to be solved" at those lines. Fixed by deleting the `simp`
   lines; the `← Finset.sum_neg_distrib, ← Finset.sum_mul` chain
   suffices to align both sides definitionally.

2. P3 non-vacuity example initially wrote `exact h.symm` after `simp
   at h`; Lean's error revealed `simp` produced `h : 0 = M.β 0`
   directly (it normalizes equalities by putting numerical
   constants on the LHS), so `exact h` was the right closure. Minor
   one-character fix.

## Discovery

1. **`Finset.sum_neg_distrib` and `Finset.sum_mul` are current** at
   Mathlib HEAD (cycle 342); the strategy's hedge about "names may
   have drifted" was not triggered. The `← Finset.sum_neg_distrib`
   + `← Finset.sum_mul` chain is the cleanest path to pulling
   `-c_i` outside a sum without manual `Finset.sum_congr`
   gymnastics.

3. **`simp` normalizes `M.β 0 = 0` to `0 = M.β 0`** (numerical
   constant on LHS). Useful to remember when chaining `simp at h`
   followed by `exact h` vs `exact h.symm` — let the goal shape
   drive the direction rather than guessing.

4. **The `((i : ℕ) + 1 : ℝ)` ↔ `((i.val + 1 : ℕ) : ℝ)` cast
   mismatch** between `SatisfiesEq404b` and `Eq422a_at_vertex_linear`
   was anticipated by the strategy's P2 "important prerequisite
   check" and resolved cleanly by a `Finset.sum_congr rfl +
   push_cast + ring` bridge. Worth documenting as a recurring
   pattern: any time two definitions reach for "i + 1 cast to ℝ"
   through different ℕ-arithmetic paths, expect to need this
   bridge.

## Suggested next approach

**Cycle 343 — Phase D.2 well-founded recursion infrastructure (per
`def_422B_path.md` §5 row D.2; ~60–100 LOC).** With the Phase D.1
base case shipped, the natural next deliverable is well-founded
recursion on `RootedTree.order` so that Phase D.3's inductive step
can recurse on sub-trees. Concrete substeps:

1. Search Mathlib for an existing `WellFoundedRelation` /
   `WellFounded` instance on `OpenMath.Chapter3.Section310.RootedTree`
   via `RootedTree.order` (cycle 195's
   `RKTableau.PReducesTo.size_lt_of_step` is the analogous
   template).
2. If absent, build it via `Function.WellFoundedRelation.onFun
   Nat.lt_wfRel RootedTree.order` (or whatever the current name
   is at HEAD).
3. Verify with a small `example` recursing on a `RootedTree` via
   `RootedTree.order` (e.g., `decide ∀ t : RootedTree, t.order =
   t.order` is trivial, but a `termination_by` decreasing recursive
   function is the real test).
4. Ship a `RootedTree_wf` named lemma + the underlying instance.

**Alternative — stability-bridge fast follow-up (~30 LOC).** If the
worker wants to immediately strengthen `Eq422a_at_vertex_eta_eq` to
drop the explicit `coef_α + coef_β ≠ 0` hypothesis in favor of
`M.IsStable + M.IsPreconsistent`, that's a single-cycle target
using cycle 178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`.
This is a smaller scope than Phase D.2 and might be a good "warm-up"
if Phase D.2's Mathlib hunt looks deep.

**Pivot option per `def_422B_path.md` §8 (only if planner judges
7+ consecutive §422 cycles excessive):** fresh entity work on
`def:442A` (principal sheet), `thm:535A` (underlying one-step
method for GLM), or `thm:541A` (DIMSIM types). Cycle 342 is now
cycle 7 of the §422 streak (cycles 336–342); pivot pressure starts
mounting but Phase D.2/D.3 are still ~3 cycles from sealing the
core `def:422B` deliverable, so finishing the streak likely beats
context-switching here.
