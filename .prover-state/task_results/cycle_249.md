# Cycle 249 Results

## Worked on

`RootedTree.theta`, `RootedTree.thetaProd`, `RootedTree.thetaProd_eq_map_prod`,
`RootedTree.theta_eq_one` (and helper `RootedTree.thetaProd_eq_one`) inserted
into `OpenMath/Chapter3/Section310.lean` per planner Strategy §B–§G.

This is the cycle-248 consultant's **Option 1** deliverable — the trivial
exact-solution operator weight scaffold. It is the foundation for the
future `α(t)`-machinery that will eventually prove the textbook
`lem:310B`. **It is NOT the textbook `lem:310B` itself** (see Faithfulness
section).

## Approach

1. Read planner Strategy §B–§C for the `theta` recipe and Section301's
   cycle-017 `density` / `densityProd` template.
2. Wrote the mutual recursion `theta` / `thetaProd` (Strategy Step 2),
   verbatim shape from `Section301.lean:123–139`.
3. Wrote the bridge `thetaProd_eq_map_prod` (Strategy Step 3), verbatim
   from `Section301.lean:142–147`.
4. **Deviation from Strategy Step 4**: the planner's recipe used
   `induction t with | mk children ih => ...`, but `RootedTree` is a
   **nested inductive type** (`mk : List RootedTree → RootedTree`) and
   Lean's `induction` tactic does not support nested inductive types
   ("The `induction` tactic does not support the type
   `OpenMath.Chapter3.Section310.RootedTree` because it is a nested
   inductive type. Hint: Consider using the `cases` tactic instead").
   The planner's claim that the cycle-017 template "transfers verbatim"
   was incorrect on this point — cycle 017's `density_eq` does not use
   induction at all (it is a pure `show` + `rw`).
5. **Pivoted to mutual structural recursion** (parallels how `theta` /
   `thetaProd` themselves were defined): proved `theta_eq_one` and
   `thetaProd_eq_one` as a `mutual` block of theorems, each pattern-
   matching the same constructors as the corresponding `def`. This is
   strictly cleaner than Strategy Backup B.2's `RootedTree.recOn` (which
   would also have failed for the same nested-inductive reason) — it
   reuses the structural-recursion machinery Lean already accepted for
   the underlying `def`s.

   ```lean
   mutual
     theorem theta_eq_one : ∀ t : RootedTree, theta t = 1
       | mk children => by
           show thetaProd children = 1
           exact thetaProd_eq_one children
     theorem thetaProd_eq_one : ∀ ts : List RootedTree, thetaProd ts = 1
       | [] => rfl
       | t :: ts => by
           show theta t * thetaProd ts = 1
           rw [theta_eq_one t, thetaProd_eq_one ts]
           ring
   end
   ```

6. Added 3 non-vacuity examples (Strategy Step 5).
7. Verified `lake build OpenMath.Chapter3.Section310` (~11 s) and
   `lake build OpenMath.Chapter3` (~6 s, no errors). Pre-existing
   Mathlib deprecation warning about `CStarAlgebra.nonneg_iff_eq_...`
   is unrelated.
8. Verified `#print axioms` for all three new headline lemmas:

   ```
   theta_eq_one          : [propext, Classical.choice, Quot.sound]
   thetaProd_eq_one      : [propext, Classical.choice, Quot.sound]
   thetaProd_eq_map_prod : [propext, Classical.choice, Quot.sound]
   ```

9. Tautology-scanner regex (`:= h_…$ | exact h_…$ | := id$`): zero hits
   in `Section310.lean`.

## Result

**SUCCESS.** Cycle 249 ships axiom-clean with sorry count `0 → 0`:

* `theta`, `thetaProd` (mutual recursion).
* `thetaProd_eq_map_prod` (list-helper → `List.prod` bridge).
* `theta_eq_one` (closure, the headline lemma).
* `thetaProd_eq_one` (helper used by the mutual proof).
* 3 non-vacuity witnesses (`vertex`, `cherry`, `broom₃`).

Total LOC delta: ~50 lines added in `OpenMath/Chapter3/Section310.lean`
(slightly above the planner's 40-LOC estimate because `thetaProd_eq_one`
is an explicit theorem rather than implicit in an `ih` hypothesis).

Strategy Success Criteria §G items 1–10 all satisfied.

## Faithfulness check

For each new `def` / `theorem` introduced this cycle:

### `RootedTree.theta : RootedTree → ℝ`

* **Entity ID**: not in `extraction/formalization_data/entities/` —
  `theta` is a structural scaffold for the future `lem:310B`
  α-machinery, not a textbook-named entity. `lean_status.json` row for
  `lem:310B` correctly stays `unformalized`.
* **Textbook origin**: §312 elementary-weight machinery (prerequisite
  for `def:312A`, the exact-solution operator `E`). The recursive form
  `θ(mk children) = ∏ θ(cᵢ)` matches the tree-product structure of `E`.
* **Lean statement captures**: scaffold (the trivial weight identically
  equal to 1). The genuine textbook content (the elementary weight
  `α(t)` and the multi-tree-sum identity of `lem:310B`) is **NOT**
  formalized this cycle.
* **Definition smuggling check**: The recursive form `θ(mk children) =
  ∏ θ(cᵢ)` is the *definition*; `θ ≡ 1` is the *theorem*. We do NOT
  define `theta` as `fun _ => 1` and then call `theta_eq_one` a
  triviality — the `mutual` recursion through `thetaProd` is genuine
  structural data and `theta_eq_one` is a real proof obligation that
  walks the tree.

### `RootedTree.thetaProd : List RootedTree → ℝ`

* List-helper paired with `theta`'s mutual recursion. Defined as the
  running product `∏ theta(cᵢ)` over a list. Directly mirrors
  `Section301.lean`'s `densityProd`. No textbook divergence — this is
  a Lean-internal helper, not a textbook entity.

### `RootedTree.thetaProd_eq_map_prod`

* Bridge lemma collapsing the recursive helper to the standard
  `List.prod` form. Verbatim port of cycle-017's
  `densityProd_eq_map_prod` (Section301.lean:142). No textbook content;
  pure refactoring lemma.

### `RootedTree.theta_eq_one` (headline)

* **Entity ID**: not a textbook lemma (see `theta` above). Documented
  in the docstring as scaffold for future `α(t)` work.
* **Textbook content captured**: the closure `∀ t, θ(t) = 1`, which is
  what makes `theta` the exact-solution operator weight (§312
  prerequisite). Genuine math (Lean must walk the tree structure to
  prove it) but trivial relative to the eventual `lem:310B`.
* **Hypothesis strength check**: no hypotheses at all — it's a closed
  statement `∀ t, theta t = 1`. Cannot be weakened.
* **Tautology check**: conclusion `theta t = 1` does not appear as a
  hypothesis (there are no hypotheses).
* **Identity check**: proof is mutual structural recursion with `show`
  + `exact thetaProd_eq_one children`, NOT `:= id` or bare `exact h`.
  The `mutual` block does real recursive work.
* **Lean statement captures**: same content as the strategy's stated
  goal. No divergence.

### `RootedTree.thetaProd_eq_one` (helper)

* Companion to `theta_eq_one` produced by the mutual structural
  recursion. Statement: `∀ ts : List RootedTree, thetaProd ts = 1`.
  No textbook entity. Real recursive work via `mutual` block.

### Three `example` lines (`vertex`, `cherry`, `broom₃`)

* Non-vacuity witnesses showing `theta` is exercisable on the canonical
  small trees defined in lines 108–114 of `Section310.lean`. Each closes
  by direct citation `theta_eq_one _`. Standard Pre-Commit-checklist
  item per CLAUDE.md "for every new `class`/`structure`, provide at
  least one concrete witness".

### Summary

The cycle ships a **scaffold**, not the textbook `lem:310B`. The planner
correctly framed this in Strategy §B.2 and Step 8's commit-message
template; the task results above honor that framing. **No
`lean_status.json` or `plan.md` row should change.**

## Dead ends

### Strategy Step 4 / Backup B.2: nested-inductive `induction` tactic

The planner's primary recipe and Backup B.2 both used `induction t`
or `RootedTree.recOn`. Both fail with:

> The `induction` tactic does not support the type
> `OpenMath.Chapter3.Section310.RootedTree` because it is a nested
> inductive type. Hint: Consider using the `cases` tactic instead.

Lean 4's `induction` and `recOn` tactics do not autogenerate a
recursor-with-induction-hypotheses for nested inductive types — for
`inductive RootedTree | mk : List RootedTree → RootedTree`, the
auto-generated `RootedTree.rec` accepts only a one-arg `mk` case
without a nested `motive_2` for the `List`. Cycle 017's `density_eq`
proof avoided this entirely by being a pure `show` + `rw` and never
needing to descend into the children.

The successful pivot (mutual structural recursion in the proof, mirroring
the mutual structural recursion in the definition) is the canonical
fix — pattern-match on the constructor in the theorem signature and
let Lean's structural-recursion checker verify the recursive calls.

## Discovery

1. **Nested inductive types lock out `induction`/`recOn`.** For Lean 4
   types like `RootedTree` whose constructor takes a `List` of itself,
   the `induction` and `recOn` tactics will not work. The proof must
   either:
   - Be done by mutual structural recursion in the theorem signature
     (this cycle's approach — cleanest),
   - Or use a manually-defined induction principle.

   Cycle 017's `density_eq` proof is *not* a faithful template for
   any future theorem that needs to descend into children of a
   `RootedTree`; it only works because `density_eq` itself doesn't
   need to. **Future planner cycles touching tree-recursion proofs
   should default to mutual structural recursion in the proof, not
   tactic-mode `induction t`.**

2. **`mutual` blocks support theorems, not just defs.** Lean 4 happily
   accepts `mutual`-block theorems with structural pattern matching
   in their signatures. Useful pattern when proving a property of two
   mutually recursive functions.

3. **`show` retoggles definitional unfolding.** In each case branch of
   the mutual proof, `show thetaProd children = 1` (resp.
   `show theta t * thetaProd ts = 1`) was needed to unfold the LHS to
   match the next recursive call — `theta (mk children)` definitionally
   equals `thetaProd children`, but Lean doesn't auto-unfold without
   the `show` hint when the next tactic is `exact`. This is a recurring
   pattern when proving identities about mutually-recursive `def`s.

## Suggested next approach

The planner now has several candidates for cycle 250+:

### Candidate A — Build on the `theta` scaffold

Define a paired weight `phi : RootedTree → ℝ` with a different recursion
(e.g. matching the implicit Runge–Kutta operator `S(λ)` from §312), and
a corresponding `phi_eq_X` closure. This continues the §312 prerequisite
chain.

### Candidate B — Tackle `lem_311A_order_two` (cycle-248 consultant Option 2)

The 2-cycle-risk deliverable. Now that the §311 lem:311A p=1 case is
shipped (cycle 248), the p=2 case requires:
- An `iteratedFDeriv ℝ 1 f y₀ ↔ fderiv ℝ f y₀` bridge.
- A chain-rule helper `iteratedDeriv 2 yex x₀ = fderiv f y₀ (f y₀)`.
- `taylor_isLittleO (n := 3)` instead of `(n := 2)`.
- `ContDiff ℝ 3 yex` strengthening.

If the planner wants to attempt this, recommend **decomposing into 2
cycles**: cycle 250 = the `iteratedFDeriv ↔ fderiv` and chain-rule
helpers (axiom-clean infrastructure), cycle 251 = the actual
`lem_311A_order_two` theorem.

### Candidate C — Section319 helper extraction (Strategy Backup B.3)

Pure refactoring cycle. Move `geometric_sum_one_plus_pos`,
`geometric_sum_one_plus_zero`, `pow_one_add_le_exp` from
`Section319.lean` into a fresh `OpenMath/Helpers/GeometricExp.lean`.
Zero new mathematical content; ~120 LOC moved + 3 imports updated.
Useful as a "low-stakes cycle" if the planner wants to reduce
`Section319.lean`'s size.

### Candidate D — Begin `α(t)` definition for genuine `lem:310B`

The big one. Define the elementary weight `α : RootedTree → ℝ` per
Butcher §310. This is the genuine textbook `lem:310B` foundation
(not the `theta` scaffold shipped this cycle). Likely 2–3 cycles of
work; first cycle should be the bare definition + a few small
algebraic lemmas, NOT the full multi-tree-sum identity.

**Recommended**: Candidate A or D, depending on whether the planner
prioritizes broad scaffolding (more `theta`-family weights for §312)
or vertical depth (start the genuine `lem:310B` chain). Candidate B is
best held until at least one of A/D is started — it doesn't compose
with the `theta` scaffold and can wait. Candidate C is a pure-refactor
fallback if no mathematical-progress cycle is available.
