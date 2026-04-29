# Cycle 018 Results

## Worked on

`def:312A` — derivative weights for Runge–Kutta methods (§312, Butcher
3rd ed., page 178). Created `OpenMath/Chapter3/Section312.lean` from
scratch; updated `OpenMath/Chapter3.lean` to import it.

## Approach

Followed the planner's strategy verbatim:

1. State sanity (HEAD = `cd5ebc0`, no sorry's, both Section301 and
   Section310 present, no tautology-scanner regressions). All passed.
2. Read `extraction/formalization_data/entities/def_312A.json`. Confirmed
   that (312a)–(312d) ARE the textbook definition (Butcher writes
   "this definition is used recursively") and that there is no
   separate textual characterisation to prove equivalent. **No σ-style
   faithfulness divergence.**
3. Skipped the "single-arg recursion + abbreviations" form mentioned
   first in the strategy and went directly to the "Fallback" mutual
   pattern (`derivativeWeight` + `derivativeWeightProd`) recommended
   for robustness, mirroring cycle 017's `density`/`densityProd` and
   `symmetry`/`symmetryProd` shape. Reason: the strategy explicitly
   says "Aim to write the file using the mutual pattern from the start
   unless `.attach` works on first try" — so I wrote it that way from
   the start to avoid any risk of `.attach` plumbing fights.
4. Added the four named API theorems (312a)–(312d), the bridge lemma
   `derivativeWeightProd_eq_map_prod`, and a concrete witness
   (`explicitEuler`).
5. Sanity check: `explicitEuler.elementaryWeight RootedTree.vertex = 1`
   verifies the order-1 condition for forward Euler computes correctly
   from the recursion.

Key implementation details:

* `RKTableau s` is a pure data structure with three fields
  (`A : Matrix (Fin s) (Fin s) ℝ`, `b c : Fin s → ℝ`). No `Prop`
  fields, so the structure-smuggling check is vacuous.
* `derivativeWeight` and `derivativeWeightProd` thread the tableau
  `M` and stage index `i` unchanged; the structural argument is the
  tree (or list of trees). The `j`-summation in the cons-case is
  value-level only, not structural — Lean's mutual structural
  recursion checker accepts the pair on first pass.
* `internalWeight` and `elementaryWeight` are non-recursive
  abbreviations that wrap the recursion in the standard
  `Σⱼ aᵢⱼ·(Φⱼ D)(t)` and `Σᵢ bᵢ·(Φᵢ D)(t)` notation.
* Bridge lemma `derivativeWeightProd_eq_map_prod` collapses the helper
  to the standard `(children.map (Φᵢ ·)).prod` form via straightforward
  list induction (`nil` → `rfl`; `cons` → `rw [ih]; rfl`).

Aristotle was NOT used this cycle. Per the cycle-017 worker's
discovery #3 (and the strategy's explicit guidance), short manual
proofs that close in 1–2 tactic attempts should not be batched to
Aristotle — the 30-min wait wastes budget. Every theorem here closes
in ≤ 4 lines manually.

## Result

**SUCCESS** —

* `lake env lean OpenMath/Chapter3/Section312.lean` clean (no errors,
  no warnings).
* `lake build` clean (`Build completed successfully (2824 jobs)`).
* `#print axioms` for `derivativeWeight`, `derivativeWeightProd`,
  `internalWeight`, `elementaryWeight`, and all four named theorems
  shows only `[propext, Classical.choice, Quot.sound]`.
* No new `sorry`'s. No `axiom` / `constant` introduced. Tautology
  scanner returns zero hits.
* `extraction/formalization_data/lean_status.json`: `def:312A` row
  updated (`lean_file: "OpenMath/Chapter3/Section312.lean"`,
  `lean_symbol: "OpenMath.Chapter3.Section312.RKTableau.derivativeWeight"`,
  `status: "formalized"`).
* `plan.md`: `def:312A` row marked `[x]`; progress counter
  `18 / 175` → `19 / 175`.

## Faithfulness check

For each new `def` and `theorem` introduced this cycle:

### `RKTableau` (structure) — `def:312A` indirectly

- Entity ID: `def:312A`. Textbook (paraphrased from `def_312A.json`):
  > Let `(c, A, b)` denote the tableau for an `s`-stage Runge–Kutta
  > method.
- Lean statement captures: **same content**. Three independent fields
  `A`, `b`, `c` matching the textbook tableau. No `Prop` fields, so
  no smuggling possible. Concrete witness `explicitEuler` provided in
  the same file (CLAUDE.md rule on new structures).

### `RKTableau.derivativeWeight` and `RKTableau.derivativeWeightProd`

- Entity ID: `def:312A`. Textbook (quoted verbatim from
  `def_312A.json`):
  > `(Φᵢ D)(τ) = 1`, (312a)
  > `(Φᵢ D)([t₁ … tₖ]) = Πⱼ Φᵢ(tⱼ)`. (312c)
- Lean statement captures: **same content**.
  * Empty-list base case in `derivativeWeightProd` returns `1`,
    giving `derivativeWeight M i (mk []) = 1` — matches (312a).
  * Cons case `(t :: ts)` returns `(Σⱼ aᵢⱼ · derivativeWeight j t) * derivativeWeightProd i ts`,
    which by induction equals `Πⱼ Φᵢ(tⱼ)` — matches (312c).
  * The textbook IS the recursion (Butcher: "this definition is used
    recursively"). No separate textual characterisation exists, so
    there is no faithfulness divergence to flag.

### `RKTableau.internalWeight`

- Entity ID: `def:312A`. Textbook:
  > `Φᵢ(t) = Σⱼ aᵢⱼ (Φⱼ D)(t).` (312b)
- Lean: `internalWeight M t i := Σⱼ M.A i j * M.derivativeWeight j t`.
  **Same content** — literal transcription of (312b).

### `RKTableau.elementaryWeight`

- Entity ID: `def:312A`. Textbook:
  > `Φ(t) = Σᵢ bᵢ (Φᵢ D)(t).` (312d)
- Lean: `elementaryWeight M t := Σᵢ M.b i * M.derivativeWeight i t`.
  **Same content** — literal transcription of (312d).

### Theorems `derivativeWeight_vertex`, `internalWeight_eq`, `derivativeWeight_mk`, `elementaryWeight_eq`

These are the four named API entry-points for (312a)–(312d).

* `derivativeWeight_vertex` (312a): proved by reducing to
  `derivativeWeightProd M i []`, which is `rfl`-equal to `1` by
  definition. **Real reduction** (one-line `show ... ; rfl`).
* `internalWeight_eq` (312b): `rfl` — exposes the abbreviation as a
  named lemma so downstream callers do not need to unfold
  `internalWeight`. **Per CLAUDE.md identity check**: not vacuous —
  this is a standard Lean idiom (see Section301's `r_recursion`,
  `γ_recursion`, `σ_recursion`, all of which are also `rfl`-style
  re-exports of underlying definitions). The statement is the API,
  not a re-export of a hypothesis.
* `derivativeWeight_mk` (312c): genuine reduction via the bridge
  lemma `derivativeWeightProd_eq_map_prod`. **Real work.**
* `elementaryWeight_eq` (312d): same pattern as `internalWeight_eq`.
  Named API, not a hypothesis re-export.

### Tautology / hypothesis-strength check

* No theorem conclusion appears verbatim as one of its hypotheses.
* No `Prop` fields on `RKTableau`, so the structure-smuggling check
  is vacuous.
* No theorem has hypotheses stronger than the textbook requires.

## Dead ends

None. The cycle-017 mutual pattern transferred cleanly. The strategy's
"Fallback" warning about `.attach` plumbing fights was preempted by
writing the mutual form from the start.

## Discovery

1. **Tableau as a data-only structure with no validity Prop fields
   composes well with downstream weight-recursion**. Validity
   conditions like `cᵢ = Σⱼ aᵢⱼ` (consistency, sometimes called the
   row-sum condition) and order conditions (`Φ(t) = 1/γ(t)` for all
   trees of order ≤ p) belong on theorems about specific tableaux,
   not on the data definition. This avoids the Prop-field-smuggling
   trap that would otherwise force every weight computation to carry
   around proofs.
2. **The mutual pattern with parameters threaded explicitly works.**
   Lean's mutual structural-recursion checker accepts
   `derivativeWeight (M : RKTableau s) (i : Fin s) : RootedTree → ℝ`
   paired with
   `derivativeWeightProd (M : RKTableau s) (i : Fin s) : List RootedTree → ℝ`
   on first try, even though the cons case calls `derivativeWeight M j t`
   with a fresh `j` from a `Σⱼ` expression. The structural argument is
   the tree/list, not `j`, so Lean's checker is happy.
3. **`#print axioms` syntax**: `#print axioms NS.foo` works; the `@`-prefixed
   form `#print axioms @NS.foo` does NOT (Lean 4 parses `@` as a term-level
   prefix and rejects it after the `#print axioms` keyword). Note for
   future axiom checks.

## Suggested next approach

For cycle 019, the natural next target is **`lem:312B`** —
"Elementary Weight Summation Formula" — which gives an alternative
formula for `Φ(t)` using the vertex/edge characterisation of trees.
The JSON says it depends only on `def:312A` (now formalised), so it
should be unblocked. Worth checking whether the proof in Butcher
actually goes through by induction on the tree structure (very
likely) before committing to it.

If `lem:312B` looks deeper than one cycle on inspection of its JSON,
two backup targets:

* A second `RKTableau` witness — Heun's method (2-stage explicit RK)
  or the classical RK4 (4-stage) — with computed elementary weights
  for `vertex`, `cherry`, `broom₃` as `example` lemmas. Useful
  infrastructure for downstream Butcher-table sanity checks; about
  half a cycle of work.
* A `symmetry_dedup_form` lemma in Section301 stating
  `symmetry (mk children) = ((children.dedup).map (fun t => Nat.factorial m * symmetry t ^ m)).prod`
  with `m := children.count t`. The cycle-017 worker explicitly
  flagged this as "worth ~½ cycle".

Do NOT pick `thm:302A` / `B` / `C` — they need α(t)/β(t) labelling
infrastructure (3–5 cycles of permutation-group work, same blocker
class as the σ-as-group issue). Also do NOT pick `lem:310B` — it
needs `thm:306A` (Taylor's theorem) as a Mathlib bridge.
