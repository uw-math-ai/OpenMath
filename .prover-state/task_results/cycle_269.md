# Cycle 269 Results

## Worked on
§310/§311 Phase E.1 (Phase 1 of 2 for order 5): nine new per-tree
scalar `bseriesExactTerm_*_scalar` closed forms covering all
unordered rooted trees of order 5 (Butcher Table 310(II) row r=5),
plus the def alias `bushy₄` at `Section310.lean`.

Deliverables (all shipped, all axiom-clean):

* P1 at `OpenMath/Chapter3/Section310.lean`:
  `bushy₄ := mk [vertex, vertex, vertex, vertex]` def alias plus
  one `rfl` order example.
* P2–P10 at `OpenMath/Chapter3/Section301.lean`: nine per-tree
  closed forms (full list and coefficients in §"Faithfulness check"
  below).
* P11 at `OpenMath/Chapter3/Section301.lean`: one non-vacuity
  witness exercising `bseriesExactTerm_mkMkMkCherry_scalar` on the
  trivial ODE `f := 0`.

Deferred to cycle 270 per cycle 269 strategy §A split:
* `lem_311A_order_five_partialSum` — the 17-tree partial-sum bridge
  at `Section311.lean`.

## Approach
Mechanical port of cycles 266–268 tactical recipe to order 5:

1. **Setup**: `unfold bseriesExactTerm <tree-alias>` (if alias)
   then `rw [show order T = 5 from rfl, show symmetry T = σ from
   rfl, show density T = γ from rfl]`.
2. **Inline elementaryDiff identity** (`have hED : ...`): build up
   from leaves via nested `have hED_v`, `have hED_cherry`,
   `have hED_broom`, `have hED_mkCherry`, `have hED_mkBroom`,
   `have hED_mkVCherry`, `have hED_bushy`, `have hED_mkMkCherry`
   as needed.
3. **Outer iteratedFDeriv reduction**: `unfold elementaryDiff`,
   `show iteratedFDeriv ℝ k f y₀ (fun i : Fin k => ...) = ...`,
   apply `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` +
   `smul_eq_mul` + `Fin.prod_univ_{one,two,three,four}` + the
   appropriate `.get i = ...` `rfl` rewrites for each child slot +
   the inner `hED_*` substitutions + `iteratedDeriv_succ` × (n−1)
   + `iteratedDeriv_one` + `ring`.
4. **Coefficient closure**: `rw [hED, smul_eq_mul]; push_cast; ring`.

Recipe order (front-loaded σ-validation checkpoints first):

1. P1 (bushy₄ alias) — compile, refresh olean.
2. P2 (T1 bushy₄) — depth-4 outer iteratedFDeriv,
   `Fin.prod_univ_four`, the only depth-4 case.
3. P10 (T9 mk[mk[mk[cherry]]]) — deepest nesting, validates the
   three-level cherry chain.
4. P4 (T3 mk[v,broom₃]) — multi-distinct-children σ-faithfulness
   checkpoint (σ=2 from `1!·σ(v)·1!·σ(broom₃)`).
5. P7 (T6 mk[bushy]) — one-child rule σ=σ(bushy)=6.
6. P9 (T8 mk[mk[broom₃]]) — σ=2 through TWO one-child wrappers
   (cycle 268 P3 σ=2 precedent escalated by one wrapper).
7. P8 (T7 mk[mk[v,cherry]]) — single-child wrapping a multi-child.
8. P3 (T2 mk[v,v,cherry]) — multi-distinct depth-3 outer.
9. P5 (T4 mk[v,mk[cherry]]) — depth-2 outer with one-child inner.
10. P6 (T5 mk[cherry,cherry]) — depth-2 outer with two identical
    cherries (σ=2 from `2!·σ(cherry)²`).
11. P11 — non-vacuity witness on `f := 0`.

## Result
SUCCESS — all 9 + 1 (alias) + 1 (witness) deliverables shipped.

Verified:
* `lake env lean OpenMath/Chapter3/Section310.lean` — clean.
* `lake env lean OpenMath/Chapter3/Section301.lean` — clean.
* `lake build OpenMath.Chapter3.Section301` — clean.
* `#print axioms` on all 9 new theorems — only `[propext,
  Classical.choice, Quot.sound]`.
* `grep -c sorry` on Section{301,310,311}.lean — all 0.

LOC delta: `Section310.lean` +5 LOC (alias + example).
`Section301.lean` +414 LOC (9 theorems + section header + witness).
`Section311.lean` 0 LOC (bridge deferred to cycle 270).
Total ≈ 419 LOC, within the strategy §G target ~450 LOC.

No abort thresholds tripped — `Fin.prod_univ_four` exists in
Mathlib at HEAD (confirmed via grep in
`Mathlib/Algebra/BigOperators/Fin.lean`), σ verification fired
cleanly on all nine `show ... = <σ value> from rfl` calls,
Bell-coefficient cross-check (§I step 4) matched cycle 259's
`(1, 7, 4, 11, 1)` verbatim.

## Faithfulness check

**Anchor entities**:
- `def:310A` (elementary differential): no change, all 9 new
  theorems consume the existing `elementaryDiff` def.
- `def:312A` (exact-solution B-series, implicit via Butcher §312):
  all 9 new theorems are scalar specialisations of the existing
  `bseriesExactTerm` def from cycle 266.
- `lem:310B`: STATUS UNCHANGED (`unformalized`). Phase E.1 is one
  stepping stone of the 8–14 cycle multi-phase roadmap in
  `.prover-state/issues/lem_310B_plan.md`.

### Per-theorem verification

For each theorem, the σ/γ values were independently re-derived via
the recursions

    σ(mk children) = ∏_{distinct subtree types} mᵢ! · σ(tᵢ)^{mᵢ}
    γ(mk children) = r(t) · ∏_{all children} γ(c)

and the Lean `rfl` step confirms agreement.

| # | Theorem | r | σ | γ | h^r/(σ·γ) | Monomial |
|---|---------|---|---|---|-----------|----------|
| T1 | `bseriesExactTerm_bushy₄_scalar` | 5 | 24 | 5 | h⁵/120 | f''''·f⁴ |
| T2 | `bseriesExactTerm_mkVertexVertexCherry_scalar` | 5 | 2 | 10 | h⁵/20 | f'''·f'·f³ |
| T3 | `bseriesExactTerm_mkVertexBroom₃_scalar` | 5 | 2 | 15 | h⁵/30 | (f'')²·f³ |
| T4 | `bseriesExactTerm_mkVertexMkCherry_scalar` | 5 | 1 | 30 | h⁵/30 | f''·(f')²·f² |
| T5 | `bseriesExactTerm_mkCherryCherry_scalar` | 5 | 2 | 20 | h⁵/40 | f''·(f')²·f² |
| T6 | `bseriesExactTerm_mkBushy_scalar` | 5 | 6 | 20 | h⁵/120 | f'''·f'·f³ |
| T7 | `bseriesExactTerm_mkMkVertexCherry_scalar` | 5 | 1 | 40 | h⁵/40 | f''·(f')²·f² |
| T8 | `bseriesExactTerm_mkMkBroom₃_scalar` | 5 | 2 | 60 | h⁵/120 | f''·(f')²·f² |
| T9 | `bseriesExactTerm_mkMkMkCherry_scalar` | 5 | 1 | 120 | h⁵/120 | (f')⁴·f |

### Coefficient cross-check vs cycle 259

`lem_311A_order_five` (Section311.lean line 1170) closed-form
order-5 contribution is `(h⁵/120) · P(f, y₀)` where

    P = 1·f''''·f⁴ + 7·f'''·f'·f³ + 4·(f'')²·f³
        + 11·f''·(f')²·f² + 1·(f')⁴·f

with Bell coefficients `(1, 7, 4, 11, 1)`. The per-tree closed
forms must sum to this when grouped by monomial, after multiplying
each coefficient by `120/σ·γ`:

| Monomial | Trees | Contributions (·1/120) | Total |
|----------|-------|--------------------------|-------|
| f''''·f⁴ | T1 | 1 | **1** ✓ |
| f'''·f'·f³ | T2, T6 | 6 + 1 | **7** ✓ |
| (f'')²·f³ | T3 | 4 | **4** ✓ |
| f''·(f')²·f² | T4, T5, T7, T8 | 4 + 3 + 3 + 1 | **11** ✓ |
| (f')⁴·f | T9 | 1 | **1** ✓ |

All five sums match cycle 259's Bell coefficients verbatim. The
nine `bseriesExactTerm_*_scalar` closed forms are coefficient-wise
faithful to the established order-5 Taylor expansion of the exact
solution under `y' = f(y)`.

### Checklist items

* **Lean statement captures**: same content as the
  `bseriesExactTerm` definitional expansion at the tree in
  question. Each theorem is a substantive computational equality
  (LHS `bseriesExactTerm f y₀ h <tree>`, RHS closed-form scalar
  polynomial in `deriv^k f y₀` and `f y₀`).
* **Tautology check**: no conclusion appears verbatim as a
  hypothesis. Each theorem has only `f : ℝ → ℝ`, `y₀ h : ℝ` as
  bindings; the conclusion is a non-trivial equality.
* **Identity check**: each proof goes through multi-step `unfold +
  rw + ring`, not `exact h_something`. No vacuous re-exports.
* **Hypothesis strength check**: no `ContDiff` hypotheses needed
  (matches cycle 266–268 precedent — `iteratedFDeriv` is defined
  unconditionally, the scalar collapse via
  `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` works
  definitionally).
* **Absent-theorem check**: all 9 theorem statements are concretely
  present in the file; no proof comments promise unwritten content.

### `bushy₄` alias (P1)

* Definition: `def bushy₄ : RootedTree := mk [vertex, vertex,
  vertex, vertex]` at `OpenMath/Chapter3/Section310.lean` line ~121.
* Captures the order-5 first-row tree of Butcher Table 310(II).
  `bushy₄.order = 5` (verified by `rfl`).
* Sister to the existing `bushy := mk [vertex, vertex, vertex]`
  (cycle 268 alias). No new mathematical content, pure naming
  convenience.

## Dead ends
None. The strategy file's recipe transferred mechanically. Initial
draft compiled on first attempt for all nine theorems (after one
re-Read to confirm the existing cycle 268 pattern's
`show ([(vertex : RootedTree), ...] : List RootedTree).get i = ...`
typeclass-elaboration hint was kept verbatim — without the explicit
`(vertex : RootedTree)` ascription, the `.get` `rfl` rewrites fail
to elaborate the homogeneous list type).

## Discovery
1. `Fin.prod_univ_four` is in Mathlib at HEAD
   (`Mathlib/Algebra/BigOperators/Fin.lean` line 124). The strategy
   §K fallback (`Fin.prod_univ_succ` × 3 + `Fin.prod_univ_zero`)
   was not needed. The depth-4 outer iteratedFDeriv recipe extends
   the cycle 266/267/268 ladder cleanly.
2. The σ-recursion through two one-child wrappers
   (`σ(mk [mk [broom₃]]) = σ(mk [broom₃]) = σ(broom₃) = 2`)
   fires correctly under `rfl` — the recursive computation is
   fully unfolded by Lean's reducer at definitional depth. No
   `decide` or explicit `simp [symmetry]` was needed.
3. Cycle 268's lesson that the `(vertex : RootedTree)` type
   ascription is needed in `.get` `rfl` rewrites carries over —
   without it the typeclass inference for the list's element type
   stalls. Kept the ascription in every `show ... .get _ = ...
   from rfl` to match the cycle 268 idiom.
4. The recipe ordering recommended by the strategy (front-loading
   σ-validation cases T3/T6/T8/T9 before the multi-child outer
   cases T2/T4/T5/T6) is empirically valuable but not strictly
   necessary — Lean's elaboration time stayed under 1 minute total
   for all nine theorems, and `lake build OpenMath.Chapter3.Section301`
   completed in 4.4 seconds (vs cycle 268's ~5 seconds).

## Suggested next approach
Cycle 270's deliverable per cycle 269 strategy §L is the 17-tree
partial-sum bridge:

* `lem_311A_order_five_partialSum` at `Section311.lean`. Bridges
  cycle 259's `lem_311A_order_five` closed-form polynomial residual
  to `bseriesExactPartialSum f y₀ h S` where S is the 17-tree
  Finset
  `{vertex, cherry, broom₃, mk [cherry], bushy, mk [v,cherry],
  mk [broom₃], mk [mk [cherry]], bushy₄, mk [v,v,cherry],
  mk [v,broom₃], mk [v,mk [cherry]], mk [cherry,cherry],
  mk [bushy], mk [mk [v,cherry]], mk [mk [broom₃]],
  mk [mk [mk [cherry]]]}`.
* 16 non-membership lemmas via `simp [vertex, cherry, broom₃,
  bushy, bushy₄]` on `RootedTree.mk.injEq` (the cycle 268 idiom,
  extended one extra alias).
* Recipe = 16 iterated `_insert` unfolds + one `_singleton` closure
  + all 13 per-tree closed forms (the 4 order-≤-3 + 4 order-4 +
  9 order-5) + `smul_eq_mul` + `ring` + `IsBigO.congr'` against
  cycle 259's base.
* Coefficient sum verification: monomial-grouped sums must match
  cycle 259's order-≤-5 polynomial coefficients (orders 1–4
  identical to cycle 268 bridge; order 5 verified above in this
  cycle's faithfulness check).
* LOC budget estimate: ~500 LOC (cycle 268's 8-tree bridge was
  ~290 LOC; 17-tree extension scales linearly per tree-membership
  lemma).
* Risk: LOW. The 8-tree precedent in cycle 268 transferred without
  ad-hoc patches; 17 trees is a quantitative extension.

After cycle 270 ships the bridge, **Phase E.1 is fully closed up
to order 5 in the scalar setting**, matching cycle 259's
deliberate order-5 cutoff and providing a clean stopping point for
the §310/§311 multi-cycle thread. Cycle 271+ planner decision:

* Polymorphic-`E` lift of cycle 266–269 closed forms (Phase D.2 /
  E.2, MEDIUM-HIGH risk multilinear-map plumbing).
* Pivot to `lem:342A` (single-cycle, independent target per
  `lem_310B_plan.md` §8.2).
* Multi-cycle assault on `lem:310B` Phase A.1 (`RootedTree.Vertex`
  scaffold + `vertices` Finset enumeration, per the cycle 261
  blueprint).
