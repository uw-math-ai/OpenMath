# Cycle 550 Results

## Worked on
Splitting `OpenMath/ButcherGroup/Section384.lean` (3408 lines, APPROACHING
CAP) into a core convolution layer + a parametric closed-form slices module,
per the cycle 550 strategy. REFACTOR_COMMIT — no new theorems, no proof
changes.

## Approach
Followed the strategy literally:

1. Identified the cleavage at line 1813. Lines 1–1812 of the original
   `Section384.lean` cover `bSeries` / upper-left block reduction /
   `foldr_mul_add_eq_powerset_sum` / `rightAuxAt` / `rightAuxAtCoef` /
   `convAt` / `bConv` / `bSeries_eq_split` / `bSeries_eq_bConv` /
   `convAt_congr_coef` / the `t₂`-permutation invariance lemmas
   (`convAt_isRKEquivalent_t2`, `bWeighted_convAt_isRKEquivalent_t2`,
   `bConv_isRKEquivalent_t2`, `bSeries_product_isRKEquivalent_t2`).
   Lines 1814–3406 are the parametric closed-form ladder added in
   cycles 538–549.
2. Created `OpenMath/ButcherGroup/Section384Slices.lean`. Imported
   `Mathlib`, `OpenMath.RungeKutta`, `OpenMath.OrderConditions`,
   `OpenMath.ButcherGroup.Core`, and `OpenMath.ButcherGroup.Section384`
   (so the moved theorems can still reference `bSeries_eq_bConv`,
   `rightAuxAtCoef`, `convAt`, etc.). Re-opened `Finset` and entered
   `namespace ButcherTableau` to preserve every fully qualified name
   (`ButcherTableau.ButcherProduct.bConv_singleton_leaf_eq` etc.).
3. Cut lines 1814–3406 from `Section384.lean` and pasted them into the
   new file verbatim. Closed the new file with `end ButcherTableau`.
4. Truncated `Section384.lean` at line 1812 and added a closing
   `end ButcherTableau`. The file is now 1814 lines.
5. Added `import OpenMath.ButcherGroup.Section384Slices` to
   `OpenMath/ButcherGroup.lean` (the umbrella that downstream callers
   already use).
6. Verified each touched file compiles with the NVMe toolchain
   (`lake env lean`), then `lake build OpenMath.ButcherGroup.Section384`
   to refresh the stale `.olean` (otherwise the slices file errored on
   "already declared" because it was importing the pre-truncation
   cached oleans), then full `lake build`.

## Result
SUCCESS — refactor only.

- `OpenMath/ButcherGroup/Section384.lean`: 3408 → **1814 lines**.
- `OpenMath/ButcherGroup/Section384Slices.lean`: **new, 1624 lines**.
- `OpenMath/ButcherGroup.lean`: 1730 → 1731 lines (one new import).
- All three files compile individually with `lake env lean`.
- Full `lake build` is green (8076 / 8076).
- Sorry count across the three touched files: **0**.
- No theorem renamed; every public name moved keeps its full path
  (`ButcherTableau.ButcherProduct.…`), so downstream consumers in
  `OpenMath.ButcherGroup` (the `QuotEquiv.bSeriesHom_product_*` and
  `IsG1Equiv.product_congr_*` families) resolve unchanged.

### Cleavage
The split happens immediately after
`ButcherProduct.bSeries_product_isRKEquivalent_t2` (the last `t₂`-permutation
invariance lemma in the §384 honest convolution layer) and before
`ButcherProduct.bWeighted_convAt_singleton_node_eq` (the first parametric
closed-form `b`-weighted right-block lemma). Every theorem above the
cleavage is core §384 convolution machinery; every theorem below is one of
the cycle 538–549 parametric shape-specific decompositions.

### Theorems moved into Section384Slices.lean
Public:
- `bWeighted_convAt_singleton_node_eq`
- `bWeighted_convAt_kept_leaf_eq`
- `bWeighted_convAt_node_all_leaves_eq`
- `bWeighted_convAt_node_kept_eq`
- `bSeries_natAdd_node_kept_eq`
- `bWeighted_kept_node_all_leaves_summand_eq`
- `bConv_singleton_leaf_eq`, `bSeries_singleton_leaf_eq`
- `bSeries_node_nil_eq`, `bSeries_node_node_nil_eq`
- `bConv_node_replicate_leaf_eq`, `bSeries_node_replicate_leaf_eq`
- `IsConvAtUnit_node_nil`
- `bWeighted_convAt_node_all_node_nil_eq`
- `bConv_node_replicate_node_nil_eq`, `bSeries_node_replicate_node_nil_eq`
- `bSeries_node_leaf_node_nil_eq`, `bSeries_node_node_nil_leaf_eq`,
  `bSeries_node_leaf_leaf_node_nil_eq`
- `bConv_node_trivial_children_eq`, `bSeries_node_trivial_children_eq`
- `bConv_node_replicate_singleton_leaf_eq`,
  `bSeries_node_replicate_singleton_leaf_eq`
- `bConv_node_mixed_leaf_singleton_leaf_eq`,
  `bSeries_node_mixed_leaf_singleton_leaf_eq`

Private support helpers were moved alongside (the
`elementaryWeight_node_replicate_leaf` /
`rightAuxAtCoef_node_nil` / `convAt_singleton_leaf_eq` /
`prod_const_add_eq_powerset` / `mixed_stage_polynomial_expand`
clusters, plus `bWeighted_convAt_node_replicate_singleton_leaf_eq*` and
`weighted_mixed_stage_sum_expand`).

## Dead ends
None — the cleavage was clean. The only minor friction was that `lake env
lean Section384Slices.lean` initially failed on duplicate declarations
because the cached `.olean` for `Section384.lean` still held the pre-split
content. Running `lake build OpenMath.ButcherGroup.Section384` to refresh
the olean fixed it. Recording this so future splits remember to refresh
oleans before checking the new sibling module.

## Discovery
- `lake env lean <file>` typechecks against the cached `.olean` for
  imports; it does **not** rewrite the importing module's olean. After
  any file is restructured, run `lake build <Module>` once before
  invoking `lake env lean` on a sibling that imports it, otherwise the
  importer sees the stale declaration set.
- The §384 file genuinely has two layers. Everything in the parametric
  ladder layer (cycles 538–549) consumes the core layer through
  `bSeries_eq_bConv`, `convAt`, `rightAuxAtCoef`, etc., but the core
  layer never references any parametric closed form. So the split has
  no circular dependency and adding more parametric slices in the
  future should land in `Section384Slices.lean`, keeping the core file
  stable.

## Suggested next approach
The next planner has two unblocked paths:

1. **§387 power arithmetic** on `QuotEquiv.npow` /
   `QuotEquiv.weightsSum_npow_*`. None of these need the §384
   convolution, and they sit in `OpenMath/ButcherGroup.lean` which is
   already at 1731 lines (well below the cap).
2. **Genuine §384 closed `(trunk, cuts)` convolution decomposition** in
   the now-uncluttered `Section384.lean` (1814 lines). This is the
   long-standing blocker for `IsG1Equiv.product_congr` /
   `G1.mul`, recorded in
   `.prover-state/issues/butcher_section384_convolution.md` and
   `.prover-state/issues/butcher_g1_mul_section384_blocker.md`. Cycles
   540–549 worked around it with parametric slices; the actual fix is
   the unrestricted bSeries-only formula, which now has room to grow in
   the core file.

What the next planner should **not** do: add another parametric
shape-specific `bSeries_node_*_eq` slice. The cycle history shows ten
consecutive cycles of that pattern without breaking the convolution
blocker; one more shape will not change that.
