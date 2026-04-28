# Cycle 534 Results

## Worked on

§384 BTree-recursive `convAt` closed form (planner-assigned pivot away
from the depth ladder of cycles 528-533).

Per strategy, added to `OpenMath/ButcherGroup.lean`:

1. `noncomputable def ButcherProduct.convAt` — closed-form recursive
   auxiliary mirroring `rightAuxAtCoef` but with `S` indexing the cut
   children and `Sᶜ` the kept children (the swap of
   `rightAuxAtCoef`'s `S = keep / Sᶜ = cut` convention).
2. `@[simp] theorem ButcherProduct.convAt_leaf`.
3. `theorem ButcherProduct.convAt_node`.
4. `theorem ButcherProduct.rightAuxAtCoef_eq_convAt` — single-step
   depth-ladder collapse via `BTree.rec` with `motive_2` over
   `List BTree`, plus complement-bijection swap on `Finset` indexing.
5. `theorem ButcherProduct.bWeighted_rightAuxAtCoef_eq_convAt_sum` —
   `b`-weighted form, one-line consequence.
6. `theorem ButcherProduct.bSeries_natAdd_eq_convAt` — bSeries-form
   corollary specialising at `coef := t₁.bSeries`.

## Approach

Followed the strategy verbatim:

- Definition uses `termination_by τ => sizeOf τ` and the same
  `decreasing_by` body that already worked for `rightAuxAtCoef` near
  line 1314 of the file (proves `sizeOf (children.get p) < sizeOf
  (BTree.node children)` via `List.sizeOf_lt_of_mem` plus
  `Nat.lt_trans`).
- For `rightAuxAtCoef_eq_convAt` the `BTree.rec` was set up with
  `motive_2 := fun children => ∀ c ∈ children, ∀ j, ...` exactly as in
  cycle 524's `rightAuxAt_eq_rightAuxAtCoef_bSeries` (lines 1633-1666
  of the existing file). Node case rewrites LHS via
  `rightAuxAtCoef_node_eq_powerset_sum` (cycle 526) and RHS via
  `convAt_node`, then bridges them by
    (a) per-child IH lifted under `Finset.prod_congr` /
        `Finset.sum_congr`, and
    (b) a complement bijection
        `complPerm : Equiv.Perm (Finset (Fin children.length))`,
        `S ↦ Sᶜ`, used through `Equiv.sum_comp` to swap the index from
        the `(∏ Sᶜ coef) * (∏ S keep)` form into the
        `(∏ S coef) * (∏ Sᶜ keep)` form. This is the same
        `complPerm` pattern already deployed inside
        `rightAuxAt_node_eq_powerset_sum` (lines ~1119-1138).
- The two consequences are immediate one-liners:
  `bWeighted_rightAuxAtCoef_eq_convAt_sum` is `Finset.sum_congr` plus
  `rightAuxAtCoef_eq_convAt`, and `bSeries_natAdd_eq_convAt` is
  `bSeries_natAdd_eq_rightAuxAtCoef` then
  `bWeighted_rightAuxAtCoef_eq_convAt_sum`.

## Result

**SUCCESS.** The full block compiled with zero sorries on the first
`lake env lean OpenMath/ButcherGroup.lean` run. No Aristotle batch was
required — the entire scaffold (def + 5 theorems) closed manually using
the templates already present in the file (cycle 524's `BTree.rec` with
`motive_2`, cycle 526's `rightAuxAtCoef_node_eq_powerset_sum`, and the
complement-permutation argument from
`rightAuxAt_node_eq_powerset_sum`).

File size: `OpenMath/ButcherGroup.lean` went from 2999 → 3150 lines
(+151). Strategy noted that crossing 3000 was acceptable for this
cycle and that the next cycle's first job is a §384 split if the file
is over 3000. That trigger has now fired — the next planner cycle
should schedule extracting the §384 right-block material into
`OpenMath/ButcherGroup/Section384.lean`.

## Dead ends

None this cycle. The proof structure laid out in the strategy was
correct on the first attempt.

## Discovery

- The complement-permutation `complPerm := { toFun := (·ᶜ); invFun :=
  (·ᶜ); left_inv/right_inv := fun S => by ext p; simp }` together with
  `Equiv.sum_comp complPerm` is now confirmed twice in this file
  (cycle 521 in `rightAuxAt_node_eq_powerset_sum`, cycle 534 here).
  This is the canonical move when the same powerset sum needs to be
  re-indexed by the complement.
- The `BTree.rec` with `motive_2 := fun children => ∀ c ∈ children,
  ∀ j, ...` shape and `List.mem_cons.mp` discharge in the cons branch
  is the load-bearing pattern for any double-recursive `BTree`
  identity. This makes cycle 524 / cycle 534 a reusable template for
  any future `Property(τ, i)` lemma where the per-child IH must reach
  inside an inner `Finset` operation.
- Aristotle was not needed this cycle. When the proof template is
  already in the file from a previous cycle, pattern-copying it is
  faster than the 30-minute Aristotle round-trip and consumes no
  external compute.

## Suggested next approach

The depth ladder is now fully collapsed. The §384 convolution gap
remains — what is still missing is the `(trunk, cuts)` closed form
that depends only on `t₁.bSeries`, not on the product tableau. The
right next move is one of:

1. **§384 split.** `OpenMath/ButcherGroup.lean` is now 3150 lines.
   Strategy preconditioned the next cycle on extracting the §384
   right-block material (everything from `rightAuxAt` through the new
   `convAt` block — roughly lines 989 through 2249 of the current
   file) into `OpenMath/ButcherGroup/Section384.lean`. The split is
   mechanical: introduce the new file, move the declarations, add an
   `import OpenMath.ButcherGroup.Section384` (or move the supporting
   imports into the new file directly), and verify
   `OpenMath/ButcherGroup.lean` and the new file both compile. No new
   theorems would land that cycle but the modular foundation is the
   right setup for the convolution work.

2. **bSeries-only convolution definition + assess
   `IsG1Equiv.product_congr`.** Define
   `ButcherProduct.bSeriesConvAt {t} (q₁ : QuotEquiv s) (coef : BTree
   → ℝ) : BTree → Fin t → ℝ` (or the analogous quotient-friendly
   shape) so that
   `(ButcherProduct t₁ t₂).bSeries τ = bSeriesConvAt q₁.bSeriesHom
   ... τ` and check whether the right-hand side depends on `t₁` only
   through `q₁.bSeriesHom`. If yes, `IsG1Equiv.product_congr` falls
   out by replacing the left factor with any `IsG1Equiv`-equivalent
   `q₁'`; if no (which the cycle 512 attempt suggests), record the
   precise dependency that survives in
   `butcher_g1_mul_section384_blocker.md` and look for a different
   bridge. Cycle 512's tautological `bSeriesConvolution` failed
   precisely because it routed through the product tableau itself; the
   right definition must consume only `q₁.bSeriesHom` values on
   subtrees, which is exactly what `convAt` exposes via its `coef`
   slot.

3. **§387 backup arithmetic seam.** If the convolution work stalls,
   `QuotEquiv.weightsSum_npow_five` / `cSum_npow_five` /
   `weightsSum_npow_six` / `cSum_npow_six` are routine
   instantiations of `weightsSum_npow` / `cSum_npow` at `n = 5, 6`
   followed by `push_cast` + `linarith` / `nlinarith`. Cycle 513
   landed `n = 4` via that template.

The natural pick for cycle 535 is #1 (the file split) — the strategy
already specified it as the next-cycle job once the file crossed 3000
lines, and it cleanly sets up cycle 536 to attempt #2.
