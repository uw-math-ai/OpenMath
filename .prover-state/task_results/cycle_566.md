# Cycle 566 Results

## Worked on
File-size split of `OpenMath/ButcherGroup.lean` (3206 lines → 2721 lines).
Extracted the 21 `QuotEquiv.bSeriesHom_product_*` slice theorems into a
new module `OpenMath/ButcherGroup/QuotEquivSlices.lean`.

## Approach
Followed the planner's mechanical extraction procedure:

1. Identified the 21 `bSeriesHom_product_*` theorem bodies in
   `ButcherGroup.lean` (theorem 1 spanning lines 100–114, theorems
   2–21 spanning lines 123–586 inclusive — total 479 verbatim lines).
2. Wrote `OpenMath/ButcherGroup/QuotEquivSlices.lean` with the
   strategy-prescribed header and imports, then pasted the 21 theorems
   verbatim inside `namespace ButcherTableau / namespace QuotEquiv`.
3. Removed those same line ranges from `ButcherGroup.lean`.
4. Added `import OpenMath.ButcherGroup.QuotEquivSlices` to the main
   file's import block.
5. Cleaned up double blank lines at the two cut seams (no semantic
   changes).
6. Built the slice file, the umbrella file, and the full project.

## Result
SUCCESS.

- `OpenMath/ButcherGroup/QuotEquivSlices.lean` builds clean.
- `OpenMath/ButcherGroup.lean` builds clean (now 2721 lines, well under
  3000).
- `lake build` is fully green (8083 jobs, no errors).
- No theorem statement, proof, or public name was modified — pure
  relocation.

Final line counts:
- `OpenMath/ButcherGroup.lean`: 3206 → **2721** lines.
- `OpenMath/ButcherGroup/QuotEquivSlices.lean`: **513** lines (in the
  480–540 target band).

## Surprises during the cut/paste

**One hidden import dependency the strategy missed**: the 21
`bSeriesHom_product_*` theorems all reference the `bSeriesHom`
*definition* (the `noncomputable def bSeriesHom` itself, originally at
lines 84–86 of the source file), not just the `bSeriesHom_one` /
`_assoc` / `_leaf` lemmas around it. The strategy's "Keep in
`ButcherGroup.lean`" list mentions the `bSeriesHom` "definition
surface" only via the lemmas, with no explicit instruction about the
def itself. If the def stayed in `ButcherGroup.lean`, the new slice
file would have a circular reference (slice file references
`bSeriesHom`, but `bSeriesHom` lives in the umbrella file that imports
the slice file).

**Resolution** — moved the 4-line `def bSeriesHom` (with its 2-line
docstring) from `ButcherGroup.lean` into
`OpenMath/ButcherGroup/QuotEquivSlices.lean`, placed immediately after
`namespace QuotEquiv` and before the 21 slices. This is the minimal
deviation from the strategy needed to make the slice file compile.

The follow-on lemmas `bSeriesHom_one`, `bSeriesHom_assoc`,
`bSeriesHom_leaf` (which the strategy explicitly named as "stay in
main file") remain in `ButcherGroup.lean` unchanged — they pick up
the moved `bSeriesHom` def transitively through the new import. All
downstream `IsG1Equiv.product_congr_*` slices in the umbrella file
also resolve `bSeriesHom_product_*` references through the new
import without any rename, exactly as the strategy predicted.

## Dead ends
None. First build attempt failed with the missing-`bSeriesHom`
errors described above; second attempt (after moving the def) built
clean.

## Discovery
The "definition surface" of `QuotEquiv.bSeriesHom` and the 21
slice-lift theorems form a tight unit: the slices unfold `bSeriesHom`
inside their `simpa` calls, so they cannot be cleanly separated from
the def. Future splits in this area should treat the def together
with its slice lifts as a single extraction target.

The bigger remaining block — `IsG1Equiv.product_congr_*` slices
(≈ 1730 lines, lines 1234–3010 of the original file) — does NOT have
this entanglement with `IsG1Equiv` itself, but it does require
careful ordering with `IsRKEquivalentExt.toG1Equiv`. That is the
natural next split target once the §384 honest convolution closure
unblocks.

## Suggested next approach
- Land the optional bonus `IsG1Equiv` slice on
  `BTree.node (List.replicate n (BTree.node [BTree.node []]))` *only*
  if the planner explicitly schedules it. **Not done this cycle** —
  the split itself was the priority and is settled.
- For cycle 567, the planner can either:
  (a) take the next file-size slice cap by extracting the
      `IsG1Equiv.product_congr_*` block (≈ 1730 lines) into a sibling
      module `OpenMath/ButcherGroup/IsG1EquivSlices.lean`, OR
  (b) push on the §384 honest convolution closure
      (`butcher_section384_convolution.md`) so the unrestricted
      `IsG1Equiv.product_congr` becomes reachable.

## Commit
`Cycle 566: split QuotEquivSlices out of ButcherGroup.lean`
