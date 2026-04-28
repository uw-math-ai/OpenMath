# Cycle 535 Results

## Worked on

Split `OpenMath/ButcherGroup.lean` after it crossed the 3000-line cap.

## Approach

Moved the declarations mechanically along the planner boundaries:

- `OpenMath/ButcherGroup/Core.lean`: relabel layer, raw `ButcherProduct`,
  quotient product, partial associativity, and §384 identity-prep material.
- `OpenMath/ButcherGroup/Section384.lean`: representative `bSeries` and the
  full §384 right-block convolution chain through
  `ButcherProduct.bSeries_natAdd_eq_convAt`.
- `OpenMath/ButcherGroup.lean`: umbrella imports plus the post-§384
  `QuotEquiv` lifts, §387 power chain, `IsRKEquivalentExt`, `IsG1Equiv`,
  and `G1`.

No theorem bodies were rewritten during the move.

## Result

SUCCESS.

Line counts after the split:

- `OpenMath/ButcherGroup/Core.lean`: 760 lines.
- `OpenMath/ButcherGroup/Section384.lean`: 1515 lines.
- `OpenMath/ButcherGroup.lean`: 926 lines.

Declaration-count audit:

- Pre-split `OpenMath/ButcherGroup.lean`: 205 declarations.
- Post-split total: 205 declarations (`47 + 48 + 110`).

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Core.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Section384.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build`
- `rg -n "sorry" OpenMath/ButcherGroup.lean OpenMath/ButcherGroup/` reported no matches.

The dependent direct `lake env lean` checks required first materializing the
new import artifacts with `lake build OpenMath.ButcherGroup.Core` and
`lake build OpenMath.ButcherGroup.Section384`; after that, all requested Lean
checks succeeded.

## Dead ends

None. The split revealed no forward-reference dependency from the §382 core
into the §384 block.

## Aristotle

No Aristotle jobs were submitted. The cycle strategy explicitly said not to
route this module-level reorganization through Aristotle, because there were
no new proof obligations or `sorry` placeholders to solve.

## Discovery

Lean accepts `OpenMath/ButcherGroup.lean` as the umbrella module while also
using the sibling directory `OpenMath/ButcherGroup/` for submodules
`Core` and `Section384`.

## Suggested next approach

Return to the §384 convolution / `IsG1Equiv.product_congr` seam recorded in
`.prover-state/issues/butcher_section384_convolution.md` and
`.prover-state/issues/butcher_g1_mul_section384_blocker.md`. The file-size
blocker is now removed.
