import OpenMath.ButcherGroup.Section384SlicesMixed.Common
import OpenMath.ButcherGroup.Section384SlicesMixed.LeafFamilies
import OpenMath.ButcherGroup.Section384SlicesMixed.Mixed3Way
import OpenMath.ButcherGroup.Section384SlicesMixed.Replicate

/-! # §384 mixed slices (cycle 564 split umbrella)

Cycle 564 split the previous monolithic `Section384SlicesMixed.lean`
(3389 lines) into cohesive family submodules under
`OpenMath/ButcherGroup/Section384SlicesMixed/`. This file is the thin
re-export umbrella; downstream consumers can keep importing
`OpenMath.ButcherGroup.Section384SlicesMixed` and the public
deliverables resolve under their existing fully-qualified names.

Submodule layout:

* `Common.lean` — foundational `elementaryWeight` / `bSeries`
  closed-form helpers for replicated-child root families, plus the
  powerset-binomial helpers `prod_const_add_eq_powerset` /
  `pow_add_eq_powerset`.
* `LeafFamilies.lean` — mixed leaf + singleton-leaf (cycles 543–549)
  and mixed leaf + double-leaf (cycles 552–553) `IsG1Equiv` slices,
  plus the `doubleLeafChoiceCount` / `doubleLeafChoiceTree` /
  `doubleLeafChoiceCoef` machinery.
* `Mixed3Way.lean` — mixed singleton-leaf + double-leaf (cycle 554)
  and three-way leaf + singleton-leaf + double-leaf (cycle 556)
  `IsG1Equiv` slices.
* `Replicate.lean` — standalone triple-leaf single tree (cycle 557),
  parametric all-double-leaf (cycle 562), parametric all-triple-leaf
  (cycle 563), plus the `tripleLeafChoiceCount` /
  `tripleLeafChoiceCoef` / `tripleLeafRootChoiceCount` /
  `tripleLeafChoiceFunctionCoef` / `tripleLeafChoiceTree` machinery.
-/
