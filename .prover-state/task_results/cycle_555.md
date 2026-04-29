# Cycle 555 Results

## Worked on
Split `OpenMath/ButcherGroup/Section384Slices.lean` into uniform-shape and mixed-root §384 slice modules.

## Approach
Moved the mixed leaf/singleton-leaf, mixed leaf/double-leaf, and mixed singleton-leaf/double-leaf families into `OpenMath/ButcherGroup/Section384SlicesMixed.lean`. Also moved the double-leaf-only private helper block that feeds those mixed families.

Because Lean `private` declarations do not cross module boundaries, the new mixed module locally duplicates the small upstream private helper facts needed by the moved proofs: the leaf/singleton `convAt` and elementary-weight/bSeries collapses. Public theorem names and the `ButcherTableau` namespace were preserved.

Updated `OpenMath/ButcherGroup.lean` to import `OpenMath.ButcherGroup.Section384SlicesMixed` after `Section384Slices`.

## Result
SUCCESS.

Line counts:
- Before: `OpenMath/ButcherGroup/Section384Slices.lean` was 3061 lines.
- After: `OpenMath/ButcherGroup/Section384Slices.lean` is 1166 lines.
- New: `OpenMath/ButcherGroup/Section384SlicesMixed.lean` is 1996 lines.

Verification:
- `lake env lean OpenMath/ButcherGroup/Section384Slices.lean` succeeded.
- `lake build OpenMath.ButcherGroup.Section384Slices` succeeded to refresh the split dependency olean.
- `lake env lean OpenMath/ButcherGroup/Section384SlicesMixed.lean` succeeded.
- `lake build OpenMath.ButcherGroup.Section384SlicesMixed` succeeded.
- `lake env lean OpenMath/ButcherGroup.lean` succeeded.
- `lake build` succeeded.
- `grep -rn "^\\s*sorry\\b\\|:= sorry\\b" OpenMath/` returned no matches.

Aristotle was intentionally skipped per the cycle strategy because this was a pure refactor with no new proof obligations, and recent cycles were immediately rate-limited.

## Dead ends
The first direct `lake env lean OpenMath/ButcherGroup/Section384SlicesMixed.lean` check saw duplicate public declarations because it imported the stale pre-split `Section384Slices.olean`. Rebuilding `OpenMath.ButcherGroup.Section384Slices` refreshed the dependency artifact and resolved the issue.

## Discovery
The mixed-root proofs depended on several private uniform-block helpers, so a literal tail cut at the mixed section boundary was not sufficient. Local duplication of the small private helper lemmas kept cross-module dependencies pointing only upstream while preserving public theorem names.

## Suggested next approach
Cycle 556 can resume adding the next §384 parametric slice on top of the post-split mixed module. Keep `Section384SlicesMixed.lean` near the cap in mind if the next slice is large; further subdivision by mixed family may be needed soon.
