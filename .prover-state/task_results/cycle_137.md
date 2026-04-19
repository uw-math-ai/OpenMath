# Cycle 137 Results

## Worked on
- `OpenMath/OrderStars.lean`: replaced the vacuous `IsAStablePadeApprox.aStable : True` placeholder with a non-vacuous imaginary-axis exclusion interface.
- `OpenMath/RootedTree.lean`: added unordered-child infrastructure (`childrenBag`) and permutation-invariance lemmas for `order` and `density`.
- Aristotle resubmission for the two remaining `OrderStars` blockers:
  `a12092b0-cb1a-41fb-baf2-dc23b1c0658d` (`thm_355D`)
  `ee4004c9-8fe9-49ab-94ca-b970f693ce59` (`ehle_barrier`)

## Approach
- Read the existing Aristotle outputs for cycles 135-136 before making new edits.
- Kept the two documented topology-blocked theorem sorrys in place rather than importing the previous circular or false “solutions”.
- Reworked `IsAStablePadeApprox` so it now records the concrete 355F-style consequence “no `𝒜⁺` points on the imaginary axis” as data, without baking in the Ehle conclusion.
- Started the rooted-tree child-model upgrade conservatively by adding an unordered multiset view of children while preserving the current `List` representation used by recursive definitions.
- Added permutation-invariance lemmas to show `order` and `density` already factor through child multiplicities, which is the key first step toward a full `Multiset` child model.
- Submitted focused Aristotle files for the two remaining `OrderStars` blockers and started the required 30-minute backoff.

## Result
- SUCCESS: cycle housekeeping completed (`.prover-state/cycle = 137`, history entry appended).
- SUCCESS: the `A-stable` interface in `OrderStars` is no longer mathematically vacuous.
- SUCCESS: `RootedTree` now has explicit unordered-child API and new permutation-invariance lemmas.
- PARTIAL: project sorry count remains `2`; neither topology blocker was closed this cycle.
- PARTIAL: local `lake build` verification was blocked by a corrupted temporary build cache under `/tmp/OpenMath-lake` (`*.setup.json` truncated while rebuilding mathlib), so I could not finish an end-to-end compile confirmation in this turn.
- PENDING: Aristotle jobs `a12092b0-...` and `ee4004c9-...` were queued/submitted; results were not yet incorporated in this turn.

## Dead ends
- The previous Aristotle “proof” for `ehle_barrier` was still circular: it solved the theorem only by storing the conclusion directly in the structure.
- The previous Aristotle analysis for `thm_355D` remained valid after re-reading: the numerical interface alone cannot prove the arrow-count inequality without the missing global trajectory theorem.
- A direct replacement of `aStable : True` by inequalities such as `n ≤ d` or `d ≤ n + 2` would have been circular and was rejected.

## Discovery
- The cleanest honest strengthening for `IsAStablePadeApprox` at the current abstraction level is to package the 355F consequence “imaginary axis avoids `𝒜⁺`”, not the full analytic stability function and not the Ehle wedge inequalities themselves.
- `RootedTree.order` can be made permutation-invariant via `List.Perm.foldr_eq`, and `density` via `List.Perm.prod_eq`; this supports a staged migration to an unordered child model without rewriting the recursive definitions immediately.
- The current build obstacle is environmental rather than theorem-specific: `lake` is rebuilding through `/tmp/OpenMath-lake`, and some generated mathlib setup files are truncated/corrupt.

## Suggested next approach
- After the 30-minute Aristotle window, check projects `a12092b0-...` and `ee4004c9-...` exactly once and incorporate any non-circular countermodels or proof fragments.
- If Aristotle again confirms unprovability, keep both sorrys as the explicit topology boundary and continue the `RootedTree` migration by extending the multiset-facing API to `symmetry`/tree isomorphism infrastructure.
- Repair or clean the temporary `/tmp/OpenMath-lake` build cache before the next cycle so touched-file verification can run normally.
