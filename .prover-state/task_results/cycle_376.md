# Cycle 376 Results

## Worked on
- §3.5.10 / Theorem 359D packaging corollaries: family-level BN-stability for
  collocation methods, in `OpenMath/CollocationFamilies.lean`.
- Aristotle bundle triage from cycle 375 (no incorporation needed; all five
  bundles dispositioned per cycle-375 strategy note).

## Approach
Step 1 (target identification): grepped the repo (`OpenMath/`,
`.prover-state/`, `plan.md`) for `359D`, `3.5.10`, `360A`, `Theorem 360`. No
in-flight reference to a concrete 359D statement exists — only the
strategy/plan placeholders.

Step 2 (decision): Per the planner's "Fallback if 359D / §3.5.10 cannot be
pinned down" branch, the textbook reference is not in hand, so I added the
clean abstract Padé-via-collocation BN-stability corollaries: package
`thm_359C_gaussLegendre`, `thm_359C_radauI`, and `thm_359B_radauIIA` with
`alg_stable_implies_bn_stable` (Theorem 357C) into single concrete
implications.

Step 3 (Aristotle): No new Aristotle batch this cycle. The five cycle-375
bundles were already dispositioned (counterexample or already-live node
certificates). Per planner: "do not submit a new Aristotle batch on cycle-375
targets". The 359D fallback corollaries are one-liners (`alg_stable_implies_bn_stable
(thm_359X t hcoll hNodes)`) and do not benefit from Aristotle.

Step 4 (writing): Added six theorems to `OpenMath/CollocationFamilies.lean`
(after the existing Radau IA node certificates), and added
`import OpenMath.BNStability` to make `IsBNStable` and
`alg_stable_implies_bn_stable` available.

## Result
SUCCESS.

New family-level BN-stability theorems:
- `thm_359C_gaussLegendre_bnStable`:
  `IsCollocation ∧ HasGaussLegendreNodes → IsBNStable`
- `thm_359B_radauIIA_bnStable`:
  `IsCollocation ∧ HasRadauIIANodes → IsBNStable`
- `thm_359C_radauI_bnStable`:
  `IsCollocation ∧ (∀ i, eval (c i) (algStabilityBoundaryPoly s 1) = 0) → IsBNStable`

New concrete-tableau BN-stability corollaries (separate from the existing
`CollocationBN.lean` direct-358A-bypass versions; these go through
358A → 357C):
- `rkGaussLegendre2_bnStable_via_358A`
- `rkGaussLegendre3_bnStable_via_358A`
- `rkRadauIIA3_bnStable_via_358A`

All proofs are one-liners composing two already-formalized theorems.

Build verification:
- `lake env lean OpenMath/CollocationFamilies.lean` — clean (no errors, no
  warnings).
- `lake build OpenMath.CollocationFamilies` — green (8039 jobs, only pre-
  existing linter warnings in unrelated files).

## Dead ends
None this cycle. The fallback was a near-trivial composition.

## Discovery
- The 359C/359B → 357C composition is a single `alg_stable_implies_bn_stable
  (thm_359X t hcoll hNodes)` term-level proof. Worth noting that
  `CollocationFamilies.lean` previously did not import `BNStability`; it
  does now, but the import is cheap (no new mathlib dependency).
- `OpenMath/CollocationBN.lean` already had concrete BN-stability for
  `rkGaussLegendre2/3`, `rkRadauIA2/3`, `rkRadauIIA3`, but those go
  `IsAlgStable → IsBNStable` directly using the file-local
  `*_algStable` proofs (not via 358A). The new `*_via_358A` corollaries are
  the §3.5.10-packaging route that fits the strategy.
- No `HasRadauIANodes` BN-stability variant was added, since the family
  bridge for that node predicate is false (cycle 375 counterexample).

## Suggested next approach
1. **Pin down the real Theorem 359D text.** The next planner cycle should
   open Iserles §3.5.10 in PDF form (or via library access) and record the
   exact statement of Theorem 359D so the placeholder in `plan.md` can be
   replaced with a concrete formal target. Likely candidates per cycle 376
   strategy:
   (a) A characterization corollary of 358A that partitions into GL / Radau
       IIA / Radau IA families (option (a) in the strategy);
   (b) A statement about A-stability of the methods produced by 358A,
       requiring the Padé/E-function machinery from `AStabilityCriterion.lean`
       and `Pade.lean`.
2. If 359D remains unpinned, move to Chapter 4 BDF downstream targets per
   the plan's "otherwise" branch.
3. The Aristotle results directory has accumulated cycles of stub bundles;
   consider an `aristotle_results/INDEX.md` cleanup pass at some point so
   stale bundles do not get re-incorporated by mistake.

## Aristotle jobs this cycle
None. (Per the strategy's explicit instruction: "Do not submit a new
Aristotle batch on cycle-375 targets," and the cycle-376 fallback is too
trivial to need Aristotle compute.)
