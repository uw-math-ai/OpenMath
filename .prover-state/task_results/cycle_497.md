# Cycle 497 Results

## Worked on
Butcher §38 / §383 prep in `OpenMath/ButcherGroup.lean`: invariance of
elementary weights and rooted-tree order conditions under `IsRKEquivalent`.

## Approach
Added `OpenMath.OrderConditions` to the imports and first landed the three
required sorry-first statements:

- `IsRKEquivalent.elementaryWeight_eq`
- `IsRKEquivalent.satisfiesTreeCondition_iff`
- `IsRKEquivalent.hasTreeOrder_iff`

Submitted five Aristotle jobs after the scaffold compiled:

- `b795a33e-f50c-4e3a-a030-c3722fd9924b`: `elementaryWeight_eq`, still
  `IN_PROGRESS` at the one post-sleep check.
- `38de27bc-f90a-4999-8b59-278d6c9f1431`: `satisfiesTreeCondition_iff`,
  `COMPLETE_WITH_ERRORS`; proof sketch was useful but not directly robust.
- `44aca302-c997-4494-abca-70847875bdff`: `hasTreeOrder_iff`,
  `COMPLETE_WITH_ERRORS`; the final `forall_congr'` proof was usable.
- `e50357d6-9012-4b68-89c2-e44cf9a77daf`: list-helper variant for
  `elementaryWeight_eq`, still `IN_PROGRESS` at the one post-sleep check.
- `43c8c3a0-cae0-477a-8ad7-62cacd5056e4`: all three lemmas,
  `COMPLETE_WITH_ERRORS`; skipped because it replaced the live API with a
  fictional `BTree` / `ButcherTableau` development.

Also inspected the two ready previous bundles:

- `77604942-404a-478b-9164-a27695a8abf3`: Grothendieck/flasque-sheaf
  material, off-target for §38, skipped.
- `8700ceb0-5cb6-422e-940d-8519c9d17134`: redefined `RKMethod` and
  `IsRKEquivalent` around equality of elementary weights, not the live
  stage-relabeling API, skipped.

## Result
SUCCESS. Landed all three requested deliverables, plus the optional
`IsRKEquivalent.c_sum_eq` sanity lemma.

`elementaryWeight_eq` uses the nested `BTree.rec` recursor with a
`motive_2` over `List BTree`, so the node case reduces to a foldr equality
over the child list. The summand equality is proved by rewriting `A` with
`hA`, applying the tree induction hypothesis at each stage, and reindexing
the finite sum with `Equiv.sum_comp`.

`satisfiesTreeCondition_iff` reindexes the weighted elementary-weight sum
with the equivalence witness, and `hasTreeOrder_iff` lifts that result
through the universal quantifier in `hasTreeOrder`.

## Dead ends
The generated all-in-one Aristotle bundle for `43c8c3a0...` used a different
two-constructor `BTree` and rational-valued tableau API, so it could not be
transplanted. The `satisfiesTreeCondition_iff` bundle assumed too much of
the rewrite shape and was used only as a high-level guide.

## Discovery
For live `BTree`, ordinary `induction τ` is unavailable because `BTree` is
a nested inductive through `List BTree`. The reliable pattern is:

- use `BTree.rec` explicitly,
- set `motive_1` to the tree-level elementary-weight equality,
- set `motive_2` to the corresponding `List.foldr` equality,
- close the `cons` case with one `Equiv.sum_comp` reindexing step.

No heartbeat increase was needed.

## Suggested next approach
Cycle 498 should either define the quotient-facing elementary-weight map
using the new invariance lemmas, or first write the issue/planning note for
the cross-stage-count embedding needed before reopening the full
`ButcherProduct` monoid/group operation. A small fallback target is §387's
single-stage-count trivial-tableau identity layer.
