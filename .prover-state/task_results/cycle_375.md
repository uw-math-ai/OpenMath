# Cycle 375 Results

## Worked on

Theorem 359B Radau IA side in `OpenMath/CollocationFamilies.lean`.

## Approach

I first added the Radau IA node predicate
`HasRadauIANodes`, defined as zeros of `algStabilityBoundaryPoly s (-1)`.
I then set up the concrete `rkRadauIA2` and `rkRadauIA3` node certificates
sorry-first and submitted focused Aristotle jobs after the skeleton compiled.

Aristotle jobs submitted:

- `0d8aad62-d194-4f03-a246-a9725194c977`: `rkRadauIA2` node proof; still
  `IN_PROGRESS` at the required single post-sleep check.
- `afcdef2a-f7da-4d68-88a4-b6415b807532`: `rkRadauIA3` node proof; still
  `IN_PROGRESS` at the required single post-sleep check.
- `ea5b7077-3181-49d1-abcc-ae4624194204`: 2-stage left-Radau collocation
  counterexample `IsCollocation`; `COMPLETE_WITH_ERRORS`.
- `fa9060f2-04a6-4f29-b226-bbea20688548`: 2-stage left-Radau collocation
  counterexample node proof; still `IN_PROGRESS` at the required single
  post-sleep check.
- `8319367b-1c25-4b6f-9b1a-2108c42ced9f`: 2-stage left-Radau collocation
  counterexample not algebraically stable; `COMPLETE_WITH_ERRORS`.

Because no usable Aristotle proof bundle was available at that check, I closed
the two live node proofs manually with direct polynomial simplification and
`nlinarith`.

## Result

PARTIAL SUCCESS.

Added and proved:

- `ButcherTableau.HasRadauIANodes`
- `ButcherTableau.rkRadauIA2_hasRadauIANodes`
- `ButcherTableau.rkRadauIA3_hasRadauIANodes`

The requested family theorem
`IsCollocation ∧ HasRadauIANodes → IsAlgStable` was not added. It is false
under the live `IsCollocation` definition.

## Dead ends

The adjoint/reflection route is not merely missing a helper lemma. The live
`IsCollocation` predicate means `C(s)`, while the concrete Radau IA tableaux in
the project satisfy the Radau IA simplifying-assumption pattern (`C(s-1)` and
`D(s)`), not `C(s)`.

The genuine 2-stage collocation tableau on left-Radau nodes `{0, 2/3}` has
`A = [[0, 0], [1/3, 1/3]]`, `b = [1/4, 3/4]`, and `c = [0, 2/3]`. It satisfies
`IsCollocation` and `HasRadauIANodes`, but `M₀₀ = -1/16`, so it is not
algebraically stable.

## Discovery

`OpenMath/ReflectedMethods.lean` already has strong transfer lemmas for
`reflect` preserving `B`, `C`, `D`, and `E`. However, this reflection has
`M(reflect t) = -M(t)` at the algebraic-stability matrix level, so it is not
an algebraic-stability-preserving bridge.

The existing Radau IA methods are algebraically stable, but their family-level
theorem needs to be stated using Radau IA simplifying assumptions rather than
the collocation theorem 358A interface.

## Suggested next approach

Move to Theorem 359D / §3.5.10 corollaries, or begin the Chapter 4 BDF
downstream target.

If the Radau IA family is revisited, formulate it as a theorem over the Radau
IA simplifying assumptions (`B(2s-1)`, `C(s-1)`, `D(s)`) or a concrete Radau IA
tableau construction, not arbitrary `IsCollocation` methods with left-Radau
nodes. See `.prover-state/issues/cycle_375_radauIA_collocation_counterexample.md`.
