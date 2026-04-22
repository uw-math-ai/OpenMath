# Issue: bridge hypotheses still do not supply a radius-covering zero-set

## Blocker
Cycle 334 narrowed the single live sorry in
`OpenMath/PadeOrderStars.lean` into two theorem-local sorries:

```lean
connectedRadiusPhaseZeroSet_of_bridgeWitnesses
phaseSelection_of_bridgeWitnesses
```

The first theorem is now the honest local continuation seam. The second is only
the selector-packaging step from that connected zero set to a continuous phase
function.

## Context
- `continuousOrderWebPath_of_phaseSelection` is already fully proved.
- `continuousOrderWebPath_of_bridgeWitnesses` now depends only on
  `phaseSelection_of_bridgeWitnesses`.
- The new local helper asks for a connected subset `Z : Set (ℝ × ℝ)` in
  radius-phase coordinates whose `Prod.fst` projection covers all radii in
  `Set.Icc a b`, with zero imaginary part and positive real part throughout.
- Once such a `Z` exists, the remaining gap is to turn it into a continuous
  section `σ : ℝ → ℝ`.

## What was tried
- Triaged the three ready Aristotle bundles from earlier cycles first. All
  three were stale wrapper proofs targeting already-replaced theorem surfaces
  (`referenceWitness_sameComponentContinuation`, `connectedSupport`, and
  `continuousOrderWebPath`) and were rejected.
- Narrowed the live code so the blocker is no longer phrased as an all-at-once
  phase-selection theorem.
- Submitted a fresh Aristotle batch on five cycle-334 surfaces:
  connected zero set, full phase selection, selector from connected zero set,
  and concrete even/odd uniform strip variants.
- The two completed cycle-334 Aristotle outputs were also rejected. They solved
  the goals only by redefining `PadeROrderWebArcPhaseBridgeNearOrigin` to
  already contain the target conclusion, so they are not transplantable to the
  live file.
- A quick local Mathlib search found image/projection lemmas for connected sets
  but no ready-made theorem giving a continuous section from a connected subset
  of a rectangle with interval projection.

## Why the previous theorem shape was still too coarse
- The generic bridge hypothesis

```lean
PadeROrderWebArcPhaseBridgeNearOrigin n d θ
```

still only gives `∀ radius > 0, ∃ t ∈ Ioo 0 radius, ...`.
- That is enough to produce one witness in each small cone, but not enough to
  cover every radius in a compact interval `[a,b]`.
- Therefore the new helper

```lean
connectedRadiusPhaseZeroSet_of_bridgeWitnesses
```

is exactly where the real mismatch sits: it asks for a radius-covering connected
zero set, while the current bridge API only produces isolated radius witnesses.
- Even if the connected zero set were available, a second nontrivial step
  remains: extract a continuous selector `σ` from it. No existing theorem for
  this was found in the current local search.

## Exact local obstruction
The live helper now asks for:

```lean
∃ a b η s0 s1 : ℝ, ∃ Z : Set (ℝ × ℝ),
  a ≤ b ∧
  0 < η ∧
  s0 ∈ Set.Icc (-η) η ∧
  s1 ∈ Set.Icc (-η) η ∧
  z0 = ((↑a : ℂ) * exp (↑(θ + s0) * I)) ∧
  z = ((↑b : ℂ) * exp (↑(θ + s1) * I)) ∧
  IsConnected Z ∧
  Z ⊆ {p : ℝ × ℝ | ... zero-imaginary and positive-real conditions ...} ∧
  (a, s0) ∈ Z ∧
  (b, s1) ∈ Z ∧
  Set.Icc a b ⊆ Prod.fst '' Z
```

The missing bridge-to-zero-set upgrade is now explicit.

## Possible solutions
- Strengthen the generic bridge API to a uniform strip statement:
  for all sufficiently small radii `r`, the whole short arc at radius `r` has
  positive real part and opposite imaginary signs at its endpoints.
- Bypass the generic bridge theorem and prove the connected-zero-set helper
  directly from the concrete even/odd sign-control proofs, which appear capable
  of yielding such a uniform strip.
- After a connected zero set is obtained, prove a local theorem turning a
  connected subset of `ℝ × ℝ` with full `Prod.fst` projection into a continuous
  section over `Set.Icc a b`.
