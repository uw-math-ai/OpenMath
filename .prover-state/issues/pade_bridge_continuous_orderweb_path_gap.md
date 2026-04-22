# Issue: `continuousOrderWebPath_of_bridgeWitnesses` still lacks a radius-selection theorem

## Blocker
Cycle 332 replaced the old support-only sorry with the narrower local helper

```lean
continuousOrderWebPath_of_bridgeWitnesses
```

inside `padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge` in
`OpenMath/PadeOrderStars.lean`.

Its statement is now:

```lean
∃ γ : ℝ → ℂ,
  ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
  γ 0 = z0 ∧
  γ 1 = z ∧
  ∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ orderWeb (padeR n d)
```

So the blocker is no longer “find a connected subset somehow”; that part is
already proved from the path image. The exact missing ingredient is now a
continuous order-web path between the two fixed bridge witnesses.

## Context
- `z0` is a fixed order-web witness in `rayConeNearOrigin θ 1 1`.
- `z` is a fixed order-web witness in `rayConeNearOrigin θ aperture radius`.
- The outer bridge data still gives only this pointwise information:
  - for each chosen radius, there is a short exact-angle arc,
  - the real part of `padeR n d w * exp (-w)` stays positive on that arc,
  - the imaginary part has opposite signs at the two endpoints,
  - IVT yields one zero on that arc.

Cycle 332 proves the easy downstream step:
if such a continuous path exists, then its image is a connected subset of
`orderWeb (padeR n d)` containing both witnesses.

## Why the current hypotheses are insufficient
- The bridge API is still only `∀ radius, ∃ witness`; it does not relate the
  witness chosen at one radius to the witness chosen at another radius.
- That means there is still no explicit preconnected subset of
  `orderWeb (padeR n d)` known to contain both `z0` and `z`.
- The obvious component lemma route remains blocked:

```lean
IsPreconnected.subset_connectedComponentIn
```

  because it cannot be applied without such an explicit preconnected subset.
- The endpoint sign estimates are also not strong enough to force the exact ray
  itself into `orderWeb` at the generic bridge angle:
  the approximation error is `O(t^(n+d+2))`, while the main imaginary term near
  phase `s = 0` is only `O(t^(n+d+1) * s)`, so sign control at fixed endpoints
  does not automatically extend all the way down to `s = 0`.

## Precise continuation theorem still needed
One of the following would close the gap:

1. A continuous phase-selection theorem on a radius interval:

```lean
∃ σ : ℝ → ℝ,
  ContinuousOn σ (Set.Icc a b) ∧
  ∀ r ∈ Set.Icc a b,
    σ r ∈ Set.Icc (-η) η ∧
    Complex.im
      (padeR n d (((↑r : ℂ) * exp (↑(θ + σ r) * I))) *
        exp (-(((↑r : ℂ) * exp (↑(θ + σ r) * I))))) = 0
```

2. An equivalent connected-zero-set theorem in the radius/phase rectangle for
   the map

```lean
(r, s) ↦ Complex.im
  (padeR n d (((↑r : ℂ) * exp (↑(θ + s) * I))) *
    exp (-(((↑r : ℂ) * exp (↑(θ + s) * I)))))
```

   showing that the zero set contains a connected subset whose radius
   projection covers the whole interval between the two witness radii.

## Possible solutions
- Prove a local implicit-function / nonvanishing-derivative lemma for the
  imaginary part in the positive-real strip.
- Alternatively, prove a compact planar continuum theorem for the zero set in
  the radius/phase rectangle, then map that continuum into `ℂ`.
- Do not go back upward to more wrappers over `connectedComponentIn`; the new
  path helper is already the correct local theorem boundary.
