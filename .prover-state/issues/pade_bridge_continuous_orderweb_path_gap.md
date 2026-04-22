# Issue: `phaseSelection_of_bridgeWitnesses` is now the exact local blocker

## Blocker
Cycle 333 incorporated the usable shape of the ready Aristotle result and proved
the topological helper

```lean
continuousOrderWebPath_of_phaseSelection
```

inside the `where` block of
`padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge` in
`OpenMath/PadeOrderStars.lean`.

The original live sorry

```lean
continuousOrderWebPath_of_bridgeWitnesses
```

is now proved by reducing it to a new narrower local theorem:

```lean
phaseSelection_of_bridgeWitnesses
```

So the blocker is no longer the path-topology step. The exact missing ingredient
is the existence of explicit radius/phase-selection data for the chosen bridge
witnesses.

## Context
- `z0` is still a fixed order-web witness in `rayConeNearOrigin θ 1 1`.
- `z` is still a fixed order-web witness in `rayConeNearOrigin θ aperture radius`.
- Cycle 333 added a fully proved helper showing:
  if one already has a continuous phase selection `σ` on a radius interval
  `[a,b]`, with
  `w(r) = (↑r : ℂ) * exp (↑(θ + σ r) * I)`,
  `Im (padeR n d (w r) * exp (-w r)) = 0`,
  `0 < Re (padeR n d (w r) * exp (-w r))`,
  and endpoint equalities tying `w(a)` and `w(b)` to `z0` and `z`,
  then one gets the desired continuous order-web path on `Set.Icc (0 : ℝ) 1`.
- The only remaining sorry is therefore the theorem that should produce exactly
  those `a`, `b`, `η`, and `σ`.

## Why the current hypotheses are insufficient
- The bridge API is still only `∀ radius, ∃ witness`; it does not relate the
  witness chosen at one radius to the witness chosen at another radius.
- The current local theorem needs endpoint-specific data:
  one interval `[a,b]`, one `η > 0`, and one continuous `σ : ℝ → ℝ` whose graph
  stays in the zero set while keeping the real part positive.
- The old generic `connectedComponentIn` route is now intentionally bypassed:
  once the phase-selection data exists, the path and connected-support steps are
  formalized already.
- The endpoint sign estimates are still too weak to force the exact ray itself
  into `orderWeb`; the same `O(t^(n+d+2))` vs. `O(t^(n+d+1) * s)` mismatch near
  `s = 0` remains.

## Precise continuation theorem still needed
The current local sorry is exactly:

```lean
∃ a b η : ℝ, ∃ σ : ℝ → ℝ,
  a ≤ b ∧
  0 < η ∧
  ContinuousOn σ (Set.Icc a b) ∧
  (∀ r ∈ Set.Icc a b, σ r ∈ Set.Icc (-η) η) ∧
  (∀ r ∈ Set.Icc a b,
    let w : ℂ := (↑r : ℂ) * exp (↑(θ + σ r) * I)
    Complex.im (padeR n d w * exp (-w)) = 0) ∧
  (∀ r ∈ Set.Icc a b,
    let w : ℂ := (↑r : ℂ) * exp (↑(θ + σ r) * I)
    0 < Complex.re (padeR n d w * exp (-w))) ∧
  z0 = ((↑a : ℂ) * exp (↑(θ + σ a) * I)) ∧
  z = ((↑b : ℂ) * exp (↑(θ + σ b) * I))
```

Any proof of this theorem closes the live blocker immediately.

## Possible solutions
- Prove a local implicit-function or continuation lemma for the zero set of the
  imaginary part inside the positive-real strip.
- Alternatively, prove a connected-zero-set / continuum theorem in the compact
  radius-phase rectangle and then parameterize that connected subset.
- Keep the proof local to `OpenMath/PadeOrderStars.lean`; the new path helper is
  already the right theorem boundary.
