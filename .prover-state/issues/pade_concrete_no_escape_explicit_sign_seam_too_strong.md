# Issue: `PadeRConcreteNoEscapeInput` local cone fields are stronger than the live explicit-sign seam

## Blocker
The downstream fields
`PadeRConcreteNoEscapeInput.local_minus_near_down` and
`PadeRConcreteNoEscapeInput.local_plus_near_up` still ask for symmetric-cone
feeders from arbitrary `IsDownArrowDir` / `IsUpArrowDir` hypotheses:

```lean
∀ θ : ℝ, IsDownArrowDir (padeR n d) θ -> ...
∀ θ : ℝ, IsUpArrowDir   (padeR n d) θ -> ...
```

The live seam now only honestly provides explicit-sign feeders:

- `padeR_local_minus_near_of_errorConst_cos_pos`
- `padeR_local_plus_near_of_errorConst_cos_neg`

Those theorems require sign information on
`padePhiErrorConst n d * cos ((↑(n + d) + 1) * θ)`, not just a direction-class
predicate.

## Context
Cycle 313 landed the generic and Padé explicit-sign plus-side theorems:

- `OrderStars.local_plus_near_of_errorConst_cos_neg`
- `PadeOrderStars.padeR_local_plus_near_of_errorConst_cos_neg`

Together with the already-landed minus-side companions, the honest local cone
inputs below the Padé no-escape seam are now:

```lean
0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)
```

for the inside-the-unit-disk feeder, and

```lean
padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0
```

for the outside-the-unit-disk feeder.

The stronger direction-only interface remains unjustified at zero-cosine rays
and invites the same false symmetric-cone route that cycles 311-312 already
ruled out.

## What was tried
- Audited the live seam after landing the explicit-sign plus theorem and its
  Padé wrapper.
- Re-checked that the new feeders are one-sided explicit-sign statements rather
  than consequences of `IsDownArrowDir` / `IsUpArrowDir`.
- Confirmed that the current `PadeRConcreteNoEscapeInput` fields still demand
  the stronger direction-only version.

## Possible solutions
- Weaken `PadeRConcreteNoEscapeInput.local_minus_near_down` to take an explicit
  positive sign-margin hypothesis, or a one-sided wedge hypothesis that
  implies it.
- Weaken `PadeRConcreteNoEscapeInput.local_plus_near_up` to take an explicit
  negative sign-margin hypothesis, or a one-sided wedge hypothesis that
  implies it.
- If direction predicates must remain, add a separate proven bridge from those
  predicates to the explicit-sign or one-sided-wedge hypotheses; do not assume
  that bridge for free.
