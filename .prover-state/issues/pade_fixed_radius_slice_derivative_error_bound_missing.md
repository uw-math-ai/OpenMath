# Issue: fixed-radius uniqueness is proved, but the clopen wrapper is still too global

## Blocker
The derivative/error-bound seam is no longer the blocker.

`oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
is now proved in `OpenMath/PadeOrderStars.lean`, and the file compiles with only
one remaining `sorry`:

```lean
oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both
```

The smallest remaining mismatch is that this wrapper theorem is stated for an
arbitrary radius `ρ` inside an arbitrary zero set `oddDownArrowRadiusPhaseZeroSet n d δ`,
while the proved uniqueness theorem only gives:

```lean
∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono, ...
```

So the wrapper currently asks for same-radius uniqueness on all fibers, but the
available theorem only covers sufficiently small radii.

## Context
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  succeeds.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`
  succeeds.
- `rg -n "sorry" OpenMath/PadeOrderStars.lean` now reports only:

```text
OpenMath/PadeOrderStars.lean:4262:  sorry
```

- The proved uniqueness theorem is local-to-small-radius and was closed by a
  theorem-local transplant from Aristotle bundle `a1c26af3-db00-4cf5-9b34-9d800c6a6ee7`,
  plus live-file cleanup:
  - `error_deriv_bound_at_of_padeQ_ne_zero`
  - `error_lipschitz_on_ball_of_padeQ_ne_zero`
  - `main_term_im_diff_bound_of_neg_errorConst`
  - `arc_norm_sub_le_of_phase`

## What was tried
- Inspected the ready Aristotle bundle `a1c26af3...` first and transplanted only
  the local theorem neighborhood around
  `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`.
- Inspected `cdef2118...` for theorem-local derivative setup, but the direct
  closure came from `a1c26af3...`; no other module edits were transplanted.
- Rebuilt the uniqueness proof against the live file by fixing:
  - current `padeR_exp_neg_local_bound` tuple order,
  - `Set.MapsTo`/Schwarz-lemma usage,
  - the sine mean-value argument,
  - the arc-norm and error-difference bookkeeping.
- Tried to route the remaining clopen wrapper directly through the new
  small-radius uniqueness theorem. That stalls because the wrapper theorem has
  no hypothesis relating its ambient `δ` or its fiber radius `ρ` to the
  produced `δmono`.

## Possible solutions
- Shrink the `δ` chosen in
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`
  to also include the uniqueness radius:

```lean
δ := min δ0 (min (δQ / 2) δmono)
```

  Then replace the current global wrapper by a theorem-local statement that is
  only invoked on radii `ρ ∈ Set.Icc (0 : ℝ) δ`.

- Equivalently, prove a localized replacement for the remaining wrapper:

```lean
∀ {δ ρ}, δ ≤ δmono → ...
```

  or

```lean
∀ {ρ}, ρ ∈ Set.Ioo (0 : ℝ) δmono → ...
```

  and feed that directly into the projection argument.

- Do **not** spend another cycle trying to recover the deleted stronger global
  theorem shape `∀ ρ, 0 < ρ → ...`; that was explicitly rejected by the plan.
