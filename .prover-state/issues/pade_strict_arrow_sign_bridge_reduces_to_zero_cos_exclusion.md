# Issue: Strict Padé arrow-sign bridge reduces to zero-cosine exact-ray exclusion

## Blocker
Cycle 315 confirmed that the live strict bridge theorems

- `PadeRDownArrowSignBridge n d`
- `PadeRUpArrowSignBridge n d`

do not reduce to any missing discrete-angle classification theorem in the
current repo. After landing the honest weakened bridge lemmas in
`OpenMath/PadeOrderStars.lean`, the strict bridge now reduces to the single
remaining input

- `PadeRDownArrowZeroCosExclusion n d`
- `PadeRUpArrowZeroCosExclusion n d`

which assert that exact-ray Padé down/up arrows cannot occur when

```lean
padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) = 0.
```

This is now the exact minimal helper needed to recover the old strict bridge
interface.

## Context
- The live file now proves:
  - `padeR_nonneg_sign_of_downArrowDir`
  - `padeR_nonpos_sign_of_upArrowDir`
- These are honest contradiction lemmas:
  - a negative sign contradicts `IsDownArrowDir` because
    `padeR_local_plus_near_of_errorConst_cos_neg` gives a nearby cone with
    `1 < ‖padeR n d z * exp (-z)‖`,
  - a positive sign contradicts `IsUpArrowDir` because
    `padeR_local_minus_near_of_errorConst_cos_pos` gives a nearby cone with
    `‖padeR n d z * exp (-z)‖ < 1`.
- The new wrappers
  - `padeR_downArrowSignBridge_of_zeroCosExclusion`
  - `padeR_upArrowSignBridge_of_zeroCosExclusion`
  show that strict positivity/negativity is now blocked only by the zero-sign
  boundary case.
- This is not a missing “355B angle classification” theorem. The current
  `IsDownArrowDir` / `IsUpArrowDir` predicates are norm-only exact-ray
  statements, so discrete inverse classification is the wrong shape here.

## What was tried
- Inspected the live bridge seam in `OpenMath/PadeOrderStars.lean`.
- Re-checked the old zero-cosine blocker history.
- Proved the honest nonstrict sign consequences from the existing explicit-sign
  cone feeders.
- Packaged the remaining strict bridge as a zero-cosine exclusion input rather
  than pretending the strict theorem is already derivable.

## Possible solutions
- If the downstream seam really needs strict sign, prove the theorem-local
  zero-cosine exclusion input for Padé exact-ray arrows:

  ```lean
  ∀ θ, IsDownArrowDir (padeR n d) θ →
    padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0
  ```

  and the up-arrow companion.
- Before spending another cycle on that target, check whether the existing
  forward-Euler / `padeR 1 0` zero-cosine evidence from
  `.prover-state/issues/pade_local_cone_feeder_false_at_zero_cos.md`
  already shows the exclusion is false, in which case the strict bridge should
  be removed from the downstream interface instead of proved.
- Alternative seam repair: weaken the downstream contradiction theorem so it
  consumes the honest nonstrict bridge together with a separate hypothesis that
  rules out only the zero-sign boundary case actually needed for the argument.
