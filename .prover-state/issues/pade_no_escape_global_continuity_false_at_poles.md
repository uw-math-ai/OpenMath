# Issue: `PadeRConcreteNoEscapeInput.cont` is false at Padé poles

## Blocker
The field

```lean
cont : Continuous (fun z => ‖padeR n d z * exp (-z)‖)
```

in `PadeRConcreteNoEscapeInput` is not valid globally for pole-bearing Padé
approximants.

## Context
The smallest counterexample is `(n, d) = (0, 1)`.

Using the existing explicit formulas in `OpenMath/Pade.lean`:

- `padeP_zero_left 1` gives `padeP 0 1 z = 1`
- `padeQ_one_right 0` gives `padeQ 0 1 z = 1 - z`

so

```lean
padeR 0 1 z = 1 / (1 - z).
```

Hence

```lean
fun z => ‖padeR 0 1 z * exp (-z)‖ = ‖exp (-z) / (1 - z)‖
```

has a pole at `z = 1`. The exponential factor is finite and nonzero at `1`,
while the denominator vanishes there, so the norm is not continuous at that
point.

## What was tried
- Audited the live seam before attempting any `PadeRConcreteNoEscapeInput`
  construction, as required by cycle 307.
- Tested the smallest pole-bearing Padé example first, rather than trying to
  prove the global continuity field abstractly.

## Possible solutions
- Replace the global continuity field by a local continuity hypothesis on the
  specific domain actually used downstream.
- Restrict the continuity field to sets avoiding the poles of `padeQ n d`.
- Refactor the no-escape interface so the Padé-side feeder theorem only supplies
  the local near-origin inequalities needed for 355C/355D/355E, without a false
  global continuity requirement.
