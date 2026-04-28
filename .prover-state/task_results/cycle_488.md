# Cycle 488 Results

## Worked on
BDF4 quadratic Lyapunov infrastructure in `OpenMath/BDFQuadraticLyapunov.lean`.
Also triaged ready Aristotle outputs from the AB13 scalar/vector work.

## Approach
Confirmed the live AB13 files are already closed:
`rg -n '^\s*sorry\b|:= by\s*sorry|by\s+sorry' OpenMath/LMMAB13Convergence.lean OpenMath/LMMAB13VectorConvergence.lean`
returned no matches. The ready AB13 Aristotle summaries were stale relative to
live code: `32e81aaf...` and `7056b0b3...` had already-incorporated vector
residual algebra/triangle proofs, while `510800b8...` and `9340dd8c...` were
`COMPLETE_WITH_ERRORS` bundles that introduced or rebuilt dependencies/stubs, so
I did not transplant them.

Created a sorry-first scaffold for the BDF4 stable-cubic Lyapunov certificate,
verified it compiled after building `OpenMath.LMMBDF4Convergence`, and submitted
five Aristotle jobs:

- `b968aa9f-e491-43d6-9f12-8a4bf52b470d`: coordinate update lemmas, COMPLETE.
- `d680a869-42f2-4c54-b437-4fc81be66500`: cubic quadratic step identity, COMPLETE.
- `8cfc273b-56e5-4181-b8d7-355e851ce36e`: lower-bound helpers and lower bound, COMPLETE.
- `1d4383ca-0b62-4816-9d02-dac9370ad34e`: upper-bound helper and upper bound, COMPLETE.
- `e762fff3-ec28-4877-ba01-f4a20d42ddf5`: optional homogeneous wrapper, COMPLETE_WITH_ERRORS.

After the required 30-minute sleep, I incorporated only proof bodies that worked
against the live module with the required `OpenMath.LMMBDF4Convergence` import.

## Result
SUCCESS. Landed:

- `bdf4RecDefect`, `bdf4LyapU`, and exact unit-coordinate update.
- Stable coordinates `bdf4StableX0/X1/X2` and their forced update equations.
- Stable cubic companion coordinate maps and explicit rational quadratic form
  `bdf4CubicQuad`.
- Exact discrete Lyapunov identity `bdf4CubicQuad_step_identity`.
- Coercive bounds `bdf4CubicQuad_lower` and `bdf4CubicQuad_upper`.
- Optional homogeneous packaged decrease
  `bdf4StableQuad_homogeneous_step_identity`.

`OpenMath.lean` was left unchanged: its current import list is not exhaustive
for the later LMM convergence modules, so importing this BDF4 infrastructure
there would be inconsistent with the observed policy. The module is checked
independently.

## Dead ends
The optional Aristotle wrapper bundle replaced the required project import with
`import Mathlib` and returned `COMPLETE_WITH_ERRORS`; I used the intended idea
but rewrote the wrapper manually via the live update lemmas and the cubic-step
identity.

## Discovery
The BDF4 stable cubic admits a compact rational certificate with loose but clean
norm-equivalence constants:
`1/4 * (x0^2 + x1^2 + x2^2) <= Q(x) <= 9 * (x0^2 + x1^2 + x2^2)`.
The exact homogeneous block decrease is now available for the next forced
Lyapunov/Grönwall step.

## Suggested next approach
Use `bdf4StableQuad_homogeneous_step_identity` plus the forced stable-coordinate
updates to derive a one-step inequality with defect forcing. Then combine the
unit-root coordinate drift and the stable quadratic bound into the BDF4 global
error recurrence. Do not return to weighted `l1` recurrences; the documented
Perron obstruction still applies.
