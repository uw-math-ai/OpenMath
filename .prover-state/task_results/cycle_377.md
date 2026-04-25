# Cycle 377 Results

## Worked on
BDF7 downstream infrastructure in `OpenMath/MultistepMethods.lean`.

## Approach
1. Re-read the cycle strategy and did the bounded local 359D search. The only
   hits remain the cycle-376 §3.5.10 packaging and placeholders, so I followed
   the BDF7 fallback.
2. Checked local Aristotle result directories before editing. No newer ready
   bundle beyond the already-dispositioned cycle-375 Radau IA results was
   available.
3. Added the BDF7 block sorry-first and verified the temporary scaffold.
4. Submitted five Aristotle jobs:
   - `572f102d-dd21-487a-8ae9-e610151c1a83`: `bdf7_rhoC_factor`
   - `b448e7fa-be3c-4049-b0cf-9866dcd651fc`: bad-root reduction
   - `8958a948-aed1-43fe-89c8-05f22fbd3927`: exact root existence
   - `6c8b2729-e006-4b88-ba58-1e4a55713e35`: Schur-Cohn/Jury certificate
   - `5c49dcda-7819-47dd-bdff-5709a1a070c6`: Rouche/interval certificate
5. Slept 30 minutes and did exactly one post-wait status check.
6. Closed the deterministic live proofs locally and removed the temporary
   `bdf7_bad_root_exists` / `bdf7_not_zeroStable` scaffold when the hard root
   certificate was not ready.

## Result
PARTIAL SUCCESS.

Landed, with no live `sorry`:
- `bdf7 : LMM 7`
- `bdf7_consistent`
- `bdf7_order_seven`
- `bdf7_implicit`
- `bdf7_rhoC_factor`
- `bdf7_not_zeroStable_of_bad_root`

The hard theorem `bdf7_not_zeroStable` was not committed because its exact
sextic root certificate did not close this cycle.

Verification:
- `lake env lean OpenMath/MultistepMethods.lean` passed.
- `lake build OpenMath.MultistepMethods` passed.

## Dead ends
The two completed Aristotle outputs were rejected as direct transplants:
- `572f102d...` rebuilt a stub `OpenMath/MultistepMethods.lean` and used a
  non-live `unfold bdf7.rhoC` proof. The live factorization was already closed
  with `simp [LMM.rhoC, bdf7, Fin.sum_univ_succ]; ring_nf`.
- `b448e7fa...` also rebuilt a stub module and targeted a simplified
  `IsZeroStable` API. The live reduction was closed directly using
  `hzs.roots_in_disk`.

The three root-certificate Aristotle jobs were still in progress at the single
post-wait check:
- `8958a948...`: 10%
- `6c8b2729...`: 17%
- `5c49dcda...`: 7%

## Discovery
The remaining exact sextic is:

```text
1089 ξ^6 - 1851 ξ^5 + 2559 ξ^4 - 2341 ξ^3 + 1334 ξ^2 - 430 ξ + 60
```

Numerical unstable roots:

```text
0.0768046058613277 +/- 1.01932879466066 i
```

Useful exact certificate data for the next cycle is recorded in
`.prover-state/issues/bdf7_zero_instability_root_certificate.md`. In short:
- Schur recursion reaches a quadratic stage
  `[4798774195, 2030751691, 7167712264]` with
  `7167712264 > 4798774195`.
- The Cayley transform produces
  `2416*w^6 + 3577*w^5 + 4431*w^4 + 3920*w^3 + 2240*w^2 + 735*w + 105`,
  whose fourth Hurwitz determinant is `-1263322645200`.

## Suggested next approach
Formalize one exact certificate route:
1. Prefer the finite Schur-Cohn/Jury recursion specialized to this real sextic,
   using the coefficient chain in the issue file.
2. Alternatively prove the Cayley-transform plus Routh-Hurwitz necessary
   condition from the negative fourth Hurwitz determinant.
3. If using numerics, turn the approximate root into a rational Rouche/interval
   certificate; do not use the approximation as an assumption.
