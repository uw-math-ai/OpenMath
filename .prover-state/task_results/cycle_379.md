# Cycle 379 Results

## Worked on
BDF7 zero-instability root certificate:
`OpenMath/MultistepMethods.lean` private lemma `bdf7_cayley_image_root`.

## Approach
Checked the two prior Aristotle bundles first. They only reproved
`bdf7_cayley_identity` and `bdf7_cayley_norm_gt_one`, which were already live,
so no transplant was needed.

Submitted the required five Aristotle jobs against the live file:
- `07cc9e40-3e90-457f-b20f-878a0645369a`: full target, Route A/Rouche prompt.
- `3f458c9b-4351-4474-ae3c-2c2be0f429b4`: full target, explicit-factor prompt.
- `64fae740-7690-4c85-849a-822b1177e9c2`: support bound at the numerical center.
- `34e5b2e1-92c9-4b35-a55d-cad496496973`: boundary estimate/Rouche prompt.
- `bc18023b-b07b-4657-b5b0-3fd4bc607bb3`: exact algebraic certificate prompt.

After the 30-minute wait, all five were still `IN_PROGRESS` (8%, 20%, 17%,
14%, and 16%), so no Aristotle proof was incorporated.

Locally closed the target with an exact algebraic quadratic-factor certificate:
isolate a real subresultant parameter `u ∈ [-1/24, -1/25]` by IVT, define
`v = -B(u)/A(u)`, prove the two remainder equations by exact polynomial
identities, and then use algebraic closedness of `ℂ` to get a root of
`w^2 + u w + v` with positive real part because `u < 0`.

## Result
SUCCESS.

Closed `bdf7_cayley_image_root`, which closes `bdf7_bad_root_exists` and
`bdf7_not_zeroStable`. Added `bdf7_not_convergent` in
`OpenMath/DahlquistEquivalence.lean`. Updated `plan.md` and removed the resolved
BDF7 issue file.

Verification:
- `lake env lean OpenMath/MultistepMethods.lean` passed.
- `lake build OpenMath.MultistepMethods` passed to refresh the `.olean`.
- `lake env lean OpenMath/DahlquistEquivalence.lean` passed.

## Dead ends
The transformed sextic is irreducible over `ℚ`; the simple rational quadratic
factor route was not available.

The Aristotle batch did not finish by the mandatory post-wait check, so it did
not contribute a usable proof this cycle.

## Discovery
The Cayley-transformed sextic admits an exact algebraic quadratic factor whose
linear coefficient lies in `[-1/24, -1/25]`. This avoids adding generic
Schur-Cohn, Jury, or Routh-Hurwitz infrastructure.

## Suggested next approach
First candidate: Theorem 359D from §3.5.10, once the concrete Iserles statement
is available. If 359D remains blocked, begin the Chapter 4 downstream items in
`plan.md`, starting with a Milne error-control or step-size-control statement.
