# Cycle 639 Results

## Worked on
§521 LMM-as-GLM implicit-row stability-matrix projections in
`OpenMath/LMMAsGLM.lean`, immediately after the cycle 638 shift-row
corollaries.

## Approach
Followed the planned sorry-first workflow:

1. Added `toGLM_stabilityMatrix_castAdd_last_apply` and
   `toGLM_stabilityMatrix_natAdd_last_apply` with `sorry`.
2. Verified `lake env lean OpenMath/LMMAsGLM.lean` accepted the
   statement shapes with only the two expected `sorry` warnings.
3. Replaced both proofs with the cycle 638 bridge recipe:
   rewrite by `toGLM_stabilityMatrix_apply`, then explicitly `show`
   the complex block entry as a coercion from the real block before
   applying the `B`/`V` projection lemmas.

## Result
SUCCESS — both target lemmas landed sorry-free:

* `LMM.toGLM_stabilityMatrix_castAdd_last_apply`
* `LMM.toGLM_stabilityMatrix_natAdd_last_apply`

The first keeps the `Vℂ` contribution and rewrites the `Bℂ` entry to
`((m.β (Fin.last s) : ℝ) : ℂ)`. The second uses
`toGLM_V_natAdd_last_apply` to remove the `Vℂ` contribution and
`toGLM_B_natAdd_last_apply` to reduce the `Bℂ` entry to `1`.

Verification:

* `lake env lean OpenMath/LMMAsGLM.lean`
* `lake env lean OpenMath/RKAsGLM.lean`
* `lake env lean OpenMath/GeneralLinearMethod.lean`

No new live `sorry`. No `maxHeartbeats` change.

## Dead ends
None. The planned proof scripts worked directly after the sorry-first
statement check.

## Discovery
The cycle 638 `show` workaround remains the right interface for these
row projections. Bridging through
`show ((m.toGLM.B ... 0 : ℝ) : ℂ) = _` (and similarly for `Vℂ` in
the `natAdd` last row) avoids the `Fin.natAdd s j` ↔ `j.addNat s`
simp-normal-form divergence that can prevent projection lemmas from
firing if one tries a single `simp [GeneralLinearMethod.Bℂ, ...]`.

## Suggested next approach
Proceed to the planned post-row-projection milestone only after this
surface is consumed deliberately: a generic or local
`Matrix.fromBlocks` charpoly factorisation for
`m.toGLM.stabilityMatrix z`, using the four shift/implicit row
projections now available. Do not reopen the §38 `cut_assoc` blocker
without a new structural plan.

## Aristotle
Skipped by strategy. These were short mechanical projection proofs, and
recent Aristotle submissions for nearby cycles have hit HTTP 429 before
doing useful work.
