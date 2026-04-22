# Cycle 316 Results

## Worked on
- Triaged the four ready Aristotle outputs against the current `OpenMath/PadeOrderStars.lean`.
- Formalized the forward-Euler truth test at `n = 1`, `d = 0`, `θ = π / 4`.
- Repaired the Padé no-escape / 355D / 355E' seam so it no longer depends on the false global strict down-arrow bridge.

## Approach
- Read the current bridge seam and current `IsDownArrowDir` / `IsUpArrowDir` definitions directly from live code.
- Proved the exact zero-cos boundary value for the forward-Euler witness.
- Proved `IsDownArrowDir (padeR 1 0) (Real.pi / 4)` by reducing the exact ray to the real weight
  `(1 + √2 t + t^2) * exp (-√2 t)` and showing it is strictly decreasing on `(0, ∞)` via an explicit derivative computation.
- Replaced the downstream strict Padé bridge assumptions with explicit theorem-local zero-cos exclusion assumptions, using the already-live nonstrict sign lemmas to recover the needed local cone feeders.

## Result
- SUCCESS: `OpenMath/PadeOrderStars.lean` now contains a formal forward-Euler counterexample:
  `padeR10_pi_div_four_zeroCos`, `padeR10_pi_div_four_isDownArrowDir`,
  `not_padeRDownArrowZeroCosExclusion_one_zero`, and `not_padeRDownArrowSignBridge_one_zero`.
- SUCCESS: `concreteRationalApproxToExp_of_padeR`, `PadeRConcreteNoEscapeInput.concrete`,
  `PadeREhleBarrierInput.concrete`, `PadeREhleBarrierInput.thm_355D`, and
  `PadeREhleBarrierInput.thm_355E'` now require theorem-local zero-cos exclusion hypotheses
  instead of the false global strict sign bridge.
- SUCCESS: Verified with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  and
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`.

## Dead ends
- The ready Aristotle artifacts did not provide a safe live delta for the current seam.
- The forward-Euler counterexample corollaries needed some manual normalization around
  `((↑(1 + 0) + 1) * (π / 4))`; direct `rw`/`change` failed and `norm_num at ...` was the stable fix.

## Discovery
- The remaining strict down-arrow bridge is not merely unproved; it is false already for the current live definitions.
- The exact remaining honest boundary is theorem-local zero-cos exclusion, not a global Padé-wide strict sign bridge.
- Artifact triage:
  `782300a6-e562-4e0a-b381-a09bcfc618a2` was rejected because it reproves the already-live `padeR_nonpos_sign_of_upArrowDir` in a stale standalone Aristotle namespace without improving the current seam.
  `fab0de81-e592-49ee-972b-3654782c3ac2` was rejected because it uses the obsolete `rayConeNearOrigin` representation with an extra angle witness, so it does not match the live geometry interface.
  `49336306-753e-4b23-8fb5-92c498428c1a` was rejected because it only restates the already-live zero-cos-to-strict-bridge wrapper and adds no value once the bridge target is falsified by the forward-Euler witness.
  `e759ed15-f94d-46fe-a94d-bdbff9f74fb2` was rejected for the same reason on the up-arrow side: it matches an already-live wrapper shape but does not repair the now-dishonest interface.

## Suggested next approach
- Audit any downstream use sites of the repaired 355D / 355E' Padé wrappers and decide where genuine zero-cos exclusion is actually available.
- If the up-arrow side matters next, run the analogous exact-ray truth test rather than assuming the symmetric strict bridge.
