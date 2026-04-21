# Cycle 282 Results

## Worked on
- Triage of ready Aristotle outputs:
  - `.prover-state/aristotle_results/e24fe038-1806-4efe-9f29-851ae4662150`
  - `.prover-state/aristotle_results/2d8579c7-9397-4273-8838-1668de85037f`
- `OpenMath/OrderStars.lean`
- The missing theorem `realizedUpArrowInfinityBranch_contradiction`
- A small packaging theorem
  `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`

## Approach
- Read `.prover-state/strategy.md` and the two blocker issue files first.
- Confirmed the live baseline with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`.
- Inspected the ready Aristotle Lean artifacts against the live interfaces.
- Reused the existing down-arrow contradiction proof as the exact template for the
  up-arrow version, swapping the near-origin and far-field inequalities.
- Reused only the live helper layer:
  `mem_orderWeb_of_mem_globalOrderArrowBranch_support`,
  `exists_mem_support_norm_gt_of_escapesEveryClosedBall`,
  `exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin`,
  `exists_mem_support_unit_level_of_connected_orderWeb_branch`.
- Added a small builder theorem packaging the down/up branch contradictions into
  `ConcreteRationalApproxToExp R data`.

## Result
- SUCCESS: both ready Aristotle result directories were rejected as non-incorporable.
  - `e24fe038-1806-4efe-9f29-851ae4662150` returned a parallel theorem-local artifact
    for the down-arrow contradiction and did not match the live interface exactly.
  - `2d8579c7-9397-4273-8838-1668de85037f` targeted the already-refuted inverse bridge
    `IsUpArrowDir -> exp (I * (p + 1) * θ) = ±1` and also shipped a replacement
    `OpenMath.lean`, so it was rejected.
- SUCCESS: added `realizedUpArrowInfinityBranch_contradiction` to the live file.
- SUCCESS: added
  `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`
  completed cleanly after the edits.
- No fresh Aristotle submission was opened this cycle. After the required ready-result
  triage, the live target theorem closed directly by symmetry against the existing
  helper layer, so there were no remaining theorem-local subgoals to batch out.

## Dead ends
- The inverse classification route remains unusable:
  `IsUpArrowDir` / `IsDownArrowDir` do not justify
  `exp (I * (p + 1) * θ) = ±1` under the live norm-only definitions.
- The returned Aristotle artifacts could not be salvaged by small edits because the
  mismatch was at the interface/statement level, not just in proof details.

## Discovery
- The up-arrow contradiction is a true line-by-line mirror of the down-arrow proof
  once the connected crossing lemma is fed the far-field `< 1` point as the “small”
  endpoint and the near-origin `> 1` point as the “large” endpoint.
- The existing public seam is now slightly easier to use concretely: theorem-local
  contradiction hypotheses can be packaged into `ConcreteRationalApproxToExp R data`
  without altering any public structures.

## Suggested next approach
- Derive the theorem-local analytic hypotheses used by the two contradiction theorems
  from the concrete rational approximation `R` under study.
- In particular, target the concrete seam for:
  - exclusion of `0` from realized branch support,
  - exclusion of nonzero unit-level points on `orderWeb R`,
  - local cone sign control near realized down/up tangents,
  - far-field sign control on large order-web points.
