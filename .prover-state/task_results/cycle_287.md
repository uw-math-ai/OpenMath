# Cycle 287 Results

## Worked on
- `OpenMath/PadeOrderStars.lean`
- live theorem seam around `padeR_no_nonzero_eq_exp_on_orderWeb`
- mandatory Aristotle triage for:
  - `de228e57-369e-471f-8c2c-9a564d634849`
  - `40f68f7a-7d40-40bc-9f0e-36f260ad786e`
  - `a7f483f7-08c4-4fdd-837a-ed9dd3db30c0`
  - `39c98115-5f6a-487d-9ccb-317b70483ebf`
  - `e26ad296-6137-4950-84fe-d4516c5812b4`
  - `61b6fd34-caeb-48e1-a86c-15dec2d4c83e`

## Approach
- Re-read `OpenMath/PadeOrderStars.lean`, the existing issue file, and the
  concrete `OrderStars` seam.
- Ran a use-site search for `thm_355D_of_padeR`, `thm_355E'_of_padeR`, and
  `padeR_no_nonzero_eq_exp_on_orderWeb`; there are zero external consumers.
- Triaged the ready Aristotle outputs only long enough to detect interface
  drift or invalid proofs:
  - `de228e57...`: invalid proof sketch; tries to read `orderWeb` membership as
    an imaginary-part condition.
  - `40f68f7a...`: stale branch API (`branch.support_sub`).
  - `a7f483f7...`: stale branch API (`branch.mem_support_norm_gt`,
    `padeR_apply_zero`).
  - `39c98115...`: tautological placeholder (`exact ⟨fun θ h => h, ...⟩`) with
    no analytic content.
  - `e26ad296...`: far-field package contradicts itself and relies on a stale
    boundedness interface.
  - `61b6fd34...`: theorem body references missing names
    (`isUpArrowDir_of_neg_errorConst_nonneg_cos`,
    `isUpArrowDir_of_pos_errorConst_nonpos_cos`), so it does not paste into the
    live file with zero interface changes.
- Checked whether the uniform theorem shape was even true. A compiled Lean
  scratch file showed a counterexample at `(n,d) = (0,0)` and
  `z = (2 * Real.pi : ℂ) * Complex.I`.
- Restated `padeR_no_nonzero_eq_exp_on_orderWeb` to the honest theorem-local
  version that derives exact coincidence exclusion from the existing unit-level
  exclusion hypothesis.

## Result
- SUCCESS: removed the only live sorry in `OpenMath/PadeOrderStars.lean`.
- SUCCESS: `lake env lean OpenMath/PadeOrderStars.lean` passes.
- SUCCESS: wrote a focused issue documenting that the old fully uniform theorem
  is false, not merely unsupported.

## Dead ends
- The five cycle-286 Aristotle bundles were not salvageable without interface
  drift or theorem-meaning changes.
- Attempting to preserve the old theorem statement would have been proving a
  false claim, due to the `(0,0)` Padé counterexample.
- The current imported `OrderStars` `.olean` does not expose the newer helper
  lemmas at lines ~1624-1664 of source, so I proved the revised theorem
  directly from `hz_eq` rather than depending on those names.

## Discovery
- Existing Padé infrastructure does **not** force the only `orderWeb`
  coincidence with `exp` to be `z = 0`; the statement fails already for
  `padeR 0 0 = 1`.
- Therefore the arbitrary `(n,d)` theorem was actually false, not just
  unsupported.
- There are zero external consumers of the old theorem shape, so weakening was
  clearly preferable.

## Suggested next approach
- When the next concrete `ConcreteRationalApproxToExp` consumer needs a Padé
  exclusion theorem, target the actual downstream Padé subfamily instead of
  reviving a false uniform claim.
- If a future cycle wants a theorem stronger than the current theorem-local
  hypothesis, start by testing whether `n + d > 0` is enough, and only then try
  to prove a Padé-specific exclusion.
