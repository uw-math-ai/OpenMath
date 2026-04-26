# Cycle 432 Results

## Worked on
- **Primary**: Bridge `LMM.ab5_global_error_bound` (scalar AB5 headline) through
  `LMM.ab_global_error_bound_generic` at `s = 5`, `p = 5`, mirroring cycle 431's
  vector AB5 bridge.
- **Secondary**: Bridge `LMM.ab6_global_error_bound` (scalar) and
  `LMM.ab6Vec_global_error_bound` through the generic AB scaffold.
- **Hygiene**: Reject Aristotle bundle `9c25564e-9424-4433-9a59-a1fd3d19469b`
  (uses placeholder `ab4GenericCoeffStub`); confirm archived in
  `.prover-state/aristotle_archive/`.

## Approach
1. Reused the cycle-431 `LMM.ab5GenericCoeff` and `LMM.abLip_ab5GenericCoeff`
   already in `OpenMath/LMMAB5Convergence.lean`. Added scalar-side bridges
   `ab5Iter_eq_abIter` and `ab5Residual_eq_abResidual`, then rewired
   `ab5_global_error_bound` through `ab_global_error_bound_generic` at
   `s = 5`, `p = 5`.
2. For AB6 scalar: introduced `ab6GenericCoeff : Fin 6 → ℝ`, six
   `@[simp]` projection lemmas, `abLip_ab6GenericCoeff` (`= (114/5) * L`),
   `ab6Iter_eq_abIter`, `ab6Residual_eq_abResidual`, and rewired
   `ab6_global_error_bound` through the generic scaffold.
3. For AB6 vector: added `ab6IterVec_eq_abIterVec` and
   `ab6VecResidual_eq_abResidualVec` (reusing the imported `ab6GenericCoeff`
   from the scalar file), then rewired `ab6Vec_global_error_bound` through
   `ab_global_error_bound_generic_vec` at `s = 6`, `p = 6`. The proof mirrors
   the cycle-431 AB5 vector pattern (specialize generic theorem, set
   `α := ab6GenericCoeff` and `y₀_sext := ![y₀, y₁, y₂, y₃, y₄, y₅]`,
   establish window-max start bound, residual bound via the bridge,
   `(N : ℝ) * h ≤ T` from `((N : ℝ) + 5) * h ≤ T`, then apply the generic
   theorem and convert back to `‖ab6IterVec ... - y(...)‖`).
4. Submitted three Aristotle bridge stub jobs upfront in parallel; refreshed
   once after manual work to incorporate any usable proofs.

## Result
**SUCCESS**.

- `OpenMath/LMMAB5Convergence.lean`, `OpenMath/LMMAB6ScalarConvergence.lean`,
  `OpenMath/LMMAB6VectorConvergence.lean` all compile cleanly.
- `lean_verify` confirms `LMM.ab5_global_error_bound`,
  `LMM.ab6_global_error_bound`, `LMM.ab6Vec_global_error_bound`,
  `LMM.ab6IterVec_eq_abIterVec`, and `LMM.ab6VecResidual_eq_abResidualVec`
  all depend only on `propext`, `Classical.choice`, `Quot.sound`.
- 0 sorrys in any of the three modified files.
- Three Aristotle projects submitted at 04:12 UTC (AB5 scalar bridge,
  AB6 scalar bridge, AB6 vector bridge); only the AB6 vector bridge
  (`a0ffd32a-b714-44c2-8352-2ee4ca86edbf`) finished `COMPLETE` in time and
  was downloaded to
  `.prover-state/aristotle_results/cycle_432_ab6_vector/` for reference.
  The other two (`618c01dd...` AB5 scalar `COMPLETE_WITH_ERRORS`, and
  `93dd03f9...` AB6 scalar still `IN_PROGRESS`) were superseded by the
  manual proofs.

## Dead ends
- An early Edit attempt that left "legacy proof body removed; placeholder"
  stubs alongside the new AB6 scalar bridge produced parse errors. Recovered
  via `git checkout HEAD -- OpenMath/LMMAB6ScalarConvergence.lean` and
  re-applied via `sed`-based line-range deletion + a single trailing-anchor
  Edit. Same pattern then worked cleanly for the AB6 vector rewrite.
- The Aristotle AB6 vector bridge proof (using `interval_cases` + `grind` /
  `norm_num [Fin.sum_univ_succ]`) was left as reference only; it would have
  required additional bridging because Aristotle re-created
  `abIterVec`/`abResidualVec`/`ab6IterVec`/`ab6VecResidual` from scratch
  instead of using the live definitions. The AB5-vector pattern with explicit
  `neg_smul` rewrites + `abel` was a cleaner port.

## Discovery
- The AB6 vector bridge slots in cleanly behind the existing
  `ab6IterVec_succ_succ_succ_succ_succ_succ` step lemma and the imported
  `ab6GenericCoeff` (no need to redefine the coefficient vector in the
  vector file). Three negative coefficients (α₀, α₂, α₄) require explicit
  `neg_smul` rewrites before `abel` closes the rearrangement, mirroring the
  AB5 pattern.
- `Fin.val_zero / val_one / val_two` simp args at the iteration-bridge
  `simp only` site are still flagged as unused by the linter but match
  the AB5 reference and the cycle 428/431 hygiene rule (load-bearing across
  index normalization in adjacent code paths).

## Suggested next approach
- AB7 / AB8 are the next generic-bridge targets if Iserles §1.2 is to be
  carried further; both should mirror the AB5/AB6 pattern with negligible
  changes (longer window of 7 / 8 starting samples).
- The Aristotle AB6 scalar job (`93dd03f9...`) was still `IN_PROGRESS` at
  cycle close — once it completes its result can be archived as a sanity
  check of the manual proof.
- Consider extracting the repeating `neg_smul` + `abel` rearrangement in
  the residual / iteration bridges into a small helper lemma; the four
  scaffold instances (AB3, AB4, AB5, AB6) now share the same shape and
  could compress to ~15 lines each.
