# Cycle 117 Results

## Worked on
- Housekeeping for cycle 116 completions in `plan.md` and `extraction/formalization_data/lean_status.json`
- `OpenMath/ANStability.lean`: added DJ-reducibility infrastructure (`IsDJReducible`, `IsDJIrreducible`) and proved Corollary 356D (`cor_356D`)
- Aristotle follow-up: checked the two carried-over BN-stability result directories and submitted four fresh cycle-117 jobs for the new Section 356 work

## Approach
- Read `.prover-state/strategy.md` and incorporated the required stale metadata fixes first.
- Checked Aristotle result directories `29f1dee7-49d9-4808-a25d-8f25db85adec` and `8184d812-f26d-4a1c-a8e3-63bc4051978b`.
  Their payloads targeted an older `BNStability.lean` / stub `StiffEquations.lean` state and were not directly applicable to the current tree, so no code was merged from them.
- Added the Section 356 sorry-first skeleton to `OpenMath/ANStability.lean`, compiled it, and submitted the new work to Aristotle:
  `bc11cf00-ba4d-4e69-aa4a-fa44fe5f3704`
  `182a4de8-31a2-47d6-a803-a3a4951b6fb9`
  `83293abc-c2c1-4632-a2b4-c5cfceb29804`
  `a23bb69f-a475-4e0f-9ff4-cb639ea894b0`
- Proved the helper lemmas manually:
  `algStabMatrix_diag_eq_zero_of_weight_zero`
  `algStabMatrix_col_eq_zero_of_diag_zero`
- Proved `cor_356D` by taking the zero-weight set `S₀ = {j | b j = 0}`, showing it is a DJ reduction whenever any weight vanishes, and contradicting DJ-irreducibility.

## Result
SUCCESS — `OpenMath/ANStability.lean` compiles with the new Section 356 results and no new sorrys.

- `plan.md` now marks 356C and 357C complete and advances the “Current Target” section past the stale cycle-116 goals.
- `lean_status.json` now marks `thm:353A`, `thm:356C`, `def:356B`, `cor:356D`, and `thm:357C` as done.
- `OpenMath/ANStability.lean` now contains the DJ-reducibility definition and Corollary 356D.
- Aristotle submissions `bc11cf00`, `182a4de8`, `83293abc`, and `a23bb69f` all completed after the mandatory 30-minute wait.
  I inspected the file-level result for `bc11cf00`; it used the same core PSD/zero-column argument as the manual proof, but the archive also included a stale replacement `OpenMath/StiffEquations.lean`, so I kept the already-compiling local proof instead of merging the Aristotle tree.

## Dead ends
- The inherited Aristotle result directories for BN-stability were obsolete relative to the current codebase and would have regressed `OpenMath/StiffEquations.lean` if merged blindly.

## Discovery
- For a PSD algebraic-stability matrix `M`, the condition `Mⱼⱼ = 0` forces the entire `j`th column to vanish. A two-coordinate test vector with entries
  `1` at `i` and `-(Mᵢᵢ + 1)/(2 Mᵢⱼ)` at `j`
  gives a compact contradiction when `Mᵢⱼ ≠ 0`.
- The exact `def:356B` extraction allows the deleted-stage set `S₀` to be all stages, so the reducibility argument for zero weights also covers the one-stage all-zero-weight edge case.

## Suggested next approach
- After harvesting the cycle-117 Aristotle jobs, continue Chapter 3 in the order-star / Ehle-barrier direction from `OpenMath/OrderStars.lean`.
- Keep `lean_status.json` synchronized whenever a theorem is closed; several stale entries had accumulated and would have misdirected future planning.
