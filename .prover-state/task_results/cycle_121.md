# Cycle 121 Results

## Worked on
- `OpenMath/ReflectedMethods.lean`
- Theorem 343A / 343B reflected-method setup
- Aristotle batch for reflected-method transfer lemmas

## Approach
- Read `.prover-state/strategy.md`, `plan.md`, and the mandatory Aristotle result directory `7a7e98b7-8ada-4f35-8a35-c0aa211f67e1` first.
- Confirmed the planner note was correct: the cycle-119 Aristotle bundle is redundant with existing `OpenMath/OrderStars.lean`, so I did not merge it.
- Added a new file `OpenMath/ReflectedMethods.lean` with:
  - `ButcherTableau.reflect`
  - a local `[ext]` theorem for `ButcherTableau`
  - proved lemmas `reflect_reflect`, `reflect_order1`, `reflect_rowSum`, `reflect_consistent`
  - a concrete reflected-tableau check `rkEuler_reflect_eq_implicitEuler`
  - theorem skeletons for reflected `B/C/D/E` transfer
- Restored local mathlib cache support by rerunning `lake exe cache get` with
  `LEAN_CC=/usr/bin/gcc` and `LIBRARY_PATH=/tmp/lean4-toolchain/lib:...`, then verified:
  `lake env lean OpenMath/ReflectedMethods.lean`
- Created five standalone Aristotle job files under
  `.prover-state/aristotle/cycle_121_reflected/` and submitted them in batch.
- Explored a local manual proof route for `B/C/D` using scratch Lean proofs of two helper identities:
  - alternating reciprocal binomial sum
  - alternating reciprocal binomial sum with an extra `x^(m+1)` factor
- The scratch proofs worked in `lean_run_code`, but the transcription into
  `OpenMath/ReflectedMethods.lean` ran into notation/transcription issues. I reverted that partial
  attempt so the source file stayed in a stable sorry-first compiling state.

## Result
- PARTIAL SUCCESS.
- `OpenMath/ReflectedMethods.lean` now exists and compiles with 4 focused `sorry`s:
  - `reflect_satisfiesB`
  - `reflect_satisfiesC`
  - `reflect_satisfiesD`
  - `reflect_satisfiesE`
- The foundational reflected-method infrastructure is now in the repo and ready for proof filling.
- Aristotle submissions:
  - `77e277e7-4747-4d28-b08e-702c6533281d` (`01_reflect_reflect.lean`) → `COMPLETE_WITH_ERRORS`
  - `4928f1e9-ad88-460a-9656-b64c3eb1ce58` (`02_reflect_satisfiesB.lean`) → `IN_PROGRESS` (12%)
  - `0384c983-e3c1-4eed-8dbf-e97e6d4db1f3` (`03_reflect_satisfiesC.lean`) → `IN_PROGRESS` (9%)
  - `1e6ea557-8273-475e-99a0-e94360593088` (`04_reflect_satisfiesD.lean`) → `IN_PROGRESS` (7%)
  - `9cc99ed3-e6ac-4582-8edb-fe07c5a30a01` (`05_reflect_satisfiesE.lean`) → `IN_PROGRESS` (10%)

## Dead ends
- The literal equalities
  `rkGaussLegendre2.reflect = rkGaussLegendre2` and
  `rkLobattoIIIA3.reflect = rkLobattoIIIB3`
  are false with the repo’s current stage ordering, because reflection reverses the node order.
  I dropped those exact statements instead of forcing incorrect theorems.
- A local manual proof for `B/C/D` was found in scratch code, but direct transcription into the
  repo file hit parser / rewriting friction around nested finite sums and `add_pow` expansions.
  The algebra is right; the blocker is Lean transcription, not the mathematics.

## Discovery
- In this environment, `lake exe cache get` works once `LEAN_CC=/usr/bin/gcc` is exported.
  The earlier failure mode came from the bundled `/tmp/lean4-toolchain/bin/clang`.
- The key reflected-method helper identities are simple enough for Lean to prove by induction in
  scratch mode:
  - `∑ (-1)^m * choose n m / (m+1) = 1/(n+1)`
  - `∑ (-1)^m * choose n m * x^(m+1)/(m+1) = (1 - (1-x)^(n+1))/(n+1)`
- Those two identities should be enough to close `reflect_satisfiesB`, `reflect_satisfiesC`,
  and `reflect_satisfiesD`; only `reflect_satisfiesE` still looks worth leaving to Aristotle.

## Suggested next approach
- Harvest the four in-progress Aristotle projects once they finish.
- For manual completion, reintroduce the scratch-proven helper lemmas into
  `OpenMath/ReflectedMethods.lean` one at a time, likely using explicit `Finset.sum` forms rather
  than the nested `∑ m in ...` notation that caused the transcription problems.
- After `B/C/D` are in place, leave only `reflect_satisfiesE` for Aristotle or a separate helper-lemma decomposition.
