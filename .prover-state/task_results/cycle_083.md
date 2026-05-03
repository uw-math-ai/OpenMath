# Cycle 083 Results

## Worked on
- Priority 0 (housekeeping): plan.md row for `lem:322A` updated to
  append the source-file pointer (the `[x]` marker was already
  correct — see "Discovery" below).
- Priority 1 (substantive): opened **Chapter 5** by formalizing
  `def:510A` (preconsistency vector for general linear methods) in
  a new file `OpenMath/Chapter5/Section510.lean`.

## Approach
1. Verified the planner's claim about `lem:322A` being stale in
   plan.md. It was *not* stale: `lem:322A` was already marked `[x]`
   and the global progress count `53 / 175` already included it.
   The only `plan.md` change needed for Priority 0 was appending
   `— OpenMath/Chapter3/Section322.lean` to the row, matching the
   convention used elsewhere (e.g. `thm:343A`, `def:310A`).
2. Created `OpenMath/Chapter5/` directory and
   `OpenMath/Chapter5/Section510.lean` containing:
   - `GeneralLinearMethod (s r : ℕ)` structure with four matrices
     `A : s×s`, `U : s×r`, `B : r×s`, `V : r×r` over `ℝ`.
   - `GeneralLinearMethod.IsPreconsistent` — predicate
     `∃ u, V *ᵥ u = u ∧ U *ᵥ u = (fun _ => 1)`.
   - `explicitEulerGLM : GeneralLinearMethod 1 1` —
     `A = !![0]`, `U = !![1]`, `B = !![1]`, `V = !![1]`.
   - `explicitEulerGLM_isPreconsistent` — non-vacuity witness using
     `u = (fun _ => 1)`. Proof closes via `funext i; fin_cases i;
     simp [explicitEulerGLM, Matrix.mulVec, dotProduct]`.
3. Added `OpenMath/Chapter5.lean` (re-exporting Section510) and
   appended `import OpenMath.Chapter5` to `OpenMath.lean`.
4. Verified compile: `lake env lean OpenMath/Chapter5/Section510.lean`
   passes with no errors. `lake build OpenMath.Chapter5.Section510`
   completes (1655/1655 jobs, 2.5s).
5. Axiom check on both new declarations:
   `[propext, Classical.choice, Quot.sound]` — standard Mathlib base.
6. Updated `extraction/formalization_data/lean_status.json` for
   `def:510A` (file, symbol, status="formalized"). Updated `plan.md`
   to mark `def:510A` `[x]` with file pointer and bump the global
   progress counter `53 / 175 → 54 / 175`.
7. Re-ran the stale-row sweep over `plan.md`: 0 stale rows;
   formalized count and `[x]` count are both 54. No further
   housekeeping needed this cycle.

## Result
SUCCESS — `def:510A` formalized with non-vacuity witness; all
status tracking consistent; clean axiom set; no regressions.

## Faithfulness check

**`GeneralLinearMethod` (new structure):**
- Entity ID: `def:510A` — textbook intro:
  > A general linear method `(A, U, B, V)` is 'preconsistent' if
  > there exists a vector `u` such that `V u = u`, `U u = 1`. The
  > vector `u` is the 'preconsistency vector'.
- The structure captures the four-matrix data exactly as Butcher
  presents it. The `(s, r)` index convention follows from the §510
  tableau presentation `[A | U; B | V]` (see also `def:520A`,
  `def:510B`). Pure data — no Prop fields — so no
  definition-smuggling risk.

**`GeneralLinearMethod.IsPreconsistent` (new def):**
- Entity ID: `def:510A` — Lean statement is the literal existential
  `∃ u, M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)`.
- Lean statement captures: **same content** as the textbook
  definition. The all-ones target `(fun _ => 1)` is the textbook
  `1` on the right of (510b).
- No extra hypotheses on `M`. No definition smuggling — this is a
  predicate on existence of `u`, not a stipulation that any specific
  `u` works.

**`explicitEulerGLM` (new def, non-vacuity witness):**
- Not a textbook entity — concrete witness required by CLAUDE.md
  rule "every new structure must have a witness in the same cycle".
- Encodes explicit Euler `y_{n+1} = y_n + h f(y_n)` with the
  trivial 1-stage / 1-value coefficients `(0, 1, 1, 1)`.

**`explicitEulerGLM_isPreconsistent` (new theorem):**
- Tautology check: conclusion `IsPreconsistent` is not a hypothesis.
- Identity check: proof constructs witness `fun _ => 1` and
  discharges two `Matrix.mulVec` equations by `simp`. Real content,
  not `exact h`.
- Hypothesis-strength check: hypothesis-free (no `M : ...`
  parameter); states a concrete fact about a concrete witness.

## Dead ends
- First simp set used the fully-qualified `Matrix.dotProduct`, which
  doesn't exist as a name (the function is just `dotProduct` in the
  `Matrix` namespace, exposed via `open Matrix`). Fixed by replacing
  `Matrix.dotProduct` with `dotProduct` in both `simp` calls. Also
  removed `Fin.sum_univ_one` from the `simp` argument list — it was
  never used (linter warned).

## Discovery
- **Planner stale-row claim was incorrect.** The cycle 083 strategy
  asserted `lem:322A` was marked `[ ]` in `plan.md` and that the
  progress counter needed to bump from 53 to 54 for that fix alone.
  In fact, `plan.md` line 73 already had `- [x] \`lem:322A\` …` and
  the count `53 / 175` already included `lem:322A`. The only
  Priority 0 fix needed was appending the file pointer; the count
  bump for this cycle is solely from `def:510A` (53 → 54).
- **`Matrix.dotProduct` is not a fully-qualified name.** `dotProduct`
  lives at the top level (`Mathlib/Data/Matrix/Basic.lean`) and is
  brought into scope by `open Matrix` for the `⬝ᵥ` notation, not
  for the bare name. When `simp`-unfolding `Matrix.mulVec`, use
  `dotProduct` (unprefixed) in the simp argument list.
- **`fin_cases i; simp [..., Matrix.mulVec, dotProduct]` is the
  canonical close** for `(matrix-literal *ᵥ vector) = vector`-style
  goals on `Fin 1` (and likely `Fin 2`, `Fin 3` too — to verify
  next cycle if `def:510B`/`def:510C` need it).

## Suggested next approach
Per the cycle-083 strategy's roadmap section, Chapter 5 §51x can
be cleared in 5-6 cycles:

- **Cycle 084**: `def:510C` (stable GLM — `‖V^n‖ ≤ C`). Depends only
  on `def:142A` (already done) and the cycle-083 GLM structure.
  Trivial wrapping. Add the matching witness on `explicitEulerGLM`.
- **Cycle 085**: `def:510B` (consistent GLM). Adds the extra
  hypothesis `B 1 + V v = u + v`.
- **Cycle 086+**: `def:512A` (convergent GLM) — analogous to the
  cycle-068 LMM `IsConvergent`.

Aristotle was not used this cycle (skipped per strategy — definitions
have no proof obligation, and the witness was a 4-line `simp`-close).
The next cluster (consistency/stability proofs in §51x and onwards)
will benefit from Aristotle batch-submission once the structures
are in place.
