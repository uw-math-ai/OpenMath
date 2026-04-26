# Cycle 454 Results

## Worked on
AM8 vector quantitative convergence — Step 1 (tenth-order vector Taylor
ladder) and Step 2 partial scaffold (trajectory + LTE + residual algebra
helpers).

## Approach
Per strategy, started with the prerequisite tenth-order vector Taylor
ladder in `OpenMath/LMMAM7VectorConvergence.lean`, then created
`OpenMath/LMMAM8VectorConvergence.lean` with the AM8 vector trajectory,
residual definition, LTE-equality lemma, and the two pure-algebra residual
helpers (the most kernel-budget-friendly pieces).

Aristotle bundles from cycle 453 were already triaged by the strategy as
non-transplantable; I did not rebase any of them onto live files this cycle
(see "Aristotle disposition" below).

## Result
SUCCESS on Step 1 (prerequisite ladder, the cycle 453 blocker resolution)
and PARTIAL on Step 2 (AM8 vector scaffold with two algebra helpers
landed; remaining chain scoped to next cycle).

### Step 1 — tenth-order vector Taylor ladder (LANDED, public)

Added to `OpenMath/LMMAM7VectorConvergence.lean`:

- `iteratedDeriv_ten_bounded_on_Icc_vec`
- `y_tenth_order_taylor_remainder_vec` (interval-integral approach,
  bound `M / 3628800 * r ^ 10`, recurses through
  `y_ninth_order_taylor_remainder_vec` on `deriv y`)
- `derivY_ninth_order_taylor_remainder_vec` (reuses
  `y_ninth_order_taylor_remainder_vec` on `deriv y`, bound
  `M / 362880 * r ^ 9`)

These are public theorems, mirroring the cycle-453 promotion of the
ninth-order ladder to public.  This unblocks the AM8 vector pointwise
residual port.

### Step 2 — AM8 vector scaffold (PARTIAL)

Created `OpenMath/LMMAM8VectorConvergence.lean` with:

- `LMM.IsAM8TrajectoryVec` (vector trajectory predicate with all 9 AM8
  weights and `•`-style implicit recurrence)
- `LMM.am8VecResidual` (textbook ten-step vector residual definition)
- `LMM.am8Vec_localTruncationError_eq` (`rfl`-shape)
- `LMM.am8Vec_residual_alg_identity` (private; pure module identity
  rewriting the AM8 residual into a ten-term abstract Taylor split,
  proved by `simp only [smul_sub, smul_add, smul_smul]; module`)
- `LMM.am8Vec_residual_bound_alg_identity` (private; pure ring identity
  collapsing the ten-term bound to
  `(4555920744497 / 6858432000 : ℝ) * M * h ^ 10 ≈ 664.28 * M * h ^ 10`,
  matching the AM8 scalar exact coefficient from cycle 452)

Both files compile cleanly under `lake env lean`.

## Aristotle disposition
All three cycle-453 COMPLETE bundles were already triaged in the strategy
as non-transplantable:

- `44ac525a-…` (AM8 vector scaffold): targets stub `import Mathlib`
  scaffold, not the live tracked file.  Used as reference confirming the
  LTE rfl-shape — that shape was ported to the live file this cycle.
- `af2bbcf1-…` (AdamsMoulton8 LTE): standalone stub project, but the live
  AM8 scalar LTE is already closed (cycle 452).  Discarded.
- `29ee838e-…` (AB7 vector): targets already-closed
  `LMMAB7VectorConvergence` (cycle 451).  Discarded.

No new Aristotle batch was submitted this cycle.  Reasoning: with the
algebra helpers already landed by direct `module` / `ring` proofs, the
remaining sub-targets (one-step Lipschitz, ten-term residual triangle,
combine, pointwise/local residual, global error) are large mechanical
ports of `LMMAM7VectorConvergence` plus `LMMAM8Convergence` rather than
isolated goals Aristotle solves quickly.  The cycle 453 experience
suggests Aristotle is unlikely to land transplantable proofs against
the live OpenMath tree on these large multi-hundred-line residual
chains.  Instead, focus the next cycle's manual budget on the chain
itself.

## Dead ends
None this cycle.  The Step 1 ladder mirror was direct (one order up from
the cycle-453 ninth-order ladder) and compiled on first attempt.  The
two algebra helpers also compiled on first attempt (`module` for the
AM8 vector residual identity, `ring` for the bound identity).

## Discovery
The AM7 vector residual abstract split uses 9 letter labels
`A B C D F G J K R` (skipping `E` for the type variable).  For AM8 vector,
the natural extension to 10 labels is `A B C D F G I J K L` (skipping
`E` and `H` to avoid clashes with the type variable and the step-size
variable `h`).

The pure-ring `am8Vec_residual_bound_alg_identity` produced exactly
`4555920744497 / 6858432000` matching cycle 452's AM8 scalar exact
coefficient — confirming that the AM8 vector residual algebra is
genuinely the AM8 scalar algebra reinterpreted with `•`, and the
slackening to `665` will be identical at the vector level.

## Suggested next approach
Next cycle should land the remaining AM8 vector chain in this order
(each step is mechanical given the AM7 vector and AM8 scalar templates):

1. `am8Vec_one_step_lipschitz` — direct mirror of
   `LMMAM7VectorConvergence.am7Vec_one_step_lipschitz` with all 9 AM8
   weights swapped in.  Proof structure identical: nine `set`
   abbreviations for `yseq`/`y` values, the step rewrite, the LTE rewrite,
   the `halg` algebraic identity (closed by `ring`), nine Lipschitz
   absolute-value bounds, an 11-term triangle inequality, and a final
   `linarith` combine.
2. `am8Vec_one_step_error_pair_bound` — slacken to growth `15·L` and
   residual coefficient `2`, after dividing by the implicit factor
   `1 - (1070017/3628800)·hL`.  Use the cycle 452 pivotal identity
   `(hL/3628800)·(28877438 - 16050255·hL) ≥ 0` plus `linarith`.
3. `am8Vec_residual_ten_term_triangle` — norm triangle over the ten
   chunks `A - B - α₁•C - α₂•D + α₃•F - α₄•G + α₅•I - α₆•J + α₇•K
   - α₈•L + α₉•R`, mirroring AM7 vector's nine-term version.  Each `α_i`
   is `(weight_i * h / 3628800)`.
4. `am8Vec_residual_combine` — slacken `4555920744497/6858432000` to `665`
   via `linarith` on `M ≥ 0`, `h ^ 10 ≥ 0`, and `665 - 4555920744497/6858432000 ≥ 0`.
   Keep this lemma separate from `am8Vec_pointwise_residual_bound` to avoid
   kernel `whnf` heartbeat exhaustion (cycle 444 pattern).
5. `am8Vec_pointwise_residual_bound` — assemble the ten Taylor remainders
   plus the four algebra helpers.  After the ten `set` abbreviations for
   the ten Taylor chunks, **call `clear_value`** to erase the let-bindings
   (cycle 450/451 lesson — load-bearing for AB7 and required at AM7/AM8
   sized contexts).  Do NOT add dead `_nn` nonneg lines (cycle 444
   discovery — they cause whnf timeout at 23+ sets).
6. `am8Vec_local_residual_bound` — uniform horizon-local bound, mirroring
   AM7 vector's structure verbatim with `T` and the eight `(N+k)·h ≤ T`
   side conditions (k=1..7) plus a new `k=8` condition.
7. `am8Vec_global_error_bound` — headline.  Route through
   `lmm_error_bound_from_local_truncation` at `p = 9` (so the headline
   error term is `K · h ^ 8` after the loose-bound stripping that AM7
   vector uses for its `K · h ^ 8` of an order-9 method).  Use `15 * L`
   as the Gronwall growth constant, eight `e_k ≤ ε₀` initial-window
   hypotheses (k=0..7), and the same eight base cases plus
   `N' + 8` Gronwall step that AM7 vector uses with seven base cases plus
   `N' + 7`.

The fallback BDF3 chain (`OpenMath/LMMBDF3Convergence.lean`) was not
touched this cycle since Step 1 closed and the manual budget went to the
two AM8 vector algebra helpers.  If the next cycle hits a wall on the AM8
vector chain, the BDF3 three-window Lyapunov recurrence is still the
recommended fallback.

## File size status
- `LMMAM7VectorConvergence.lean`: 2705 lines (was 2236; +469 for the
  three tenth-order helpers)
- `LMMAM8VectorConvergence.lean`: 204 lines (new)
- `LMMBDF3Convergence.lean`: 254 lines (unchanged)

All under the 3000-line cap.
