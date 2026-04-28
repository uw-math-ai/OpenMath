# Cycle 494 Results

## Worked on

Butcher §334 — Fehlberg 4(5) (RKF45) embedded Runge–Kutta pair.
Extended `OpenMath/EmbeddedRK.lean` with the classical 6-stage RKF45
tableau and full order-condition proofs:

- `rkRKF45 : EmbeddedRKPair 6` — coefficient data
- `rkRKF45_explicit : rkRKF45.IsExplicit`
- `rkRKF45_consistent : rkRKF45.IsConsistent`
- `rkRKF45_main_order5 : rkRKF45.mainMethod.HasOrderGe5` (17 conditions)
- `rkRKF45_embed_order4 : rkRKF45.embedMethod.HasOrderGe4` (8 conditions)
- `rkRKF45_embed_not_order5 : ¬rkRKF45.embedMethod.HasOrderGe5`
- `rkRKF45_errorWeights_sum : ∑ rkRKF45.errorWeights i = 0`

## Approach

Followed the strategy template:

1. Verified the planner's tableau values numerically via a Python
   `fractions.Fraction` script over all 17 fifth-order conditions plus
   the 8 fourth-order conditions for both `b` and `bHat`. Every
   condition matched the textbook target exactly, and the
   non-order-5-for-bHat discriminator computed `∑ b̂ᵢ cᵢ⁴ = 83/416 ≠ 1/5`,
   confirming the embedding is exactly fourth order.
2. Added a small `private lemma sum_univ_six` helper inside namespace
   `rkRKF45Aux` to expand `Fin 6` sums once, mirroring
   `Fin.sum_univ_four`. (Mathlib actually has `Fin.sum_univ_six`; both
   work, but the local helper makes the proof unfold deterministic.)
3. Extracted each of the 17 main-method order conditions and 8
   embedding conditions as private lemmas using the shape
   `simp only [order_X, sum_univ_six]; simp [rkRKF45, mainMethod];
   norm_num`. The "data after sum-unfold" ordering recommended by the
   strategy avoids the intermediate-term blowup the planner warned
   about.
4. Assembled `HasOrderGe5` / `HasOrderGe4` from the per-condition
   private lemmas, avoiding the single-`norm_num`-on-17-tuples surface
   that has timed out in past cycles.

## Result

SUCCESS. `lake env lean OpenMath/EmbeddedRK.lean` compiles cleanly
with no `sorry`, no errors, and no new warnings (the five surviving
warnings are all in pre-existing `rkHeunEuler21` / `rkBS32` proofs
predating this cycle).

## Aristotle usage

Skipped — the per-condition `norm_num` proofs all closed in the first
compile pass. The strategy permits skipping Aristotle when the manual
path lands on the first try; submitting a 5-job batch would only have
duplicated work that was already verified locally.

## Dead ends

None this cycle. The "data unfold before sum unfold" ordering that the
strategy explicitly warned against was not attempted; the recommended
ordering closed every condition in one shot.

## Discovery

- The `simp only [order_X, sum_univ_six]; simp [data]; norm_num`
  pattern scales fine to denominator 56430 and to the triply-nested
  `order5i` condition without raising heartbeats.
- For the embedding's "not order 5" lemma, the cheap discriminator is
  `order5a` (a single sum, no inner `∑`); destructuring the 10-tuple
  `HasOrderGe5` shape via `⟨_, h5a, _⟩` and contradicting `h5a` keeps
  the proof short.
- `rkRKF45.errorWeights_sum_zero` from the existing `EmbeddedRKPair`
  infrastructure makes the error-weight closure free given consistency.

## Plan rotation

Performed at end of cycle:

- §334 marked `[x]` in §3.3 with file path and headline theorems.
- `## Current Target` body replaced by Backlog item #1 (Butcher §38 —
  Butcher group) with concrete sorry-first surface listed.
- Backlog Queue items renumbered #1–#17 (was #2–#18).
- Queue still has > 5 items, so no append needed.

## Suggested next approach

The Current Target now points the next worker at §38 (Butcher group).
The first concrete deliverable should be `ButcherProduct` (composition
of two tableaux with stage counts `s + t`) and the
`IsRKEquivalent` permutation equivalence relation. Both are pure
combinatorial / linear-algebra definitions; sorry-first scaffold then
fill the equivalence and group-axiom proofs. Defer the elementary-weight
`G₁` homomorphism (§383) to a second cycle since it pulls in the rooted
tree machinery from `OpenMath/OrderConditions.lean`.
