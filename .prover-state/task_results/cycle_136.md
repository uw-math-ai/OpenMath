# Cycle 136 Results

## Worked on
Negative non-vacuity witness for `def:520E` (A-stability):
`explicitEulerGLM_not_isAStable : ¬ explicitEulerGLM.IsAStable`.

This complements cycle 088's trivial positive witness
(`trivialZeroGLM_isAStable`) and cycle 135's substantive positive
witness (`implicitMidpointGLM_isAStable`). The negative witness
proves `IsAStable` is non-vacuous in *both* directions — a real
predicate that some GLMs satisfy and others refute.

## Approach
Direct proof following the planner's skeleton:

1. Specialize A-stability at `z := −3` (`Re(−3) = −3 ≤ 0`).
2. Reduce `M(−3) = !![1 + (−3)] = !![−2]` via the existing
   cycle 088 lemma `explicitEulerGLM_stabilityMatrix` and a single
   `ext + fin_cases + simp + ring` step.
3. Compute `‖M(−3)^k‖ = ‖!![(−2)]^k‖ = ‖−2‖^k = 2^k` using the
   cycle 135 private helpers `norm_pow_fin_one` and the identity
   `‖(−2 : ℂ)‖ = 2` (`norm_neg` + `Complex.norm_ofNat`).
4. Apply `pow_unbounded_of_one_lt C (1 < 2)` to obtain `k` with
   `C < 2^k`, contradicting the power-bound `‖M(−3)^k‖ ≤ C`.

No infrastructure additions required — fully reused cycle 088 +
cycle 135 helpers.

## Result
SUCCESS — theorem closed; `lake env lean OpenMath/Chapter5/Section520.lean`
returns no diagnostics; `lean_verify` confirms axioms are
`[propext, Classical.choice, Quot.sound]`.

No Aristotle submissions (manual proof was faster than the 30-minute
submit/sleep cycle for an ~30-LOC routine norm calculation, as the
planner anticipated).

## Faithfulness check

`explicitEulerGLM_not_isAStable`:

- This is the **negation** of `def:520E.IsAStable` applied to a
  specific GLM (`explicitEulerGLM`). There is no textbook entity
  ID for the negation itself — it is an operational non-vacuity
  fact, not a numbered Butcher result.
- The mathematical content matches the textbook fact (Butcher §520,
  example contrast at p. 419) that explicit Euler's stability
  region is the *closed unit disc centred at* `−1`. The witness
  `z = −3` lies strictly outside that disc (`|1 + (−3)| = 2 > 1`),
  with `Re(−3) = −3 ≤ 0`, so it certifies failure of A-stability.
- Lean statement captures: **same content** as the mathematical claim
  "`explicitEulerGLM` is not A-stable."
- Tautology check: conclusion is `¬ IsAStable`; not a hypothesis.
- Identity check: proof does real arithmetic work (matrix-norm
  reduction + Archimedean argument); not `exact h`/`id`.
- Hypothesis-strength check: theorem has no hypotheses.
- Absent-theorem check: no helper sorries or promised content.
- Definition smuggling check: `IsAStable` was defined faithfully in
  cycle 088 (`∀ z, Re(z) ≤ 0 → z ∈ stabilityRegion`); negating it
  for explicit Euler does not introduce smuggling.

## Dead ends
None. Primary plan proceeded without surprises; `pow_unbounded_of_one_lt`
exists under the planner-quoted name in
`Mathlib.Algebra.Order.Archimedean.Basic` with signature
`(x : R) (hy1 : 1 < y) : ∃ n, x < y ^ n` over `Archimedean` rings.

## Discovery
- `Complex.norm_ofNat` (in `Mathlib.Analysis.Complex.Norm`) closes
  `‖(2 : ℂ)‖ = 2` directly when written via `OfNat.ofNat`. Combined
  with `norm_neg`, the bridge `‖(−2 : ℂ)‖ = 2` becomes a one-liner
  after `show (-2 : ℂ) = -(2 : ℂ) from by ring`.
- The cycle 135 private helper trio (`fin_one_pow`, `norm_fin_one`,
  `norm_pow_fin_one`) is reusable for *both* positive A-stability
  proofs (Padé(1,1) ≤ 1) and negative ones (`(−2)^k → ∞`); the
  abstraction `‖!![a]^k‖ = ‖a‖^k` is the key bridge between matrix
  power-bound and scalar Archimedean reasoning.
- The `simp` tactic alone closes `((-3 : ℂ)).re ≤ 0` (after
  `Complex.neg_re` + `Complex.ofNat_re` reductions); no `norm_num`
  needed.

## Suggested next approach
Recommended for cycle 137 (in priority order):

1. **Negative L-stability witness `¬ explicitEulerGLM.IsLStable`**
   (planner backup B2). Now a one-line corollary: L-stability requires
   A-stability, so `fun h => explicitEulerGLM_not_isAStable h.1`
   closes it. This adds another non-vacuity-strengthening data point
   for `def:520F` at near-zero cost. Fast, single-cycle deliverable.

2. **Padé(1,1) order-2 stability for implicit midpoint**
   (planner backup B1). `implicitMidpointGLM.HasStabilityOrder 2`.
   Requires Taylor remainder for `Φ(exp z, z) = (1 − z/2) · (exp z
   − R(z))`. Heavier (~150 LOC) — needs holomorphic / big-O machinery
   not yet used in §520; would extend the order story for §520
   meaningfully.

3. **Substantive `def:530A` non-degenerate** definition (Chapter 5
   leaf, single-cycle scope) — would unblock the §530 line.

4. **`def:381F` P-equivalent** (Chapter 3, single-cycle scope,
   builds on `def:381E`). Cleanest entry point if shifting away from
   §520.

Of these, **(1)** is the planner-recommended natural follow-up:
single-cycle, leverages today's theorem directly, and matches the
recent cadence of one focused predicate-non-vacuity addition per
cycle.
