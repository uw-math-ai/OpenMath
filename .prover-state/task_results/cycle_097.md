# Cycle 097 Results

## Worked on
- Housekeeping in `extraction/formalization_data/lean_status.json`
- Definition of the simplifying assumption `E(η,ζ)` in `OpenMath/Collocation.lean`
- Matrix-algebra subset of Theorem 342C

## Approach
- Verified the exact `E(η,ζ)` formula from the extraction before coding:
  equation `(321c)` is
  `∑ i, ∑ j, b_i c_i^(k-1) a_ij c_j^(l-1) = 1 / (l * (k + l))`.
- Added `ButcherTableau.SatisfiesE`.
- Wrote the four theorem stubs from the planner strategy and verified the sorry-first file
  compiled with `lake env lean OpenMath/Collocation.lean`.
- Submitted the file to Aristotle with prompt scoped to the four new lemmas.
- Manually proved the forward implications:
  `SatisfiesE_of_B_C` and `SatisfiesE_of_B_D`.
- Removed the unproved converse stubs so the file returned to sorry-free state.

## Result
- SUCCESS (partial): `SatisfiesE` is now formalized, and two of the four matrix-algebra
  implications from Theorem 342C are proved in `OpenMath/Collocation.lean`.
- SUCCESS: `lean_status.json` updated for `def:110A`, `thm:110C`, `thm:212A`, `thm:213A`,
  and `thm:342C`.
- SUCCESS: `plan.md` updated to reflect partial `342C` progress.
- FAILED (remaining work): the converse implications
  `B(2s) ∧ E(s,s) ⇒ C(s)` and `B(2s) ∧ E(s,s) ⇒ D(s)` are not yet formalized.

## Dead ends
- The textbook converse proof uses a non-singular weighted Vandermonde matrix.
  That non-singularity is not currently available from the present `ButcherTableau` API.
- A polynomial-orthogonality alternative also stalled: from `B(2s)` and `E(s,s)` one can force
  vanishing weighted moments, but turning that into pointwise stage identities still needs
  distinct nodes / nonzero weights or an equivalent injectivity theorem.
- Aristotle did not produce usable output during this cycle; the submitted project remained
  queued when checked.

## Discovery
- The extraction for theorem `343B` gives the clean polynomial interpretation of `E(η,ζ)`:
  `∑ i,j b_i P(c_i) a_ij Q(c_j) = ∫_0^1 P(x) (∫_0^x Q(v) dv) dx`.
- The forward `342C` implications are genuinely easy finite-sum manipulations once `E` is stated
  with the exact `321c` normalization.
- The converse directions appear to require a reusable Gaussian quadrature uniqueness lemma, not
  just more local algebra.

## Suggested next approach
- Formalize a lemma package deriving distinct nodes / weighted Vandermonde injectivity from
  `B(2s)` for `s` stages, then revisit the converse `342C` implications.
- If that is too large for one cycle, introduce an intermediate theorem with an explicit
  `Function.Injective t.c` hypothesis and prove the converse under that assumption first.
- Re-check Aristotle project `c776d9e1-9ced-477d-96b5-d00f54e42908`; if it eventually completes,
  harvest any partial proof ideas for the converse directions.
