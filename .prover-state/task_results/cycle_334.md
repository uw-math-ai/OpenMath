# Cycle 334 Results

## Worked on
§344 Phase D.13 follow-up: `SatisfiesC 3` certificate for the
cycle-333 collocation-assembled `butcherLobattoIIIA_three` tableau.
Per the planner's option 2: continue the §344 ladder one more cycle
with a low-risk small ship before cycle 335 pivots.

New symbol introduced (1 total, axiom-clean
`[propext, Classical.choice, Quot.sound]`):

- `butcherLobattoIIIA_three_satisfiesC : butcherLobattoIIIA_three.SatisfiesC 3`
  (theorem)

## Approach
Verbatim port of cycle 329's `butcherRadauIDirect_two.SatisfiesC 2`
recipe scaled from 2 stages × 2 exponents (4 arms) to 3 stages × 3
exponents (9 arms):

1. Route via cycle 333's coincidence theorem to the direct form:
   `rw [butcherLobattoIIIA_three_eq_direct]`.
2. Introduce the four bound variables: `intro i k h1 hk`.
3. `fin_cases i <;> interval_cases k <;>
    simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three] <;>
    norm_num` — the planner's primary recipe, which closes all 9
   arms via a single 4-tactic chain.

Paper-verification ahead of writing the Lean code (per strategy §C):

* Row 0 (`c_0 = 0`): all three arms reduce to `0 = 0`.
* Row 1 (`c_1 = 1/2`, A-row `(5/24, 1/3, -1/24)`): arms close to
  `1/2 = 1/2`, `1/8 = 1/8`, `1/24 = 1/24`.
* Row 2 (`c_2 = 1`, A-row `(1/6, 2/3, 1/6)`): arms close to
  `1 = 1`, `1/2 = 1/2`, `1/3 = 1/3`.

All 9 arms paper-verified before writing the Lean proof — no
arithmetic risk.

## Result
SUCCESS — `lake env lean OpenMath/Chapter3/Section344.lean` and
`lake env lean OpenMath/Chapter3.lean` exit 0; sorry count in
Section344.lean = 0; the 4-tactic chain
(`fin_cases <;> interval_cases <;> simp <;> norm_num`) closed all 9
arms without needing the §C R1 fallback decomposition. Axiom-clean
verified: `OpenMath.Chapter3.Section344.butcherLobattoIIIA_three_satisfiesC`
depends on `[propext, Classical.choice, Quot.sound]`. Section344.lean
LOC: 2572 → 2587 (+15, on the strategy's ~10 LOC estimate +
docstring).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `butcherLobattoIIIA_three_satisfiesC` (theorem)
- Entity ID: `thm:344A` (Butcher §344 Lobatto IIIA C(s) classification
  row, Table 344(I) p. 226). The C(s) condition is Butcher §321
  equation (321b):
  > `∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k / k`, for `1 ≤ k ≤ s` and all stages `i`.

  At `s = 3`, the C(s) condition is the 9-arm system asserted by
  Butcher Table 344(I)'s "Lobatto IIIA C(s)" row label.
- Lean statement captures: **same content**. The deliverable is
  exactly the cycle 321 `SatisfiesC` predicate applied to the
  cycle 333 `butcherLobattoIIIA_three` tableau at `ξ = 3`. The proof
  routes via cycle 333's coincidence theorem to the direct Simpson's-
  rule form, then discharges the 9 concrete identities by
  `fin_cases + interval_cases + simp + norm_num`.

Tautology / identity / hypothesis-strength / absent-theorem checks
per CLAUDE.md:

* **Tautology check**: conclusion is the C(3) predicate, a
  9-equation system, not a hypothesis. Pass.
* **Identity check**: proof is a 9-arm rational-arithmetic
  computation via a 4-tactic chain. Non-vacuous. Pass.
* **Hypothesis strength check**: no hypotheses beyond the standard
  `SatisfiesC` `intro` pattern. Pass.
* **Absent theorem check**: no promised content omitted. Pass.

No new `def`, no new `class` or `structure`. No `Prop` fields with
ambiguous hypothesis-vs-conclusion status.

## Dead ends
None. The 4-tactic chain closed all 9 arms on first attempt — the
§C R1 fallback (explicit nested `fin_cases` per row) was not
required. The §C R2 / R4 risks (row-0 `0^k / k` and `k - 1` Nat-sub
edge cases) were also handled silently by the `simp` set without
needing manual `pow_zero` / `zero_pow` augmentation. R3 (rational
arithmetic) closed cleanly by `norm_num`.

## Discovery
- The same `fin_cases i <;> interval_cases k <;>
  simp [<direct tableau>, Fin.sum_univ_three] <;> norm_num` chain
  that cycles 322/323/324/325/329/332/333 used at 4 arms now scales
  cleanly to 9 arms at `s = 3` without performance degradation or
  arithmetic noise. The chain is fully mechanical at this scale.
- The row-0 `0^k / k` case (where `c_i = 0` makes both sides `0`)
  is handled silently by the default `simp` set when `k ≥ 1`.
  Cycle 327's "mechanical-template" hypothesis is now validated
  across **eight** consecutive C(s)-coincidence / direct-form /
  SatisfiesC ships (322 → 334).

## Suggested next approach
Cycle 335 should pivot per the cycle-333 §G outlook. Candidates,
ranked by single-cycle feasibility:

1. **`def:422B` (underlying one-step method, §422)** — needs a
   scoping cycle first (cycle 222's `def:381B` quotient-group
   machinery is adjacent but not directly applicable). Write a
   Phase-decomposition issue file *before* writing Lean.

2. **`def:442A` (principal sheet, §442)** — Riemann surfaces +
   complex analysis. Multi-cycle; needs scoping doc + Mathlib
   audit (complex-analytic infrastructure may be incomplete).

3. **`thm:302A` / `thm:302B` (rooted-tree generating function /
   enumerative identity)** — uses cycles 254–270 rooted-tree
   infrastructure; `thm:302A` may be single-cycle if enumerative.

4. **Continue §344 ladder one more cycle**: e.g.
   `butcherLobattoIIIDirect_three` (Lobatto III C(s−1) variant at
   `s = 3`, mechanical extension of cycle 331's `s = 2` ship) —
   valuable only as a safe small-cycle parking-orbit deliverable
   if cycle 335 wants to scope a multi-cycle pivot in parallel.

The cycle-335 planner should pick **one** target and commit to a
Phase-decomposition / scoping document if multi-cycle. The 18-cycle
§344 streak (cycles 322–334) demonstrates that the mechanical-
template rhythm works; cycle 335 is the moment to break it.
