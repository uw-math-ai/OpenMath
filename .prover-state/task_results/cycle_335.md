# Cycle 335 Results

## Worked on
* **P1 (Lean code)**: §344 Phase D.14 — three new symbols in
  `OpenMath/Chapter3/Section344.lean`:
  * `butcherLobattoIIIDirect_three : RKTableau 3` (`noncomputable def`).
  * Anonymous `example : butcherLobattoIIIDirect_three.SatisfiesB 4`
    (non-vacuity at order `p = 2s − 2 = 4`).
  * `butcherLobattoIIIDirect_three_satisfiesC : SatisfiesC 2`
    (`theorem`, the C(s − 1) certificate).
* **P2 (scoping doc)**: `.prover-state/issues/cycle_336_pivot_options.md`
  — 4-candidate menu for cycle 336's planner.

## Approach
* **Step 1 — Audit (P1.1)**: Read `extraction/raw_text/ch03.txt:5399–5405`.
  The printed Lobatto III s=3 table reads:
  ```
  0    0    0    0
  1    1    1
  2    4    4    0       ← c₁=1/2, A_{1,*} = (1/4, 1/4, 0)
  1    0    1    0       ← c₂=1, A_{2,*} = (0, 1, 0)
        1    2    1      ← b numerators
        6    3    6      ← b denominators
  ```
  Reads as `c = (0, 1/2, 1)`, `b = (1/6, 2/3, 1/6)`,
  `A = !![0, 0, 0; 1/4, 1/4, 0; 0, 1, 0]`. The printed values **agree
  exactly** with the C(2) + last-column-zero derivation predicted by
  the strategy. No audit divergence; ship.
* **Step 2 — Definition**: 4-line `noncomputable def` of
  `butcherLobattoIIIDirect_three` with literal A/b/c values.
* **Step 3 — `SatisfiesB 4` non-vacuity (`example`)**: 4-arm
  `interval_cases k` decomposed into explicit arms per cycle 327
  precedent (each `simp [..., Fin.sum_univ_three]; norm_num`). Paper-
  verified all 4 arms before writing — confirmed in docstring.
* **Step 4 — `SatisfiesC 2` certificate (`theorem`)**: Verbatim port
  of cycle 331's 4-arm `fin_cases i <;> interval_cases k <;> simp
  <;> norm_num` chain at `s = 2`, scaled to 9 arms at `s = 3` with
  one extra row + the same `Fin.sum_univ_three` simp lemma. Paper-
  verified all 9 arms before writing — confirmed in docstring.
* **P2 deliverable**: 4-candidate menu (`def:422B`, `thm:302A`,
  `thm:302B`, partial `thm:384A`) with JSON-sourced statements,
  dependency status, LOC estimates, and risk assessment. Default
  recommendation: candidate B (`thm:302A`) for clean single-cycle
  break of the §344 streak. ≤100 lines met (about 100 lines).

## Result
**SUCCESS** on both deliverables.

* `lake env lean OpenMath/Chapter3/Section344.lean` exits 0.
* `lake env lean OpenMath/Chapter3.lean` exits 0.
* `lake build OpenMath.Chapter3.Section344` exits 0; full project
  build 2803 jobs all green.
* Axiom check: both `butcherLobattoIIIDirect_three` and
  `butcherLobattoIIIDirect_three_satisfiesC` depend only on
  `[propext, Classical.choice, Quot.sound]` (Lean core).
* Sorry count remains 0 (66th consecutive clean cycle since the
  cycle 201 rollback).
* Single-shot tactic chain in `SatisfiesC 2`: all 9 arms closed
  uniformly by the same 4-tactic chain (`fin_cases i <;>
  interval_cases k <;> simp [..., Fin.sum_univ_three] <;> norm_num`)
  — no per-arm decomposition needed at s=3.

## Faithfulness check

### `butcherLobattoIIIDirect_three` (`noncomputable def`)
* Entity: portion of `thm:344A` (Butcher §344 Table 344(I), Lobatto
  III row at `s = 3`, printed table p. 226,
  `extraction/raw_text/ch03.txt:5399-5405`).
  > Lobatto III    (s = 3, p = 4),
  >                  0       0       0       0
  >                  1/2     1/4     1/4     0
  >                  1       0       1       0
  >                          1/6     2/3     1/6
* Lean statement captures: **same** as textbook.
  `c = ![0, 1/2, 1]`, `b = ![1/6, 2/3, 1/6]`,
  `A = !![0, 0, 0; 1/4, 1/4, 0; 0, 1, 0]` — literal transcription.
* No definition smuggling: direct `RKTableau` declaration with
  literal numeric values.

### `butcherLobattoIIIDirect_three_satisfiesC` (`theorem`)
* Statement: `butcherLobattoIIIDirect_three.SatisfiesC 2`, i.e. the
  `C(s − 1) = C(2)` collocation simplifying assumption — the
  Table 344(I) "Choice of A" defining property for the Lobatto III
  row (`ch03.txt:5221`).
* Lean statement captures: **same** content as the textbook's
  defining condition for the Lobatto III (unsuffixed) family.
* Tautology check: 9-arm rational-arithmetic system, not a
  hypothesis.
* Identity check: 4-tactic chain is genuine `norm_num` rational
  arithmetic, not `exact h`.
* Hypothesis strength: standard `SatisfiesC` `intro` pattern with
  `1 ≤ k ≤ 2`; no extra hypotheses.

### Anonymous `example : SatisfiesB 4`
* No `lean_status.json` update (anonymous example).
* No tautology / identity / strength concerns.

### `lean_status.json` and `plan.md`
* **Not touched** (per strategy: no entity status changes —
  `thm:344A` stays `[~]`).

## Dead ends
None. Both deliverables landed first-pass, no Aristotle needed.

The single-shot `fin_cases <;> interval_cases <;> simp <;> norm_num`
chain at s=3 closes within default heartbeats, validating the
strategy's prediction that cycle 331's s=2 template scales mechanically.

## Discovery
1. **Lobatto III s=3 printed table audit**: confirmed exact agreement
   with the C(2) + last-column-zero derivation (no Radau IA / cycle
   326-style divergence). The `C(s−1)` characterization is faithful
   at s=3 as predicted.

2. **9-arm uniform closure at s=3**: unlike `SatisfiesB 4` (which
   needed 4-arm decomposition per cycle 327 precedent), the
   `SatisfiesC 2` certificate at s=3 closes uniformly under the
   single 4-tactic `<;>` chain (no per-arm decomposition). At s=3
   the 9 SatisfiesC arms are uniformly mechanical because the
   `c = (0, 1/2, 1)` abscissae and `A_{*, 2} = 0` last-column-zero
   structure produce only `0`, `1/2`, `1`, `1/4`, `1/8` constants
   that `norm_num` handles trivially. Future §344 ladder revivals at
   higher s should attempt the same `<;>`-chain first before
   decomposing.

3. **Saturating closure milestone**: with this ship, the §344
   small-`s` direct-form ladder for the Lobatto III sub-family is
   complete (s=2: cycle 331; s=3: cycle 335). Combined with the
   IIIA (cycles 323/333), IIIB (cycle 327), and IIIC (cycle 330)
   small-s ladders, the §344 Lobatto family at s ∈ {2, 3} is now
   fully represented modulo IIIB at s=2 (which doesn't exist —
   Butcher line 5263).

## Suggested next approach
Cycle 336's planner: read `.prover-state/issues/cycle_336_pivot_options.md`
and pick a candidate. Default recommendation per the P2 doc:

* **First choice — candidate B (`thm:302A`)**: clean single-cycle ship
  in fresh territory. Leverages cycles 254–270 rooted-tree
  infrastructure. Prerequisite check first: grep
  `OpenMath/Chapter3/Section30*.lean` for `α`/`β`/`alphaCount`/
  `betaCount`/`labellings`. If both defined ⇒ direct equation ship;
  if either missing ⇒ Phase 1 definition + Phase 2 equations split.

* **Second choice — candidate D (`thm:384A`)**: closes the
  100+ cycle §381–§383 group-homomorphism infrastructure path.
  Prerequisite check: read `thm_381H_deferred.md` to determine if
  the §382 → §383 inclusion direction is single-cycle closeable or
  hits a deferred blocker.

* **Avoid candidate C (`thm:302B`)** unless cycle 336 is explicitly
  committed to a multi-cycle scoping doc (formal power-series
  infrastructure).

**Do NOT continue the §344 ladder.** The streak ends with cycle 335
as planned. No `butcherRadauIA_three`, no `butcherLobattoIIIA_four`,
no further parking-orbit ships — those belong to a future §344
revival cycle, not cycle 336.
