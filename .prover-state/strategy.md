# Cycle 335 strategy

## Context

Cycle 334 shipped `butcherLobattoIIIA_three_satisfiesC` (C(3) certificate
for the s=3 Lobatto IIIA tableau) axiom-clean, closing 18 consecutive
§344 cycles (322–334). Sorry count remains 0; tautology scanner clean;
no Aristotle results pending. The cycle 334 worker recommended cycle
335 break the §344 streak and pivot to a fresh entity, while listing
`butcherLobattoIIIDirect_three` as a safe parking-orbit option **if
the cycle wants to pair the §344 ship with a pivot scoping doc**.

## Target

**Primary (P1, code ship)**: Ship `butcherLobattoIIIDirect_three :
RKTableau 3` (unsuffixed Lobatto III family, C(s−1) + last-column-zero
variant per Butcher Table 344(I) ch03.txt:5221 + printed table at
ch03.txt:5372–5378) plus:

* `SatisfiesB 4` certificate (Lobatto III at s=3 achieves classical
  order `p = 2s − 2 = 4`, so B(4) is maximal — mechanical 4-arm
  `interval_cases k` + `simp + norm_num`).
* `butcherLobattoIIIDirect_three_satisfiesC : SatisfiesC 2` certificate
  (the C(s−1) = C(2) defining condition — cycle 331's 4-arm recipe at
  s=2 scaled to 9 arms at s=3, mechanical
  `fin_cases i <;> interval_cases k <;> simp [..., Fin.sum_univ_three]
  <;> norm_num`).

**Secondary (P2, scoping doc only)**: After P1 ships, write a brief
scoping note at `.prover-state/issues/cycle_336_pivot_options.md`
enumerating 3–4 fresh-entity candidates for cycle 336+ with their JSON
statements, dependency status, and rough LOC estimates. Goal: give
cycle 336's planner a head start on choosing the §344-breaking pivot
target. Do **NOT** scope deeply — this is a 1-page menu, not a
multi-phase plan.

## Why this target

1. **Mechanical safety**: The §344 D-ladder has shipped 13 consecutive
   axiom-clean cycles (322–334). The cycle-331 template for
   `butcherLobattoIIIDirect_two` (C(s−1) variant) is verbatim portable
   to s=3 with one extra row + one extra `Fin.sum_univ_three` simp
   lemma. Risk of stall is near-zero.

2. **Breaks the streak partially**: Pairing the §344 ship with a P2
   scoping doc moves cycle 336+ off the §344 path explicitly. Cycle
   336 then ships the substantive pivot (chosen from the P2 menu).

3. **Lobatto III saturation at s=3**: With this ship, the §344 Lobatto
   family has all three small-s ladders represented:
   * IIIA: cycle 323 (s=2) + cycle 333 (s=3)
   * IIIB: cycle 327 (s=3 only — does not exist at s=2)
   * IIIC: cycle 330 (s=2)
   * III: cycle 331 (s=2), **cycle 335 (s=3)** ← saturating
   Clean closure milestone for the §344 small-s direct-form ladder.

## Approach

### P1 — `butcherLobattoIIIDirect_three`

**Step 1 (audit-first, MANDATORY, ~10 min)**: Read
`extraction/raw_text/ch03.txt` around lines 5372–5378 (the printed
Lobatto III tables) to verify the printed A-matrix at s=3.

The C(s−1) + last-column-zero derivation forces (uniquely under
those constraints + Lobatto quadrature b=(1/6, 2/3, 1/6),
c=(0, 1/2, 1)):

```
A = !![ 0  ,  0  , 0 ;
       1/4 , 1/4 , 0 ;
        0  ,  1  , 0 ]
```

(Derivation: from `A i 2 = 0` and `C(2)` at k=1 / k=2, row 0 = (0,0,0),
row 1 = (1/4, 1/4, 0), row 2 = (0, 1, 0).)

If the printed table at ch03.txt:5372–5378 agrees with this derivation
⇒ proceed to Step 2. If it disagrees ⇒ **STOP, file
`.prover-state/issues/lobatto_iii_three_audit.md` documenting the
divergence**, then ship the printed-table values (per cycle 326's
Radau IA precedent) — in that branch the `SatisfiesC 2` claim may
not hold and should be replaced with whatever the printed values
support (typically `SatisfiesC 1` for "C(s−1) for s=3" if the
printed table doesn't satisfy C(2)).

**Step 2 (definition, ~10 LOC)**: Insert immediately after cycle 334's
`butcherLobattoIIIA_three_satisfiesC` in `Section344.lean`:

```lean
noncomputable def butcherLobattoIIIDirect_three : RKTableau 3 where
  A := !![0, 0, 0; 1/4, 1/4, 0; 0, 1, 0]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]
```

**Step 3 (`SatisfiesB 4` non-vacuity, ~10 LOC)**: 4-arm
`interval_cases k` close. Paper-verify each arm before writing:

* k=1: `∑ b_i = 1/6 + 2/3 + 1/6 = 1`. RHS = `1/1`. ✓
* k=2: `∑ b_i · c_i = 0 + (2/3)(1/2) + (1/6)(1) = 1/3 + 1/6 = 1/2`.
  RHS = `1/2`. ✓
* k=3: `∑ b_i · c_i² = 0 + (2/3)(1/4) + (1/6)(1) = 1/6 + 1/6 = 1/3`.
  RHS = `1/3`. ✓
* k=4: `∑ b_i · c_i³ = 0 + (2/3)(1/8) + (1/6)(1) = 1/12 + 1/6 = 1/4`.
  RHS = `1/4`. ✓

Recipe:

```lean
example : butcherLobattoIIIDirect_three.SatisfiesB 4 := by
  intro k h1 hk
  interval_cases k <;>
    simp [butcherLobattoIIIDirect_three, Fin.sum_univ_three] <;>
    norm_num
```

If the 4-tactic chain stalls on one arm, decompose to four explicit
arms (per cycle 327's two-arm recipe).

**Step 4 (`SatisfiesC 2` certificate, ~15 LOC)**: 9-arm
`fin_cases i <;> interval_cases k` close. Paper-verify all 9 arms
before writing:

* i=0 (c=0): all three arms reduce to `0 = 0`.
* i=1 (c=1/2):
  - k=1: `∑ A_{1,j} = 1/4 + 1/4 + 0 = 1/2`. RHS = `1/2`. ✓
  - k=2: `∑ A_{1,j} c_j = (1/4)(0) + (1/4)(1/2) + (0)(1) = 1/8`.
    RHS = `(1/2)²/2 = 1/8`. ✓
* i=2 (c=1):
  - k=1: `∑ A_{2,j} = 0 + 1 + 0 = 1`. RHS = `1`. ✓
  - k=2: `∑ A_{2,j} c_j = (0)(0) + (1)(1/2) + (0)(1) = 1/2`.
    RHS = `1²/2 = 1/2`. ✓

All 9 arms paper-verified. C(2) holds by construction. Recipe:

```lean
theorem butcherLobattoIIIDirect_three_satisfiesC :
    butcherLobattoIIIDirect_three.SatisfiesC 2 := by
  intro i k h1 hk
  fin_cases i <;> interval_cases k <;>
    simp [butcherLobattoIIIDirect_three, Fin.sum_univ_three] <;>
    norm_num
```

### P2 — `cycle_336_pivot_options.md`

After P1 lands, create a 1-page menu at
`.prover-state/issues/cycle_336_pivot_options.md` listing 3–4
candidates:

* **A. `def:422B`** (underlying one-step method for LMM, §422 Ch.4):
  definition-only target, 2–3 cycles estimate, needs Butcher §422
  read.
* **B. `thm:302A`** (Some combinatorial questions, §302 Ch.3):
  may be single-cycle if enumerative; leverages cycles 254–270
  rooted-tree infrastructure. Read entity JSON first.
* **C. `thm:302B`** (Rooted Tree Generating Function Identity, §302):
  multi-cycle if generating functions need Mathlib `MvPowerSeries`
  infrastructure.
* **D. Continue some other partial entity** (e.g., extend cycle 235's
  §384 `thm:384A` group homomorphism infrastructure, or close one
  of the `[~]` partial entities like `cor:342D`'s remaining G(2s)
  clauses — blocked on `thm:314A` infrastructure, so unlikely
  single-cycle).

Keep the doc under 100 lines. Cycle 336's planner does the deep
scoping per their chosen target.

## What NOT to do

1. **Do NOT attempt a collocation-form `butcherLobattoIII_three` with
   coincidence theorem.** Per cycle 331's audit, Lobatto III is the
   "C(s−1) + last-column-zero" variant, not plain Lagrange collocation.
   Cycle 333's collocation/coincidence template only applies to
   Lobatto IIIA (the C(s) variant). Any
   `butcherLobatto_collocationA_three`-style construction would
   diverge from Lobatto III's printed table — this is the cycle 326
   Radau IA pattern.

2. **Do NOT extend the §344 ladder past `butcherLobattoIIIDirect_three`.**
   Cycle 334 worker's option 4 was explicit: one more parking-orbit
   ship, then break. Cycle 335 should NOT attempt
   `butcherLobattoIIIA_four`, `butcherRadauIA_three`, or any other
   §344 entry even if time permits — those belong to cycle 337+ if
   the streak resumes.

3. **Do NOT scope multi-cycle pivots deeply in P2.** The P2
   deliverable is a 1-page menu. Cycle 336's planner does the deep
   scoping. Cycle 260 (`lem_310B_plan.md`, 774 lines) and cycle 222
   (`thm_382A_path.md`) are reserved for *dedicated planning cycles*,
   not parallel deliverables.

4. **Do NOT attempt `thm:302A` or `def:422B` Lean code this cycle.**
   Both require entity JSON reads + multi-cycle scoping. Cycle 335's
   P1 deliverable is the §344 parking orbit; pivot Lean code is
   cycle 336's job.

5. **Do NOT use `decide` or `set_option maxHeartbeats 800000`.** The
   cycle 334 4-tactic chain (`fin_cases <;> interval_cases <;> simp
   <;> norm_num`) closes within default heartbeats at s=3. If a
   `simp` arm stalls, decompose the simp set into explicit per-arm
   tactics — do NOT raise heartbeats.

6. **Do NOT skip the audit step (P1 Step 1).** Per the cycle 326
   Radau IA audit, even "mechanical extensions" of the §344 ladder
   can hide table-divergence surprises. Read ch03.txt:5372–5378
   before writing the definition. If the printed values diverge from
   the C(s−1) derivation, ship the printed values and document the
   divergence (per cycle 326's
   `radau_ia_collocation_divergence.md` precedent).

7. **Do NOT introduce sorries.** The cycle 200/201 rollback precedent
   forbids sorry-first scaffolds when there is no path to single-cycle
   closure. P1's deliverables are all axiom-clean targets.

## Risk assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Printed Lobatto III s=3 table diverges from C(s−1) derivation | Medium | Audit step (P1.1); fall back to printed-table direct-form ship; document in audit issue file |
| C(2) certificate's i=0 row collapse fails `simp` | Low | All three i=0 arms reduce to `0 = 0` (paper-verified); default `simp` set handles `mul_zero` / `zero_mul` |
| `Fin.sum_univ_three` not in simp set | Low | Cycle 333 already uses it; same lemma name |
| Cycle 336 planner has no menu (P2 skipped) | Medium | P2 is the explicit mitigation; ship even a 50-line skeleton |
| 4-tactic chain unifies across 9 arms incorrectly | Low | Decompose to explicit per-arm tactics if needed (cycle 322 / 327 precedent) |

## Verification checklist (CLAUDE.md pre-commit)

### `butcherLobattoIIIDirect_three` (`noncomputable def`)
- Entity: portion of `thm:344A` (Butcher §344 Lobatto III row, Table
  344(I) p. 226). Textbook A-matrix at s=3 per printed table
  ch03.txt:5372–5378.
- Lean type captures: **same** as textbook tableau, subject to P1.1
  audit confirming printed values match the C(s−1) derivation.
- No definition smuggling — this is a direct `RKTableau` declaration
  with literal values.

### `butcherLobattoIIIDirect_three_satisfiesC` (`theorem`)
- Tautology check: conclusion is 9-arm C(2) system, not a hypothesis.
- Identity check: 4-tactic chain is real rational arithmetic.
- Hypothesis strength: standard `SatisfiesC` `intro` pattern.
- Absent-theorem check: no promised content omitted.

### Anonymous `example` for `SatisfiesB 4`
- Anonymous `example`s do not require `lean_status.json` or `plan.md`
  updates. The `thm:344A` row stays `[~]` in `plan.md`.

## Cycle 335 deliverable bar

* **P1** (mandatory): `butcherLobattoIIIDirect_three` def +
  `SatisfiesB 4` `example` + `butcherLobattoIIIDirect_three_satisfiesC`
  `theorem`, all axiom-clean
  (`[propext, Classical.choice, Quot.sound]`), 0 sorries introduced,
  Section344.lean LOC delta ~30–50. Verify
  `lake env lean OpenMath/Chapter3/Section344.lean` exits 0;
  `lake env lean OpenMath/Chapter3.lean` exits 0.
* **P2** (mandatory, scoping-only): create
  `.prover-state/issues/cycle_336_pivot_options.md` with the 4-candidate
  menu, ≤100 lines.

Both should fit in a single worker cycle (~60–90 min total).

Update task results, commit, push. Do NOT touch `lean_status.json` or
`plan.md` (no entity status changes — `thm:344A` stays `[~]`).

## Cycle 336 entry point

After cycle 335 ships, cycle 336 should:
1. Read the P2 menu.
2. Pick one candidate.
3. Read the entity JSON for the chosen candidate.
4. Write either a scoping doc (if multi-cycle) or Lean code (if
   single-cycle).
5. Do **NOT** continue the §344 ladder. The streak ends with cycle
   335.
