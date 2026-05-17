# Cycle 357 Results

## Worked on
Per the planner's §B–§C strategy:

* **P1 (mandatory) — BDF3 end-to-end η(τ) = 1 witness**: one
  anonymous `example` (~21 LOC with docstring) at the end of
  `OpenMath/Chapter4/Section422.lean`, mirroring cycle 356's
  implicit-Euler and explicit-Euler P3/P4c examples. Completes the
  5-LMM × 3-theorem consumer-witness matrix
  {explicitEulerLMM, implicitEulerLMM, trapezoidalLMM, bdf2LMM,
  bdf3LMM} ×
  {sum_β_pos_of_stable_consistent,
   coef_α_plus_coef_β_ne_zero,
   Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened}.
* **P2 (recommended) — Phase D.3 scoping document**: ~430 LOC
  Markdown file at
  `.prover-state/issues/def_422B_phase_D_3_scoping.md`, §1–§10
  structure per the `def_422B_path.md` template. Decomposes Phase
  D.3 (the inductive-step linear-equation solver for `r(t) ≥ 2`,
  the unique remaining multi-cycle gap before Phase E sealing of
  `def:422B`) into 4 sub-phases (D.3.a per-tree convolution
  expansion, D.3.b linear-coefficient extraction, D.3.c `ρ'(1) ≠ 0`
  non-vanishing, D.3.d `noncomputable def underlyingOneStepMethod_aux`
  + spec lemma) at ~1 cycle each.

Two deliverables. No new entities. No `class`/`structure` changes.
No sorries opened (sorry count remains 0 in Section422). No
`axiom`/`constant` introduced.

## Approach

**P1**: copy cycle 356's BDF2 (line 1258) and implicit Euler (line
1280) and explicit Euler (line 1300) `example` structure verbatim
and adapt:

1. Swap `bdf2LMM` → `bdf3LMM` everywhere.
2. Update `(0 : ℕ) < 2` → `(0 : ℕ) < 3` (BDF3 has `k = 3`).
3. Update `Fin.sum_univ_two, Fin.sum_univ_three` →
   `Fin.sum_univ_three, Fin.sum_univ_four`.
4. Use the cycle 355 `bdf3LMM_coef_α_plus_coef_β_ne_zero` for the
   weakened non-vanishing hypothesis.
5. The arithmetic `(6/11) / (6/11) = 1` closes via `norm_num` after
   `simp` unfolds the LMM coefficients.

Numerical verification: `sum_β(bdf3LMM) = 6/11 + 0 + 0 + 0 = 6/11`,
`coef_α(bdf3LMM) = 1·(18/11) + 2·(-9/11) + 3·(2/11) = 6/11`,
`coef_β(bdf3LMM) = 0·(6/11) + 1·0 + 2·0 + 3·0 = 0`,
`η(τ) = (6/11) / (6/11) = 1`. Same numerical pin as implicit Euler
and BDF2 but with distinct intermediate values (`sum_β = 6/11` is
unique among the 5 LMMs).

**P2**: read Butcher §422 (ch04.txt:1148–1173) for the textbook
proof of `thm:422A` (the existence theorem whose substantive content
Phase D.3 will formalise), cross-reference with
`def_422B_path.md` §4.4–§5 to identify the inductive-step gap, then
draft the 4-phase decomposition. Cited project hooks (cycle 343's
`WellFoundedRelation`, cycle 239's `composeQ_phi_mk`, cycle 341's
P1–P3 vertex cases, cycle 350's weakened template) and Mathlib hook
status. Documented the σ-faithfulness deferral and the GPFS / §441
avoidance constraint.

**Verification**: `time lake env lean OpenMath/Chapter4/Section422.lean`
completed in 9m16s (cold) with zero errors and zero warnings.
Tautology scanner `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
returns 0 matches. Sorry count `grep -c sorry
OpenMath/Chapter4/Section422.lean` = 0.

## Result

SUCCESS — both priorities shipped.

* P1: `OpenMath/Chapter4/Section422.lean` 1576 → 1597 LOC (+21,
  matching the ~15-LOC planner estimate plus the multi-line
  docstring). One anonymous `example` added at line 1315–1335. Build
  clean. All cycle 356 named theorems still build axiom-clean. The
  5-LMM × 3-theorem consumer matrix is now saturated.
* P2: `.prover-state/issues/def_422B_phase_D_3_scoping.md` created
  (~430 LOC, 10 sections). Cycle 358 entry point concretely
  specified.

Plus a third deliverable: cycle 357 trailing note appended to
plan.md's `def:422B` row (single-paragraph append per the planner's
§E.9 checklist item).

## Faithfulness check

**Cycle 357 introduces no new `def`, no new `class`/`structure`, and
no new named `theorem`.** P1 is an anonymous `example` (a
non-vacuity discharge, not a theorem claim, so no entity ID applies);
P2 is markdown-only.

### P1 — BDF3 end-to-end η witness (anonymous `example`)

* No textbook entity ID; this is a *consumer-witness* exercise of
  cycle 350's `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
  on BDF3, parallel to cycle 356's BDF2 (line 1258), implicit Euler
  (line 1280), and explicit Euler (line 1300) `example`s.
* The numerical conclusion `η(τ) = 1` is a verified instantiation
  of the cycle 350 weakened ship's formula `η(τ) = sum_β / (coef_α +
  coef_β)` at `bdf3LMM`. Calculation: `sum_β = 6/11`, `coef_α +
  coef_β = 6/11 + 0 = 6/11`, ratio `= 1`. Matches the planner's §B
  arithmetic verification.
* Definition smuggling: N/A (no new `def`).
* Tautology / identity / hypothesis-strength: the `example` invokes
  the cycle 350 template's signature exactly (`hk = (by norm_num :
  (0 : ℕ) < 3)`, `hStab = bdf3LMM_isStable`, `hPre =
  bdf3LMM_isPreconsistent`, `h_denom_ne =
  bdf3LMM_coef_α_plus_coef_β_ne_zero`). No hypothesis strengthening.
  The body is `have h := ...; rw [h]; simp [...]; norm_num` — non-
  trivial arithmetic work (rational evaluation `(6/11) / (6/11) = 1`),
  not a vacuous `exact h` re-export.

### Pre-commit faithfulness checklist

* Tautology check: P1 conclusion (`elementaryWeightQ_phi η_q
  RootedTree.vertex = 1`) is not among its hypotheses (one
  hypothesis: `hEq : Eq422a bdf3LMM η_q`, which is the predicate
  *characterising* `η_q`, not the elementary-weight value). ✓
* Identity check: P1 proof is `have ... ; rw ; simp ; norm_num` —
  doing real arithmetic work (rational division collapse). Not an
  `exact h` re-export. ✓
* Definition smuggling: no new `def`. ✓
* Hypothesis strength check: P1's hypothesis list mirrors cycle
  356's BDF2 P3 example exactly with k → 3. The cycle 350 template
  is the strictly weaker `coef_α + coef_β ≠ 0` form (vs cycle 345's
  `0 ≤ coef_β`); P1 does not strengthen this further. ✓
* Absent theorem check: no promised `sorry`s in P1's body or
  docstring. Sorry count `grep -c sorry
  OpenMath/Chapter4/Section422.lean` = 0. ✓

### P2 — Phase D.3 scoping document

Markdown only, no Lean entity. Faithfulness considerations:

* §1 textbook source: Butcher §422 (ch04.txt:1148–1173) reproduced
  verbatim. No paraphrase risk.
* §5 phase decomposition: 4 sub-phases at ~1 cycle each (D.3.a–d),
  each with concrete deliverable and LOC budget. No phase exceeds
  ~150 LOC. No phase requires `axiom`/`constant`.
* §6 risk assessment: cycle 336-style rollback risks (Phase D.3.a
  wrong-shape, Phase D.3.c Mathlib gap, σ-faithfulness deferral)
  flagged explicitly with mitigation.
* §7 cycle 358 entry point: NOT to attempt D.3.b in the same cycle.
  Per cycle 343 precedent (Phase D.2 shipped alone) — Phase D.3.a
  worth one cycle on its own.

## Dead ends

None. The build was clean on the first attempt. No mid-cycle
linter adjustments needed — the canonical `simp [bdf3LMM,
Fin.sum_univ_three, Fin.sum_univ_four]; norm_num` recipe (cycle
353's `bdf3LMM_hasOrderAtLeast_three` precedent) fired without
over-provisioning. The planner's §B "Possible mid-cycle linter
adjustment" note ("BDF3's β = (6/11, 0, 0, 0) has three vanishing
entries, so the β-sum may collapse before all Fin.sum_univ_*
unfolds fire") turned out not to apply — both `Fin.sum_univ_three`
(for the α-sum) and `Fin.sum_univ_four` (for the β-sum, where the
vanishing entries are needed for `simp` to discharge `if`-discriminants)
are required.

## Discovery

**Full 5-LMM × 3-theorem consumer-witness matrix shipped**: cycles
349 → 350 → 353 → 354 → 355 → 356 → 357 have now produced the
complete consumer matrix:

| LMM | sum_β_pos | coef_α + coef_β ≠ 0 | η(τ) value |
|---|---|---|---|
| explicitEulerLMM | cycle 356 | cycle 356 | 1/2 (cycle 356) |
| implicitEulerLMM | cycle 356 | cycle 356 | 1 (cycle 356) |
| trapezoidalLMM | cycle 355 | cycle 355 | 2/3 (cycle 355) |
| bdf2LMM | cycle 349 | cycle 350 | 1 (cycle 350) |
| bdf3LMM | cycle 354 | cycle 355 | **1 (cycle 357)** |

The matrix is now saturated for all 5 canonical LMMs in the
codebase. Extending it requires shipping a 6th LMM definition first
(e.g. Adams-Bashforth-2), which is a multi-cycle infrastructure
ship — not on cycle 358's near-term horizon.

**Numerical coincidence at `η(τ) = 1`**: three of five LMMs
(implicit Euler, BDF2, BDF3) all pin `η(τ) = 1`. Trapezoidal pins
`2/3`, explicit Euler pins `1/2`. The `η(τ) = 1` coincidence
across the implicit-stable family (implicit Euler, BDF-k for k =
2, 3) is the expected behavior — these methods all approximate the
exact backward-difference operator near the origin, whose elementary
weight at the single-vertex tree is `1`.

**Phase D.3 is the unique remaining multi-cycle gap**: with the
5-LMM × 3-theorem matrix saturated, the only substantive forward-
progress target in §422 (before Phase E sealing) is Phase D.3 (the
inductive-step linear-equation solver for `r(t) ≥ 2`). The cycle
357 P2 scoping doc decomposes this into 4 sub-phases at ~1 cycle
each. After D.3.a–d land, Phase E (lift + seal `def:422B`) is the
final phase before §422 ships.

**Axiom-clean confirmation**: anonymous `example`s can't be queried
via `#print axioms` directly, but the underlying named ships
(`Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`,
`bdf3LMM_isStable`, `bdf3LMM_isPreconsistent`,
`bdf3LMM_coef_α_plus_coef_β_ne_zero`) are all axiom-clean from
their respective cycles (cycles 350, 354, 353, 355 respectively).
P1 is a mechanical composition of these.

## Suggested next approach

**Cycle 358 P1 (mandatory)**: ship Phase D.3.a per the cycle 357 P2
scoping doc §7. Three named theorems generalising cycle 341 P1–P3
from `vertex` to arbitrary trees:

* `elementaryWeightQ_phi_mul_mk` (cycle 341 P1 generalisation),
* `elementaryWeightQ_phi_inv_mk` (cycle 341 P2 generalisation),
* `elementaryWeightQ_phi_zpow_mk` (cycle 341 P3 generalisation).

Per scoping doc §7 preliminaries: cycle 358 worker should
`lean_hover_info` on `elementaryWeightQ_phi_composeQ_phi_mk`
(Section381.lean:4730) **before** writing the lemma signatures, to
confirm the convolution decomposition shape. Aristotle-suitable for
the algebraic sub-lemmas (4–5 atomic congruence steps after the
main expansion is stated).

**Cycle 358 NON-deliverable**: do NOT attempt D.3.b in the same
cycle. Per scoping doc §5, D.3.a is one full cycle on its own.

**Alternative cycle 358 priority (if Phase D.3.a stalls)**:
* Pivot to a fresh entity per `cycle_336_pivot_options.md` —
  `def:442A` (principal sheet, definition-only) is the lowest-risk
  candidate. The 22-cycle §422 streak (336–357) is a reasonable
  diversification trigger.
* Phase D′.2.2 Step 2 (`0 ≤ coef_β`) per
  `eq422a_eta_phase_D_prime_step_2_scoping.md` remains a
  multi-cycle blocker — NOT a single-cycle target.

**Cycle 358+ horizon**: if D.3.a–d land at one cycle each (cycles
358–361), Phase E (cycle 362) seals `def:422B`. Optional Phase F
(cycle 363) connects to `thm:422A` (existence proof) and `thm:422C`
(convergence). Total `def:422B` completion target: cycle 363 at
earliest.
