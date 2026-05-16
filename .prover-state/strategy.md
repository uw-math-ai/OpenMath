# Cycle 329 Strategy — §344 Phase D.9: Radau I `s = 2` direct-form `RKTableau` (C(s) variant)

## §A. Status check

Cycle 328 shipped `butcherRadauIIDirect_two : RKTableau 2` (D(s)
variant of Radau II) plus `B(3)` and `D(2)` non-vacuity witnesses,
all axiom-clean. Section344.lean is at 1883 LOC, sorry count 0.
The audit-first protocol has now caught divergence three times in a
row (cycles 326 Radau IA, 327 Lobatto IIIB, 328 Radau II) — keep it.

## §B. Target

Ship **`butcherRadauIDirect_two : RKTableau 2`** (the C(s) variant of
Radau I at `s = 2`) plus non-vacuity witnesses. This is the natural
continuation of the small-`s` ladder and the most-likely-to-coincide-
with-collocation case from the cycle 328 task results §I outlook.

### §B.1 Why Radau I s=2 first (vs Lobatto IIIC or Radau I s=3)

* **Lower LOC budget**: same template as cycles 326/327/328 (~50 LOC).
* **Tests the C(s) recipe specifically**: per Butcher Table 344(I)
  p. 244, Radau I uses `Choice of A = C(s)`. C(s) is *defined* as
  the plain Lagrange-collocation matrix `A_{ij} = ∫₀^{c_i} L_j(x) dx`
  at the chosen abscissae (Butcher §321 (321b)). So this case is the
  one where direct-form should **agree** with collocation — opposite
  of cycles 326 (Radau IA) and 328 (Radau II D(s)) where direct-form
  diverged from collocation.
* **Validates the audit pattern**: a "coincidence" outcome (rather
  than divergence) is just as informative — confirms that audit-first
  catches both divergent AND coincident cases cleanly.
* **Existing infrastructure**: cycles 320–321 already shipped
  `butcherRadauI_zeros_two = ![0, 2/3]` and
  `butcherRadauI_quadratureWeights_two = ![1/4, 3/4]`, so `b` and `c`
  fields conceptually match (definitional `rfl` against those defs is
  a stretch goal, not a requirement).

## §C. Audit-first protocol (MANDATORY before writing any Lean code)

Cycles 326/327/328 established that the audit step is load-bearing.
Run it FIRST.

### §C.1 Quote Butcher's printed Radau I `s = 2` table

From `extraction/raw_text/ch03.txt:5265–5270`:

```
Radau I        (s = 2, p = 3),
                                                      0        0       0
                                                      2        1       1
                                                      3        3       3
                                                               1       3
                                                               4       4
```

Parsing the column layout (`c | A` on top, `b` row at bottom):

* **c**: `c₁ = 0, c₂ = 2/3`
* **A** row 1: `A₁₁ = 0, A₁₂ = 0`
* **A** row 2: `A₂₁ = 1/3, A₂₂ = 1/3`
* **b**: `b₁ = 1/4, b₂ = 3/4`

So the audited values are
`A = !![0, 0; 1/3, 1/3]`, `b = ![1/4, 3/4]`, `c = ![0, 2/3]`.

### §C.2 Verify against plain Lagrange collocation

Per Butcher Table 344(I), Radau I uses `Choice of A = C(s)`. C(s) is
the collocation matrix `A_{ij} = ∫₀^{c_i} L_j(x) dx` at the Radau I
abscissae. Compute by hand:

* Lagrange basis at `(0, 2/3)`:
  * `L₀(x) = (x − 2/3) / (0 − 2/3) = 1 − (3/2)x`
  * `L₁(x) = x / (2/3) = (3/2)x`
* `A_{0,0} = ∫₀^0 (1 − (3/2)x) dx = 0` ✓
* `A_{0,1} = ∫₀^0 ((3/2)x) dx = 0` ✓
* `A_{1,0} = ∫₀^{2/3} (1 − (3/2)x) dx = 2/3 − (3/4)·(4/9) = 2/3 − 1/3 = 1/3` ✓
* `A_{1,1} = ∫₀^{2/3} ((3/2)x) dx = (3/4)·(4/9) = 1/3` ✓

**Audit conclusion**: Radau I `s = 2` **agrees with plain Lagrange
collocation** at the Radau I abscissae. This is the OPPOSITE of cycle
326 (Radau IA) and cycle 328 (Radau II D(s) variant), where direct-
form values diverged from collocation. The cycle 324 collocation
template **does** lift to Radau I `s = 2`.

### §C.3 Implication for the ship

This means cycle 329 has **two valid paths**:

* **Path α (direct-form only, recommended)**: Ship
  `butcherRadauIDirect_two` declared inline with the audited values
  (matches cycle 326/327/328's pattern; ~50 LOC, low risk). Add a
  docstring note that audit-first confirmed agreement with plain
  collocation, deferring the formal collocation-tableau lift.
* **Path β (collocation-derived, more work)**: Build
  `butcherRadauI_collocationA_two : Fin 2 → Fin 2 → ℝ` (mirror of
  cycle 324's `butcherRadauII_collocationA_two`), four `_apply`
  theorems, then assemble `butcherRadauI_two` from cycles 320/321
  arrays plus the collocation A-matrix. Stretches into ~200 LOC and
  reduces parity with cycles 326/327/328.

**Pick Path α.** Path β is more LOC, and the cycle 327 worker's
discovery that mechanical direct-form ships are the robust pattern
across `s = 2` variants means Path α is the right scope. The audit
note in the docstring documents the coincidence with collocation for
future cycles that might want to build the formal bridge.

## §D. Lean implementation — Path α

### §D.1 File location

Append a new `D.9` section to `OpenMath/Chapter3/Section344.lean`
after the existing `D.8` block (cycle 328's
`butcherRadauIIDirect_two` example block).

### §D.2 Required deliverables

1. **`butcherRadauIDirect_two : RKTableau 2`** (~15 LOC including
   docstring). Inline declaration matching the cycle 326/327/328
   template:

   ```lean
   /-- Butcher Table 344(I) p. 245: the Radau I s=2 RK tableau, direct
   form (the C(s) variant — agrees with plain Lagrange collocation at
   the Radau I abscissae `(0, 2/3)` per the cycle 329 audit). Distinct
   from cycle 326's `butcherRadauIADirect_two`, which is the
   "reflections of Radau II" variant at the same abscissae. … -/
   noncomputable def butcherRadauIDirect_two : RKTableau 2 where
     A := !![0, 0; 1/3, 1/3]
     b := ![1/4, 3/4]
     c := ![0, 2/3]
   ```

2. **`SatisfiesB 3` non-vacuity** (~12 LOC). Radau I `s = 2` achieves
   classical order `p = 2s − 1 = 3`, so `B(3)` is maximal. Use cycle
   324's exact three-arm `interval_cases k` recipe:

   ```lean
   example : butcherRadauIDirect_two.SatisfiesB 3 := by
     intro k hk1 hk3
     interval_cases k
     all_goals (simp [butcherRadauIDirect_two, Fin.sum_univ_two]; norm_num)
   ```

3. **`SatisfiesC 2` certificate** (~12 LOC). This is the cycle 329
   analogue of cycle 328's `D(2)` certificate — it certifies the
   defining property of the C(s) variant. C(s) at `s = 2` covers
   `(i, k) ∈ {0, 1} × {1, 2}`. Mechanical four-arm close:

   ```lean
   example : butcherRadauIDirect_two.SatisfiesC 2 := by
     intro i k hk1 hk2
     fin_cases i <;> interval_cases k <;>
       simp [butcherRadauIDirect_two, Fin.sum_univ_two] <;> norm_num
   ```

   `SatisfiesC` is defined in `OpenMath/Chapter3/Section321.lean`.
   Verify the exact `intro` arity before writing the example — it
   should match cycle 328's `D(2)` pattern (`intro` arity 4:
   `j, k, hk1, hk_max`, or `i, k, hk1, hk_max`). Adjust accordingly
   if it differs.

### §D.3 Optional fourth deliverable (stretch, ship only if §D.2 takes <30 min)

A **collocation-coincidence cross-check** — a lemma showing that the
plain collocation integral `∫₀^{c_i} L_j(x) dx` evaluated at the Radau
I abscissae produces the same values as `butcherRadauIDirect_two.A i j`,
for one entry (e.g. `(1, 0)`). This would be ~20 LOC mirroring cycle
324's `butcherRadauII_collocationA_two_apply_one_zero` shape.

**Skip this if it doesn't fit the cycle budget cleanly.** Path α's
P1/P2/P3 are the required deliverable; the cross-check is a future-
cycle pickup point.

## §E. Faithfulness checklist

For the `def butcherRadauIDirect_two`:

* **Entity ID**: no per-entity JSON exists for `def:RadauI_s2` (the
  extractor only emits `thm:344A`). The reference is Butcher Table
  344(I) p. 245, `ch03.txt:5265–5270`.
* **Textbook statement**: quote the printed table in the docstring
  (see §C.1). Lean values must agree entry-for-entry with the
  printed table.
* **No equivalence required**: printed values copied verbatim.

For the `SatisfiesB 3` and `SatisfiesC 2` examples:

* **Tautology check**: examples have no hypotheses beyond the
  `intro k hk1 hk_max` / `intro i k hk1 hk_max` quantification.
* **Definition smuggling**: `RKTableau`, `SatisfiesB`, `SatisfiesC`
  are existing structure / Prop definitions; no new ones introduced.

## §F. Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter3/Section344.lean` → exit 0.
2. `lake build OpenMath.Chapter3.Section344` → exit 0.
3. `lake env lean OpenMath/Chapter3.lean` → exit 0 (aggregator).
4. `grep -c sorry OpenMath/Chapter3/Section344.lean` → 0.
5. `#print axioms OpenMath.Chapter3.Section344.butcherRadauIDirect_two`
   → `[propext, Classical.choice, Quot.sound]`.

## §G. What NOT to do this cycle

* Do **NOT** build the formal collocation A-matrix
  `butcherRadauI_collocationA_two` (Path β). The audit confirms the
  values agree, but the formal lift would consume the cycle budget
  on `_apply` proofs that mirror cycle 324's Radau IIA construction.
  Path α ships the direct-form anchor; the formal bridge is a future
  cycle pickup point.
* Do **NOT** skip the audit step. Three consecutive cycles
  (326/327/328) have caught divergences that would have produced
  silently wrong tableaux. Even though §C.2 above already does the
  audit, the worker MUST re-verify the values against the raw text
  before writing the `def`.
* Do **NOT** push to `s = 3` (Radau I `s = 3` at `ch03.txt:5307`).
  The `s = 3` Radau I table involves `√6` arithmetic and is multi-
  cycle work per the cycle 328 task results §"Suggested next
  approach". Cycle 330+ territory.
* Do **NOT** pursue Lobatto IIIC `s = 2` this cycle. Per
  `ch03.txt:5224`, Lobatto IIIC uses `"reflections of Lobatto III"`,
  which is the C(s)-vs-reflection question and a separate audit-
  divergence flavor. Cycle 330 candidate.
* Do **NOT** introduce `sorry`, `axiom`, or `constant`. Direct-form
  ships are axiom-clean by construction.
* Do **NOT** raise `maxHeartbeats`. The `SatisfiesB 3` and
  `SatisfiesC 2` `norm_num` arithmetic is within default limits at
  `s = 2`.
* Do **NOT** modify cycle 326 (`butcherRadauIADirect_two`) or
  cycle 328 (`butcherRadauIIDirect_two`). They are independent direct-
  form shipments and reference different tableau values.
* Do **NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`
  on GPFS. The 43+ consecutive timeout pattern from cycles 182–239
  is still in force per `.prover-state/issues/cycle_182_gpfs_slowness.md`.

## §H. Workflow

1. (~5 min) Re-read `extraction/raw_text/ch03.txt:5265–5270` to
   confirm §C.1's parse of Butcher's printed Radau I `s = 2` table.
2. (~5 min) Open `OpenMath/Chapter3/Section344.lean`, locate the
   cycle 328 `D.8` section (around line 1807+). Inspect how cycle
   328's `butcherRadauIIDirect_two` is declared, including its
   docstring format and the `SatisfiesB 3` / `SatisfiesD 2`
   examples that follow it. Use this as the literal template.
3. (~5 min) Read `OpenMath/Chapter3/Section321.lean::SatisfiesC` to
   confirm the `intro` arity expected by the `SatisfiesC 2` example.
4. (~20 min) Write the `D.9` section: header docstring, the `def`,
   the `SatisfiesB 3` example, the `SatisfiesC 2` example.
5. (~10 min) Build + verify per §F. If `lake env lean` complains
   about `SatisfiesC` signature mismatch, adjust the `intro` arity
   from step 3.
6. (~10 min) Update `.prover-state/task_results/cycle_329.md` and
   the §344 row in `plan.md` (append the cycle 329 ship note).
   `lean_status.json` does NOT need updating — `thm:344A` remains
   `partial` until the full polynomial-exactness Phase B.2 lands.
7. (~5 min) Verify axiom-cleanliness via the §F.5 `#print axioms`
   check.
8. Commit + push per CLAUDE.md commit workflow.

## §I. Expected outcome and cycle 330+ outlook

**Cycle 329 delivers**: 3 new public symbols (1 `def` + 2 anonymous
`example`s), all axiom-clean, ~50 LOC delta to Section344.lean.
File grows 1883 → ~1935 LOC. Sorry count stays at 0.

**Cycle 330 candidates** (planner decides next cycle):

* **Lobatto IIIC `s = 2` direct form** (mirrors cycle 327's Lobatto
  IIIB pattern; `ch03.txt` has the printed table near the §344
  Lobatto cluster). Likely-divergent A-matrix per `ch03.txt:5224`
  ("reflections of Lobatto III"). Same ~50 LOC small cycle.
* **Lobatto III `s = 2` (unsuffixed family)** if it exists in
  printed form. Need to grep `ch03.txt` first.
* **`butcherRadauIDirect_three`** (Radau I `s = 3`, multi-cycle
  due to `√6` arithmetic per `ch03.txt:5307`). Defer until the
  small-`s` ladder is saturated.
* **Investigation of Butcher's "reflections of X" precise meaning**
  (multi-cycle, unlocks canonical Radau IA / Lobatto IIIB / IIIC
  collocation/reflection bridges).
* **Pivot to a fresh Chapter 5 entity** (cycle 327 outlook
  candidates: `def:451A` G-stable companion, `def:422B`,
  `def:442A`, `thm:535A`, `thm:541A`).

**Pattern consolidated**: cycles 326/327/328/329 confirm the audit-
first direct-form template across **four** small-`s` Radau/Lobatto
variants. The cycle 327 worker's "mechanical-template" hypothesis
is now robust to four data points across both the divergent (IA,
IIIB, II D(s)) and coincident (I C(s)) cases.
