# Cycle 324 strategy — §344 Phase D.4: Radau IIA `s = 2` `RKTableau`

## §A. Decision tree

* **Skip §441**: 43+ consecutive GPFS timeouts on
  `OpenMath/Chapter4/Section441.lean`. Do **not** attempt a smoke
  test or any §441 work. Skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* **No pending Aristotle results**: nothing to incorporate.
* **No sorries in the repo**: cycle 323 closed clean.
* **No phantom verdicts**: cycle 323 scored +2; nothing to verify.

## §B. Substantive target — `thm:344A` Phase D.4: Radau IIA `s = 2` `RKTableau`

Ship the **2-stage Radau IIA** Runge–Kutta tableau (Butcher §344
Table 344(II), p. 245). Direct two-stage extension of cycle 322's
Radau IIA `s = 1` and structural mirror of cycle 323's Lobatto IIIA
`s = 2` ship, but with non-trivial integration over `[0, 1/3]` for
the `(0, j)` A-matrix entries.

### §B.1 The Butcher §344 Table 344(II) tableau

```
c = (1/3, 1)
b = (3/4, 1/4)               ← cycle 321 already shipped these
A = !![5/12, -1/12;
       3/4,   1/4 ]
```

The `(1, j)` entries are by design the quadrature weights (since
`c_1 = 1` makes the upper limit of integration coincide with `[0, 1]`
in the cycle-321 weight definitions). The `(0, j)` entries integrate
the basis polynomials `L_j` (over abscissae `c = (1/3, 1)`) on
`[0, 1/3]`:

* `L_0(x) = (3/2) - (3/2)·x` (cycle 321's `_quadratureWeights_two_apply_zero`
  h_eval lemma).
* `L_1(x) = (3/2)·x - (1/2)` (cycle 321's `_quadratureWeights_two_apply_one`
  h_eval lemma).

Paper-verified closed forms:

* `∫₀^{1/3} ((3/2) - (3/2)·x) dx = (3/2)(1/3) - (3/4)(1/9)
    = 1/2 - 1/12 = 5/12`.
* `∫₀^{1/3} ((3/2)·x - (1/2)) dx = (3/4)(1/9) - (1/2)(1/3)
    = 1/12 - 1/6 = -1/12`.

### §B.2 Six new public symbols + one direct-form witness + one coincidence theorem + one non-vacuity example

Insert in `OpenMath/Chapter3/Section344.lean` immediately after
cycle 323's `example : butcherLobattoIIIA_two.SatisfiesB 2` block
(before `end OpenMath.Chapter3.Section344`):

#### (1) `butcherRadauII_collocationA_two : Fin 2 → Fin 2 → ℝ`

```lean
noncomputable def butcherRadauII_collocationA_two
    (i j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..butcherRadauII_zeros_two i,
    (Lagrange.basis Finset.univ butcherRadauII_zeros_two j).eval x
```

Mirror of cycle 323's `butcherLobatto_collocationA_two`, swapping
`butcherLobatto_zeros_two` for `butcherRadauII_zeros_two`.

#### (2-5) Four `_apply` theorems

* `butcherRadauII_collocationA_two_apply_zero_zero : ... = 5 / 12`
* `butcherRadauII_collocationA_two_apply_zero_one  : ... = -(1 / 12)`
* `butcherRadauII_collocationA_two_apply_one_zero  : ... = 3 / 4`
* `butcherRadauII_collocationA_two_apply_one_one   : ... = 1 / 4`

**Recipe for (4) and (5) (the `(1, j)` entries — c_1 = 1)**: copy
cycle 321's `butcherRadauII_quadratureWeights_two_apply_zero/_one`
proofs *verbatim*, prepending one `show ∫ x in (0 : ℝ)..
butcherRadauII_zeros_two ⟨1, _⟩, ... = ...` reframing, then a
`have h_c1 : butcherRadauII_zeros_two ⟨1, by omega⟩ = 1 := rfl`,
then `rw [h_c1]`. The h_erase + h_eval + simp_rw + integration
chain is identical to cycle 321's recipe (the upper limit `1`
matches `[0, 1]` exactly). The values `3/4` and `1/4` are unchanged.

**Recipe for (2) and (3) (the `(0, j)` entries — c_0 = 1/3)**: same
shape but with upper limit `1/3` instead of `1`. Concrete sketch
for `_apply_zero_zero` (target `5/12`):

```lean
theorem butcherRadauII_collocationA_two_apply_zero_zero :
    butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = 5 / 12 := by
  unfold butcherRadauII_collocationA_two
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨0, by omega⟩,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = 5 / 12
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = (3/2) - (3/2) * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨0, by omega⟩,
      ((3 : ℝ)/2 - (3/2) * x) = 5 / 12
  have h_c0 : butcherRadauII_zeros_two ⟨0, by omega⟩ = 1 / 3 := rfl
  rw [h_c0]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 (1/3) :=
    continuous_id.intervalIntegrable 0 (1/3)
  have hx : ∫ x in (0 : ℝ)..(1/3 : ℝ), x = 1/18 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := (1/3 : ℝ)) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hi_x.const_mul (3/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      hx]
  norm_num
```

`_apply_zero_one` (target `-1/12`): same shape, h_eval reduces to
`(3/2)*x - (1/2)`, h_c0 same. Integral chain becomes `∫ - ∫`
(mirror of cycle 321's `_apply_one` with `[0, 1] → [0, 1/3]`).
Paper arithmetic: `(3/2) · (1/18) - (1/2) · (1/3) = 1/12 - 1/6 = -1/12`.

**The `(1, j)` entries (cases 4 and 5) should be shorter than the
`(0, j)` cases (2 and 3) — they don't introduce any new integration
arithmetic vs cycle 321.**

#### (6) `butcherRadauIIA_two : RKTableau 2`

```lean
noncomputable def butcherRadauIIA_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := butcherRadauII_collocationA_two
  b := butcherRadauII_quadratureWeights_two
  c := butcherRadauII_zeros_two
```

#### (7) `butcherRadauIIADirect_two : RKTableau 2` (optional cross-validation form)

```lean
noncomputable def butcherRadauIIADirect_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := !![5/12, -(1/12); 3/4, 1/4]
  b := ![3/4, 1/4]
  c := ![1/3, 1]
```

No famous shorter name (cycle 322 had backward Euler, cycle 323 had
trapezoidal — Radau IIA s=2 has no equally well-known alias). This
is just for `RKTableau.mk.injEq`-style cross-validation. Ship if
LOC budget allows; skip if it inflates the cycle.

#### (8) `butcherRadauIIA_two_eq_direct` (optional coincidence theorem)

If shipping (7), include this. Same shape as cycle 323's
`butcherLobattoIIIA_two_eq_trapezoidal`: `RKTableau.mk.injEq` + four
A-field `_apply` rewrites + two b-field `_apply` rewrites + four
c-field `rfl` reductions:

```lean
theorem butcherRadauIIA_two_eq_direct :
    butcherRadauIIA_two = butcherRadauIIADirect_two := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i <;> fin_cases j
    · show butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_zero_zero]; rfl
    · show butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_zero_one]; rfl
    · show butcherRadauII_collocationA_two ⟨1, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_one_zero]; rfl
    · show butcherRadauII_collocationA_two ⟨1, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_one_one]; rfl
  · funext i; fin_cases i
    · show butcherRadauII_quadratureWeights_two ⟨0, by omega⟩ = _
      rw [butcherRadauII_quadratureWeights_two_apply_zero]; rfl
    · show butcherRadauII_quadratureWeights_two ⟨1, by omega⟩ = _
      rw [butcherRadauII_quadratureWeights_two_apply_one]; rfl
  · funext i; fin_cases i <;> rfl
```

#### (9) Non-vacuity: `SatisfiesB 2`

Radau IIA `s = 2` has classical order `2s − 1 = 3`, so it should
satisfy `B(3)`. To mirror cycle 322's `B(1)` and cycle 323's `B(2)`
non-vacuity bars and keep the example short, ship the **B(2)**
witness as the default:

```lean
example : butcherRadauIIA_two.SatisfiesB 2 := by
  rw [butcherRadauIIA_two_eq_direct]   -- if (8) shipped
  intro k h1 hk
  interval_cases k
  · simp [butcherRadauIIADirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIIADirect_two, Fin.sum_univ_two]; norm_num
```

Sanity values:

* `k = 1`: `3/4 + 1/4 = 1 = 1/1` ✓
* `k = 2`: `(3/4)·(1/3) + (1/4)·1 = 1/4 + 1/4 = 1/2` ✓

**Stretch — try `B(3)` first**: Radau IIA s=2 has order 3. The
`k = 3` arm checks `(3/4)·(1/3)² + (1/4)·1² = (3/4)·(1/9) + 1/4
= 1/12 + 3/12 = 1/3` ✓. If `simp + norm_num` closes the `k = 3`
arm in one shot, ship `B(3)`. If `norm_num` doesn't close after
~30 seconds, drop back to `B(2)` — don't burn the cycle on this
optional stretch.

If (7)+(8) skipped, replace the `rw [butcherRadauIIA_two_eq_direct]`
opener with `unfold butcherRadauIIA_two` and inline the per-`k`
field applications via `butcherRadauII_zeros_two`,
`butcherRadauII_quadratureWeights_two_apply_*`. The direct-form
version (7)+(8) is the cleaner path; default to shipping it.

### §B.3 LOC budget

| Component | LOC |
|---|---|
| (1) `_collocationA_two` def + docstring | ~10 |
| (2) `_apply_zero_zero = 5/12` | ~30 |
| (3) `_apply_zero_one = -1/12` | ~30 |
| (4) `_apply_one_zero = 3/4` (cycle 321 mirror) | ~25 |
| (5) `_apply_one_one = 1/4` (cycle 321 mirror) | ~25 |
| (6) `butcherRadauIIA_two` def | ~5 |
| (7) `butcherRadauIIADirect_two` def (optional) | ~5 |
| (8) `butcherRadauIIA_two_eq_direct` (optional) | ~25 |
| (9) `SatisfiesB 2` non-vacuity | ~10 |
| Docstrings + section comments | ~20 |
| **Total** | **~185 LOC** |

Larger than cycle 323's 162 LOC because the `(0, j)` entries
require a substantive `∫₀^{1/3}` integration step that cycle 323's
vacuous `∫₀⁰` cases collapsed. If LOC overshoots ~250, drop
(7)+(8) and replace the `SatisfiesB` example opener with direct
field unfolding (cycle 323 used `rw [_eq_trapezoidal]` as a
convenience; not strictly required).

### §B.4 Risk register

* **R1 — h_c0 := rfl bridging `butcherRadauII_zeros_two ⟨0, _⟩ = 1/3`.**
  Cycle 320's def of `butcherRadauII_zeros_two` should pattern-match
  to `1/3` at `i.val = 0`. The cycle 323 Lobatto `h_c1 := rfl` worked
  cleanly under the same shape. Fallback: if `rfl` fails, use
  `by simp [butcherRadauII_zeros_two]` or `by decide`.

* **R2 — h_c1 := rfl for `butcherRadauII_zeros_two ⟨1, _⟩ = 1`.**
  Same as R1. Should work.

* **R3 — sign handling on `-1/12`.** The goal might render as
  `-(1/12)`, `(-1)/12`, or `-1/12` depending on simp normalisation.
  `norm_num` should handle all three. If it doesn't, add `show ... =
  -(1/12)` before `norm_num`, or include `neg_div` /
  `neg_eq_neg_one_mul` in the final simp set.

* **R4 — `integral_pow` over fractional upper limit.** Cycle 321
  used `integral_pow (a := 0) (b := 1)`; we now need `(b := 1/3)`.
  Mathlib's `integral_pow` works for arbitrary real bounds. The
  resulting `(1/3)^2 / 2 = 1/18` is closed by `norm_num`.

* **R5 — `IntervalIntegrable` on `[0, 1/3]`.** Same shape as cycle
  321's `[0, 1]` usage; `continuous_id.intervalIntegrable 0 (1/3)`
  and `continuous_pow ...` should produce the required witnesses
  without surprises.

* **R6 — `SatisfiesB 3` stretch arm.** If `simp [_, Fin.sum_univ_two]
  + norm_num` doesn't close `(3/4)·(1/3)² + (1/4)·1² = 1/3` in one
  shot, the `(1/3)^2` term may need an extra `pow_two` or `mul_self`
  step. Don't fight this — drop back to `B(2)` if it sticks.

### §B.5 Verification

After writing, run:

1. `lake env lean OpenMath/Chapter3/Section344.lean` — clean exit.
2. `lake env lean OpenMath/Chapter3.lean` — aggregator clean.
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` → expect `0`.
4. `lean_verify` on each new public symbol:
   - `OpenMath.Chapter3.Section344.butcherRadauII_collocationA_two`
   - `_apply_zero_zero` / `_apply_zero_one` / `_apply_one_zero` /
     `_apply_one_one`
   - `butcherRadauIIA_two`
   - `butcherRadauIIADirect_two` (if shipped)
   - `butcherRadauIIA_two_eq_direct` (if shipped)
   All should report `[propext, Classical.choice, Quot.sound]`.
5. Sorry count delta: 0 → 0.

If any axiom check leaks `sorryAx`, treat it as a fatal error
(rollback and use a hand-written proof instead).

### §B.6 Faithfulness check

For each new `def`/`theorem`:

* `butcherRadauII_collocationA_two` (def):
  - Textbook reference: Butcher §344 p. 245, Table 344(II)
    collocation A-matrix.
  - The Lean def integrates Lagrange basis polynomials from 0 to
    `c_i`. Matches the textbook collocation recipe exactly. No
    definition smuggling.

* `butcherRadauIIA_two` (def):
  - Textbook reference: Butcher §344 Table 344(II), Radau IIA at
    `s = 2`. The Lean def is `RKTableau` assembled from cycle 320's
    zeros, cycle 321's weights, and this cycle's collocation
    A-matrix. Faithful.

* Four `_apply` theorems: closed-form values (5/12, -1/12, 3/4,
  1/4). Match Butcher Table 344(II). Paper-verified in §B.1 above.

* `butcherRadauIIA_two_eq_direct` (coincidence, optional):
  Tautology check: structure equality across two distinct
  definitions, not a hypothesis re-export. Identity check: proof
  routes through 6 substantive `rw` calls + 4 `rfl` reductions, not
  a single `exact h`.

## §C. NOT to try this cycle

* **§441 in any form.** 43+ GPFS timeouts. Skip per
  `cycle_182_gpfs_slowness.md`.
* **Lobatto IIIA s=3 (Simpson's rule).** The 9-entry A-matrix is
  multi-cycle scope per cycle 323's task results. Defer.
* **Radau IA s=1 (forward Euler analogue).** Mathematically smaller
  than Radau IIA s=2 (no novel integration arithmetic since `c_1 = 0`
  makes all A-matrix entries vacuous via `integral_same`). Reserve
  for cycle 325 (an easier cycle if the planner wants).
* **Full `thm:344A`.** Phase B.2 polynomial-exactness clauses
  (`2s − 2`, `2s − 3`) require polynomial-division infrastructure
  and are multi-cycle. Phase D.4 ships *one specific RKTableau* —
  the headline thm:344A iff remains open.
* **A direct one-shot `simp; ring` for the `_apply_zero_*` proofs.**
  Cycle 321/322/323 confirmed that the cycle 321 recipe (unfold →
  show → h_erase → h_eval → simp_rw → integration chain → norm_num)
  is the working pattern; don't deviate.
* **Renaming `h_*` hypotheses to dodge the tautology scanner.** The
  patterns used in cycle 321/322/323 (`h_erase`, `h_eval`, `h_c1`,
  `hi_x`, `hx`) have not triggered scanner false positives — keep
  them.
* **`axiom` or `constant` declarations.** Not allowed under
  CLAUDE.md rules.
* **`maxHeartbeats` above 200000.** Default is sufficient for every
  step above; if any single tactic stalls, decompose.
* **Pivoting to a different cluster.** Cycle 322/323's ladder is
  the right shape; cycle 324 is a clean port. Don't redirect to
  thm:381G / lem:312B / etc. — those are multi-cycle pre-requisite
  work.

## §D. Aristotle policy

* **No new submissions this cycle.** All deliverables above are
  mechanical ports of well-validated cycle 321/322/323 patterns.
  Manual is cleaner.
* **No polls.** No pending project IDs from prior cycles relevant
  to §344.

## §E. Deliverable order

1. (5 min) §B.2 (1): define `butcherRadauII_collocationA_two`.
2. (15 min) §B.2 (4) `_apply_one_zero = 3/4`: port from cycle 321.
   Compile, axiom-check.
3. (15 min) §B.2 (5) `_apply_one_one = 1/4`: port from cycle 321.
   Compile, axiom-check.
4. (30 min) §B.2 (2) `_apply_zero_zero = 5/12`: substantive new
   `[0, 1/3]` integration. Compile, axiom-check.
5. (20 min) §B.2 (3) `_apply_zero_one = -1/12`: mirror of (4) with
   sign change. Compile, axiom-check.
6. (5 min) §B.2 (6) `butcherRadauIIA_two`: assemble.
7. (10 min, optional) §B.2 (7)+(8): direct form + coincidence.
8. (5 min) §B.2 (9): `SatisfiesB 2` non-vacuity. Try `B(3)` first;
   fall back if it sticks.
9. (5 min) Run §B.5 verification commands.
10. (5 min) Run faithfulness check §B.6.
11. (5 min) Update `extraction/formalization_data/lean_status.json`
    `thm:344A` row to record Phase D.4 closure (status stays
    `partial`).
12. (5 min) Update `plan.md` `thm:344A` row with the cycle 324
    closure paragraph appended to the existing trailing notes.
13. (15 min) Write `.prover-state/task_results/cycle_324.md`.
14. (5 min) Commit:
    `Cycle 324 — §344 Phase D.4: Radau IIA \`s = 2\` RKTableau shipped.`

Total budget: ~2.5 hrs (slightly longer than cycle 323 due to the
`[0, 1/3]` integration steps in (2) and (3)).

## §F. Stretch (if cycle 324 closes in ≤ 1.5 hrs)

Open `OpenMath/Chapter3/Section344.lean` and inspect cycle 320's
`butcherRadauI_zeros_one` and cycle 321's
`butcherRadauI_quadratureWeights_one_apply` (Radau I, `s = 1`,
`c = (0)`). If the infrastructure is in place, ship Radau IA s=1:

* Define `butcherRadauI_collocationA_one : Fin 1 → Fin 1 → ℝ`
  (single entry `∫₀⁰ L_0(x) dx = 0`, vacuous via
  `intervalIntegral.integral_same` — cycle 323 `(0, j)` template).
* `_apply` theorem returning `0`.
* `butcherRadauIA_one : RKTableau 1` — assembles to `A = !![0]`,
  `b = ![1]`, `c = ![0]` (essentially forward Euler).
* Optionally `butcherForwardEulerRK : RKTableau 1` (`A = 0`, `b = 1`,
  `c = 0`) + coincidence theorem.
* `SatisfiesB 1` non-vacuity.

Adds ~80 LOC. Do **not** attempt Radau IA s=2 as stretch — its
A-matrix needs integration on `[0, c_1]` with `c_1 = ...` (need to
check; nontrivial). Reserve for a dedicated cycle.

## §G. Status flags

* sorry count target: 0 → 0.
* axiom target: `[propext, Classical.choice, Quot.sound]` on every
  new symbol.
* `lean_status.json` `thm:344A` row: remains `partial`. Update the
  cycle-324 note to record Phase D.4 ship (Radau IIA s=2 RKTableau).
* `plan.md` `thm:344A` row: stays `[~]`; append cycle 324 closure
  paragraph to the existing trailing notes.
* `extraction/formalization_data/lean_status.json` other rows: no
  change.
