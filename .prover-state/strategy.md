# Cycle 325 Strategy — §344 Phase D.5: Radau IA `s = 1` `RKTableau`

## A. State summary

- Repo: `OpenMath/Chapter3/Section344.lean` at 1631 LOC, 0 sorries, axiom-clean.
- Phase D shipped to date:
  - D.1 (cycle 321): small-`s` Lagrange quadrature weights.
  - D.2 (cycle 322): Radau IIA `s = 1` `RKTableau` (backward Euler).
  - D.3 (cycle 323): Lobatto IIIA `s = 2` `RKTableau` (trapezoidal).
  - D.4 (cycle 324): Radau IIA `s = 2` `RKTableau` (Butcher Table 344(II)).
- No Aristotle jobs pending.
- No reported blockers; "stuck on" framing in prompt is empty.

## B. Cycle 325 target — Radau IA `s = 1` (forward Euler analogue)

Ship Phase D.5: the simplest remaining single-cycle RKTableau in the
Radau / Lobatto family. Radau IA at `s = 1` uses `c = (0)`, so the
collocation integral is `∫₀^0 L_0(x) dx = 0` via
`intervalIntegral.integral_same` (vacuous; cycle 323 `(0, *)` template).
This is structurally the *forward* Euler analogue: `c₁ = 0`, `b₁ = 1`,
`A₁₁ = 0` — the explicit method matching cycle 322's backward-Euler
template flipped.

### Why this target

1. **Smallest single-cycle scope** in the cycle 324 task results' menu
   (~80 LOC estimate, vs ~150 LOC for Radau IA `s = 2` and multi-cycle
   for Lobatto IIIA `s = 3`).
2. **Completes the `s = 1` Radau pair**: with cycle 322's Radau IIA
   `s = 1` and a new Radau IA `s = 1`, both `s = 1` Radau collocation
   methods in Butcher's §344 are shipped (Lobatto requires `s ≥ 2`,
   so no Lobatto-`s = 1` case exists).
3. **Validates the vacuous-integral pattern** at the `RKTableau` lift
   level — cycle 323's `(0, *)` entries used
   `intervalIntegral.integral_same` to collapse to `0`; cycle 325
   exercises this for *every* entry of the A-matrix at `s = 1`.

### Concrete deliverables

Five new public symbols, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

1. **`butcherRadauI_collocationA_one : Fin 1 → Fin 1 → ℝ`**
   defined as `∫ x in (0 : ℝ)..butcherRadauI_zeros_one i,
   (Lagrange.basis Finset.univ butcherRadauI_zeros_one j).eval x`.
   The single entry evaluates to `0` because the upper limit
   `butcherRadauI_zeros_one ⟨0, _⟩ = 0` (cycle 320's
   `butcherRadauI_zeros_one` packs the leaf at `0`, not `1` like
   Radau II).

2. **`butcherRadauI_collocationA_one_apply : butcherRadauI_collocationA_one
   ⟨0, _⟩ ⟨0, _⟩ = 0`** — single `_apply` theorem. Proof:
   `unfold butcherRadauI_collocationA_one` + `show ∫ x in
   (0 : ℝ)..butcherRadauI_zeros_one ⟨0, _⟩, … = 0` reframing +
   `h_c0 : butcherRadauI_zeros_one ⟨0, _⟩ = 0 := rfl` + `rw [h_c0]` +
   `intervalIntegral.integral_same`. Verify cycle 320's
   `butcherRadauI_zeros_one_apply` (or read the def directly) to
   confirm the leaf value is `0`, not `2/3` or something else, before
   committing to the proof shape.

3. **`butcherRadauIA_one : RKTableau 1`** assembling cycle 320's
   `butcherRadauI_zeros_one = (0)`, cycle 321's
   `butcherRadauI_quadratureWeights_one = (1)`, and the new
   `butcherRadauI_collocationA_one`.

4. **`butcherForwardEulerRK : RKTableau 1`** — direct-form mirror
   `c = (0)`, `b = (1)`, `A = !![0]`. Forward Euler in classical
   notation. (Distinguish from cycle 322's `butcherBackwardEulerRK`
   which has `c = b = !![1]`, `A = !![1]`.)

5. **`butcherRadauIA_one_eq_forwardEuler`** — coincidence theorem
   via `RKTableau.mk.injEq` + `funext + fin_cases` per field. The
   A-field cites the new `_apply` theorem; the b-field cites
   cycle 321's `butcherRadauI_quadratureWeights_one_apply`; the
   c-field reduces by `funext + fin_cases` with one `rfl` arm since
   `butcherRadauI_zeros_one ⟨0, _⟩ = 0` definitionally.

### Non-vacuity stretch — `SatisfiesB 1`

Per cycle 324's discovery that `SatisfiesB` arms close uniformly
under `simp [direct_form, Fin.sum_univ_one]; norm_num`, ship a
`SatisfiesB 1` non-vacuity example routed through
`butcherRadauIA_one_eq_forwardEuler`:

```lean
example : (butcherRadauIA_one).SatisfiesB 1 := by
  rw [butcherRadauIA_one_eq_forwardEuler]
  intro k h1 hk
  interval_cases k
  · simp [butcherForwardEulerRK, Fin.sum_univ_one]; norm_num
```

Radau IA `s = 1` (forward Euler) has classical order `2s − 1 = 1`,
so `B(1)` is the maximal stretch. Per CLAUDE.md, do NOT attempt
`B(2)` — forward Euler is *not* second-order exact and the proof
would fail.

### Recipe (use cycle 322 verbatim with three swaps)

The cycle 322 template at `OpenMath/Chapter3/Section344.lean`
(Radau IIA `s = 1`, ~lines 1158–1247) is the closest precedent.
Three swaps:

- **Name swap**: `RadauII` → `RadauI` in every name (matrix
  definition, A-matrix definition, apply theorem, RKTableau,
  direct form, coincidence theorem). Cycle 320's
  `butcherRadauI_zeros_one` and cycle 321's
  `butcherRadauI_quadratureWeights_one` already exist — verify
  this by `grep -n "butcherRadauI_zeros_one\|butcherRadauI_quadratureWeights_one" OpenMath/Chapter3/Section344.lean`
  before writing the new lifts.
- **Integral swap**: the substantive integral is now vacuous
  (`∫₀^0 … = 0`). Use `intervalIntegral.integral_same` rather than
  cycle 322's `Lagrange.basis_singleton` + `Polynomial.eval_one`.
  The cycle 323 `(0, *)` Lobatto IIIA entries are the template for
  this collapse — read them at `Section344.lean` around the
  `_apply_zero_zero = 0` / `_apply_zero_one = 0` proofs.
- **Direct-form swap**: `BackwardEuler` → `ForwardEuler` and
  matrix literal `!![1]` → `!![0]`. The `c` and `b` vectors are
  unchanged shape (`![0]`, `![1]`), only `A` swaps from `!![1]`
  to `!![0]`.

LOC estimate: ~80 LOC, well within single-cycle budget.

## C. What NOT to do

- **Do NOT pursue Lobatto IIIA `s = 3` (Simpson's rule).**
  Multi-cycle scope per cycle 323/324 task results. The 9-entry
  A-matrix splits into three substantive integration zones
  (`[0, 0]` vacuous, `[0, 1/2]` new, `[0, 1]` reusing cycle 321's
  Simpson weight machinery). Not single-cycle.
- **Do NOT pursue Radau IA `s = 2`** in this cycle. Per cycle 324
  estimate it is ~150 LOC; doable in one cycle but adds two
  substantive `[0, 2/3]` integrations vs cycle 325's vacuous
  integral. Defer to cycle 326 once Radau IA `s = 1` lands.
- **Do NOT attempt `SatisfiesB 2` for Radau IA `s = 1`.**
  Forward Euler has classical order 1, not 2. `B(2)` is false
  on this method and `norm_num` will fail.
- **Do NOT start Phase B.2** (polynomial exactness `2s − 2` /
  `2s − 3` via polynomial division). This is the headline
  `thm:344A` deliverable but is multi-cycle work. Phase D
  non-vacuity remains the priority.
- **Do NOT introduce sorries.** Cycle 200/201 and cycle 149/150
  rollback precedents forbid sorry-first scaffolds for multi-cycle
  targets. Cycle 325 must ship axiom-clean or skip the cycle.
- **Do NOT raise `maxHeartbeats`.** The cycle 322 / 323 / 324
  proofs all closed under the default 200000 limit; cycle 325 is
  a strict simplification (vacuous integral) so should be even
  faster.
- **Do NOT touch `OpenMath/Chapter4/Section441.lean`.** The GPFS
  stall on §441 is persistent across cycles 182–239 (43+ consecutive
  timeouts) and remains loop-maintainer territory per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
- **Do NOT poll Aristotle.** No pending jobs.
- **Do NOT freelance into the §342C remaining clauses (342j / k / l).**
  Those are blocked on `thm:314A` elementary-differential
  infrastructure (multi-cycle, out of scope).
- **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
  territory.

## D. Pre-flight verification (do this FIRST)

Before writing any Lean code, the worker should confirm:

1. **Cycle 320's `butcherRadauI_zeros_one` packs the leaf at `0`,
   not `1` or `2/3`.** Read the def in `Section344.lean` (around
   the Phase C.2 block). If the single entry is not `0`, the
   vacuous-integral recipe in §B.2 will not work and the strategy
   must be revisited.
2. **Cycle 321's `butcherRadauI_quadratureWeights_one_apply = 1`
   exists as a public theorem.** Grep for it; if it does not exist
   (only e.g. an inline `example`), the coincidence theorem proof
   shape must adapt.
3. **`butcherRadauI_one : Polynomial ℝ`** (the polynomial from
   Phase A, cycle 317) has the explicit form that lets us prove
   the single root is `0`. Already shipped per the plan.md row,
   so this should be a trivial check.

If any of these checks fail, escalate via task results and
reconsider the strategy. The expected outcome is that all three
checks pass and the recipe in §B applies verbatim.

## E. Verification checklist for the worker (post-write)

1. `lake env lean OpenMath/Chapter3/Section344.lean` exits 0.
2. `lake build OpenMath.Chapter3` succeeds (full aggregator).
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` returns 0.
4. `#print axioms` (via `lean_verify`) on each of the 5 new public
   symbols returns `[propext, Classical.choice, Quot.sound]`
   (no `sorryAx`).
5. `SatisfiesB 1` non-vacuity example compiles.
6. Tautology-scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` returns no new
   hits on the cycle 325 additions.

## F. Faithfulness checklist for cycle 325 commit

Per CLAUDE.md pre-commit faithfulness checklist:

- **`butcherRadauI_collocationA_one`** (new `def`): Butcher §344
  Radau IA collocation A-matrix at `s = 1`. Lean def is the
  textbook collocation formula `A_{ij} = ∫₀^{c_i} L_j(x) dx`
  specialised to the Radau I one-leaf abscissa `c_1 = 0`. Same
  content; no smuggling. The fact that this evaluates to `0`
  (forward Euler explicit method) is a *consequence* of the
  abscissa choice, not a redefinition.
- **`butcherRadauIA_one`** (new `def`): textbook Radau IA `s = 1`
  tableau assembly from canonical abscissae + weights +
  collocation A. Same content as Butcher's §344 Radau IA
  Table at `s = 1`.
- **`butcherForwardEulerRK`** (new `def`): classical forward Euler
  Runge–Kutta tableau. Standard textbook form, no smuggling.
- **`butcherRadauIA_one_eq_forwardEuler`** (new theorem):
  coincidence between two distinct definitions. Conclusion does
  NOT match any hypothesis verbatim (tautology check: pass).
  Proof routes through 3 substantive field reductions
  (identity check: pass — not a one-liner `exact h`).
  No extra hypotheses beyond what `RKTableau.mk` requires
  (hypothesis strength check: pass).
- **`butcherRadauI_collocationA_one_apply`** (new theorem):
  evaluates the new `def` at its single index. Tautology /
  identity / strength checks all pass.

## G. End-of-cycle housekeeping

- Update `plan.md`'s `thm:344A` row to record Phase D.5 closure
  (and the now-complete `s = 1` Radau pair status).
- `extraction/formalization_data/lean_status.json` — `thm:344A`
  remains `[~]`/`partial` since Phase B.2 (polynomial exactness)
  is still open.
- Write `.prover-state/task_results/cycle_325.md` documenting:
  the 5 new symbols, the `SatisfiesB 1` stretch, axiom-cleanliness
  verification, and a candidate menu for cycle 326. Recommend
  Radau IA `s = 2` (~150 LOC, single-cycle, mechanical port of
  cycle 324's Radau IIA `s = 2` template with `(1/3, 1)` swapped
  to `(0, 2/3)` and the upper-limit `[0, 1/3]` integral swapped to
  `[0, 2/3]`).

## H. Estimated cycle budget

- Pre-flight verification (§D): ~10 min.
- Reading cycle 322 template + cycle 320/321 Radau I prerequisites:
  ~10 min.
- Writing 5 new symbols (closely following cycle 322 with three
  swaps): ~25 min.
- Compile + iterate on any minor issues: ~10 min.
- Axiom-cleanliness + non-vacuity verification: ~5 min.
- Task results + housekeeping: ~10 min.

Total: ~70 min. Single-cycle deliverable with comfortable margin.

## I. Fallback if pre-flight fails

If §D.1 reveals that `butcherRadauI_zeros_one` does NOT pack the
leaf at `0` (e.g. it's `2/3` because Phase C.2 picked the textbook
Radau I "right-handed" leaf at the right endpoint), then:

- **Fallback Option 1**: ship Radau IA `s = 1` with a single
  substantive integral `∫₀^{2/3} 1 dx = 2/3` (constant
  Lagrange basis since `s = 1`). Still single-cycle. Direct form
  swaps to `A = !![2/3]` and `butcherForwardEulerRK` is replaced
  by a one-off `butcherRadauIA_one_direct` since there's no
  classical name. LOC estimate similar (~80 LOC).
- **Fallback Option 2**: pivot to Lobatto IIIB `s = 2` (the
  reflection partner of Lobatto IIIA shipped in cycle 323).
  Lobatto IIIB has `c = (0, 1)`, `b = (1/2, 1/2)`,
  `A = !![1/2, -1/2; 1/2, 1/2]`. The cycle 323 template applies
  verbatim with `IIIA` → `IIIB`. ~150 LOC; doable in one cycle.

Choose Option 1 if the abscissa surprise is small (just a leaf
position); choose Option 2 if Phase C for Radau I has structural
problems that block even the `s = 1` case.
