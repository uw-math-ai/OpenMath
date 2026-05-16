# Cycle 325 Results

## Worked on

§344 Phase D.5: shipping the small-`s` Radau IA `s = 1` `RKTableau`
(forward Euler analogue) in `OpenMath/Chapter3/Section344.lean`.
Strategy target: complete the `s = 1` Radau pair by mirroring cycle
322's Radau IIA `s = 1` ship (backward Euler) with three swaps —
name (`RadauII` → `RadauI`), integral (`Lagrange.basis_singleton`-
substantive → `intervalIntegral.integral_same`-vacuous since `c_1 = 0`),
and direct-form A-matrix (`!![1]` → `!![0]`).

## Approach

1. **Pre-flight verification** (per strategy §D):
   - Confirmed `butcherRadauI_zeros_one ⟨0, _⟩ = 0` definitionally at
     `Section344.lean:618` — the leaf is at `0`, not `2/3`, so the
     vacuous-integral recipe applies.
   - Confirmed `butcherRadauI_quadratureWeights_one_apply : … = 1`
     exists as a public theorem at `Section344.lean:833`.
   - Confirmed `butcherRadauI_one : Polynomial ℝ` was shipped Phase A
     cycle 317 at `Section344.lean:179`.

2. **Lifted cycle 322 template verbatim** with the three documented
   swaps. The `_apply` proof recipe differs only in the closing
   `simp` argument:
   - Cycle 322 (Radau II, `c_1 = 1`):
     `simp [butcherRadauII_zeros_one, Lagrange.basis_singleton,
            Polynomial.eval_one]`
     — collapses the singleton Lagrange basis to `1` and integrates
     `∫₀¹ 1 dx = 1`.
   - Cycle 325 (Radau I, `c_1 = 0`):
     `simp [butcherRadauI_zeros_one, intervalIntegral.integral_same]`
     — collapses the upper limit to `0` so the interval is degenerate
     and the integral is `0` without ever touching the integrand.

3. **Coincidence theorem** (`butcherRadauIA_one_eq_forwardEuler`)
   replicates cycle 322's `RKTableau.mk.injEq` + `funext + fin_cases`
   per-field proof. A-field cites the new `_apply` (`= 0`); b-field
   cites cycle 321's `_quadratureWeights_one_apply` (`= 1`); c-field
   closes by `rfl` since the pattern-matched zeros array reduces
   definitionally.

4. **Non-vacuity stretch** (`SatisfiesB 1`): closed by
   `rw [butcherRadauIA_one_eq_forwardEuler]; intro k h1 hk;
    interval_cases k; · simp [butcherForwardEulerRK]`.
   Per strategy §C, deliberately stopped at `B(1)` (forward Euler's
   classical order is `2s − 1 = 1`); `B(2)` would be false.

5. **Compile-iteration note**: initial proof had
   `simp [butcherForwardEulerRK, Fin.sum_univ_one]; norm_num` (mirror
   of cycle 322's closer). Got "no goals to be solved" + unused-simp-
   argument warning on `Fin.sum_univ_one`. Trimmed to bare
   `simp [butcherForwardEulerRK]`. The forward-Euler direct form
   `A = 0`, `b = 1` is enough simpler than backward Euler `A = b = 1`
   that the single `simp` arm closes the order-1 condition without
   needing arithmetic.

## Result

SUCCESS. All five new public symbols ship axiom-clean; the file
compiles 0-warning, 0-error; the `SatisfiesB 1` non-vacuity example
compiles. Verification checklist (strategy §E):

1. `lake env lean OpenMath/Chapter3/Section344.lean` — exit 0,
   no diagnostics.
2. `lake build OpenMath.Chapter3` — succeeds (full aggregator,
   2939/2939 jobs).
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` — `0`.
4. `#print axioms` on each new symbol returns
   `[propext, Classical.choice, Quot.sound]`:
   - `butcherRadauI_collocationA_one` ✓
   - `butcherRadauI_collocationA_one_apply` ✓
   - `butcherRadauIA_one` ✓
   - `butcherForwardEulerRK` ✓
   - `butcherRadauIA_one_eq_forwardEuler` ✓
5. `SatisfiesB 1` non-vacuity example compiles.
6. Tautology-scanner regex (per strategy §E.6) returns no new hits
   on cycle 325 additions.

Section344.lean: 1631 → 1711 LOC (+80, on target with the strategy's
~80 LOC estimate).

## Faithfulness check

Per CLAUDE.md pre-commit checklist + strategy §F.

### `butcherRadauI_collocationA_one` (new `def`)

- Entity ID: `thm:344A` (Butcher §344 Radau IA tableau at `s = 1`).
- Textbook source: Butcher §344, p. 244 — the Radau IA collocation
  A-matrix `A_{ij} = ∫₀^{c_i} L_j(x) dx` specialised to the
  one-leaf Radau I abscissa `c_1 = 0`.
- Lean def matches textbook: same `∫₀^{c_i} L_j(x) dx` collocation
  formula at `s = 1`, with the abscissa supplied by cycle 320's
  `butcherRadauI_zeros_one`.
- **Smuggling check**: the fact that this integral evaluates to `0`
  (i.e. that forward Euler is explicit) is a *consequence* of the
  abscissa choice `c_1 = 0`, not part of the definition. The
  definition is the abstract collocation integral; the apply
  theorem performs the evaluation. PASS.

### `butcherRadauI_collocationA_one_apply` (new theorem)

- Statement: `butcherRadauI_collocationA_one ⟨0, _⟩ ⟨0, _⟩ = 0`.
- Tautology check: conclusion `= 0` is not a hypothesis (no
  hypotheses). PASS.
- Identity check: proof is `unfold; show …; simp [_zeros_one,
  intervalIntegral.integral_same]` — substantive evaluation, not
  `exact h`. PASS.
- Hypothesis strength check: no hypotheses; nothing to weaken. PASS.

### `butcherRadauIA_one` (new `def`)

- Entity ID: `thm:344A` (Butcher §344 Radau IA tableau at `s = 1`).
- Textbook source: Butcher §344 Radau IA at `s = 1` (the
  collocation method derived from quadrature on the Radau I
  abscissa). Algebraically: `c = (0)`, `b = (1)`, `A = !![0]`.
- Lean def: assembles cycle 320's `butcherRadauI_zeros_one`,
  cycle 321's `butcherRadauI_quadratureWeights_one`, and this
  cycle's `butcherRadauI_collocationA_one` into a
  `Section312.RKTableau 1`. Same content as Butcher's textbook
  tableau. PASS.

### `butcherForwardEulerRK` (new `def`)

- Textbook source: forward Euler is the standard explicit one-stage
  Runge–Kutta method `y_{n+1} = y_n + h f(t_n, y_n)`. As an `RKTableau 1`
  this is `c = (0)`, `b = (1)`, `A = !![0]`.
- Lean def: matches, declared directly via the field shapes
  `A := fun _ _ => 0`, `b := fun _ => 1`, `c := fun _ => 0`.
- No smuggling: this is a direct algebraic statement of the
  classical method, not a derivation from collocation. PASS.

### `butcherRadauIA_one_eq_forwardEuler` (new theorem)

- Statement: `butcherRadauIA_one = butcherForwardEulerRK`.
- Tautology check: conclusion is an equality between two distinct
  `def`s; neither name appears in a hypothesis (the theorem has no
  hypotheses). PASS.
- Identity check: proof routes through three field-equality
  sub-proofs (A-field via `_collocationA_one_apply`, b-field via
  cycle 321's `_quadratureWeights_one_apply`, c-field via `rfl`).
  Not `exact h`. PASS.
- Hypothesis strength check: no hypotheses; nothing to weaken.
  PASS.
- This theorem does *real* work: it bridges the abstract
  collocation construction to the classical direct form, validating
  that the cycle 320 / 321 / 325 abstract assembly recovers the
  textbook tableau.

### `SatisfiesB 1` non-vacuity (anonymous example)

- Not a named theorem; documents that the abstract tableau is not
  the trivial / empty case. Not subject to faithfulness fields. PASS.

## Dead ends

**One minor compile-iteration loop**. The first attempt copied
cycle 324's closing tactic style for `SatisfiesB`:

```
· simp [butcherForwardEulerRK, Fin.sum_univ_one]; norm_num
```

This produced:
- `error: No goals to be solved` (after the first `simp`, the goal
  is already closed; the trailing `norm_num` has nothing to operate
  on).
- `warning: This simp argument is unused: Fin.sum_univ_one` (the
  direct form's `A = 0`, `b = 1` is simpler than cycle 322's
  `A = b = 1`, and the `1 · 1` term simplifies without needing
  `Fin.sum_univ_one` explicitly).

Trimmed to `· simp [butcherForwardEulerRK]` and the file recompiles
clean. Discovery: forward Euler is *strictly* simpler than backward
Euler for `B(1)` because `b ⋅ c^0 = 1 · 1 = 1` requires no
arithmetic — `simp` collapses the sum and the equality in one step.

No other dead ends. The vacuous-integral pattern from cycle 323's
`(0, *)` Lobatto IIIA entries lifted directly.

## Discovery

1. **`intervalIntegral.integral_same` is the right closer for
   vacuous integrals** — `simp [..., intervalIntegral.integral_same]`
   handles the upper-limit-equals-lower-limit case without needing
   to touch the integrand at all. This is the
   `[0, c_1] with c_1 = 0` analogue of cycle 322's
   `[0, c_1] with c_1 = 1` substantive integration. Cycle 323
   established the pattern at the `(0, *)` entries of the Lobatto
   IIIA two-stage table; cycle 325 confirms it lifts unchanged to
   the `s = 1` Radau IA case where *every* entry is vacuous.

2. **Forward Euler is `SatisfiesB 1`-closable in one tactic.**
   Cycle 322's backward-Euler `SatisfiesB 1` proof needed
   `simp [butcherBackwardEulerRK]` (no `norm_num` needed because
   `1 · 1 = 1` is `simp`-closable too). Cycle 325's forward-Euler
   variant has `1 · 0^0 = 1` — also `simp`-closable. The pattern
   `simp [direct_form]` is robust at the `B(1)` order condition for
   any `s = 1` `RKTableau` whose direct form has `b = 1`. No
   `Fin.sum_univ_one` needed.

3. **Pre-flight verification value** — strategy §D ran three
   checks (abscissa value, quadrature-weight apply existence,
   polynomial existence). All three passed, and the cycle ran on
   the primary recipe without falling back to Option 1 or 2.
   Documenting this for future planners: when the strategy supplies
   explicit pre-flight checks, the worker should run them *before*
   writing Lean code — they are cheap (grep / file-read) and
   eliminate fork-detection mid-cycle.

## Suggested next approach

**Primary candidate: Cycle 326 — Radau IA `s = 2`** (~150 LOC,
single-cycle). Per cycle 324's task-results estimate, this is
the next mechanical port: Radau IA `s = 2` has `c = (0, 2/3)`,
`b = (1/4, 3/4)`, `A = !![1/12, -1/12; 1/4, 5/12]` (Butcher Table
344(I) p. 245). The proof recipe is cycle 324's verbatim with the
following swaps:

- `RadauII` → `RadauI` throughout.
- Substantive upper limit changes from `[0, 1/3]` (cycle 324) to
  `[0, 2/3]` for the `(1, *)` entries (the `(0, 0)` entry is
  vacuous since `c_0 = 0`).
- `_zeros_two ⟨0, _⟩ = 1/3 := rfl` becomes
  `_zeros_two ⟨0, _⟩ = 0 := rfl` (vacuous for `(0, *)` row).
- `_zeros_two ⟨1, _⟩ = 1 := rfl` becomes
  `_zeros_two ⟨1, _⟩ = 2/3 := rfl` (the `(1, *)` row's
  substantive integration).
- The closed-form Lagrange basis polynomials become:
  `L_0(x) = (3/2)x − 1/2` (Radau II at `c_1 = 1/3`, `c_2 = 1` →
  `(1 − x)/(1 − 1/3) = (3/2)(1 − x)` for `j = 0`) reflected to
  `L_0(x) = 1 − (3/2)x` (Radau I at `c_1 = 0`, `c_2 = 2/3` →
  `(x − 2/3)/(0 − 2/3) = 1 − (3/2)x` for `j = 0`); etc.
- `hp1 := integral_pow (a := 0) (b := 1/3) 1` becomes
  `hp1 := integral_pow (a := 0) (b := 2/3) 1` for the substantive
  `(1, *)` arms; the `(0, *)` arms close immediately by
  `intervalIntegral.integral_same`.
- `SatisfiesB 3` stretch is still maximal (Radau IA `s = 2` also
  achieves classical order `2s − 1 = 3`); the `simp [direct,
  Fin.sum_univ_two]; norm_num` per-arm closer should still work.

**Why not Lobatto IIIA `s = 3` (Simpson's rule):** still
multi-cycle scope per cycles 323 / 324 / 325 task results. The
9-entry A-matrix splits into three substantive integration zones,
and the `[0, 1/2]` middle row introduces new closed-form Lagrange
basis polynomials not previously seen.

**Why not Lobatto IIIB `s = 2`:** doable in one cycle (~150 LOC,
the reflection partner of Lobatto IIIA shipped cycle 323), but
Radau IA `s = 2` is the more direct continuation of the cycle
322 / 325 Radau pair completion arc.

**Why not Phase B.2 (polynomial exactness `2s − 2` / `2s − 3`):**
this is the headline `thm:344A` deliverable but is multi-cycle
work. Phase D non-vacuity (the small-`s` `RKTableau` constructions)
remains the priority and one more cycle (Radau IA `s = 2`) closes
the small-`s` Radau pair to completeness.
