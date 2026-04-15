# Strategy — Cycle 78

## Current sorry inventory (3 total)

| File | Line | Theorem | Blocked since |
|------|------|---------|---------------|
| DahlquistEquivalence.lean | 284 | `uniformly_bounded_tupleSucc_iterates` | Cycle 35 |
| MultistepMethods.lean | 1241 | `hasDerivAt_Gtilde_one` | Cycle 19 |
| MultistepMethods.lean | 1258 | `continuousOn_Gtilde_closedBall` | Cycle 19 |

## Aristotle results

- **32aa0177** (sdirk3_poly_ineq): COMPLETE — proof found but SDIRK3 is already sorry-free in repo. No action needed.
- All other Aristotle results: download failed or COMPLETE_WITH_ERRORS. No actionable results.

## PRIMARY TASK: Prove `uniformly_bounded_tupleSucc_iterates`

This is the highest-priority sorry. It blocks the Dahlquist equivalence theorem (the most important result in Chapter 1). The Dahlquist barrier sorrys (lines 1241, 1258) have been attempted for 14+ cycles with no progress and require complex analysis infrastructure that Mathlib lacks — do NOT touch them this cycle.

### What to prove

```lean
theorem uniformly_bounded_tupleSucc_iterates (m : LMM s) (hzs : m.IsZeroStable) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : Fin s → ℂ),
      ‖(m.toLinearRecurrence.tupleSucc^[n]) v‖ ≤ M * ‖v‖
```

### Approach: Three sub-lemmas + decomposition

**Phase 1 (THIS CYCLE — mandatory):** Prove the three foundation lemmas. These are mechanical and well-understood.

#### Sub-lemma 1: `aeval_tupleSucc_charPoly_eq_zero`

```lean
lemma aeval_tupleSucc_charPoly_eq_zero (E : LinearRecurrence ℂ) :
    Polynomial.aeval E.tupleSucc E.charPoly = 0
```

**Proof strategy:**
1. `ext v; ext j` to reduce to pointwise equality
2. Expand `aeval` on `charPoly = X^order - ∑ coeffs_i * X^i`
3. Convert `(T ^ k) v` to `T^[k] v` (by induction: `pow_succ` + `iterate_succ'`)
4. Use `tupleSucc_iterate_eq_mkSol` (already at line 239) to get `(T^[k] v) j = mkSol v (k + j)`
5. The sum equals the recurrence, which is 0 by `E.is_sol_mkSol`

**Key Mathlib:** `Polynomial.aeval_monomial`, `LinearMap.mul_apply`, `Function.iterate_succ'`

#### Sub-lemma 2: `charPoly_eval_eq_rhoC`

```lean
theorem charPoly_eval_eq_rhoC (m : LMM s) (μ : ℂ) :
    m.toLinearRecurrence.charPoly.eval μ = m.rhoC μ
```

**Proof:** Both expand to `μ^s + ∑_{j<s} (α_j : ℂ) μ^j`. Use `Fin.sum_univ_castSucc`, `m.normalized` (α_s = 1), then `ring`.

#### Sub-lemma 3: `tupleSucc_eigenvalue_is_rhoC_root`

```lean
theorem tupleSucc_eigenvalue_is_rhoC_root (m : LMM s) (μ : ℂ)
    (hμ : m.toLinearRecurrence.tupleSucc.HasEigenvalue μ) : m.rhoC μ = 0
```

**Proof:**
1. Get eigenvector from `hμ.exists_hasEigenvector`
2. Apply `Module.End.aeval_apply_of_hasEigenvector` (verified in Mathlib)
3. Combined with sub-lemma 1: `charPoly.eval μ • v = 0`
4. Since `v ≠ 0`: `charPoly.eval μ = 0`
5. By sub-lemma 2: `rhoC μ = 0`

**Phase 2 (THIS CYCLE if time permits):** Decompose the main theorem using these sub-lemmas.

After proving sub-lemmas 1-3, decompose `uniformly_bounded_tupleSucc_iterates` into:
- Unit-circle eigenvalue bound (T acts as scalar μ with |μ| = 1)
- Interior eigenvalue bound (T^n → 0 via polynomial×geometric decay)

Use `minpoly.dvd` (from sub-lemma 1: `aeval T charPoly = 0` → `minpoly ∣ charPoly`) and `Polynomial.rootMultiplicity_le_of_dvd` to show unit-circle eigenvalues have `rootMultiplicity ≤ 1` in `minpoly`, hence nilpotency order = 1 on those eigenspaces.

### What NOT to try

- Do NOT compute `det(XI - companion matrix)` or prove `LinearMap.charpoly = charPoly`
- Do NOT use Gelfand formula for the unit-circle part
- Do NOT try induction on n using the recurrence (gives exponential bound, not constant)
- Do NOT spend more than 15 minutes on any single tactic step — leave a focused sorry and move on
- Do NOT touch MultistepMethods.lean lines 1241 or 1258

### If blocked on Phase 1

Submit the three sub-lemmas to Aristotle as a batch. Frame each as standalone with relevant Mathlib hints.

### If Phase 1 completes quickly and Phase 2 is blocked

Write infrastructure for Phase 2 and submit the remaining sorry to Aristotle. Then pivot to **new content** for the remainder of the cycle (see fallback below).

## FALLBACK: New content (only if Phase 1 is done)

If sub-lemmas 1-3 are proved and the main decomposition is written, use remaining time on:

### Option A: Stiff order conditions / B-series (Section 4.4)
- Define stiff order conditions for DIRK methods
- Prove SDIRK methods satisfy stage order conditions
- Connect to existing Collocation framework

### Option B: Extend explicit RK barriers (Section 2.2)
- Prove s-stage explicit RK has order ≤ s for s = 5, 6
- Butcher barriers: 4-stage explicit RK cannot have order 5

### Option C: Dense output / continuous extensions
- Define continuous extension (interpolation between steps)
- Hermite interpolation framework

**Preference: Option A** — it connects to the existing SDIRK3 work from cycle 77.

## Mandatory deliverables

1. At least one sub-lemma proved and compiled
2. Task result written to `.prover-state/task_results/cycle_078.md`
3. All modified files verified with `lake env lean OpenMath/<file>.lean`
4. Commit and push

## Rules reminder

- Sorry-first: write full structure with sorry, verify compilation, then close
- Aristotle-first: submit ~5 jobs, sleep 30 min, incorporate results
- Do NOT increase maxHeartbeats above 200000
- A cycle with zero changes is UNACCEPTABLE
