# Issue: Iterated V-norm bound from `M.IsStable` for §515D — RESOLVED cycle 124

**Resolution (cycle 124)**: This issue is FULLY CONSUMED. Cycle 120's
`aux_515D_iterated_V_bound` (Frobenius-norm hypothesis) is no longer
the active path — instead cycle 124 introduced
`aux_515D_iterated_V_bound_linfty` (Section515.lean:2257) in a
sub-section that opens `Matrix.Norms.Operator`, since `M.IsStable` is
L∞-operator-norm-bounded (defined in Section510.lean with that scope)
and Section515's Frobenius scope was incompatible. The `linfty`
variant produces the same sup'-form bound directly from `M.IsStable`'s
L∞-operator content via `Matrix.linfty_opNNNorm_def`. Cycle 120's
`aux_515D_iterated_V_bound` remains in the file as a
Frobenius-flavoured alternative (kept for narrowing audit) but is
unused on the §515D capstone path. Capstone
`stable_consistent_isConvergent` is now axiom-clean.

---

## Blocker

Closing the §515D `aux_515D_max_deviation_geometric_bound` (cycle
119 narrower helper, `OpenMath/Chapter5/Section515.lean:1819`)
requires bounding `(V_inf_norm + α·h)^n · δ_init n` where
`V_inf_norm := max_i Σ_j |M.V i j|` (i.e. `‖M.V‖_∞` operator-style).

For general stable GLMs, `V_inf_norm` may exceed 1 — `M.IsStable`
only gives `∃ C, ∀ n, ‖M.V^n‖ ≤ C` (power-boundedness), not
`‖M.V‖ ≤ 1`. The naive scalar bound `(V_inf_norm + α·h)^n` therefore
*diverges* as `n → ∞` even though the underlying vector recursion
`δ_(m+1) = M.V · δ_m + K_m` (matrix-vector form) yields a *bounded*
trajectory by power-boundedness.

The fix requires a **vector-typed iterated-V bound** that exploits
power-boundedness directly:

```
∀ k : ℕ, ∀ x : Fin r → ℝ,
  sup'_i |((M.V)^k *ᵥ x) i| ≤ C' · sup'_i |x i|
```

with `C'` depending on the stability constant.

## Context

Per cycle 118 task results §"Dead ends":

> The existing `aux_515D_per_step_recurrence` (cycle 113) and
> `aux_515D_gronwall_bound` (cycle 113) take a SCALAR `δ : ℕ → ℝ`
> sequence with abstract `V_norm` (per_step) or no `V_norm` at all
> (gronwall — sum form). Bridging the per-step recurrence
> `δ(m+1) ≤ V_norm · δ m + α·h·δ m + β·h²` (closed-form) to the
> sum-form `δ m ≤ a + α·h·Σ_{i ∈ Ico 1 m} δ i + β·h²·m` (Grönwall
> input) requires either `V_norm ≤ 1` (telescoping) OR a more
> sophisticated argument exploiting `M.IsStable`'s `‖V^k‖ ≤ C`
> bound.

Per cycle 119 strategy "Backup plan — decomposition fallback if
Step 4 stalls":

> **Option B1**: introduce ONE new helper `aux_515D_iterated_V_bound`
> with sorry body and conclusion:
>
> ```lean
> private theorem aux_515D_iterated_V_bound {r : ℕ}
>     (V : Matrix (Fin r) (Fin r) ℝ)
>     (hStab : ∃ C, 0 ≤ C ∧ ∀ k, ‖V^k‖ ≤ C) :
>     ∃ C', 0 ≤ C' ∧ ∀ k, ∀ x : Fin r → ℝ,
>       Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |(V^k *ᵥ x) i|)
>         ≤ C' * Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |x i|)
> ```

This helper is NOT yet introduced; cycle 119 instead introduces the
broader `aux_515D_max_deviation_geometric_bound` which absorbs the
iterated-V-bound issue inside its sorry'd body.

## What was tried

* **Cycle 118**: drafted manual composition through the cycle 113
  scalar `aux_515D_per_step_recurrence`. Stalled at the
  per-step → sum-form Grönwall bridge (requires `V_norm ≤ 1`).
* **Cycle 119**: introduced
  `aux_515D_max_deviation_geometric_bound` as a Backup B1 helper.
  This abstracts the entire geometric-bound output (including the
  iterated-V bound), narrowing cycle 118's sorry to the geometric
  helper.

## Possible solutions

### Path A: Direct iterated-V bound

Introduce `aux_515D_iterated_V_bound` (per cycle 119 strategy
quoted above) as a separate helper. Its proof:
1. From `hStab`, extract `C : ℝ`, `0 ≤ C`, `∀ k, ‖V^k‖ ≤ C`.
2. Use a Mathlib bridge between matrix `‖·‖` (Frobenius) and
   `linfty_opNorm` to convert: `‖V^k‖_∞ ≤ √r · ‖V^k‖_F ≤ √r · C`.
3. Use `Matrix.linfty_opNorm`'s sup'-bound: for any x,
   `sup'_i |((V^k)·x) i| ≤ ‖V^k‖_∞ · sup'_i |x i| ≤ √r · C · sup'_i |x i|`.
4. Set `C' := √r · C`.

The Mathlib bridge step (3) requires confirming
`Matrix.linfty_opNorm` definition (max row sum of |·|) gives the
right max-abs bound.

### Path B: Schur form / similarity transform

The textbook's argument goes via a similarity transform `V = P·J·P⁻¹`
where `J` is in Jordan normal form, giving `V^k = P·J^k·P⁻¹` and
boundedness of `J^k` from stability. This requires Jordan canonical
form in Mathlib, which is partial (see
`.prover-state/issues/jordan_canonical_form_missing.md`).

Path A is simpler and matches the cycle 119 strategy.

### Path C: Avoid power-boundedness, use M-matrix infrastructure

The §515 M-matrix tools (cycle 106-107) handle `(I − h·L·|A|)`-style
inversions but don't apply directly to V (different matrix, different
hypothesis). An M-matrix-style approach for V would require
re-deriving the analog of `aux_515D_construct_ell_U_phi_A` for V,
which is overkill.

## Recommended path

**Path A** (cycle 119 strategy Backup B1): introduce
`aux_515D_iterated_V_bound` in cycle 120, close it via
`Matrix.linfty_opNorm` bounds + the stability constant.

This keeps the `aux_515D_max_deviation_geometric_bound` sorry
narrowed to the *outer composition*: M-matrix construction + per-step
chain + iterated-V invocation + geometric closed form. Each piece
becomes a clean sub-step.

Once Path A is closed, the §515D capstone closes fully.

## Cycle 120 update — Path A CLOSED

Path A landed in cycle 120 at `OpenMath/Chapter5/Section515.lean:1854`.

The lemma is now a `private theorem` axiom-clean except for standard
Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Constant choice**: `C' := r · C` (with `r : ℕ` cast to `ℝ`). The
proof bypasses the `Matrix.linfty_opNorm` ↔ Frobenius bridge entirely
(which would have required a `√r` factor and a non-default norm scope
switch). Instead it uses the entrywise Frobenius bound
`|V^k_{i,j}| ≤ ‖V^k‖_F` (proved inline via `Matrix.frobenius_norm_def`
+ `Real.sq_sqrt` + `abs_le_of_sq_le_sq`), then a crude row-sum bound
`∑_i |V^k_{j,i}| ≤ r · max_i |V^k_{j,i}| ≤ r · C`, and finally an
elementwise `Finset.sup'_le` argument. Total ~75 LOC.

**Why the elementwise approach worked here**:
- Section515.lean opens `scoped Matrix.Norms.Frobenius`, so the default
  `‖·‖` for matrices is the Frobenius norm — making
  `Matrix.linfty_opNorm_mulVec` (which expects the linfty op norm
  instance to be default) *not directly applicable* without scope
  manipulation.
- The crude `r · C` bound avoids the bridge altogether by working
  entrywise.
- For §515D, the constant doesn't have to be tight — only that it
  exists and is non-negative; `r · C` works fine downstream.

**What remains**: Cycle 120 chose NOT to attempt the body composition
of `aux_515D_max_deviation_geometric_bound` (Priority 2 of the cycle
120 strategy). Per the strategy's "If only iterated-V helper closes:
net advance is +1 closed sub-helper" branch, this is a valid outcome.
The remaining sorry sits at `OpenMath/Chapter5/Section515.lean:1961`
(the geometric_bound itself).

The composition of `aux_515D_max_deviation_geometric_bound`'s body
(now armed with `aux_515D_iterated_V_bound`) is the cycle 121 target.
It will require:
1. Adding `0 ≤ M.glmAbscissae v` as a hypothesis (Step 2a of cycle
   120 strategy) and propagating it upstream — high-risk for §513
   / §514 cascade integrity (see Backup B3 of cycle 120 strategy).
2. M-matrix construction (cycle 114 helper).
3. Per-step recurrence chain via `localStepError_bound` (cycle 116).
4. Closed-form via `aux_515D_per_step_recurrence` (cycle 113).
5. Geometric sum bound + invocation of
   `aux_515D_iterated_V_bound` (cycle 120, this file).
6. Combine into the two-term `C_init · δ_init + C_lin · h_n` shape.

Estimated ~120 LOC. Cycle 121 should plan whether to:
- (a) Attempt the full composition with `0 ≤ c` propagated upstream
  (high risk).
- (b) Introduce one further narrower helper per Backup B2 of cycle
  120 strategy, sorry'd, to isolate the per-step chain.

## Cross-references

* `OpenMath/Chapter5/Section515.lean:1819` —
  `aux_515D_max_deviation_geometric_bound` (cycle 119 narrowing,
  current location of the §515D sorry).
* `OpenMath/Chapter5/Section515.lean:1681` —
  `aux_515D_per_step_recurrence` (cycle 113 closed scalar helper).
* `OpenMath/Chapter5/Section515.lean:1742` —
  `aux_515D_gronwall_bound` (cycle 113 closed sum-form helper).
* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` —
  full §515D blocker history (cycles 110–119).
* `.prover-state/task_results/cycle_118.md` — cycle 118 stall
  analysis on the per-step ↔ Grönwall bridge.
* `.prover-state/task_results/cycle_119.md` — cycle 119 Backup B1
  execution.
