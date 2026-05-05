# Issue: Iterated V-norm bound from `M.IsStable` for §515D

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
