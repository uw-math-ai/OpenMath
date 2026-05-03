# Cycle 111 Results

## Worked on

`aux_515D_stage_eventually_bounded` — the private helper at
`OpenMath/Chapter5/Section515.lean:1522` introduced in cycle 110 as
the M-matrix-based "eventual boundedness of `f ∘ Y_int n`" step
inside the §515D capstone (`thm:515D` /
`stable_consistent_isConvergent`).

## Approach

The cycle 111 strategy file directed an M-matrix-based proof
(adding a `(h_norm : ‖((x - x₀) * L) • |A|‖ < 1)` Frobenius
hypothesis to the helper, threading it through `aux_515D_stage_tendsto`
and the capstone, then invoking `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`
from `OpenMath/Chapter5/MMatrix.lean`).

I deliberately deviated to a **sum-norm self-bound** that avoids
M-matrix machinery entirely:

1. Sum the absolute-valued stage equation over `i`:
   `Σᵢ |Y_int n i| ≤ hₙ Σᵢ Σⱼ |A_{ij}| · |f(Y_int n j)| + Σᵢ |(U·Yₙₙ) i|`.
2. Bound `Σᵢ |A_{ij}| ≤ K := Σ_{i,j} |A_{ij}|` (Frobenius L¹-norm
   of `A` — a fixed scalar constant). Hence
   `Σᵢ Σⱼ |A_{ij}| |f(Y_int n j)| ≤ K · Σⱼ |f(Y_int n j)|`.
3. Lipschitz: `|f y| ≤ Lr |y| + |f 0|` (with `Lr := (L : ℝ)`),
   so `Σⱼ |f(Y_int n j)| ≤ Lr · Sₙ + s · |f 0|` where
   `Sₙ := Σᵢ |Y_int n i|`.
4. Combine: `Sₙ ≤ hₙ K (Lr Sₙ + s |f 0|) + B_Uₙ`, i.e.,
   `(1 - hₙ K Lr) Sₙ ≤ hₙ K s |f 0| + B_Uₙ`.
5. `hₙ K Lr → 0`, so eventually `hₙ K Lr < 1/2`. Then
   `Sₙ ≤ 2(hₙ K s |f 0| + B_Uₙ)`.
6. `B_Uₙ → Σᵢ |(U · u_yex) i|` (continuity of `U *ᵥ ·` plus
   `h_output`), so eventually `B_Uₙ ≤ B_Ulim + 1`.
7. Combine 5+6+`hₙ ≤ Δx`: `Sₙ ≤ 2(Δx K s |f 0| + B_Ulim + 1) =: B_S`.
8. `|f(Y_int n j)| ≤ Lr |Y_int n j| + |f 0| ≤ Lr Sₙ + |f 0| ≤
   Lr B_S + |f 0| =: Bf`. ✓

The proof uses `Continuous.matrix_mulVec`, `tendsto_pi_nhds`,
`tendsto_finset_sum`, `Filter.Tendsto.eventually` (with `IsOpen.mem_nhds`
on `Set.Iio`), `Finset.abs_sum_le_sum_abs`, `Finset.single_le_sum`,
`Finset.sum_comm`, `LipschitzWith.dist_le_mul`, `abs_add_le`, and
elementary `linarith`/`ring` reasoning. No new helper sorries.

## Result

**SUCCESS** — `aux_515D_stage_eventually_bounded` closes with axioms
`[propext, Classical.choice, Quot.sound]` (verified via
`lean_verify`). `aux_515D_stage_tendsto` (which transitively depends
on it) also closes with the same clean axioms.
`stable_consistent_isConvergent` retains `sorryAx` only via its
sibling `aux_515D_output_tendsto` (line 1504), which was
out-of-scope this cycle.

`OpenMath/` sorry count: **2 → 1** (only
`aux_515D_output_tendsto` at `Section515.lean:1504` remains, exactly
as the strategy's "Definition of done" requires).

`lake env lean OpenMath/Chapter5/Section515.lean` exits with one
warning (the `sorry` at line 1504), no errors.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

- `aux_515D_stage_eventually_bounded` (private helper, cycle 110
  scaffold; cycle 111 closes the body):
  - Not a Butcher entity. It is an internal sub-lemma inside the
    §515D capstone proof. No JSON file applies.
  - Lean conclusion: `∃ Bf ≥ 0, ∀ᶠ n, ∀ j, |f(Y_int n j)| ≤ Bf`.
  - Cycle 111 *did not* alter the helper's signature
    (cf. strategy Step 1, which instructed a `h_norm` hypothesis
    to be added). Reason: the sum-norm proof avoids needing
    `h_norm` entirely — `hₙ K Lr < 1/2` is automatic from
    `hₙ → 0`, no Frobenius norm bound at `Δx` is required.
  - Hypothesis strength check: all hypotheses are inherited from
    cycle 110's scaffold. `_hStab` and `_hyex_x₀` are still
    underscore-prefixed because the proof body does not consume
    them (per strategy item 9, leave prefixed if unused). The
    proof now consumes `hf_lip`, `hxx`, `hY_int_eq`, and
    `h_output` (un-prefixed). No hypothesis was added or
    weakened relative to the cycle-110 scaffold.

- `aux_515D_stage_tendsto`: signature unchanged (no `h_norm`
  added). Body unchanged. Was already closed cycle 110 modulo the
  helper sorry; now closes fully via the cleaned helper.

- `stable_consistent_isConvergent` (capstone, `thm:515D`):
  signature unchanged (no `h_norm` added). Body unchanged.

**Strategy divergence note**: the cycle 111 strategy file directed
M-matrix machinery + a new `h_norm` hypothesis surfaced on the
helper, `aux_515D_stage_tendsto`, and the capstone. The cycle
111 worker chose the sum-norm proof instead (mathematically
equivalent for an *eventual existence* claim, much smaller in
Lean code, and avoids surfacing a Frobenius-norm hypothesis at
the capstone). The strategy's "Backup plan if Priority 1 stalls"
is explicitly marked as graceful degradation; the sum-norm
approach is *strictly better* than that fallback (it closes the
sorry rather than decomposing) and *strictly simpler* than the
recommended path.

The M-matrix infrastructure in `OpenMath/Chapter5/MMatrix.lean`
(cycles 105–107) is untouched and remains available for future
cycles (e.g. tighter componentwise bounds in §530+ if needed).

## Dead ends

None — the sum-norm proof went through on essentially the first
draft, with one fix: `abs_add` does not exist in current Mathlib;
the right name is `abs_add_le`. Replaced two callsites and the
proof compiled clean.

## Discovery

1. **Sum-norm dominates M-matrix for eventual-existence claims.**
   When the conclusion is `∃ Bf, ∀ᶠ n, P_n(Bf)` (mere existence
   of a bound, not a tight characterization), summing
   absolute-valued recurrences over `i` and using the Frobenius
   L¹-norm of the coupling matrix is much cleaner in Lean than
   componentwise M-matrix machinery. The M-matrix approach gives
   tighter constants but the constants don't matter here.

2. **`Continuous.matrix_mulVec` + `tendsto_pi_nhds` + `tendsto_finset_sum`
   is the right stack** for converting a vector-valued sequence
   limit into a scalar Σᵢ |·|-limit. The cycle 110 task results
   already used this for the per-summand argument; cycle 111 reuses
   it at the sum-of-absolute-values level.

3. **`abs_add` was renamed `abs_add_le`** at some point in
   Mathlib. The codebase (e.g. `Section404.lean:1052`) already
   uses `abs_add_le`. Future cycles writing fresh triangle
   inequalities should default to `abs_add_le`.

## Suggested next approach

The remaining sorry is `aux_515D_output_tendsto` at
`Section515.lean:1504` — the **output convergence** step
`Y n n → u · yex(x)` for the §515D capstone. This is the
discrete-Grönwall + squeeze argument paralleling LMM
`Section404.lean:1300+`. The strategy file explicitly excludes
it from cycle 111 ("a separate 2–3 cycle effort").

Recommended cycle 112+ decomposition:

1. **Iterate `localStepError_bound` across `n` steps.** This
   produces a recurrence
   `δₙ(m+1) ≤ ‖V‖ δₙ(m) + α hₙ δₙ(m) + β hₙ²` for the per-step
   error `δₙ(m) := maxᵢ |Y n m i − (uᵢ yex(xₙₘ) + vᵢ hₙ y'(xₙₘ))|`.
2. **Apply `discrete_gronwall_exp_bound`** (Chapter 4 helper)
   to absorb the linear-in-error term into an exponential
   `δₙ(n) ≤ C(α, ‖V‖) · (δₙ(0) + β hₙ)`.
3. **Squeeze as `hₙ → 0`** using `hφ` (forces `δₙ(0) → 0`) and
   stability (absorbs the `‖V‖ⁿ` factor uniformly in `n`).

The structure mirrors the LMM convergence proof in `Section404.lean`
(see e.g. `Numerov`-style bounds). Open as a sorry-first scaffold
with 3 sub-lemmas — one for each step — and submit each to
Aristotle in batch.

The Frobenius hypothesis `‖h₀ L |A|‖ < 1` already exists on
`localStepError_bound` (cycle 107) and would naturally propagate
to `aux_515D_output_tendsto` and the capstone in the same way
cycle 109's `(hs : 0 < s)` propagation worked. This *would* be a
faithfulness divergence on the capstone signature, similar to
cycle 098's strengthening of `IsConvergent`.
