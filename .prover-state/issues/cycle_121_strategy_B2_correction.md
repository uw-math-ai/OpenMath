# Issue: Cycle 121 strategy Backup B2 has an analytical bug; corrected outline for cycle 122 — RESOLVED cycle 124

**Resolution (cycle 124)**: This issue is RESOLVED. The B2 path was
abandoned in cycle 122 in favour of Path B (per-step K-bound
`α·h·δ_max + β·h²` shape, encapsulated in cycle 123's
`aux_515D_per_step_K_bound`). Cycle 124 closed
`aux_515D_max_deviation_geometric_bound`'s body using Path B
composition + closed-form δ expansion (helper:
`aux_515D_delta_closed_form`) + iterated-V bound (helper:
`aux_515D_iterated_V_bound_linfty`) + sum-form Grönwall (cycle 117).
No B2 was ever needed. Capstone is axiom-clean.

---

## Blocker

The cycle 121 strategy's Backup B2 path (closing `aux_515D_max_deviation_geometric_bound`)
proposes a per-step residual helper

```lean
∃ K_R : ℝ, 0 ≤ K_R ∧
  ∀ n : ℕ, 0 < n → ∀ m : ℕ, m < n →
    sup'_i | (Y n (m+1) i − target (m+1) i)
            − (M.V *ᵥ (fun j => Y n m j − target m j)) i |
      ≤ K_R · h_n^2
```

— claiming the residual `δ(m+1) − V·δ(m)` is bounded by `K_R · h²`,
i.e. *purely* `O(h²)`.

**This claim is mathematically incorrect.** From `localStepError_bound`
(`Section515.lean:1355`, Butcher Lemma 515B), the "leftover" term `K`
in the identity

  `(GLM next-step output) − (target at xn1+h) = (M.V *ᵥ δ) + K`

is bounded as

  `|K i| ≤ α · h · δ_max + β · h²`,

where `δ_max := sup_j |δ j| = sup_j |yt_prev j − target_prev j|`.
The `α · h · δ_max` term is **not** `O(h²)` — it is `O(h) · δ_max`,
where `δ_max` itself can be `O(1)` (the GLM iterate is not a priori
uniformly bounded).

So Backup B2's residual statement, taken literally, is an unprovable
claim. Cycle 122 attempting to prove it as stated will stall.

## Context

Cycle 120 closed `aux_515D_iterated_V_bound`
(`Section515.lean:1835`, Path A): for any power-bounded `V` (i.e.
`∃ C ≥ 0, ∀ k, ‖V^k‖ ≤ C`), there exists `C₀ ≥ 0` with

  `sup'_i |((V^k) *ᵥ x) i| ≤ C₀ · sup'_j |x j|`  for all `k, x`.

This is the load-bearing tool. The remaining `sorry` is at
`Section515.lean:1995`
(`aux_515D_max_deviation_geometric_bound`), which packages the
two-term geometric bound `C_init · sup|δ_init| + C_lin · h_n`.

## What is actually true and provable

The local-step recurrence from `localStepError_bound` is

  `δ(m+1) = M.V *ᵥ δ(m) + K(m)`,
  `|K(m) i| ≤ α · h_n · sup_j |δ(m) j| + β · h_n²`.

By induction on `m`, this unrolls to

  `δ(m) = (M.V)^m *ᵥ δ(0) + ∑_{k<m} (M.V)^(m−1−k) *ᵥ K(k)`.

Applying cycle 120's `aux_515D_iterated_V_bound`:

  `sup'_i |δ(m) i|
     ≤ C₀ · sup'_j |δ(0) j|
       + ∑_{k<m} C₀ · (α · h_n · sup'_j |δ(k) j| + β · h_n²)`.

Letting `u(m) := sup'_i |δ(m) i|`, this is exactly

  `u(m) ≤ C₀ · u(0)
          + C₀ · α · h_n · (∑_{k<m} u(k))
          + C₀ · β · h_n² · m`.

Splitting the sum at `k = 0`:

  `u(m) ≤ (C₀ + C₀ · α · h_n) · u(0)
          + C₀ · α · h_n · (∑_{k ∈ Ico 1 m} u(k))
          + C₀ · β · h_n² · m`.

This **is** the sum-form input of `aux_515D_gronwall_bound`
(`Section515.lean:1742`) with

  `a := (C₀ + C₀ · α · h_n) · u(0)`,
  `α' := C₀ · α`,
  `β' := C₀ · β`.

Applying it gives, for `m = n` (so `n · h_n = x − x₀`):

  `u(n) ≤ exp(α' · (x − x₀)) · a
          + (exp(α' · (x − x₀)) − 1) · (β' · h_n / α')`
        `= exp(α' · (x − x₀)) · (C₀ · (1 + α · h_n)) · u(0)
          + ((exp(α' · (x − x₀)) − 1) · β' / α') · h_n`.

Since `h_n ≤ x − x₀`, we can absorb `(1 + α · h_n)` into a uniform
constant. So:

  `C_init := C₀ · (1 + α · (x − x₀)) · exp(C₀ · α · (x − x₀))`,
  `C_lin  := (exp(C₀ · α · (x − x₀)) − 1) · (C₀ · β) / (C₀ · α)
           = (exp(C₀ · α · (x − x₀)) − 1) · (β / α)`     (cancel C₀)

both non-negative. This closes the geometric bound.

(For the edge case `α = 0` — pure `O(h²)` truncation — the bound
simplifies; handle by case split.)

## Why the cycle 121 strategy blacklisted `aux_515D_gronwall_bound`

The strategy says:

> Do NOT invoke `aux_515D_gronwall_bound` (cycle 113) — it consumes
> a sum-form bound that the vectorial recurrence does not produce
> naturally.

This is mistaken. The vectorial recurrence DOES produce a sum-form
naturally — via the closed-form expansion (Step 4 of the strategy)
combined with cycle 120's iterated V bound (Step 5). The strategy
seems to conflate two different obstacles:

1. The **scalar** `aux_515D_per_step_recurrence` blow-up (`(C₀ + α·h)^n`
   for `C₀ > 1`): this is the cycle 118 dead end, and it IS a real
   obstacle for the *scalar* path.

2. The **sum-form** Grönwall: the cycle 120 iterated V bound
   delivers a **uniform** `C₀` factor on each `V^k *ᵥ K(k)` term,
   which collapses the per-step blow-up. The sum-form Grönwall
   `aux_515D_gronwall_bound` then converts this to an `exp(α' Δx)`
   factor that's bounded.

So `aux_515D_gronwall_bound` IS the right tool, used through the
vectorial path, not the scalar path.

## Why the strategy's B2 helper claim `K_R · h²` is wrong

The strategy's B2 outline (Step 3) splits `R` into:

> (a) Stage-difference contribution: `h_n · M.B *ᵥ (f ∘ Y_int_full m
>     − f ∘ exact_target_int m)`.
> (b) Truncation contribution from the consistency rewrite (Taylor
>     remainder on `yex`).

It claims `localStepError_bound` bounds (a) by
`(stage-error-coefficient) · h_n`, yielding `O(h_n²)` after
multiplying by `‖M.B‖_∞`. But `localStepError_bound`'s actual
conclusion bounds the COMBINED `K = (a) + (b)` by
`α · h · δ_max + β · h²`, with the `α · h · δ_max` term coming
from the propagated stage-deviation `η = Y_int − Yhat` (cycle 107
M-matrix bound: `|η j| ≤ ell_U j · δ_max + h² L² M · phi_A j`).

The propagated `δ_max`-dependent term cannot be eliminated: the
stage error of an implicit GLM is a fixed-point bound that genuinely
depends on the previous-step deviation. The strategy's wishful
splitting "stage error is `O(h)` uniformly" is incorrect.

## Recommended path for cycle 122

### Path A (recommended): full composition via vectorial sum-form Grönwall

Use the corrected outline above. Total expected size: ~150 LOC,
broken into:

1. **Setup** (~10 LOC): set `h_n`, `target`, `δ`, `δ_max(m)`.
2. **Per-step recurrence** (~40 LOC): For each `m < n`, apply
   `localStepError_bound` (cycle 116, full hypothesis package
   already in scope) with `yt_prev := Y n m`, `xn1 := x₀ + m·h_n`.
   Need to choose `c := M.glmAbscissae v`, `ell_U`, `phi_A` via
   `aux_515D_construct_ell_U_phi_A` (cycle 114). Need to choose
   `α`, `β` per `_hα_def`/`_hβ_def`. Extract `K(m)` and the
   identity `δ(m+1) = V·δ(m) + K(m)`.
3. **Iterated V bound** (~5 LOC): `obtain ⟨C₀, hC₀_nn, hC₀⟩` from
   `aux_515D_iterated_V_bound` applied to `M.V` and `_hStab`.
4. **Closed-form expansion** (~30 LOC): Prove by induction on `m`
   that `δ(m) = V^m·δ(0) + ∑_{k<m} V^(m−1−k)·K(k)`.
5. **Sum-form bound** (~25 LOC): Use cycle 120 `hC₀` to bound each
   term of the closed form, deriving
   `u(m) ≤ a + α'·h_n·∑_{k∈Ico 1 m} u(k) + β'·h_n²·m`.
6. **Grönwall application** (~15 LOC): Apply `aux_515D_gronwall_bound`,
   handle `α = 0` edge case via `by_cases`.
7. **Output existential** (~10 LOC): set `C_init`, `C_lin`,
   discharge non-negativity via `linarith`.

### Issue with Path A: `0 ≤ c := M.glmAbscissae v` propagation

`aux_515D_construct_ell_U_phi_A` requires `_hc_nn : 0 ≤ c`.
The current signature of `aux_515D_max_deviation_geometric_bound`
does NOT include this hypothesis. Two sub-paths:

* **A1** (clean, low-risk): prove `0 ≤ M.glmAbscissae v` from the
  existing hypotheses *internally*, as a `have`. The `glmAbscissae`
  is `M.U *ᵥ (M.A · 1)` or similar — needs verification of the
  exact definition, but in practice the consistency hypothesis
  `_hUu : M.U *ᵥ u = (fun _ => 1)` and the existing `_hCons_eq`
  should suffice (or the GLM's structure forces non-negativity).
* **A2**: propagate `_hc_nn` upstream to the
  `aux_515D_max_deviation_geometric_bound` signature. Per the
  cycle 121 strategy (and `cycle_113_isconvergent_strengthening_514_blocker.md`),
  this is high-risk for §513/§514 cascade integrity. AVOID
  unless A1 is genuinely impossible.

Cycle 122 should first verify the `glmAbscissae` definition, then
choose A1 or A2.

### Path B (fallback): introduce a corrected B2 helper

If the full composition stalls, introduce ONE narrower helper with
the **correct** signature

```lean
private theorem aux_515D_per_step_K_bound {s r : ℕ}
    (M : GeneralLinearMethod s r)
    -- (full hypothesis package matching aux_515D_max_deviation_geometric_bound)
    (Y : ℕ → ℕ → Fin r → ℝ) ... :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      ∀ n : ℕ, 0 < n → ∀ m : ℕ, m < n →
        let h_n := (x - x₀) / (n : ℝ)
        let δ := fun (k : ℕ) (i : Fin r) =>
          Y n k i - (u i * yex (x₀ + k * h_n)
                     + v i * h_n * deriv yex (x₀ + k * h_n))
        ∀ i : Fin r,
          |δ (m+1) i - (M.V *ᵥ δ m) i|
            ≤ α * h_n * Finset.sup' Finset.univ Finset.univ_nonempty (fun j => |δ m j|)
              + β * h_n^2
```

with `sorry` body. This isolates the `localStepError_bound`
per-step application + `aux_515D_construct_ell_U_phi_A` invocation
(which is the load-bearing 80 LOC). The outer composition becomes
~70 LOC of induction + sum-form Grönwall, also tractable.

This is the cycle-121-strategy-B2 *with the correct signature*.

## What was tried in cycle 121

Cycle 121 stopped at hygiene-only (Priority 0 + 1 in the strategy):

* **P0 (rename)**: applied — `h_abs_sum`/`h_sum_bd`/`h_card`
  → `habs_sum`/`hsum_bd`/`hcard` in `aux_515D_iterated_V_bound`.
* **P1 (Aristotle)**: cancelled both stale jobs (Job 2: cycle 117
  `aux_515D_componentwise_deviation_tendsto_zero`, redundant since
  cycle 118 already closed; Job 3: cycle 118
  `aux_515D_max_deviation_bound_tendsto_zero`, redundant since
  cycle 119 already closed). Both jobs were `IN_PROGRESS` at
  poll time; cancellation freed the slots without consuming
  results.
* **P2 (geometric bound body)**: NOT attempted. Reason: the
  strategy's B2 fallback path has the analytical bug documented
  above; attempting it as stated would have produced a stalled
  helper with an unprovable signature. Documenting the correction
  here was judged higher-value than producing a cycle-122-blocking
  draft.

## Severity

**Medium**. The strategy bug only affects cycle 121's recommended
fallback path. The recommended Path A (full composition) is
analytically correct and tractable in ~150 LOC, but has not been
attempted. Cycle 122's planner should:

* Plan around Path A with the corrected outline above.
* Be aware that the strategy's B2 needs the corrected signature
  (Path B above) if used as fallback.
* Verify `M.glmAbscissae` definition early (Path A1 vs A2 split).

## Cross-references

* `.prover-state/issues/aux_515D_iterated_V_bound.md` — cycle 120
  Path A closure record (cycle 120 helper).
* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` —
  full §515D blocker history.
* `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md` —
  `_hc_nn` cascade analysis.
* `OpenMath/Chapter5/Section515.lean:1355` — `localStepError_bound`
  (correct K bound).
* `OpenMath/Chapter5/Section515.lean:1681` — `aux_515D_per_step_recurrence`
  (scalar form, has blow-up issue for `C₀ > 1`).
* `OpenMath/Chapter5/Section515.lean:1742` — `aux_515D_gronwall_bound`
  (sum-form, the right tool through the vectorial path).
* `OpenMath/Chapter5/Section515.lean:1835` — `aux_515D_iterated_V_bound`
  (cycle 120, the load-bearing iterated-V bound).
* `OpenMath/Chapter5/Section515.lean:1995` — the `sorry` to close.

## Cycle 122 update — Path B narrowing landed

Cycle 122 implemented Path B (the corrected-signature narrowing helper):

* **New private helper** `aux_515D_per_step_K_bound`
  (`Section515.lean:1898`, sorry'd body) with the analytically-correct
  residual shape

  ```
  |R(m) i| ≤ α · h_n · sup_j |δ(m) j| + β · h_n²
  ```

  matching `localStepError_bound`'s output. The strategy's broken
  `K_R · h²` shape is NOT used.

* **`_hc_nn` propagated** through the §515D internal chain:
  `aux_515D_max_deviation_geometric_bound` ← `..._bound_tendsto_zero`
  ← `..._componentwise_deviation_tendsto_zero` ← `aux_515D_output_tendsto`
  ← `stable_consistent_isConvergent` (added as `hc_nn_witness`).
  See `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`
  for the faithfulness divergence record.

* **No §513 / §514 cascade regression** — both still build cleanly.
  The cascade is contained inside `Section515.lean`.

* **Body composition of `aux_515D_max_deviation_geometric_bound`
  (Step 4 of the cycle 122 strategy)**: deferred. The recipe is
  fully analytical (closed-form expansion + iterated V bound +
  sum-form Grönwall + α=0 case split), but the full composition is
  ~120-150 LOC and exceeds a single-cycle implementation budget when
  combined with the structural narrowing + cascade work + faithfulness
  documentation. Cycle 123 should attempt it.

The §515D `sorry` count is now **2** (in `aux_515D_per_step_K_bound`'s
body and `aux_515D_max_deviation_geometric_bound`'s body), down from
**1 broad sorry** in `aux_515D_max_deviation_geometric_bound` covering
the entire ~150-LOC analytical claim. The narrowing splits the locus
into a focused per-step claim (the new helper) and an outer composition
that is tractable from cycle 120's iterated V bound.
