# Cycle 124 Strategy — close `aux_515D_max_deviation_geometric_bound`

## Status snapshot (post-cycle-123)

* §515D sorry count: **1**, at `OpenMath/Chapter5/Section515.lean:2271`
  (body of `aux_515D_max_deviation_geometric_bound`, signature at line 2235).
* All upstream helpers needed for closure are CLOSED and available:
  * `aux_515D_per_step_K_bound` (cycle 123, line 1953) —
    `∃ α β ≥ 0, ∀ n m i, |Y(m+1) i − target_{m+1} i − (V·δ(m)) i| ≤ α·h_n·sup'_j |δ(m) j| + β·h_n²`.
  * `aux_515D_iterated_V_bound` (cycle 120, line 1835) —
    `∃ C' ≥ 0, ∀ k x, sup'_i |((V^k) *ᵥ x) i| ≤ C' · sup'_j |x j|`.
  * `aux_515D_gronwall_bound` (cycle 117, line 1742) — sum-form
    discrete Grönwall with closed-form `exp(α·n·h)·a + (exp(α·n·h) − 1)·(βh/α)`.
  * `aux_515D_construct_ell_U_phi_A` (cycle 114) — already consumed by
    cycle 123's helper; no need to invoke directly here.
* No pending Aristotle results; no Aristotle work needed this cycle.
* `Section513`/`Section514`/`Section515` all build clean.
  `#print axioms stable_consistent_isConvergent` shows
  `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx`
  traces solely to the line 2271 sorry.

## Priority 1 — close the body of `aux_515D_max_deviation_geometric_bound`

This is the **only** §515D sorry. Closing it makes
`stable_consistent_isConvergent` axiom-clean (drops `sorryAx`) and
flips `lean_status.json` `thm:515D` from `partial` → `formalized`.

### Recipe (~150–200 LOC, follow verbatim)

The body lives at `Section515.lean:2235-2271`. Hypotheses already
include everything you need: `_hStab`, `_hf_lip`, `_hyex_x₀`,
`_hyex_ode`, `_hVu`, `_hUu`, `_hCons_eq`, `_hxx`, `_hM_nn`,
`_hyex_C1`, `_hyex_M`, `_hyex'_LM`, `_h_norm`, `_hc_nn`, `_hc_le_one`,
`[Nonempty (Fin r)]`, `Y`, `Y_int`, `_hY_iter`. Conclusion is

```
∃ C_init C_lin ≥ 0, ∀ n > 0,
  sup'_i |Y n n i − (u_i · yex(x) + v_i · h_n · deriv yex(x))|
    ≤ C_init · sup'_j |Y n 0 j − (u_j · yex(x₀) + v_j · h_n · deriv yex(x₀))|
        + C_lin · h_n
```

where `h_n := (x − x₀) / n`.

#### Step 1 — Setup (~15 LOC)

```lean
have hΔx_pos : 0 < x - x₀ := sub_pos.mpr _hxx
have hΔx_nn : 0 ≤ x - x₀ := hΔx_pos.le
set h_n : ℕ → ℝ := fun n => (x - x₀) / (n : ℝ) with hh_n_def
-- target sequence: target n k i := u_i · yex(x₀ + k·h_n) + v_i · h_n · deriv yex(...)
set target : ℕ → ℕ → Fin r → ℝ := fun n k i =>
  u i * yex (x₀ + (k : ℕ) * h_n n)
    + v i * h_n n * deriv yex (x₀ + (k : ℕ) * h_n n)
  with htarget_def
-- δ-sequence: δ n k i := Y n k i - target n k i
set δ : ℕ → ℕ → Fin r → ℝ := fun n k i => Y n k i - target n k i
  with hδ_def
-- δ_max n k := sup'_i |δ n k i|
set δ_max : ℕ → ℕ → ℝ := fun n k =>
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin r => |δ n k i|)
  with hδ_max_def
have hδ_max_nn : ∀ n k, 0 ≤ δ_max n k := by
  intro n k
  rcases (inferInstance : Nonempty (Fin r)) with ⟨i₀⟩
  exact (abs_nonneg _).trans (Finset.le_sup' _ (Finset.mem_univ i₀))
```

#### Step 2 — Extract α, β from `aux_515D_per_step_K_bound` (~10 LOC)

```lean
obtain ⟨α, β, hα_nn, hβ_nn, hKbnd⟩ :=
  aux_515D_per_step_K_bound M _hStab _hf_lip _hyex_x₀ _hyex_ode _hVu _hUu
    _hCons_eq _hxx _hM_nn _hyex_C1 _hyex_M _hyex'_LM _h_norm
    _hc_nn _hc_le_one Y Y_int _hY_iter
```

`hKbnd : ∀ n > 0, ∀ m + 1 ≤ n, ∀ i, |Y n (m+1) i − target_{m+1} i − (V·δ_m) i| ≤ α·h_n·δ_max n m + β·h_n²`.

The K-bound LHS is precisely `R(m) i` where
`R n m i := Y n (m+1) i − target n (m+1) i − (M.V *ᵥ δ n m) i`.

#### Step 3 — Extract C₀ from `aux_515D_iterated_V_bound` (~10 LOC)

`M.IsStable` unfolds to `∃ C, ∀ k, ‖M.V^k‖ ≤ C` (no `0 ≤ C` clause).
Bridge to the helper's expected `∃ C, 0 ≤ C ∧ ...` shape via `max C 0`:

```lean
obtain ⟨C_raw, hC_pow⟩ := _hStab
have hStab_helper : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖M.V ^ k‖ ≤ C := by
  refine ⟨max C_raw 0, le_max_right _ _, ?_⟩
  intro k
  exact (hC_pow k).trans (le_max_left _ _)
obtain ⟨C₀, hC₀_nn, hC₀_bnd⟩ := aux_515D_iterated_V_bound M.V hStab_helper
```

Now `hC₀_bnd : ∀ k x, sup'_i |((M.V^k) *ᵥ x) i| ≤ C₀ · sup'_j |x j|`.
**Confirm `IsStable`'s definition** in `Section510.lean` first — if
the unfolded form differs, adjust the destructuring (it may have a
named `C_glm` field or similar).

#### Step 4 — Establish the per-step recurrence identity (~20 LOC)

The key algebraic identity is:

```
Y n (m+1) i = (M.V *ᵥ Y n m) i + (M.B *ᵥ (h_n • f∘Y_int_at_step_m)) i
```

(from `M.IsGLMSolution h_n f (Y n)` in `_hY_iter n hn`'s output side).
Subtracting `target_{m+1} i` and rearranging gives the identity

```
δ n (m+1) i = (M.V *ᵥ δ n m) i + R n m i
```

where `R n m i := Y n (m+1) i − target_{m+1} i − (V·δ_m) i` is the
quantity bounded by `hKbnd`.

This identity is purely algebraic — it does NOT require unfolding the
GLM iteration, just the `δ`-definition plus `M.V *ᵥ (Y n m − target n m) =
M.V *ᵥ Y n m − M.V *ᵥ target n m`. Prove inline:

```lean
have hδ_rec : ∀ n k i, δ n (k+1) i = (M.V *ᵥ δ n k) i + R n k i := by
  intros n k i
  simp [δ_def, R_def, Matrix.mulVec_sub]
  ring
```

(define `R` via `set` first to keep proof clean.)

#### Step 5 — Closed-form expansion via induction (~35 LOC)

Prove the vectorial closed form:

```
δ n m = (V^m) *ᵥ δ n 0 + Σ_{k ∈ range m} (V^(m−1−k)) *ᵥ R n k
```

By induction on `m`:

* `m = 0`: `δ n 0 = V^0 · δ n 0 = δ n 0 + Σ ∅`, immediate via
  `pow_zero, Matrix.one_mulVec, Finset.sum_range_zero`.
* `m + 1` (with IH on `m`): from `hδ_rec n m` plus IH:
  ```
  δ n (m+1) = V·δ n m + R n m
            = V · (V^m · δ n 0 + Σ_{k<m} V^(m−1−k) · R n k) + R n m
            = V^(m+1) · δ n 0 + Σ_{k<m} V^(m−k) · R n k + V^0 · R n m
            = V^(m+1) · δ n 0 + Σ_{k<m+1} V^((m+1)−1−k) · R n k
  ```
  Uses `Matrix.mulVec_add`, `Matrix.mulVec_smul`, `pow_succ`,
  `Matrix.mul_mulVec`, `Finset.sum_range_succ`, plus
  `Matrix.mulVec_sum` to commute `V` past the sum.
  The reindexing `m + 1 − 1 − k = m − k` for `k < m` and
  `m + 1 − 1 − m = 0` is `omega`-discharged.

```lean
have hδ_closed : ∀ n, 0 < n → ∀ m, m ≤ n → ∀ i : Fin r,
    δ n m i = ((M.V ^ m) *ᵥ δ n 0) i +
      ∑ k ∈ Finset.range m,
        ((M.V ^ (m - 1 - k)) *ᵥ (R n k)) i := by
  intro n hn m hmn i
  induction m with
  | zero => simp [pow_zero, Matrix.one_mulVec]
  | succ m ih =>
    -- Apply ih at m (with m ≤ n inherited from m+1 ≤ n)
    have hm_le : m ≤ n := Nat.le_of_lt hmn  -- hmn : m+1 ≤ n
    -- Use hδ_rec and pow_succ + Matrix.mul_mulVec
    sorry
```

If induction is heartbeat-heavy, factor as a private helper
`aux_515D_delta_closed_form` (Priority 2 below).

#### Step 6 — Sum-form bound on `δ_max` (~30 LOC)

For each `n > 0` and `1 ≤ m ≤ n`, derive

```
δ_max n m ≤ C₀ · δ_max n 0
            + (C₀ · α) · h_n · (∑_{k ∈ Ico 1 m} δ_max n k)
            + (C₀ · β) · h_n² · (m : ℝ)
```

(NOTE: the sum is over `Ico 1 m` — that's the index range
`aux_515D_gronwall_bound` expects.)

Derivation: take `sup'_i |·|` on both sides of `hδ_closed`, apply
triangle inequality, then use `hC₀_bnd` term-by-term:

```
sup'_i |(V^m · δ n 0) i|         ≤ C₀ · δ_max n 0
sup'_i |(V^(m−1−k) · R n k) i|  ≤ C₀ · sup'_i |R n k i|
                                ≤ C₀ · (α · h_n · δ_max n k + β · h_n²)   [hKbnd]
```

Then the sum-of-sup' is bounded by sum-of-RHS:

```
δ_max n m ≤ C₀ · δ_max n 0 + C₀ · Σ_{k=0}^{m-1} (α·h_n·δ_max n k + β·h_n²)
        = C₀ · δ_max n 0
            + C₀·α·h_n · (Σ_{k=0}^{m-1} δ_max n k)
            + C₀·β·h_n² · m
```

To convert `Σ_{k=0}^{m-1}` to `Σ_{k ∈ Ico 1 m}`, split off `k = 0`:

```
Σ_{k=0}^{m-1} δ_max n k = δ_max n 0 + Σ_{k ∈ Ico 1 m} δ_max n k
```

Absorbing the `δ_max n 0` term into the leading constant:

```
δ_max n m ≤ (C₀ + C₀·α·h_n) · δ_max n 0
            + C₀·α·h_n · (Σ_{k ∈ Ico 1 m} δ_max n k)
            + C₀·β·h_n² · m
```

Since `h_n ≤ x − x₀` (for `n ≥ 1`), `(C₀ + C₀·α·h_n) ≤ C₀ · (1 + α·(x − x₀))`.
Use this as the `a` in `aux_515D_gronwall_bound`.

```lean
have hsum_form : ∀ n, 0 < n → ∀ m, 1 ≤ m → m ≤ n →
    δ_max n m ≤ (C₀ * (1 + α * (x - x₀))) * δ_max n 0
                + (C₀ * α) * h_n n * (∑ k ∈ Finset.Ico 1 m, δ_max n k)
                + (C₀ * β) * (h_n n)^2 * (m : ℝ) := by
  sorry
```

#### Step 7 — Apply Grönwall and emit `C_init`, `C_lin` (~30 LOC)

Two cases:

**Case `α > 0`:** apply `aux_515D_gronwall_bound` with
`a := C₀ · (1 + α·(x − x₀)) · δ_max n 0`, `α' := C₀·α`, `β' := C₀·β`,
`h := h_n n`. At `m = n`, since `n · h_n = x − x₀`:

```
δ_max n n ≤ exp(C₀·α·(x−x₀)) · C₀ · (1 + α·(x − x₀)) · δ_max n 0
            + (exp(C₀·α·(x−x₀)) − 1) · (C₀·β · h_n / (C₀·α))
        = exp(C₀·α·(x−x₀)) · C₀ · (1 + α·(x−x₀)) · δ_max n 0
            + (exp(C₀·α·(x−x₀)) − 1) · (β/α) · h_n
```

So `C_init := exp(C₀·α·(x−x₀)) · C₀ · (1 + α·(x − x₀))`,
`C_lin := (exp(C₀·α·(x−x₀)) − 1) · (β/α)`.

**Case `α = 0`:** the `α·h·Σ δ_max` term vanishes. From Step 6:

```
δ_max n m ≤ C₀ · δ_max n 0 + C₀·β·h_n² · m
```

At `m = n`: `δ_max n n ≤ C₀ · δ_max n 0 + C₀·β·h_n·(x − x₀)`. So
`C_init := C₀`, `C_lin := C₀ · β · (x − x₀)`.

```lean
by_cases hα_pos : 0 < α
· -- α > 0 branch: invoke aux_515D_gronwall_bound
  refine ⟨Real.exp (C₀ * α * (x - x₀)) * C₀ * (1 + α * (x - x₀)),
          (Real.exp (C₀ * α * (x - x₀)) - 1) * (β / α), ?_, ?_, ?_⟩
  · -- C_init ≥ 0
    have hexp_pos : 0 < Real.exp (C₀ * α * (x - x₀)) := Real.exp_pos _
    have h1 : 0 ≤ 1 + α * (x - x₀) := by positivity
    positivity
  · -- C_lin ≥ 0: exp ≥ 1, β/α ≥ 0
    have h_exp_ge_one : 1 ≤ Real.exp (C₀ * α * (x - x₀)) :=
      Real.one_le_exp (by positivity)
    have hβα_nn : 0 ≤ β / α := div_nonneg hβ_nn hα_pos.le
    have : 0 ≤ Real.exp (C₀ * α * (x - x₀)) - 1 := by linarith
    exact mul_nonneg this hβα_nn
  intro n hn
  -- Apply aux_515D_gronwall_bound to (fun m => δ_max n m), at m = n
  have hgron := aux_515D_gronwall_bound (fun m => δ_max n m)
    (C₀ * (1 + α * (x - x₀)) * δ_max n 0)  -- a
    (C₀ * α)                                -- α'
    (C₀ * β)                                -- β'
    (h_n n)                                 -- h
    (by positivity)                          -- ha
    (by positivity)                          -- hα_pos'
    (mul_nonneg hC₀_nn hβ_nn)                -- hβ'_nn
    (div_nonneg hΔx_nn (Nat.cast_nonneg _))  -- hh_nn
    (by sorry : δ_max n 0 ≤ _)              -- hu0 (use hsum_form at m=1? or trivial)
    (by sorry : ∀ m, 1 ≤ m → δ_max n m ≤ _) -- hu_rec via hsum_form
    n
  -- Massage hgron's conclusion into the conclusion shape using
  -- (n : ℝ) · h_n n = x - x₀, then β'/α' = β/α.
  sorry
· -- α = 0 branch: direct from hsum_form with empty sum
  push_neg at hα_pos
  have hα0 : α = 0 := le_antisymm hα_pos hα_nn
  refine ⟨C₀, C₀ * β * (x - x₀), hC₀_nn, by positivity, ?_⟩
  intro n hn
  have hsum := hsum_form n hn n (Nat.one_le_iff_ne_zero.mpr hn.ne') le_rfl
  rw [hα0] at hsum
  simp [zero_mul, mul_zero, add_zero] at hsum
  have hΣrange : (n : ℝ) * h_n n = x - x₀ := by
    field_simp [hh_n_def]
    exact (mul_comm _ _).trans (mul_div_cancel₀ _ (by exact_mod_cast hn.ne'))
  -- δ_max n n ≤ C₀ · δ_max n 0 + C₀ · β · h_n² · n
  --        = C₀ · δ_max n 0 + (C₀ · β · (x − x₀)) · h_n
  sorry
```

The conclusion's first sup' (the `Y n 0 j − ...` form) **equals**
`δ_max n 0` definitionally — verify this:

```
target n 0 j = u_j · yex(x₀ + 0 · h_n) + v_j · h_n · deriv yex(x₀ + 0 · h_n)
            = u_j · yex(x₀) + v_j · h_n · deriv yex(x₀)
```

This is exactly the conclusion's initial-deviation expression. So
`δ_max n 0 = sup'_j |Y n 0 j − (u_j · yex(x₀) + v_j · h_n · deriv yex(x₀))|`
by `simp [δ_def, target_def, mul_comm, ...]` or `rfl`-up-to-`Nat.cast_zero`.

### Avoid these failure modes (from previous cycles)

1. **DO NOT** invoke `aux_515D_per_step_recurrence` (cycle 113) on a
   *scalar* `δ_max` recurrence — that path produces the
   `(V_norm + α·h)^n` blow-up identified in cycle 118 as a dead end.
   Use the **vectorial** closed form (Step 5) chained with
   `aux_515D_iterated_V_bound`.
2. **DO NOT** attempt the Backup B2 strategy from
   `cycle_121_strategy_B2_correction.md` with the broken `K_R · h²`
   shape — `aux_515D_per_step_K_bound` (cycle 123) already
   encapsulates the analytically-correct `α·h·δ_max + β·h²` shape;
   use it.
3. **DO NOT** propagate new hypotheses to the capstone signature
   beyond the existing `_hc_nn` + `_hc_le_one`. Everything else is
   already in scope.
4. **DO NOT** raise `maxHeartbeats`. If Step 5's induction is
   heartbeat-heavy, factor it into a private helper
   `aux_515D_delta_closed_form` (Priority 2 fallback).
5. **DO NOT** strengthen `M.IsStable`'s shape — bridge via `max C 0`
   as in Step 3.
6. **DO NOT** use Aristotle for this body — the proof requires tight
   composition with five §515 helpers; Aristotle will fail without
   extensive axiomatic stubs. Manual composition only.
7. **DO NOT** rename `hδ_*`/`hα_*`/`hβ_*`/`hC₀_*` to the
   underscore-prefixed `h_<name>` form — that triggers the tautology
   scanner. Keep all new hypothesis names underscore-free where they
   are the body of an `exact`/`:= h_*` closer (see
   `tautology_scanner_false_positives.md`).
8. **DO NOT** factor `R n m i := ...` and the cycle-123 helper's
   internal `K_term_eq` together — cycle 123's helper proof is
   already closed; touching it risks regressions. Re-derive the
   `δ`-recurrence identity (Step 4) inline, fresh.

### Verification gates (in order, ALL must pass before commit)

1. `lake env lean OpenMath/Chapter5/Section515.lean` exits 0
   (warnings allowed; pre-existing linter on `hβ_nn`).
2. `lake env lean OpenMath/Chapter5/Section513.lean` exits 0.
3. `lake env lean OpenMath/Chapter5/Section514.lean` exits 0.
4. `lake build OpenMath.Chapter5.Section515` (rebuild .olean to
   avoid stale-cache `sorryAx` false positives — CRITICAL per
   `attempts.md` cycle 072 note).
5. `#print axioms
   OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
   returns `[propext, Classical.choice, Quot.sound]` ONLY (no
   `sorryAx`). If `sorryAx` appears, the cycle is INCOMPLETE — do
   NOT mark `thm:515D` as `formalized`.
6. Tautology scanner: 0 hits via
   ```
   grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' \
     OpenMath/Chapter5/Section515.lean
   ```
7. **If steps 1–6 all pass**: update
   `extraction/formalization_data/lean_status.json` `thm:515D` row:
   `"status": "formalized"`, `"cycle": 124`. Move from `partial`.
8. Update `plan.md` Chapter 5 row for `thm:515D` from `[~]` → `[x]`,
   add the `OpenMath/Chapter5/Section515.lean` reference and update
   the inline note to "(cycle 124: §515D fully closed; capstone
   axiom-clean)".
9. Update issue files:
   * Append a "Cycle 124 update — §515D fully closed" section to
     `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`.
   * Mark `.prover-state/issues/cycle_121_strategy_B2_correction.md`
     as RESOLVED at top.
   * Mark `.prover-state/issues/aux_515D_iterated_V_bound.md` as
     fully consumed.

## Priority 2 — Backup plan if Step 5 induction stalls

If the closed-form expansion in Step 5 produces a Lean elaboration
failure (heartbeat overflow, `motive`-handling issue, or unification
stall), fall back to **factoring a single helper**:

```lean
private theorem aux_515D_delta_closed_form {s r : ℕ}
    (V : Matrix (Fin r) (Fin r) ℝ)
    (δ : ℕ → Fin r → ℝ) (R : ℕ → Fin r → ℝ)
    (hδ_rec : ∀ k i, δ (k+1) i = (V *ᵥ δ k) i + R k i)
    (m : ℕ) (i : Fin r) :
    δ m i = ((V ^ m) *ᵥ δ 0) i +
      ∑ k ∈ Finset.range m, ((V ^ (m - 1 - k)) *ᵥ R k) i := by
  sorry  -- left for cycle 125
```

Then use this helper in the geometric bound's body. Net sorry count:
1 → 1 (+1 helper sorry, −1 main sorry — NET ZERO). This matches the
cycle 122 narrowing pattern.

**Acceptable fallback only if:**
* Direct inline induction in the body produces a verified Lean
  failure (heartbeat overflow, `motive` issue) — verify by
  attempting first.
* The new helper's signature is genuinely cleaner.

**NOT acceptable**: factoring the iterated-V invocation (cycle 120),
the K-bound (cycle 123), or the Grönwall (cycle 117). Those exist;
use them.

## Priority 3 — Hygiene (only if Priority 1 closes early with budget)

If Priority 1 lands cleanly with cycle budget remaining (unlikely
given ~150–200 LOC + verification overhead), run:

* Tautology scanner pass — verify no new `h_<name>` introductions in
  the new code.
* `#print axioms` audit on the three §513/§514 `convergent_*`
  consumers to confirm no regression.
* Trim stale issue file content per supervisor's earlier guidance
  (do NOT remove issue files entirely; mark RESOLVED instead).

Do NOT attempt to start Chapter 4/5 next-target work in this cycle.
The cycle 124 ROI is concentrated in closing §515D's last sorry; a
clean close + faithful documentation is the deliverable.

## Faithfulness gate

The current §515D capstone signature carries TWO documented
faithfulness divergences:

1. `_hc_nn` propagation
   (`stable_consistent_isConvergent_hc_nn.md`).
2. `_hc_le_one` propagation (cycle 123 update in same file).

These are **stable** for cycle 124 — do NOT add new ones. If a new
hypothesis seems necessary during composition, **stop and audit**:
the upstream helpers (cycle 114, 116, 117, 120, 123) all close
without further hypotheses on the inputs already in scope. Any new
hypothesis indicates a missed substitution, a stale signature, or a
bug in the recipe.

## Score expectation

* **Successful Priority 1 close**: §515D sorry count 1 → 0,
  `thm:515D` partial → formalized, capstone axiom-clean. **+2**.
  (§515D was the largest open Chapter-5 entity; closing it unblocks
  forward planning toward §520-§553.)
* **Priority 2 fallback (helper factoring)**: net 0 sorry change,
  structural narrowing to a focused inductive lemma. **+1**.
* **Failure to close + no factored helper**: must produce a
  substantive issue file documenting the obstruction. Worth **0**;
  missing both = **−1**.
