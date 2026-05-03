# Cycle 096 Results

## Worked on

* **PRIMARY DELIVERABLE — `convergence_witness_isVfixed`**: a fresh
  sorry-free private theorem in `OpenMath/Chapter5/Section514.lean`
  asserting that the convergence-witness vector `u'` extracted from
  `M.IsConvergent` (applied to the trivial IVP `y'(x) = 1, y(0) = 0,
  yex := id`) is a fixed point of `M.V`, i.e. `M.V *ᵥ u' = u'`.
* **Algebraic helper — `V_mulVec_glmConstOneIterate_eq`**: a
  sorry-free private lemma encoding the textbook identity
  `V *ᵥ glm h n = glm h n + h • (V^n *ᵥ B𝟙 - B𝟙)`.
* Updated `.prover-state/issues/u_prime_equals_u_bridge.md` to mark
  the `V·u' = u'` half DONE.

Sorry count: **2 → 2** (unchanged; the two pre-existing sorries
`cesaro_residual_tendsto_zero` and `exists_inverse_of_cesaro_zero`
remain — they were explicitly out of scope per Rule 2 of the
strategy).

## Approach

### Priority 0 — Aristotle (skipped)

The strategy explicitly stated to use Aristotle for the algebraic
helper Step 4 *only if* manual work stalled after 30 minutes. The
helper closed cleanly on first attempt after one minor reordering
fix (see Dead Ends), so no Aristotle submission was made.

### Priority 1 — `V_mulVec_glmConstOneIterate_eq` (Step 4 helper)

Direct algebra using cycle 095's closed form:

1. Substitute the closed form on both sides:
   `glm h n = h • Σ_{k<n} V^k *ᵥ B𝟙`.
2. Push `V *ᵥ` through the `h •` and `Σ` shells:
   `Matrix.mulVec_smul`, `Matrix.mulVec_sum`.
3. Inner term rewrite: `V *ᵥ (V^k *ᵥ B𝟙) = V^(k+1) *ᵥ B𝟙` via
   `Matrix.mulVec_mulVec` (forward) + `← pow_succ'`. Wrapped in a
   per-`k` `have hterm` to avoid `simp_rw` over-merging into
   `(V * V^k * B) *ᵥ 𝟙`.
4. Reindex `Σ_{k<n} V^(k+1) = Σ_{k<n+1} V^k - V^0` via
   `Finset.sum_range_succ` (peels `k = n` from the end) +
   `Finset.sum_range_succ'` (peels `k = 0` from the start). Note:
   `sum_range_succ'` puts the constant `f 0` on the **right**, not
   the left.
5. Distribute the leftover `h • ` via `smul_sub`, then close
   componentwise with `linear_combination h * hi` after a `simp only`
   to push `Pi.smul_apply`/`Pi.add_apply`/`Pi.sub_apply`/
   `Finset.sum_apply` through the goal.

### Priority 2 — `convergence_witness_isVfixed` (main deliverable)

Followed the strategy's seven-step skeleton verbatim:

1. **IVP setup**: `f := fun _ => 1`, `yex := id`, `x₀ = y₀ = 0`.
   * `LipschitzWith 0 (fun _ => 1)`: `LipschitzWith.const _`.
   * `id 0 = 0`: `rfl`.
   * `∀ x, HasDerivAt id (f (id x)) x`: `hasDerivAt_id x` (since
     `f (id x) = 1` is the constant-`1` derivative of `id`).
2. **Extract `u'`**: `obtain ⟨u', hu'_ne, hConv'⟩ := hConv f 0
   hf_lip 0 0 yex hyex_x₀ hyex_ode`.
3. **Apply `hConv'` at `φ ≡ 0, x = 1, Y := glmConstOneIterate (1/n)`**:
   * `φ`-tendsto: `u' i * 0 = 0`, RHS is `nhds 0`, LHS is constant
     `0`. Closed by `tendsto_const_nhds`.
   * `Y n 0 = (fun _ => 0)`: definitional `rfl` after `funext`.
   * `M.IsGLMSolution _ f (Y n)`: cycle 095's
     `glmConstOneIterate_isGLMSolution`.
4. **Continuity lift**: `Continuous.matrix_mulVec continuous_const
   continuous_id` gives `Continuous (fun w => M.V *ᵥ w)`. Compose
   with `Tendsto`.
5. **Algebraic step (Step 4 helper)**: pointwise rewrite of
   `M.V *ᵥ Y n n` using `V_mulVec_glmConstOneIterate_eq`.
6. **Residual vanishing**: `‖V^n *ᵥ B𝟙 - B𝟙‖ ≤ K · ‖B𝟙‖ + ‖B𝟙‖` via
   `Matrix.linfty_opNorm_mulVec` + power-boundedness (from §513
   stability via `IsStable.powerBound`). Combined with `(1/n) → 0`
   (`tendsto_one_div_atTop_nhds_zero_nat`) via
   `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded`.
7. **Uniqueness of limits**: `Filter.Tendsto.add` to lift the
   per-`n` identity into a `Y n n + residual → u' + 0 = u'` claim,
   then `tendsto_nhds_unique` against the continuity-lifted
   `M.V *ᵥ Y n n → M.V *ᵥ u'` claim. Done.

## Result

**SUCCESS — sorry count 2 → 2; new closed-form theorem added.**

* `lake env lean OpenMath/Chapter5/Section514.lean` →
  only the two pre-existing sorries (`cesaro_residual_tendsto_zero`,
  `exists_inverse_of_cesaro_zero`) at lines 157/180. No errors.
* `lean_verify` of
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.convergence_witness_isVfixed`
  → axioms `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
* `lean_verify` of
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.V_mulVec_glmConstOneIterate_eq`
  → axioms `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

This hits the strategy's primary success bar (clean new lemma added,
no sorry-count regression) and matches the cycle 095 worker's
recommended option 1.

## Faithfulness check

### `V_mulVec_glmConstOneIterate_eq`

* **Entity ID**: not a textbook entity — Lean-side algebraic
  identity. No JSON to consult.
* **Statement**: pure mechanical identity `V *ᵥ glm h n = glm h n +
  h • (V^n *ᵥ B𝟙 - B𝟙)`. Derivable directly from
  `glmConstOneIterate_closed_form` (cycle 095) by index shifting.
* **Tautology check**: conclusion not present as hypothesis. ✓
* **Identity check**: proof is a multi-step rewrite chain plus a
  reindexing argument. Not `exact h`. ✓
* **Hypothesis strength check**: only requires `h : ℝ` and `n : ℕ`.
  No external assumptions. ✓
* **Absent theorem check**: no comments promising content not
  present. ✓

### `convergence_witness_isVfixed`

* **Entity ID**: no textbook entity — a Lean-side helper toward
  closing `thm:514A`. Documented in the docstring as a partial
  bridge with reference to `u_prime_equals_u_bridge.md`.
* **Statement**: `(hConv : M.IsConvergent) → ∃ u' ≠ 0, M.V *ᵥ u' = u'`.
  This is **half** of the textbook's implicit `u' = u` identification
  in §514's proof outline (Butcher 2008, p. 410). The textbook
  asserts the full bridge implicitly; we prove only the `V·u' = u'`
  half rigorously and document the gap.
* **Lean statement captures**: weaker than the textbook's implicit
  claim (which would be `u' = u` for the preconsistency `u`). The
  difference is documented in the theorem's docstring and in
  `.prover-state/issues/u_prime_equals_u_bridge.md`.
* **Justification for divergence**: the full bridge requires
  multi-cycle work (either a uniqueness theorem for preconsistency
  vectors, or a smarter `φ` argument extracting `U·u' = 𝟙`); cycle
  096 is scoped to the partial bridge per the strategy.
* **Tautology check**: `M.V *ᵥ u' = u'` is not a hypothesis — `u'`
  is an existential extracted from `hConv`. ✓
* **Identity check**: proof is a 100+ LOC multi-step argument. Not
  vacuous. ✓
* **Hypothesis strength check**: requires only `hConv`. Stability /
  power-boundedness derived inline via `M.convergent_isStable hConv`
  (cycle 093) and `IsStable.powerBound`. No textbook-foreign
  hypothesis. ✓
* **Absent theorem check**: no comments promise unwritten content. ✓

## Dead ends

### Dead end 1 — `← Matrix.mulVec_mulVec` direction

First attempt used `simp_rw [← Matrix.mulVec_mulVec, ← pow_succ']`
mirroring cycle 095. This was the **wrong direction**: cycle 095
goes from `V^(k+1) *ᵥ v` to `V *ᵥ (V^k *ᵥ v)` (split direction);
cycle 096 needs the opposite (combine direction). Fixed by
switching to `Matrix.mulVec_mulVec` (forward).

### Dead end 2 — `simp_rw` over-merging

After fixing direction, `simp_rw [Matrix.mulVec_mulVec, ← pow_succ']`
over-merged: turned `V *ᵥ (V^k *ᵥ (B *ᵥ 𝟙))` into the fully-merged
`(V * V^k * B) *ᵥ 𝟙` rather than the intended
`(V * V^k) *ᵥ (B *ᵥ 𝟙)`. Fixed by isolating the per-`k` rewrite into
a `have hterm : ∀ k, M.V *ᵥ (M.V ^ k *ᵥ ...) = M.V ^ (k+1) *ᵥ ...`
auxiliary, then `simp_rw [hterm]` (which only fires the specific
hypothesis, not the whole `Matrix.mulVec_mulVec` simp lemma).

### Dead end 3 — `Finset.sum_range_succ'` order

Initial draft assumed `sum_range_succ'` gives `f 0 + Σ f(k+1)`
(constant on the **left**). The actual lemma puts the constant on
the **right**: `Σ_{k<n+1} f k = Σ_{k<n} f(k+1) + f 0`. Fixed by
flipping the `h1` order.

### Dead end 4 — `linarith` on `h * Σ` goals

Initial proof of `V_mulVec_glmConstOneIterate_eq` used `linarith`
after `simp only` with smul lemmas. `linarith` failed because the
goal's `h * Σ ...` is a nonlinear term (multiplication by an unknown
`h : ℝ`). Switched to `linear_combination h * hi`, which handles
the per-component vector identity by treating the summations as
opaque atoms and multiplying through by `h`.

### Dead end 5 — `simpa using tendsto_one_div_atTop_nhds_zero_nat`

`simpa` triggered an unrelated typeclass instance failure
(`ContinuousSMul ℚ≥0 ?m`). Replaced with an explicit
`funext ... ring` rewrite plus `exact
tendsto_one_div_atTop_nhds_zero_nat`.

## Discovery

* **Cycle 095's `V^(k+1) *ᵥ v ↔ V *ᵥ (V^k *ᵥ v)` reindex idiom is
  bidirectional**: `simp_rw [pow_succ', ← Matrix.mulVec_mulVec]`
  splits, `simp_rw [Matrix.mulVec_mulVec, ← pow_succ']` combines.
  When using the combine direction, isolate the rewrite to a single
  `have` to avoid `simp_rw`'s greedy over-merging across multiple
  `*ᵥ` levels.
* **`Continuous.matrix_mulVec`** is the canonical Mathlib continuity
  fact: takes `Continuous A : X → Matrix m n R` and
  `Continuous B : X → n → R`, returns `Continuous (fun x => A x *ᵥ B
  x)`. For a fixed `M.V` and the identity vector, use
  `continuous_const` and `continuous_id`. Combine with `.tendsto`
  and `.comp` to lift sequence limits.
* **`NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded`** is
  the right tool for `(1/n) • bounded → 0`. Requires
  `IsBoundedUnder (· ≤ ·) l (norm ∘ f)`, which is just an existential
  bound delivered as `⟨bound, Filter.Eventually.of_forall ...⟩` after
  unfolding `Filter.eventually_map`.
* **`linear_combination h * hi`** is a clean closer for vector
  equations of the form "LHS = RHS implies h • LHS = h • RHS"
  componentwise — it handles the multiplication-by-unknown-coefficient
  case where `linarith` fails.
* **`Finset.sum_range_succ'`'s peel direction**: constant `f 0` is
  on the right, summation `Σ f(k+1)` on the left.

## Suggested next approach

For cycle 097 the planner has three candidate priorities:

1. **`U·u' = 𝟙` half of the bridge** — option (b) from
   `u_prime_equals_u_bridge.md`. Apply `hConv'` with a more
   informative `φ` (e.g. `φ(h) i = u_i` for some externally-fixed
   non-zero `u`, satisfying the φ-tendsto with `y₀ = 0` trivially
   since `u_i * 0 = 0`). Examine the GLM stage equation under this
   φ to extract `U·u' = 𝟙` from the structure of the limit. **Hard**
   — likely 200+ LOC, may stall on the stage-vector existential.
2. **Preconsistency-vector uniqueness** (option (c)) — prove "the
   preconsistency vector is unique up to scalar" as a §510 theorem.
   Combined with cycle 096's `V·u' = u'` and `u' ≠ 0`, this would
   give `u' = c · u` for some `c ≠ 0`; the limit at `yex 1 = 1`
   then forces `c = 1`. **Most textbook-faithful path** but requires
   a uniqueness argument that may itself be non-trivial when
   `dim ker(I-V)` could exceed 1.
3. **Pivot to §515/§516** — work ahead while §514 awaits its full
   bridge resolution. May surface infrastructure needs that
   simplify the §514 closure.

I'd recommend option 2 (preconsistency uniqueness) since it's the
closest to the textbook intent and produces an artifact (the
uniqueness lemma) that's reusable beyond `thm:514A`. If the
uniqueness argument requires structural assumptions on `V` that
exceed the textbook hypothesis set, escalate to a parallel issue
and pivot to option 3.
