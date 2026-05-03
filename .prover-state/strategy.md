# Cycle 101 — Close `localStageError_bound_a` (515a) by manual T1+T2+T3+T4 proof

## Headline target

**REDUCE SORRY COUNT 2 → 1.** Cycle 100 scored −2 because two new sorries
were introduced without closing any. Cycle 101 must close
`localStageError_bound_a` at `OpenMath/Chapter5/Section515.lean:225`
to make positive progress. `localStageError_bound_b` at line 262 stays
as `sorry`; it will be mirrored from the cycle-101 (515a) closure in
cycle 102.

## State of play (already verified by planner)

* Branch tip: `79c0e8b Cycle 100 — open §515 with lem:515A scaffold + aux_y_diff_norm_bound`.
* `OpenMath/Chapter5/Section515.lean` exists, compiles, has 2 sorries
  (lines 225 and 262 — the bodies of `localStageError_bound_a` and
  `localStageError_bound_b`).
* `aux_y_diff_norm_bound` (lines 125–172) is **proved and axiom-clean**.
  It gives: `|y(x + h·ξ) − y(x)| ≤ h · |ξ| · (L · M_bound)` for any
  sign of ξ. **This is your workhorse for both T3 and T4.**
* `glmAbscissae` def + `explicitEulerGLM_glmAbscissae_eq_zero` witness
  are also closed.
* Aristotle project `18cdd9f8-0168-4a49-9721-f214918a7afe` was at
  **1% complete after 40 minutes** when the planner checked. **Do
  NOT poll it repeatedly.** Run `mcp__aristotle__get_status` ONCE at
  the start of the cycle (≤30 seconds). If still <50% complete or
  unchanged, treat Aristotle as not contributing this cycle. Do
  not spawn a new batch — the cycle-100 batch will likely finish
  during cycle 102.

## Priority 0 — Quick Aristotle check (≤30 seconds, ONCE)

Call `mcp__aristotle__get_status` on
`18cdd9f8-0168-4a49-9721-f214918a7afe`. Three cases:

1. **>50% complete or `COMPLETED`**: download via
   `mcp__aristotle__download_result`, copy any returned proofs into
   the corresponding private lemmas (T1/T2/T3/T4) below, verify each
   with `lake env lean OpenMath/Chapter5/Section515.lean`. Then
   continue with Priority 2 (composition step) and any remaining
   sub-lemmas.
2. **<50% complete or unchanged**: skip Aristotle entirely this
   cycle. Go to Priority 1 (manual proofs).
3. **`FAILED`**: same as case 2, skip and go manual. Note in task
   results.

## Priority 1 — Add four private lemmas to `Section515.lean`

Open `OpenMath/Chapter5/Section515.lean`. After
`aux_y_diff_norm_bound` (line 172) and BEFORE the
`/-! ## Lemma 515A — local truncation error bounds` block at line 174,
insert the following four `private theorem`s. Each is closed with a
manual proof. Estimated total: ~180 LOC.

The decomposition is already documented in
`.prover-state/aristotle_submissions/cycle_100/sub_lemmas.lean` —
copy each lemma's signature, but keep the proof bodies in
`Section515.lean` (not the Aristotle file).

### Step 1 — `private theorem aux_T1_eq_zero` (~30 LOC)

Statement (paraphrasing the Aristotle file's `aux_T1_bound`):

```
y (x + h * c_i) - y x - h * ∫ ξ in (0 : ℝ)..c_i, f (y (x + h * ξ)) = 0
```

Hypotheses needed:
* `(hy_C1 : ContDiff ℝ 1 y)`
* `(hy_ode : ∀ t, deriv y t = f (y t))`
* `(x h c_i : ℝ)` (no sign assumption on `c_i`)

**Proof approach** (FTC + affine change of variables):

```
1. Show `f ∘ y` is continuous (already a step in `aux_y_diff_norm_bound`).
2. Apply `intervalIntegral.smul_integral_comp_mul_add` (verified to
   exist in pinned Mathlib by cycle-040 consultant note §H) with
   `c := h, d := x, a := 0, b := c_i, f := fun t => f (y t)`:
     h * ∫ ξ in (0 : ℝ)..c_i, f (y (h * ξ + x))
       = ∫ t in (h * 0 + x)..(h * c_i + x), f (y t)
   The LHS integrand `f (y (h * ξ + x))` matches `f (y (x + h * ξ))`
   modulo `add_comm`; rewrite with `add_comm` once.
3. The RHS bounds simplify: `h * 0 + x = x`, `h * c_i + x = x + h * c_i`.
4. By FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt` applied
   to the derivative `HasDerivAt y (f (y t)) t` (from `hy_C1` and
   `hy_ode`) plus integrability:
     ∫ t in x..(x + h * c_i), f (y t) = y (x + h * c_i) - y x.
5. Cancellation: `y(x + h c_i) - y(x) - (y(x + h c_i) - y(x)) = 0`.
   Closed by `ring` or `linarith`.
```

If the affine substitution is finicky, fall back: define
`G : ℝ → ℝ := fun c => y (x + h * c) - y x - h * ∫ ξ in (0 : ℝ)..c, f (y (x + h * ξ))`
and prove `G c_i = 0` by showing `G 0 = 0` (trivially) and `G` is
constant via `HasDerivAt G 0 c` for all `c` (chain rule + FTC for
the derivative of an integral). This is the alternative cycle-040
consultant §D.2 sketched.

### Step 2 — `private theorem aux_T2_eq_zero` (~30 LOC)

Statement (from Aristotle file's `aux_T2_bound`):

```
y x + c i * h * deriv y x
  - (∑ j, M.U i j * (u j * y x + v j * h * deriv y x))
  - (∑ j, M.A i j * h * deriv y x) = 0
```

Hypotheses (besides `M`, `i : Fin s`):
* `(hUu : M.U *ᵥ u = (fun _ => 1))`
* `(hc_def : c = M.glmAbscissae v)` — equivalently
  `c i = (M.A *ᵥ (fun _ => 1)) i + (M.U *ᵥ v) i`

**Proof approach** (pure algebra):

```
1. Distribute Σ U_{ij} (u_j · y + v_j · h · y'):
     = (Σ U_{ij} u_j) · y + (Σ U_{ij} v_j) · h · y'
     = (M.U *ᵥ u) i · y + (M.U *ᵥ v) i · h · y'      [by definition of mulVec]
     = 1 · y + (M.U *ᵥ v) i · h · y'                  [by hUu]
2. Compute Σ A_{ij} · h · y' = (Σ A_{ij}) · h · y'
   = (M.A *ᵥ (fun _ => 1)) i · h · y'.
3. Apply hc_def: c i = (M.A *ᵥ (fun _ => 1)) i + (M.U *ᵥ v) i.
4. Substitute and `ring`.
```

Useful Mathlib lemmas: `Matrix.mulVec_apply` (or `Matrix.mulVec`
unfold), `Finset.sum_add_distrib`, `Finset.mul_sum`,
`Finset.sum_congr`. Sum-out-constants is `Finset.mul_sum` (or
`mul_comm` then `Finset.sum_mul`).

### Step 3 — `private theorem aux_T3_bound` (~80 LOC, the load-bearer)

**Add new hypothesis** `(hc_i_nonneg : 0 ≤ c_i)`.

> **Faithfulness note** (document in the lemma's docstring): the
> bound is sign-symmetric in `c_i` (textbook §515 doesn't restrict
> the sign), but the proof for `c_i < 0` requires sign-flipping the
> integration interval which doubles the case-split. Cycle 101
> proves the `c_i ≥ 0` case, which covers all standard GLMs
> (explicit Euler `c = 0`, classical RK `c ∈ [0, 1]`, Gauss
> `c ∈ (0, 1)`). The `c_i < 0` case can be added in a follow-up
> if any downstream method needs it.

Statement:

```
|h * ∫ ξ in (0 : ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))|
  ≤ (1/2) * h^2 * L^2 * M_bound * c_i^2
```

Hypotheses: `hL`, `hM`, `hf_lip`, `hy_C1`, `hy_ode`, `hf_y_bound`,
`hh : 0 ≤ h`, `hc_i_nonneg : 0 ≤ c_i`.

**Proof approach** (FTC + Lipschitz + integral_id):

```
1. abs_mul + abs_of_nonneg hh: |h * ∫ …| = h * |∫ …|.
   Goal reduces to: h * |∫ …| ≤ (1/2) * h² * L² * M c_i².
   Divide both sides by h (handle h = 0 separately via `rcases hh.eq_or_lt`):
     |∫ ξ in 0..c_i, (f(y(x+hξ)) - f(y x))|
       ≤ (1/2) * h * L² * M_bound * c_i²

2. Apply `intervalIntegral.abs_integral_le_integral_abs` (need 0 ≤ c_i):
     |∫ …| ≤ ∫ ξ in 0..c_i, |f(y(x+hξ)) - f(y x)|

3. Per-point bound on the integrand (use `intervalIntegral.integral_mono_on`):
   For ξ ∈ [0, c_i]:
     |f(y(x+hξ)) - f(y x)|
       ≤ L * |y(x+hξ) - y(x)|                    [Lipschitz: hf_lip.dist_le_mul + Real.dist_eq]
       ≤ L * (h * |ξ| * (L * M_bound))           [aux_y_diff_norm_bound]
       = L * (h * ξ * (L * M_bound))             [|ξ| = ξ since ξ ∈ [0, c_i] and c_i ≥ 0]
       = h * ξ * (L^2 * M_bound)
   So: ∫_0^{c_i} |…| dξ ≤ ∫_0^{c_i} h * ξ * (L² * M_bound) dξ.

4. Evaluate the bound integral:
     ∫ ξ in 0..c_i, h * ξ * (L² * M_bound)
       = h * (L² * M_bound) * ∫ ξ in 0..c_i, ξ        [intervalIntegral.integral_const_mul, twice]
       = h * (L² * M_bound) * (c_i² / 2)              [intervalIntegral.integral_id]

5. ring to match `(1/2) * h * L² * M_bound * c_i²`.

6. Multiply back by h to recover the original |h * ∫ …| bound.
```

For the Lipschitz step, the bridge is:
`hf_lip.dist_le_mul (y (x + h * ξ)) (y x)` then `Real.dist_eq` and
`NNReal.coe_toNNReal _ hL` to unwrap to absolute values.

Integrability for `integral_mono_on` is discharged by
`Continuous.intervalIntegrable` on each side (continuity follows
from `hy_C1.continuous` and `hf_lip.continuous`).

### Step 4 — `private theorem aux_T4_bound` (~40 LOC)

Statement (from Aristotle file's `aux_T4_bound`):

```
|h * ∑ j, M.A i j * (f (y (x + h * c j)) - f (y x))|
  ≤ h^2 * L^2 * M_bound * ∑ j, |M.A i j * c j|
```

Hypotheses: `hL`, `hM`, `hf_lip`, `hy_C1`, `hy_ode`, `hf_y_bound`,
`hh : 0 ≤ h`. **No** sign assumption on `c j` (uses `|c j|` from
`aux_y_diff_norm_bound`).

**Proof approach** (Lipschitz at discrete abscissae, no integration):

```
1. abs_mul + abs_of_nonneg hh: |h * Σ| = h * |Σ|.
2. Finset.abs_sum_le_sum_abs: |Σ_j A_{ij} * (f(y(x+hc_j)) - f(y x))|
                            ≤ Σ_j |A_{ij}| * |f(y(x+hc_j)) - f(y x)|.
3. Per summand:
     |A_{ij}| * |f(y(x+hc_j)) - f(y x)|
       ≤ |A_{ij}| * L * |y(x+hc_j) - y(x)|                [Lipschitz]
       ≤ |A_{ij}| * L * (h * |c_j| * (L * M_bound))       [aux_y_diff_norm_bound]
       = |A_{ij} * c_j| * h * L² * M_bound                [abs_mul: |A_{ij}*c_j|=|A_{ij}|·|c_j|]
4. Sum and pull h * L² * M_bound out:
     Σ_j |A_{ij} * c_j| * h * L² * M_bound
       = h * L² * M_bound * Σ_j |A_{ij} * c_j|.
5. Multiply by outer h to match h² * L² * M_bound * Σ.
```

Useful Mathlib lemmas: `Finset.abs_sum_le_sum_abs`,
`Finset.sum_le_sum`, `Finset.sum_mul`, `abs_mul`, plus the same
Lipschitz bridge as T3.

## Priority 2 — Close `localStageError_bound_a` by composition

After T1/T2/T3/T4 are all closed, **replace the `sorry` at line 225**
of `localStageError_bound_a` with a ~30 LOC proof:

```lean
intro i
-- Decompose: LHS = T1 + T2 + T3 + T4, where T1 = T2 = 0.
-- Add `(hc_nonneg : ∀ i, 0 ≤ c i)` to the hypothesis bundle for T3.
have hT1 : yex (xn1 + h * c i) - yex xn1
              - h * ∫ ξ in (0 : ℝ)..(c i), f (yex (xn1 + h * ξ)) = 0 :=
  aux_T1_eq_zero hy_C1 hy_ode xn1 h (c i)
have hT2 : yex xn1 + c i * h * deriv yex xn1
            - (∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1))
            - (∑ j, M.A i j * h * deriv yex xn1) = 0 :=
  aux_T2_eq_zero M hUu (hc_def ▸ rfl) xn1 h i  -- adjust to your T2 signature
have hT3 : |h * ∫ ξ in (0 : ℝ)..(c i), (f (yex (xn1 + h * ξ)) - f (yex xn1))|
              ≤ (1/2) * h^2 * L^2 * M_bound * (c i)^2 :=
  aux_T3_bound hL hM hf_lip hy_C1 hy_ode hy'_LM xn1 h hh (c i) (hc_nonneg i)
have hT4 : |h * ∑ j, M.A i j * (f (yex (xn1 + h * c j)) - f (yex xn1))|
              ≤ h^2 * L^2 * M_bound * ∑ j, |M.A i j * c j| :=
  aux_T4_bound M hL hM hf_lip hy_C1 hy_ode hy'_LM xn1 h hh i
-- Algebraic identity: LHS_of_main_theorem = (T1 expression) + (T2 expression)
--                                         + (T3 expression) + (T4 expression).
-- After substituting hT1 = 0 and hT2 = 0, the goal becomes
--   |T3_expr + T4_expr| ≤ (1/2 c_i² + Σ|A_{ij} c_j|) * h² L² M.
-- Apply abs_add and linarith [hT3, hT4].
have hdecomp : (yex (xn1 + h * c i)
                  - h * (∑ j, M.A i j * f (yex (xn1 + h * c j)))
                  - (∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1)))
              = (yex (xn1 + h * c i) - yex xn1
                  - h * ∫ ξ in (0:ℝ)..(c i), f (yex (xn1 + h * ξ)))
              + (yex xn1 + c i * h * deriv yex xn1
                  - (∑ j, M.U i j * (u j * yex xn1 + v j * h * deriv yex xn1))
                  - (∑ j, M.A i j * h * deriv yex xn1))
              + (h * ∫ ξ in (0:ℝ)..(c i), (f (yex (xn1 + h * ξ)) - f (yex xn1)))
              + (h * ∑ j, M.A i j * (f (yex (xn1 + h * c j)) - f (yex xn1))) * (-1) := by
  -- Open the integral split: ∫(f(y(x+hξ))) = ∫(f(y(x+hξ)) - f(y x)) + ∫f(y x)
  -- and ∫_0^{c_i} f(y x) = c_i * f(y x) = c_i * deriv yex xn1 (by hy_ode).
  -- Then ring-normalize. ⚠ This is the only step that may need linarith /
  -- careful manipulation. The integral split requires
  -- `intervalIntegral.integral_sub` plus the constant integral
  -- `intervalIntegral.integral_const`.
  sorry  -- ⚠ the planner expects this `have` to also close, but if it
         -- proves intricate, fall back: prove
         -- |LHS_of_main_theorem| ≤ |T1| + |T2| + |T3| + |T4_signed|
         -- directly via abs_add chained four times. Same outcome.
rw [hdecomp, hT1, hT2, zero_add, zero_add]
-- Goal now: |T3 + (-T4_signed)| ≤ ...
-- ⚠ The (-1) factor on T4 requires |·| = |·|; absorb via
-- `abs_neg` or substitute T4_negated_bound.
calc |…| ≤ |T3_expr| + |T4_expr| := abs_add _ _
       _ ≤ (1/2) * h^2 * L^2 * M_bound * (c i)^2
           + h^2 * L^2 * M_bound * ∑ j, |M.A i j * c j| :=
           add_le_add hT3 hT4
       _ = h^2 * L^2 * M_bound * ((1/2) * (c i)^2 + ∑ j, |M.A i j * c j|) := by ring
```

⚠ The `hdecomp` step is the only non-trivial algebraic step beyond
T1–T4. If it proves intricate, an alternative composition is to
directly bound `|LHS|` via four `abs_add` steps without ever stating
the algebraic identity. The textbook proof works the same way.

## Priority 3 — Update the main theorem signature

`localStageError_bound_a` (line 199) needs an additional hypothesis
`(hc_nonneg : ∀ i, 0 ≤ c i)` for T3 to apply. Add this hypothesis
right before `_hc_def` at line 213:

```lean
(hc_nonneg : ∀ i, 0 ≤ c i)
(_hc_def : c = M.glmAbscissae v) :
```

Update the docstring (lines 182–198) to note the new hypothesis and
the faithfulness divergence (cycle 101 narrowing per Step 3 above).

For consistency, add the same `hc_nonneg` to
`localStageError_bound_b`'s signature (line 237) — even though that
theorem stays as `sorry` this cycle, the signature should be stable
so cycle 102's mirror proof doesn't churn it.

## Priority 4 — Verify, write task results, commit

1. **Verify**: run
   `lake env lean OpenMath/Chapter5/Section515.lean` (no errors,
   exactly 1 sorry warning at line 262 = `localStageError_bound_b`).
2. **Axiom check**: run `lean_verify` on
   `OpenMath.Chapter5.Section510.GeneralLinearMethod.localStageError_bound_a`
   and on each of `aux_T1_eq_zero`, `aux_T2_eq_zero`, `aux_T3_bound`,
   `aux_T4_bound`. Expected: `[propext, Classical.choice, Quot.sound]`.
   Run `lake build OpenMath.Chapter5.Section515` BEFORE the
   axiom check to refresh the .olean cache (per cycle-072 lesson on
   stale-cache `sorryAx` false positives).
3. **Update plan.md**: in the `lem:515A` row, change the cycle-100
   note from
   `(cycle 100 partial: scaffold + aux_y_diff_norm_bound closed; 515a/515b inequalities sorry-first pending T1+T2+T3+T4 sub-bounds)`
   to
   `(cycle 101 partial: 515a closed via T1+T2+T3+T4; 515b mirror pending cycle 102)`.
4. **Faithfulness check** per CLAUDE.md: each new private theorem
   needs a one-liner stating textbook content captured (T1/T2 are
   algebraic identities not in the textbook explicitly; T3/T4 are
   sub-bounds of inequality (515a); the `c_i ≥ 0` narrowing on T3
   is documented).
5. **Update lean_status.json**: bump the `lem:515A` entry's
   `lean_status` from `partial` to (still) `partial` with new
   pointer `OpenMath/Chapter5/Section515.lean::localStageError_bound_a`.
6. **Write `task_results/cycle_101.md`** per CLAUDE.md format.
7. **Commit + push** with message
   `Cycle 101 — close lem:515A inequality (515a) via T1+T2+T3+T4`.

## Hard rules — DO NOT

* **Do NOT** spawn another Aristotle batch this cycle. The cycle-100
  batch is at 1% complete after 40 minutes; spawning another would
  not return in time.
* **Do NOT** modify `aux_y_diff_norm_bound` (already proved,
  axiom-clean). It is the workhorse for both T3 and T4.
* **Do NOT** modify any file outside `OpenMath/Chapter5/Section515.lean`,
  `extraction/formalization_data/lean_status.json`, `plan.md`, and
  `.prover-state/task_results/cycle_101.md`. In particular, do NOT
  touch `Section512.lean`, `Section513.lean`, or `Section514.lean` —
  they hold cycle-098 (`def:512A` strengthening), cycle-093
  (`thm:513A` closure), and cycle-099 (`thm:514A` closure)
  load-bearing for §515.
* **Do NOT** introduce `axiom` or `constant` declarations. If the
  T1 affine substitution proves intractable, use the
  `G(c_i) = G(0) + ∫ G'` fallback per Step 1's note.
* **Do NOT** generalize `localStageError_bound_a` to vector-valued
  `y : ℝ → ℝ^N` — stay scalar to match `aux_y_diff_norm_bound`.
* **Do NOT** raise `maxHeartbeats` above 200000. If a proof step
  hangs, decompose further (e.g., split the `hdecomp` algebraic
  identity into 4 sub-`have`s by piece).
* **Do NOT** remove the `sorry` at line 262 (`localStageError_bound_b`)
  by deleting the theorem or weakening it. The supervisor counts
  sorries in committed files; the right answer is to leave it as
  scaffolding for cycle 102, not to hide it.
* **Do NOT** use the cycle-100 phantom "REVERTED" verdict as a
  reason to undo work. The cycle-100 commit `79c0e8b` is the
  branch tip and was not actually reverted (the score-2 was a
  rubric judgment, not a `git revert`). Build on top of it.
* **Do NOT** rename or restructure `aux_y_diff_norm_bound` — it is
  reused as-is by T3 and T4.

## Faithfulness flags to call out in `cycle_101.md`

For the `Faithfulness check` section, the planner expects the
following entries:

* **`aux_T1_eq_zero`**: not a textbook-numbered lemma. Captures
  the FTC telescoping step from Butcher §515 proof of (515a):
  `Ŷ_i − y(x_{n−1}) − h ∫_0^{c_i} f(y(x_{n−1} + hξ)) dξ = 0`. No
  divergence.
* **`aux_T2_eq_zero`**: not a textbook-numbered lemma. Captures
  the algebraic step using `c = A·𝟙 + U·v` and `U·u = 𝟙`. No
  divergence.
* **`aux_T3_bound`**: not a textbook-numbered lemma; corresponds to
  Butcher's `T3` sub-bound. **Faithfulness divergence**: textbook
  treats `c_i ∈ ℝ`; we restrict to `c_i ≥ 0`. Justification: bound
  is sign-symmetric, all standard GLMs have `c ∈ [0, 1]`,
  `c_i < 0` case can be added when needed. **Strength**: weakening
  hypothesis (extra `0 ≤ c_i`).
* **`aux_T4_bound`**: not a textbook-numbered lemma; corresponds
  to Butcher's `T4` sub-bound. No divergence.
* **`localStageError_bound_a`**: textbook entity `lem:515A`,
  inequality (515a). Captures: same content. **Faithfulness
  divergence**: extra hypothesis `∀ i, 0 ≤ c i` per the T3
  narrowing (inherited).

## Backup plan (only if mid-cycle the manual proofs aren't closing)

If by ~60% of the cycle's compute budget T3 still hasn't closed:

1. Extract T3 to its own one-lemma Aristotle batch
   (`.prover-state/aristotle_submissions/cycle_101/T3_bound.lean`)
   and submit it. Do NOT wait for results — flag it for cycle 102.
2. Close T1, T2, T4 manually (all tractable per the LOC estimates
   above).
3. Leave the composition step in `localStageError_bound_a` partially
   structured: replace the line-225 `sorry` with the four `have`
   blocks (T1/T2/T3 sorry, T4 closed) and a final `sorry` for the
   composition. Net file: 2 sorries (one in the body, one in
   localStageError_bound_b) — same count as cycle 100, no
   regression but no improvement either. Score: probably 0–1, not
   −2.

If instead by ~60% you find yourself re-deriving Mathlib FTC plumbing
from scratch, **stop and use `lean_local_search`/`lean_loogle`** on
the key lemma names listed in the cycle-040 consultant note §H
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`,
`intervalIntegral.norm_integral_le_of_norm_le_const`,
`intervalIntegral.smul_integral_comp_mul_add`,
`intervalIntegral.integral_const_mul`,
`intervalIntegral.abs_integral_le_integral_abs`,
`intervalIntegral.integral_id`, `intervalIntegral.integral_const`,
`intervalIntegral.integral_mono_on`,
`intervalIntegral.integral_sub`, `LipschitzWith.dist_le_mul`).
These are all confirmed to exist in pinned Mathlib v4.28.0.

## Worker action item summary (terse)

1. Quick Aristotle status check (≤30s, ONCE).
2. Add 4 private theorems (`aux_T1_eq_zero`, `aux_T2_eq_zero`,
   `aux_T3_bound`, `aux_T4_bound`) to `Section515.lean`, all closed
   manually (~180 LOC total).
3. Add `(hc_nonneg : ∀ i, 0 ≤ c i)` hypothesis to
   `localStageError_bound_a` (line 199) and to
   `localStageError_bound_b` (line 237) — same signature for both.
4. Replace the `sorry` at line 225 with a ~30 LOC composition
   proof using T1+T2+T3+T4.
5. Verify build + axioms + sorry count = 1.
6. Write `cycle_101.md` and commit.

**Success criteria**: sorry count goes 2→1, axioms clean, faithfulness
documented. Bonus: if 515b also closes (mirror), sorry count goes
2→0; this is the cycle-102 target but counts as positive overhang
this cycle.
