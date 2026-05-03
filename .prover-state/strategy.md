# Cycle 093 Strategy — Close all 3 sorries in `Section513.lean` (`thm:513A` complete)

## Context

Cycle 092 scored **−2 (REVERTED in evaluator log)** because the
sorry count rose from 0 → 3. The substantive work (φ-encoding repair
for `def:512A`, scaffold of `thm:513A`, three closed helpers, two
deferred helpers) is correct and committed at `528fdd7`. The score
reflects the strict reading of CLAUDE.md's "no sorry's in committed
code, unless mid-restructuring" rule.

**Cycle 093's job is to drive the sorry count back to 0.**

Three sorries remain in `OpenMath/Chapter5/Section513.lean`:

| Line | Theorem | Difficulty | Approach |
|---|---|---|---|
| 222 | Helper 2 — `unit_vector_witness_of_not_stable` | medium | row-realiser via `Matrix.linfty_opNNNorm_def` |
| 248 | Helper 5 — `unbounded_zero_iterate_contra` | easy | mirror `unbounded_homogeneous_contra` (Section404.lean:5789) |
| 285 | `convergent_isStable` (main) | medium | line-by-line port of Section405.lean:101–227 |

All three close in one cycle. Total expected manual effort: ~250 lines
across the three. Aristotle is already running on these from cycle 092
(project `82f24aa0-e3e9-457c-9bea-3aede964de8e`); start by checking
its status.

---

## Priority 0 — Aristotle status check (5 minutes)

**Project ID** (from `.prover-state/aristotle_submissions/cycle_092/project_ids.txt`):
`82f24aa0-e3e9-457c-9bea-3aede964de8e`

1. Call `mcp__aristotle__get_status` once.
2. If COMPLETED with returned proofs:
   - For Helpers 1, 3, 4 — already manually closed in cycle 092; **discard
     Aristotle's results unless they are visibly cleaner**. Do not destabilise
     working proofs.
   - For Helpers 2, 5 — port any returned proof. Verify it compiles
     (`lake env lean OpenMath/Chapter5/Section513.lean`). If it works,
     skip the corresponding manual section below and move to the
     remaining work.
3. If still IN_PROGRESS or FAILED — **do not poll again**. Per CLAUDE.md
   ("one check after 30 min is enough"; cycle 092 already waited 30 min).
   Proceed to manual proofs.

---

## Priority 1 — Close Helper 5 `unbounded_zero_iterate_contra` (~25 lines)

**Template**: `LinearMultistepMethod.unbounded_homogeneous_contra` at
`OpenMath/Chapter4/Section404.lean:5789–5813`. The structure is identical;
only the underlying sequence type differs (norm of vectors vs. abs of
reals).

Substitution table:

| LMM template (Section404.lean) | GLM port (Section513.lean) |
|---|---|
| `|η n|` | `‖(M.V ^ n) *ᵥ w n‖` |
| `ζ` (= `runningMaxAbs y`) | `runningMaxNorm (fun n => ‖(M.V ^ n) *ᵥ w n‖)` |
| `hζ_ge : ∀ n, |η n| ≤ ζ n` | derived from `runningMaxNorm_ge` after introducing `z n := ‖V^n *ᵥ w n‖` |
| `hrecord` from `runningMaxAbs_record_above` | `runningMaxNorm_record_above` (extra `hz_nn` hypothesis — supply `fun n => norm_nonneg _`) |
| Final `cases abs_cases (η n)` | **Not needed.** Since `z n ≥ 0` always, no sign split. |

Concrete proof template:

```lean
theorem GeneralLinearMethod.unbounded_zero_iterate_contra
    {s r : ℕ} {M : GeneralLinearMethod s r}
    {w : ℕ → Fin r → ℝ}
    (_hw_unit : ∀ n, ‖w n‖ ≤ 1)
    (hw_unbd : ∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖)
    (hY : Filter.Tendsto
            (fun n : ℕ => ‖(M.V ^ n) *ᵥ w n‖ /
                            runningMaxNorm
                              (fun i => ‖(M.V ^ i) *ᵥ w i‖) n)
            Filter.atTop (nhds 0)) :
    False := by
  set z : ℕ → ℝ := fun n => ‖(M.V ^ n) *ᵥ w n‖ with hz_def
  have hz_nn : ∀ n, 0 ≤ z n := fun n => norm_nonneg _
  have hζ_atTop : Filter.Tendsto (runningMaxNorm z) Filter.atTop Filter.atTop :=
    runningMaxNorm_atTop_of_unbounded hw_unbd
  -- Threshold beyond which `z n / runningMaxNorm z n < 1/2`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, z n / runningMaxNorm z n < 1 / 2 := by
    have hT := Metric.tendsto_atTop.mp hY (1/2) (by norm_num)
    obtain ⟨N, hN⟩ := hT
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    -- `dist (z n / ζ n) 0 < 1/2` ⇒ `|z n / ζ n| < 1/2` ⇒ `z n / ζ n < 1/2`
    -- (since z n ≥ 0 and ζ n ≥ 0 ⇒ ratio ≥ 0).
    rw [Real.dist_eq, sub_zero] at h
    have hnn : 0 ≤ z n / runningMaxNorm z n :=
      div_nonneg (hz_nn n) (le_trans (hz_nn n) (runningMaxNorm_ge z n))
    linarith [abs_of_nonneg hnn]
  -- Threshold beyond which `runningMaxNorm z n > 0`.
  obtain ⟨M', hM⟩ := Filter.eventually_atTop.mp
    (hζ_atTop.eventually_gt_atTop 0)
  -- Find a record index ≥ max N M'.
  obtain ⟨n, hn_ge, hn_record⟩ :=
    runningMaxNorm_record_above hz_nn hw_unbd (Max.max N M')
  have hN' := hN n (le_trans (le_max_left _ _) hn_ge)
  have hM' := hM n (le_trans (le_max_right _ _) hn_ge)
  -- At a record index, `z n / runningMaxNorm z n = 1`.
  rw [hn_record, div_self hM'.ne'] at hN'
  linarith
```

Optional: if `Metric.tendsto_atTop` shape gives trouble, use
`Filter.eventually_atTop.mp` of `(Filter.tendsto_iff_norm_sub_zero.mp hY).eventually …`,
or convert via `nnreal` / abs bridges. The cleanest is the
`Real.dist_eq` rewrite shown above.

---

## Priority 2 — Close Helper 2 `unit_vector_witness_of_not_stable` (~80–100 lines)

**The hardest piece this cycle.** Submit to Aristotle first if not
already returned. While waiting / as backup, build manually.

### Mathlib lemmas verified by consultant search

* `Matrix.linfty_opNorm_def` (`Mathlib/Analysis/Matrix/Normed.lean:280`):
  `‖A‖ = Finset.univ.sup (fun i => ∑ j, ‖A i j‖)` (as `ℝ≥0` via `linfty_opNNNorm_def`).
* `Matrix.linfty_opNorm_mulVec` (`Normed.lean:349`): `‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖`
  — useful for sanity checks, not for the lower bound we need.
* `norm_le_pi_norm` (Mathlib std): `‖f i‖ ≤ ‖f‖` for `f : Π i, α i`
  with the Pi (linfty) norm — gives `‖V^n *ᵥ w n‖ ≥ |((V^n *ᵥ w n) i_n)|`.
* For sign vectors: `Real.sign` is unsuitable (returns `0` at `0`,
  but we want a `±1` choice). Use a custom `if 0 ≤ A i₀ j then 1 else -1`
  — that gives `(if 0 ≤ a then 1 else -1) * a = |a|` for all `a`.

### Proof skeleton

```lean
theorem GeneralLinearMethod.unit_vector_witness_of_not_stable
    {s r : ℕ} {M : GeneralLinearMethod s r} (h_ns : ¬ M.IsStable) :
    ∃ w : ℕ → Fin r → ℝ,
      (∀ n, ‖w n‖ ≤ 1) ∧
      (∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖) := by
  -- Step 1: unfold ¬ IsStable to get an unbounded ‖V^n‖.
  -- M.IsStable = ∃ C, PowerBounded C M.V = ∃ C, ∀ n, ‖V^n‖ ≤ C.
  have hVn_unbd : ∀ C : ℝ, ∃ n, C < ‖M.V ^ n‖ := by
    intro C
    by_contra h
    push_neg at h
    apply h_ns
    refine ⟨C, ?_⟩
    intro n
    exact h n
  -- Step 2: handle r = 0 (degenerate empty matrix) separately.
  by_cases hr : r = 0
  · subst hr
    exfalso
    obtain ⟨n, hn⟩ := hVn_unbd 0
    -- Fin 0 empty ⇒ ‖V^n‖ = 0; contradicts 0 < ‖V^n‖.
    have h0 : ‖M.V ^ n‖ = 0 := by
      simp [Matrix.linfty_opNorm_def, Finset.univ_eq_empty]
    linarith
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
  -- Step 3: for each n, pick a row i_n realising the linfty op norm of V^n.
  -- linfty_opNorm_def: ‖A‖ = sup_i (∑ j, |A i j|). Realiser exists by
  -- Finset.sup' on Finset.univ : Finset (Fin r) (nonempty by hr_pos).
  have hrow_realiser : ∀ n : ℕ,
      ∃ i₀ : Fin r, ∑ j, ‖((M.V ^ n) i₀ j)‖ = ‖M.V ^ n‖ := by
    intro n
    have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
      ⟨⟨0, hr_pos⟩, Finset.mem_univ _⟩
    -- Sup is achieved on a nonempty Finset; bridge sup ↔ sup'.
    -- The exact name may be `Finset.exists_mem_eq_sup'`; try also
    -- `Finset.exists_max_image`, `Finset.sup'_mem_image`. If none of
    -- these exact spellings work, copy the realiser construction from
    -- Mathlib's proof of `linfty_opNNNorm_eq_opNNNorm`
    -- (Mathlib/Analysis/Matrix/Normed.lean:430–447).
    sorry  -- LEAVE HOOK; replace with the appropriate Finset.sup realiser + linfty_opNorm_def bridge
  -- Step 4: build w using Classical.choose on hrow_realiser.
  classical
  let w : ℕ → Fin r → ℝ := fun n j =>
    let i₀ := Classical.choose (hrow_realiser n)
    if 0 ≤ ((M.V ^ n) i₀ j) then 1 else -1
  refine ⟨w, ?_, ?_⟩
  · -- ‖w n‖ ≤ 1: each entry is ±1, sup of |w n j| = 1 ≤ 1.
    intro n
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro j
    show ‖(if 0 ≤ ((M.V ^ n) (Classical.choose _) j) then (1:ℝ) else -1)‖ ≤ 1
    split_ifs <;> simp
  · -- Unboundedness of ‖V^n *ᵥ w n‖.
    intro C
    obtain ⟨n, hn⟩ := hVn_unbd C
    refine ⟨n, ?_⟩
    have hrow := Classical.choose_spec (hrow_realiser n)
    set i₀ := Classical.choose (hrow_realiser n) with hi₀_def
    -- (V^n *ᵥ w n) i₀ = ∑ j, (V^n) i₀ j · w n j = ∑ j, |(V^n) i₀ j|
    have hrow_eq : (M.V ^ n *ᵥ w n) i₀ = ∑ j, ‖((M.V ^ n) i₀ j)‖ := by
      simp only [Matrix.mulVec, Matrix.dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      show (M.V ^ n) i₀ j *
            (if 0 ≤ ((M.V ^ n) i₀ j) then (1:ℝ) else -1) = ‖((M.V ^ n) i₀ j)‖
      rcases le_or_lt 0 ((M.V ^ n) i₀ j) with h | h
      · simp [if_pos h, Real.norm_eq_abs, abs_of_nonneg h]
      · have h' : ¬ 0 ≤ ((M.V ^ n) i₀ j) := not_le.mpr h
        simp [if_neg h', Real.norm_eq_abs, abs_of_neg h]; ring
    -- ‖V^n *ᵥ w n‖ ≥ ‖((V^n *ᵥ w n) i₀)‖ = (∑ j, ‖(V^n) i₀ j‖) = ‖V^n‖.
    have h_pi : ‖((M.V ^ n *ᵥ w n) i₀)‖ ≤ ‖M.V ^ n *ᵥ w n‖ := norm_le_pi_norm _ i₀
    rw [hrow_eq] at h_pi
    have hsum_nn : (0:ℝ) ≤ ∑ j, ‖((M.V ^ n) i₀ j)‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn] at h_pi
    -- h_pi : ∑ j, ‖(V^n) i₀ j‖ ≤ ‖V^n *ᵥ w n‖, and `hrow` rewrites the LHS to ‖V^n‖.
    rw [hrow] at h_pi
    linarith
```

**Note:** the `hrow_realiser` step has one local `sorry` placeholder
because the exact `Finset.sup`-realiser API in Mathlib needs verification.
Try in this order:

1. `lean_local_search "Finset.exists_mem_eq_sup"` — find the exact name.
2. `Finset.exists_max_image` — gives `∃ i ∈ s, ∀ j ∈ s, f j ≤ f i`,
   which combined with `linfty_opNorm_def` gives the realiser via
   `le_antisymm` + sup characterisation.
3. `Finset.sup'`-based route (uses nonemptiness witness explicitly):
   ```
   have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr_pos⟩, Finset.mem_univ _⟩
   obtain ⟨i₀, _, hi₀⟩ :=
     Finset.exists_mem_eq_sup' hne (fun i => ∑ j, ‖((M.V^n) i j)‖)
   ```
   Then bridge `Finset.sup` ↔ `Finset.sup'` via `Finset.sup'_eq_sup`-style
   lemmas, and equate to `‖M.V^n‖` through `linfty_opNNNorm_def` /
   `linfty_opNorm_def` (be careful about `ℝ≥0` ↔ `ℝ` casts).
4. **Last resort**: copy the realiser construction from Mathlib's proof
   of `linfty_opNNNorm_eq_opNNNorm` at
   `Mathlib/Analysis/Matrix/Normed.lean:430–447`. That proof builds the
   row witness inline via `Finset.le_sup`-style reasoning.

---

## Priority 3 — Close `convergent_isStable` (main theorem, ~80 lines)

**Template**: `LinearMultistepMethod.convergent_isStable` at
`OpenMath/Chapter4/Section405.lean:101–227` (full proof). The cycle 092
scaffold already does Steps 1–3 (extract `u`, set up the trivial IVP,
apply `hConv` partially). You need to complete the φ-construction, the
`Y`-construction, the `hY_props` discharge, and the final contradiction.

### Substitution table

| LMM template (Section405.lean) | GLM port (Section513.lean) |
|---|---|
| `intro y hy; by_contra h_bnd; push_neg at h_bnd` | already done — replaced by `obtain ⟨w, hw_unit, hw_unbd⟩ := unit_vector_witness_of_not_stable h_ns` |
| `set ζ := runningMaxAbs y` | `set z : ℕ → ℝ := fun n => ‖(M.V ^ n) *ᵥ w n‖`<br>`set ζ := runningMaxNorm z` |
| `hζ_*` lemmas (4 of them) | same shape via `runningMaxNorm_*` from Section513.lean (use `hz_nn := fun n => norm_nonneg _` where needed) |
| `set start : ℝ → Fin k → ℝ := fun h i => if 0 < h then y i.val / ζ ⌈1/h⌉ else 0` | `set start : ℝ → Fin r → ℝ := fun h i => if 0 < h then ((1:ℝ) / ζ ⌈1/h⌉) * w ⌈1/h⌉ i else 0` |
| `set Y : ℕ → ℕ → ℝ := fun m n => y n / ζ m` | `set Y : ℕ → ℕ → Fin r → ℝ := fun m n i => ((1:ℝ) / ζ m) * ((M.V^n *ᵥ w m) i)` |
| Boilerplate hypotheses for joint-Lipschitz / ContDiff / M_bound | **DROP** — GLM's `IsConvergent` is the simpler textbook version (see `Section512.lean:138`, no `is_convergent_strengthened` clauses). Just `hf_lip : LipschitzWith 0 f` (already have it in scaffold). |
| `hConv f hf_cont 0 hf_lip 0 0 yex hyex_x₀ hyex_C1 hyex_ode 0 hM_bound_nn hf_yex_bound start hstart_tendsto 1 hxx Y hY_props` (10+ args) | `hConv'.2 start hstart_tendsto 1 hxx Y hY_props` — much shorter; `hConv'` already discharged the Lipschitz/ode args at the `obtain` site |
| `hstart_tendsto i` proof: `(y i.val) / ζ ⌈1/h⌉ → 0` via `Tendsto.const_div_atTop` | More involved: `(1/ζ ⌈1/h⌉) * w ⌈1/h⌉ i → 0`. Use `squeeze_zero` with bound `|·| ≤ 1/ζ ⌈1/h⌉` (since `|w ⌈1/h⌉ i| ≤ ‖w ⌈1/h⌉‖ ≤ 1`) and the existing `1/ζ ⌈1/h⌉ → 0` argument. |
| `IsHomogeneousSolution.const_smul` for `Y m`'s recurrence | `glmZeroIterate_const_smul` (Helper 4 from cycle 092) — apply with `c := 1/ζ m` and `y₀ := w m` |
| `LinearMultistepMethod.unbounded_homogeneous_contra ...` | `unbounded_zero_iterate_contra hw_unit hw_unbd htendsto` (Helper 5 from Priority 1) |

### Where the GLM proof differs in detail

1. **`hstart_tendsto`** — the only structurally heavier step. The LMM
   version had a constant numerator `y i.val`; here the numerator
   `w ⌈1/h⌉ i` *also* depends on `h` (via the ceiling). Two routes:

   * **`squeeze_zero` route** (cleanest): bound
     `|start h i| ≤ 1/ζ ⌈1/h⌉` for `0 < h` (using
     `|w ⌈1/h⌉ i| ≤ ‖w ⌈1/h⌉‖ ≤ 1` from `norm_le_pi_norm`), then
     squeeze via `1/ζ ⌈1/h⌉ → 0`. For the `h ≤ 0` branch,
     `start h i = 0` trivially. Combine via `nhdsLE_sup_nhdsGT`
     exactly as in the LMM template's `h_combined`.
   * **`Filter.Tendsto.bdd_mul` route**: less clean because of the
     `h`-dependent boundedness; not recommended.

2. **`hY_props` initial-value clause** — `Y m 0 i = (1/ζ m) * (V^0 *ᵥ w m) i = (1/ζ m) * w m i`
   (using `Matrix.pow_zero` + `Matrix.one_mulVec` or
   `Matrix.mulVec_one`-style). Match against `start (1/m) i = (1/ζ m) * w m i`
   exactly (via the ceiling identity `⌈1 / (1/m)⌉ = m`, which the LMM
   template establishes via `one_div_one_div` + `Nat.ceil_natCast`).

3. **`hY_props` recurrence clause** — `M.IsGLMSolution (1/m) f (Y m)`
   reduces (via `isGLMSolution_zero_iff`) to the homogeneous V-recurrence.
   Apply `glmZeroIterate_const_smul M (1/m) (w m) (1/ζ m)` — that is
   exactly the predicate, after a small algebraic equality
   (`Y m n i = (1/ζ m) * (M.glmZeroIterate (w m) n) i`, which is
   definitional once you unfold `glmZeroIterate`).

4. **Final contradiction** — `hConv'` gives
   `Tendsto (fun n => Y n n) atTop (nhds (fun i => u i * yex 1))`.
   With `yex ≡ 0`, the target is `(fun i => u i * 0) = (fun _ => 0)`
   (the zero vector). Take norms: `‖Y n n‖ → 0` via
   `Tendsto.norm` + `norm_zero`. Then
   `‖Y n n‖ = (1/|ζ n|) * ‖V^n *ᵥ w n‖ = z n / ζ n`
   (use `ζ n ≥ 0` from `runningMaxNorm_ge` chain + `hz_nn`). Apply
   `unbounded_zero_iterate_contra hw_unit hw_unbd htendsto`.

   Do NOT extract a single component `(Y n n) i₀ → 0` and try to use
   that — the norm-of-vector approach is more direct and matches
   Helper 5's signature exactly.

---

## Aristotle batch — keep one running for cycle 094 fallback

If you finish all three sorries manually with time remaining, submit a
fresh batch to Aristotle for `thm:514A` (the next §5 target —
"convergent ⇒ consistent"). This is *not* a cycle 093 deliverable; it
just lets cycle 094 start with Aristotle compute already in flight.
**Skip if cycle 093 takes the full budget.**

---

## Faithfulness check (mandatory before commit)

For `thm:513A` / `convergent_isStable`:

* **Entity ID**: `thm:513A`. **Textbook quote** (from
  `entities/thm_513A.json`): "A general linear method `(A, U, B, V)` is
  convergent only if it is stable."
* **Lean statement**: `M.IsConvergent → M.IsStable`. Captures
  **same content**.
* **Tautology check**: `M.IsStable` is not a hypothesis. ✓
* **Identity check**: the proof body does real work
  (extracts witness, sets up trivial IVP, derives contradiction). ✓
* **Hypothesis-strength check**: only `M.IsConvergent`. ✓
* **Absent theorem check**: every helper used (Helpers 1–5,
  `isGLMSolution_zero_iff`) actually exists and is non-`sorry` in the
  same file or in `Section512.lean`. ✓

For Helpers 2 and 5: each is a genuine intermediate lemma extracted
from the §513 proof, not a re-export. Both have non-trivial bodies.
Pass tautology / identity / smuggling checks.

---

## Build & commit checklist

```bash
# Verify the file compiles with NO sorries.
lake env lean OpenMath/Chapter5/Section513.lean

# Confirm sorry count is 0.
rg '^\s*sorry|by sorry|:= sorry' OpenMath/Chapter5/Section513.lean
# Expected: no matches.

# Axiom check on the main theorem.
lake build OpenMath.Chapter5.Section513
# Then in a temp file or via #print axioms:
#   #print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.convergent_isStable
# Expected: [propext, Classical.choice, Quot.sound] only.

# Update extraction/formalization_data/lean_status.json:
#   thm:513A → status: "formalized", lean_file, lean_symbol, cycle: 93.

# Update plan.md:
#   `[~] thm:513A` → `[x] thm:513A ... — `OpenMath/Chapter5/Section513.lean` (cycle 093)`

# Commit (NEW commit, never amend):
git add OpenMath/Chapter5/Section513.lean \
        extraction/formalization_data/lean_status.json \
        plan.md \
        .prover-state/task_results/cycle_093.md
# also any new aristotle submission dir for cycle 093 if you submitted one
git commit -m "Cycle 093 — close thm:513A (convergent GLM ⇒ stable)"
git push
```

Verify after push:
```bash
git log -1 origin/Main/Experiments --format='%H %s'
# Should match local HEAD.
```

---

## What NOT to do (failed approaches from prior cycles)

* **DO NOT** attempt `thm:514A` ("convergent ⇒ consistent") in cycle 093.
  That is its own cycle. The cycle 092 task results explicitly warn
  against this.
* **DO NOT** revert the cycle 092 scaffold or the φ-encoding repair.
  Both are correct; the −2 score reflects sorry count, not soundness.
  Reverting would lose the strategy work. **Only close the sorries.**
* **DO NOT** modify `def:512A`'s φ encoding back to `∃ φ`. The cycle
  092 repair is mandatory for `thm:513A`'s textbook proof to apply
  (per `glm_convergence_witness_deferred.md` and the LMM precedent at
  `Section404.lean:333`).
* **DO NOT** introduce `axiom`/`constant` shortcuts. CLAUDE.md is
  explicit; if a Mathlib lemma seems missing, build it as a private
  helper in this file.
* **DO NOT** raise `maxHeartbeats` above 200000. Decompose proofs
  instead.
* **DO NOT** edit `scripts/autonomous_loop.py` from the worker. The
  prompt-builder phantom flagged in past consultant notes
  (`tautology_scanner_false_positives.md`) is loop maintainer territory.
* **DO NOT** poll Aristotle more than once. CLAUDE.md is explicit.
* **DO NOT** strengthen GLM's `IsConvergent` predicate (no joint
  Lipschitz / ContDiff / M_bound clauses). The definition committed in
  cycles 091/092 is the textbook-faithful version (see
  `Section512.lean:138–154`); strengthening it would invalidate the
  cycle 091/092 axiom-clean status and require parallel issue work à la
  `is_convergent_strengthened.md`.
* **DO NOT** delete `glmZeroIterate_const_smul` (Helper 4) — even if
  Aristotle returns a "cleaner" inline proof for the main theorem.
  Helper 4 is reused in the `hY_props` recurrence discharge.
* **DO NOT** assume `‖w n‖` means linfty operator norm — for vectors
  `Fin r → ℝ` it is the Pi (linfty) norm, which is `sup_i ‖w n i‖`.
  Use `norm_le_pi_norm` for the bound `‖w n i‖ ≤ ‖w n‖`.
* **DO NOT** spend cycle time chasing the "REVERTED in cycle history"
  framing. The commit `528fdd7` IS in the repo; "REVERTED" here means
  evaluator score, not a git revert. Pattern matches the recurring
  `attempts.md` propagation phantom; verify with `git log -1`.

---

## Fallback if Helper 2 stalls completely

If Aristotle returns nothing for Helper 2 AND the row-realiser
construction takes more than ~90 minutes of manual effort:

1. Close Helper 5 + main theorem (both compile against the *signature*
   of Helper 2, even if its body is `sorry`).
2. Leave Helper 2 as `sorry` with a TODO comment pointing to a
   follow-up issue file.
3. File `.prover-state/issues/glm_helper2_row_realiser.md` documenting
   the specific Mathlib API friction encountered (which lemma name
   you tried, what the goal-state looked like).
4. Commit with sorry count = 1 (down from 3). Still a positive cycle
   relative to the −2 starting point.

But **try** to land all three. The row-realiser has a clear template
in `Mathlib/Analysis/Matrix/Normed.lean:430–447` (the proof of
`linfty_opNNNorm_eq_opNNNorm`) — copy-paste the construction style if
you can't find a one-shot `Finset.sup'` realiser lemma.

---

## Suggested deliverable shape for `task_results/cycle_093.md`

* **Worked on** — the 3 sorries from cycle 092
* **Approach** — Aristotle status check, then mirror Section405.lean +
  Section404.lean templates per substitution tables above
* **Result** — SUCCESS / PARTIAL with sorry count delta (target: 3 → 0)
* **Faithfulness check** — for `thm:513A` and any new helpers
* **Discovery** — anything noticed about the Mathlib `Finset.sup`
  realiser API or `Matrix.linfty_opNorm_def` ergonomics that future
  cycles can reuse
* **Suggested next approach** — `thm:514A` (convergent ⇒ consistent),
  or `thm:515D` (stability + consistency ⇒ convergence), per planner
  preference for cycle 094.
