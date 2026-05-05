# Cycle 125 Strategy

## State summary

* Cycle 124 closed §515D capstone (`thm:515D`) axiom-clean. `#print axioms
  GeneralLinearMethod.stable_consistent_isConvergent` returns
  `[propext, Classical.choice, Quot.sound]`.
* **0 sorries** anywhere in `OpenMath/`.
* No pending Aristotle results.
* Progress: 65 / 175 entities.

The §515D closure was the load-bearing Chapter 5 capstone. Forward
progress now opens up §520-§553 stability theory. The cycle 124 task
results recommended forward planning toward §550 / §552, OR a hygiene
cycle. **This cycle does forward progress** with a single targeted
hygiene item.

---

## Priority 1 (PRIMARY) — `thm:520B` Stability Matrix for Linear DE

### Why this target

* §520 already has the stability matrix `M(z) = V + zB(I−zA)⁻¹U`,
  the stability function `Φ(w, z) = det(wI − M(z))`, the stability
  region, the instability region, A-stability, L-stability, and
  stability order — all formalized in cycles 086–088
  (`OpenMath/Chapter5/Section520.lean`, 407 LOC).
* The only §520 theorem still unformalized is `thm:520B` (and
  `thm:520D`, which is heavier — see Priority 3).
* `thm:520B` is the textbook bridge that justifies the
  stability-matrix definition: it says that for the linear test
  equation `y' = qy`, one step of the GLM transforms `y^[n−1] →
  y^[n] = M(hq) y^[n−1]`. **Without this theorem, all of §520's
  apparatus is structurally stable in isolation but not connected to
  GLM dynamics.**
* The textbook proof is 4 lines (Butcher §520, p. 397).
* Dependencies (`def:520A`, `def:520C`) are already formalized.
* Single-cycle target. Estimated 80–120 LOC.

### Textbook statement and proof (Butcher §520, p. 397)

> **Theorem 520B.** Let `M(z)` denote the stability matrix for a general
> linear method. Then, for a linear differential equation (520a),
> (520b) holds with `z = hq`.
>
> **Proof.** For the special problem defined by `f(y) = qy`, the vector
> of stage derivatives `F` is related to the vector of stage values
> `Y` by `F = qY`. Hence, (500c) reduces to the form
> `(Y; y^[n]) = ((A,U); (B,V)) (zY; y^[n−1])`.
> It follows that `Y = (I − zA)⁻¹ U y^[n−1]`, and that
> `y^[n] = zBY + V y^[n−1] = M(z) y^[n−1]`.

The substitution `F = qY` plus `z = hq` eliminates `f` from the GLM
step: stage equation `Y = h·A·F + U·y^[n−1]` becomes
`Y = z·A·Y + U·y^[n−1]`, output equation `y^[n] = h·B·F + V·y^[n−1]`
becomes `y^[n] = z·B·Y + V·y^[n−1]`. Then solve the stage equation
for `Y`, substitute into the output, and the algebraic factorisation
collapses to `M(z) y^[n−1]`.

### Recommended Lean formulation

State as a pure linear-algebra identity over `ℂ` in
`OpenMath/Chapter5/Section520.lean` (just below the existing
`stabilityMatrix` infrastructure, so the new theorem is grouped with
its definitional siblings):

```lean
namespace OpenMath.Chapter5.Section510

open Matrix
open OpenMath.Chapter5.Section520 (complexify)

/-- **Theorem 520B** — Stability matrix governs one step of a GLM
applied to the linear test equation `y' = q·y` with `z = h·q`.

For the linear test equation, `f(y) = q·y` so `F = q·Y` (stage
derivatives = `q` times stage values). The GLM step
`Y = h·A·F + U·y^[n−1]`, `y^[n] = h·B·F + V·y^[n−1]` reduces, with
`z := h·q`, to `Y = z·A·Y + U·y^[n−1]` and
`y^[n] = z·B·Y + V·y^[n−1]`. Provided `(I − z·A)` is invertible,
solving the stage equation gives `Y = (I − z·A)⁻¹·U·y^[n−1]` and
substituting into the output collapses to `y^[n] = M(z)·y^[n−1]`.

Butcher (Theorem 520B, p. 397): "Let `M(z)` denote the stability
matrix for a general linear method. Then, for a linear differential
equation (520a), (520b) holds with `z = hq`." -/
theorem GeneralLinearMethod.stabilityMatrix_linearTest_step
    {s r : ℕ} (M : GeneralLinearMethod s r) (z : ℂ)
    (h_inv : IsUnit (1 - z • complexify M.A))
    (yPrev : Fin r → ℂ) (Y : Fin s → ℂ)
    (hY_stage : Y = z • complexify M.A *ᵥ Y
                    + complexify M.U *ᵥ yPrev) :
    z • complexify M.B *ᵥ Y + complexify M.V *ᵥ yPrev
      = M.stabilityMatrix z *ᵥ yPrev := by
  sorry

end OpenMath.Chapter5.Section510
```

Encoding rationale:

* **Why `IsUnit (1 - z • complexify M.A)` as a hypothesis?** Our
  `stabilityMatrix` definition (line 94) uses `Matrix.inv`, which
  returns junk-zero when the matrix is singular. Without
  `IsUnit`, the theorem is genuinely false — the stage equation
  has either no solution or many, and `M(z)·yPrev` collapses to
  `V·yPrev` (since junk-inverse is 0). The textbook *implicitly*
  restricts to invertible `(I − z·A)`; we surface this faithfully
  as a hypothesis. This is the same pattern as the existing
  `stabilityMatrix` docstring's note (lines 86–93): "downstream
  theorems that need invertibility ... will provide the appropriate
  hypothesis."
* **Why `Y` as a parameter, not `(I−zA)⁻¹·U·yPrev`?** Stating the
  theorem as "any `Y` satisfying the stage equation, under the
  output formula, gives `M(z)·yPrev`" is more flexible for downstream
  callers and avoids re-proving the inversion in each consumer.
  Existence/uniqueness of `Y` is a separate corollary
  (NOT required for `thm:520B` itself).
* **Faithfulness**: the textbook frames this as a step of the GLM
  *applied to* the linear test equation. Our Lean form encodes that
  application's algebraic content directly: `F = qY` plus `z = hq`
  has been pre-substituted into the stage and output equations. No
  fidelity is lost; we are simply working in the post-substitution
  form throughout.
* **Why over `ℂ`?** `def:520A`'s `stabilityMatrix` is `ℂ`-valued
  (the textbook treats `z` as a complex parameter throughout §520).
  Stating `thm:520B` over `ℝ` and then complexifying would create
  a redundant adapter and miss the textbook's `z := hq ∈ ℂ`
  parameterisation.

### Proof outline (concrete)

1. **Solve stage equation.** From `hY_stage`, rearrange:
   ```
   (1 - z • A) *ᵥ Y = U *ᵥ yPrev
   ```
   This uses `Matrix.sub_mulVec` / `Matrix.one_mulVec` /
   `Matrix.smul_mulVec`. Save as `h_stage_solved`.

2. **Apply inverse.** From `h_inv`, the matrix `(1 - z·A)` is a
   `Matrix.IsUnit` (or `Invertible`), so `Matrix.inv` is the genuine
   inverse. Multiply both sides by `(1 - z·A)⁻¹`:
   ```
   Y = (1 - z • A)⁻¹ *ᵥ (U *ᵥ yPrev) = ((1 - z • A)⁻¹ * U) *ᵥ yPrev
   ```
   Use `Matrix.nonsing_inv_mul` or `Matrix.mul_nonsing_inv` plus
   `Matrix.mulVec_mulVec`. Save as `hY_solved`.

3. **Substitute into output.** The goal LHS is
   `z • B *ᵥ Y + V *ᵥ yPrev`. Rewrite `Y` using `hY_solved`:
   ```
   z • B *ᵥ (((1 - z • A)⁻¹ * U) *ᵥ yPrev) + V *ᵥ yPrev
     = (z • B * ((1 - z • A)⁻¹ * U)) *ᵥ yPrev + V *ᵥ yPrev
     = (z • B * ((1 - z • A)⁻¹ * U) + V) *ᵥ yPrev      -- via Matrix.add_mulVec
   ```

4. **Match `M(z)`.** The RHS is
   `M.stabilityMatrix z *ᵥ yPrev`. Unfold `stabilityMatrix`:
   ```
   stabilityMatrix M z = V + z • B * (1 - z • A)⁻¹ * U
   ```
   The two big matrices are equal up to `add_comm`,
   `smul_mul_assoc`, and `mul_assoc`. Close with `congr 1` then
   `noncomm_ring` or by hand via `simp [GeneralLinearMethod.stabilityMatrix]`
   and `ring`.

### Mathlib lemmas to feed Aristotle / use manually

| Goal | Lemma |
|---|---|
| `(1 - C) *ᵥ x = x - C *ᵥ x` | `Matrix.sub_mulVec`, `Matrix.one_mulVec` |
| `(c • C) *ᵥ x = c • (C *ᵥ x)` | `Matrix.smul_mulVec` |
| `(C * D) *ᵥ x = C *ᵥ (D *ᵥ x)` | `Matrix.mulVec_mulVec` |
| `(A + B) *ᵥ x = A *ᵥ x + B *ᵥ x` | `Matrix.add_mulVec` |
| Recover `Y` from `(I − zA)·Y = U·yPrev` under `IsUnit` | `Matrix.IsUnit.inv_mul_cancel_left`-style (search via `lean_local_search "nonsing_inv"` on the actual goal) |
| Unfold `IsUnit` to `Invertible` if needed | `Matrix.IsUnit.invertible` (or use `obtain ⟨Inv, hInv⟩ := h_inv` directly) |
| Prove `nonsing_inv` is a left inverse | `Matrix.nonsing_inv_mul` |

If `Matrix.IsUnit.inv_mul_cancel_left` (the natural shape) doesn't
exist verbatim, use the unfold:

```lean
have hInv : (1 - z • complexify M.A)⁻¹ * (1 - z • complexify M.A) = 1 := by
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det.mp h_inv)
```

Then conclude `Y = (1 - z·A)⁻¹ *ᵥ U *ᵥ yPrev` via:
```lean
have : (1 - z • complexify M.A)⁻¹ *ᵥ ((1 - z • complexify M.A) *ᵥ Y) = Y := by
  rw [← Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
```

### Aristotle batch suggestion

Submit the full proof body as **Job A** (single submission). The
proof is ~30-40 LOC of canonical Mathlib lemmas; Aristotle's
strength on premise selection should land it. Submit in parallel
with Priority 2 (manual) so the 30-min Aristotle wait is amortised.

If Aristotle fails: the proof outline above is concrete enough
that a manual proof is ~80 LOC at worst. Use `lean_multi_attempt`
on each of Steps 1–4 separately to debug.

### Non-vacuity witness

Add a non-vacuity check at end of file:

```lean
/-- Non-vacuity: at `z = 0`, the linear-test step says
`y^[n] = V·y^[n−1]` (since `M(0) = V`), with the trivial stage
witness `Y := U·y^[n−1]`. -/
theorem GeneralLinearMethod.stabilityMatrix_linearTest_step_at_zero
    {s r : ℕ} (M : GeneralLinearMethod s r) (yPrev : Fin r → ℂ) :
    complexify M.V *ᵥ yPrev
      = M.stabilityMatrix 0 *ᵥ yPrev := by
  rw [M.stabilityMatrix_at_zero]
```

This is one line and confirms the theorem reduces correctly at the
identity case. (At `z = 0`, the LHS of the main theorem
`0 • B *ᵥ Y + V *ᵥ yPrev` reduces to `V *ᵥ yPrev`; the witness is
trivial.) Optional — include if the cycle has time.

### Faithfulness check (PRE-COMMIT, MANDATORY)

Before committing, write the following into `cycle_125.md`:

* **Entity ID**: `thm:520B`.
* **Textbook statement** (verbatim from
  `extraction/raw_text/ch05.txt` lines 1556–1570): "Let `M(z)`
  denote the stability matrix for a general linear method. Then,
  for a linear differential equation (520a), (520b) holds with
  `z = hq`."
* **Lean statement captures**: SAME content. The `f(y) = qy` /
  `F = qY` substitution that the textbook performs in the proof's
  setup is pre-applied to the hypotheses (i.e. `hY_stage` is the
  post-substitution form). The conclusion `y^[n] = M(z)·y^[n−1]`
  is identical.
* **Divergences**: hypothesis `IsUnit (1 - z • complexify M.A)` is
  added to surface the textbook's tacit invertibility assumption.
  Documented in the docstring.
* **Tautology check**: theorem conclusion (`y^[n] formula = M(z)·y^[n−1]`)
  is NOT verbatim in the hypotheses (`hY_stage` is the stage equation,
  not the output identity). Real work — passes.

### Update `lean_status.json` and `plan.md`

After the theorem closes:
* `lean_status.json` row `thm:520B`: `not_started` → `formalized`,
  `cycle: 125`, file pointer
  `OpenMath/Chapter5/Section520.lean::GeneralLinearMethod.stabilityMatrix_linearTest_step`.
* `plan.md` Chapter 5 row for `thm:520B`: `[ ]` → `[x]` with the
  cycle 125 note.

---

## Priority 2 — Hygiene: silence the `hβ_nn` warning

`OpenMath/Chapter5/Section515.lean:1713` —
`aux_515D_discrete_gronwall_raw` declares parameter `hβ_nn` but
the proof body uses `nlinarith` only with the hint set
`[mul_div_cancel₀ (β * h) hα_pos.ne', mul_nonneg hα_pos.le hh]`.
The compiler flags `hβ_nn` as unused.

Two fixes are acceptable:

1. **Rename to `_hβ_nn`** (drop the warning by convention; the
   parameter remains in the signature for API symmetry with
   `aux_515D_gronwall_bound` which actually uses `hβ_nn` via
   the wrapper at line 1753).
2. **Add `hβ_nn` to the `nlinarith` hint** at line 1729 and 1733
   (e.g. `nlinarith [..., mul_nonneg hβ_nn hh, ...]`). This is more
   honest if `hβ_nn` is genuinely needed by `nlinarith`'s internal
   search.

Recommended: option 1 (rename to `_hβ_nn`). Verify by `lake env lean
OpenMath/Chapter5/Section515.lean` showing 0 unused-variable warnings
on lines 1713 and similar. **Do NOT touch any other proof body** —
this is a pure rename of one binder.

This also gets cycle 125's `lake env lean Section515.lean` output to
"clean compile" status, which is a useful regression baseline for
the §520-§553 work that consumes §515.

---

## Priority 3 (BONUS, only if Priorities 1+2 land with time to spare)

Skip these unless the cycle is comfortably under-budget. Document
intent if attempted but not closed.

### 3a. Plan `thm:520D` for cycle 126

`thm:520D` (Instability Region Boundary Characterization) is the
last open §520 theorem. Its statement involves "instability region
⊆ {z : Φ(w,z) = 0 for some |w| ≥ 1}" and the reverse with `> 1`.
This is a power-bounded ↔ spectral-radius bridge, requiring
`Module.End.spectralRadius_lt_one_iff_isPowerBounded` or the
matrix-flavoured analog, which Mathlib has only for elements of
a Banach algebra in spectral form. Likely needs a Mathlib bridge
via `Matrix.linfty_op_spectralRadius` or similar. **Don't attempt
this cycle.** File a planning note in
`.prover-state/issues/thm_520D_spectral_radius_bridge.md` if cycle
budget allows: it documents the Mathlib gap and the recommended
proof approach (via Gelfand's formula in
`Mathlib.Analysis.NormedSpace.Spectrum`).

### 3b. NOT recommended: §523A or §550A this cycle

* **`thm:523A`** is a clean algebraic identity but requires
  encoding the *G-norm on r-fold direct sums* (each component a
  vector in `ℝ^N`), the M-norm on `(s+r)·N`-dimensional direct
  sums, and the GLM step over vector-valued outputs. None of this
  infrastructure exists. Multi-cycle target.
* **`thm:550A`** requires the *doubly companion matrix* data
  structure and the polynomial coefficient-extraction machinery
  of (550b). Also multi-cycle.

Both are appropriate cycle-126+ targets. For cycle 125, focus on
the surgical `thm:520B` deliverable.

---

## What NOT to try this cycle

1. **Do NOT modify `IsConvergent`'s strengthening hypotheses
   (cycle 116) or remove `_hc_nn`/`_hc_le_one`** propagated in
   cycle 122/123. The cycle 124 capstone is axiom-clean *given*
   these hypotheses. Reviewing them is post-mortem work; if
   pursued, it is a dedicated cycle, not a side-task.

2. **Do NOT extend `IsGLMSolution` to ℂ-valued solutions.**
   `thm:520B` is a single-step matrix identity; introducing
   `IsGLMSolution_ℂ` would be premature abstraction. State the
   theorem in plain-matrix form (as outlined above) — `IsGLMSolution`
   is for Chapter 5's iteration / convergence theory, not for §520's
   stability theory.

3. **Do NOT introduce `(I − z·A)⁻¹` as a separate definition.** Use
   `Matrix.inv` (the existing `(1 - z • complexify M.A)⁻¹` notation
   in `stabilityMatrix`) directly. A wrapper would create dual
   names and confuse downstream §521-§553 work.

4. **Do NOT touch `scripts/autonomous_loop.py`** — loop-maintainer
   territory per the standing
   `tautology_scanner_false_positives.md` issue.

5. **Do NOT raise `maxHeartbeats`.** The Priority 1 proof is
   ~80 LOC of clean linear algebra; if it hits a heartbeat limit,
   decompose into a stage-solve helper + output-substitute helper.

6. **Do NOT attempt `thm:520D`, `thm:523A`, `thm:550A`** as the
   primary deliverable this cycle. Each requires non-trivial
   infrastructure (spectral radius bridge / G-norm machinery /
   doubly-companion-matrix data) that exceeds a single-cycle
   budget. See Priority 3 above for plan-only treatment.

7. **Do NOT defer the non-vacuity witness** (`stabilityMatrix_linearTest_step_at_zero`)
   if the main theorem closes — it's one line and confirms the
   `z = 0` collapse matches `M(0) = V`. CLAUDE.md's "non-vacuity"
   rule is automatically met by the existing `stabilityMatrix_at_zero`
   theorem, but the linear-test specialisation adds clarity at no
   cost.

8. **Do NOT poll Aristotle more than once.** Submit Job A at the
   start of the cycle, sleep ≥30 min, check once. If still
   IN_PROGRESS at < 50%, treat as a miss and execute the manual
   proof. Per CLAUDE.md.

---

## Cycle order of operations

1. **Submit Aristotle Job A** for `thm:520B` body
   (`stabilityMatrix_linearTest_step`'s `sorry`). Use the proof
   outline above as the prompt. Sleep 30 min.
2. **Apply Priority 2 hygiene fix** (one-line rename). Verify
   with `lake env lean OpenMath/Chapter5/Section515.lean`.
3. **Author the `thm:520B` scaffold** in
   `OpenMath/Chapter5/Section520.lean`: signature, docstring, and
   the four-step proof outline with `sorry` at each step. Verify
   the signature compiles (`lake env lean Section520.lean`).
4. **Manually prove Steps 1–2** (stage equation rearrangement +
   inverse application). Estimated 30 LOC.
5. **Check Aristotle Job A.** If complete, drop in the proof.
   If failed/incomplete, manually prove Steps 3–4 (output
   substitution + `M(z)` matching). Estimated 40 LOC.
6. **Add the `_at_zero` non-vacuity witness.**
7. **Pre-commit faithfulness check** per the section above.
8. **Update `lean_status.json` and `plan.md`.**
9. **Run scanner** (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`)
   — expected zero hits.
10. **`#print axioms`** on the new theorem; expect
    `[propext, Classical.choice, Quot.sound]`.
11. **Write `cycle_125.md`** task results.
12. **Commit** with message `Cycle 125 — close thm:520B
    stabilityMatrix_linearTest_step`.

---

## Success criteria

* `thm:520B` (Stability Matrix for Linear Differential Equation) closed
  axiom-clean.
* `lean_status.json` row updated.
* `plan.md` Chapter 5 row marked `[x]`.
* No new sorries introduced anywhere in `OpenMath/`.
* No tautology-scanner hits.
* `Section515.lean:1713` `hβ_nn` warning silenced.
* §513/§514/§515 build clean as regression baseline.

A cycle that closes Priority 1 alone is a +2. Priority 2 only is a +1
(net hygiene). Both is a +2 with bonus credit for the regression baseline.
