# Cycle 145 Strategy

## Context summary

* No pending Aristotle results; sorry count is 0.
* Cycle 144 closed Priority 1 cleanly (axiom-clean
  `doublyCompanionMatrix_det_factorization_n_three`, the third
  concrete-`n` stepping stone for Theorem 550A).
* `thm:550A` now has axiom-clean witnesses at `n = 1, 2, 3`. The
  general-`n` proof remains deferred per
  `.prover-state/issues/thm_550A_general_n.md` (Aristotle Job A
  cancelled at 6 % after 24 h in cycle 141; manual cofactor expansion
  remains multi-cycle infrastructure work).
* Cycle 144's discovery: the **explicit-`!![…]` matrix expansion**
  (cycle 138 `_one_eq` style) is the robust template for `det_fin_n`
  proofs over `doublyCompanionMatrix` at small `n` — pre-extract via
  `ext i j; fin_cases i <;> fin_cases j <;> simp
  [doublyCompanionMatrix]`, then a second `fin_cases` block reduces
  `1 - z • X`, then `Matrix.det_fin_n` + `simp; ring` closes the
  polynomial identity. The `unfold doublyCompanionMatrix` + `norm_num`
  shortcut from cycle 140 (n = 2) does **not** transfer to higher `n`
  because the if-then-else chain on `j.val + 1 = n` doesn't decide
  fully under `simp only`.

## Priority 1 (PRIMARY): thm:550A n = 4 stepping stone

**Target.** Add a fourth concrete-`n` axiom-clean witness for
Theorem 550A:

```lean
theorem doublyCompanionMatrix_det_factorization_n_four
    (α β : Fin 4 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 5)
```

(Note `z ^ (n + 1) = z ^ 5` for `n = 4`.)

**Location**: `OpenMath/Chapter5/Section550.lean`, immediately after
`doublyCompanionMatrix_det_factorization_n_three` (currently the last
declaration in the namespace, ending around line 272).

**Why this target**:

1. Mechanical extension following the proven cycle 144 template.
2. Establishes a fourth data point confirming the textbook
   leading-coefficient pattern
   `det(I − zX) − α(z)·β(z) ≡ −Σᵢ αᵢ·β_{n−i} · z^{n+1} + O(z^{n+2})`.
3. Builds toward general-`n` proof by accumulating concrete data with
   explicit residue closed forms.
4. Single-cycle, axiom-clean target with realistic ~150–200 LOC
   budget.
5. Strict net advance (sorry count stays at 0; one new public
   theorem).

## Approach (follow cycle 144 n = 3 template verbatim)

### Step 0 (read precedent — first action of the cycle)

Open `OpenMath/Chapter5/Section550.lean` and re-read
`doublyCompanionMatrix_det_factorization_n_three` (lines ~206–272).
The proof sequence is:

1. `have h_diff : (residue) = (fun z => z^4 * (a + z * b + z² * c)) := by`
2. `funext z; ext-and-fin-cases` to extract `doublyCompanionMatrix α β`
   as an explicit `!![…]` matrix `hX`.
3. `rw [hX]; ext-and-fin-cases` to expand `1 − z • X` as another
   explicit `!![…]` matrix `hmat`.
4. `rw [hmat, Matrix.det_fin_n]; simp [alphaPoly, betaPoly,
   Fin.sum_univ_n]; ring` to close the polynomial identity.
5. `rw [h_diff]`; then `IsBigO.of_bound C` with constant
   `‖a‖ + ‖b‖ + ‖c‖ + …`.
6. `Metric.eventually_nhds_iff` + `⟨1, by norm_num, fun y hy => ?_⟩`
   localize to `‖y‖ < 1`.
7. Triangle-inequality chain for the inner-factor norm.
8. Multiply through by `‖y^(n+1)‖` and close with `ring`.

### Step 1 (paper algebra — DO THIS BEFORE TOUCHING LEAN)

The `n = 4` doubly companion matrix `X = doublyCompanionMatrix α β`
has shape (per the `doublyCompanionMatrix` definition; verify by
checking the case-split on each `(i, j)` of `Fin 4 × Fin 4`):

```
X = !![−α 0,  −α 1,  −α 2,  −α 3 − β 3;
       1,     0,     0,     −β 2;
       0,     1,     0,     −β 1;
       0,     0,     1,     −β 0]
```

Then `1 − z • X` is

```
!![1 + z·α 0,   z·α 1,    z·α 2,    z·(α 3 + β 3);
   −z,          1,        0,        z·β 2;
   0,           −z,       1,        z·β 1;
   0,           0,        −z,       1 + z·β 0]
```

Compute `det(1 − z • X)` via cofactor expansion or `Matrix.det_fin_four`.
The `Matrix.det_fin_four` lemma exists in Mathlib (verify with
`lean_local_search "det_fin_four"` or `Grep` first; if absent, fall
back to manual cofactor expansion along the first column or use
`Matrix.det_succ_column_zero` recursively — see Step 4 fallback).

Compute `alphaPoly α z · betaPoly β z` symbolically up to `z⁵`. The
product is a polynomial of degree `2·4 = 8`. The cancellation of the
`z⁰…z⁴` terms is the textbook content; the residue should be:

* leading `z⁵` coefficient: `−(α 0·β 3 + α 1·β 2 + α 2·β 1 + α 3·β 0)`
  (the convolution `−Σᵢ αᵢ·β_{n−i}` at `n = 4`).
* `z⁶`: `−(α 1·β 3 + α 2·β 2 + α 3·β 1)`.
* `z⁷`: `−(α 2·β 3 + α 3·β 2)`.
* `z⁸`: `−(α 3·β 3)`.

Factor the residue as `z^5 · (a + z·b + z²·c + z³·d)` with
* `a := −(α 0·β 3 + α 1·β 2 + α 2·β 1 + α 3·β 0)`
* `b := −(α 1·β 3 + α 2·β 2 + α 3·β 1)`
* `c := −(α 2·β 3 + α 3·β 2)`
* `d := −(α 3·β 3)`

**WRITE THE PAPER ALGEBRA INTO A SCRATCH NOTE FIRST.** Verify the
cancellation of `z⁰…z⁴` terms explicitly before writing Lean. The
worker MUST not skip this step — if the residue's leading
coefficients are wrong, the `ring` step in Lean will fail and waste
cycle time.

### Step 2 (Lean encoding — follow cycle 144 template)

```lean
theorem doublyCompanionMatrix_det_factorization_n_four
    (α β : Fin 4 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 5) := by
  -- Step 1: rewrite the residue pointwise.
  have h_diff : (fun z : ℂ =>
      (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z)
      = (fun z : ℂ => z ^ 5 *
          (a + z * b + z ^ 2 * c + z ^ 3 * d)) := by
    funext z
    -- 2a: reduce X to !![…].
    have hX : doublyCompanionMatrix α β =
        !![-α 0,  -α 1,  -α 2,  -α 3 - β 3;
           1,     0,     0,     -β 2;
           0,     1,     0,     -β 1;
           0,     0,     1,     -β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]
    rw [hX]
    -- 2b: reduce `1 - z • X` to !![…].
    have hmat :
        (1 - z • !![…the matrix above…] : Matrix (Fin 4) (Fin 4) ℂ)
          = !![1 + z * α 0,   z * α 1,    z * α 2,    z * (α 3 + β 3);
               -z,            1,          0,          z * β 2;
               0,             -z,         1,          z * β 1;
               0,             0,          -z,         1 + z * β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | (simp; ring) | simp
    rw [hmat, Matrix.det_fin_four]   -- or fallback per Step 4
    simp [alphaPoly, betaPoly, Fin.sum_univ_four]
    ring
  rw [h_diff]
  -- Step 3: IsBigO bound.
  refine Asymptotics.IsBigO.of_bound (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) ?_
  rw [Metric.eventually_nhds_iff]
  refine ⟨1, by norm_num, fun y hy => ?_⟩
  rw [Complex.dist_eq, sub_zero] at hy
  -- Bound: ‖a + y·b + y²·c + y³·d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖.
  have h_inner : ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
                   ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    have hyb : ‖y * b‖ ≤ ‖b‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hy.le
    have hyc : ‖y ^ 2 * c‖ ≤ ‖c‖ := by
      rw [norm_mul, norm_pow]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      calc ‖y‖ ^ 2 ≤ 1 ^ 2 := by gcongr
        _ = 1 := one_pow _
    have hyd : ‖y ^ 3 * d‖ ≤ ‖d‖ := by
      rw [norm_mul, norm_pow]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      calc ‖y‖ ^ 3 ≤ 1 ^ 3 := by gcongr
        _ = 1 := one_pow _
    have h1 : ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
                ≤ ‖a + y * b + y ^ 2 * c‖ + ‖y ^ 3 * d‖ := norm_add_le _ _
    have h2 : ‖a + y * b + y ^ 2 * c‖
                ≤ ‖a + y * b‖ + ‖y ^ 2 * c‖ := norm_add_le _ _
    have h3 : ‖a + y * b‖ ≤ ‖a‖ + ‖y * b‖ := norm_add_le _ _
    linarith
  rw [norm_mul]
  calc ‖y ^ 5‖ * ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
      ≤ ‖y ^ 5‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) :=
        mul_le_mul_of_nonneg_left h_inner (norm_nonneg _)
    _ = (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) * ‖y ^ 5‖ := by ring
```

Use `set a := … with ha_def` etc. to introduce the four bound
constants cleanly (cycle 144 used three; here we have four).

### Step 3 (axiom check + faithfulness)

After the proof compiles:

1. `lean_verify
   OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_four`
   — must return `[propext, Classical.choice, Quot.sound]` only.
2. `lake build OpenMath.Chapter5.Section550` — must succeed.
3. Add a docstring quoting the textbook entity row, mirroring the
   cycle 144 docstring on `_n_three`.
4. Update `extraction/formalization_data/lean_status.json` row for
   `thm:550A` (status remains `partial`; bump the cycle pointer to
   145 and add a one-line note about n = 4).

### Step 4 (fallback if `Matrix.det_fin_four` is absent)

Verify Mathlib has `Matrix.det_fin_four` BEFORE writing the body:

```
lean_local_search "det_fin_four"
```

If absent (Mathlib only has `det_fin_one`, `det_fin_two`,
`det_fin_three`), use cofactor expansion along the first column:

```lean
rw [Matrix.det_succ_column_zero]
simp [Fin.sum_univ_four, Matrix.det_fin_three]
ring
```

Or expand fully via `Matrix.det_succ_row_zero` recursively. Either
form should close the polynomial identity once combined with `simp
[alphaPoly, betaPoly, Fin.sum_univ_four]; ring`.

If neither approach works in the polynomial-identity step, **stop
and pivot to Backup Plan A (Priority 2 below)**. Do NOT raise
`maxHeartbeats` and do NOT introduce sorries.

## What NOT to do

* **Do NOT use the cycle 140 (n = 2) `unfold + norm_num` shortcut.**
  Per cycle 144 dead end #1, this does not generalise — `simp only`
  cannot decide the nested `j.val + 1 = n` if-then-else chains at
  `n ≥ 3`. Use the explicit `!![…]` matrix template from cycle 144.
* **Do NOT raise `maxHeartbeats` above 200000.** Decompose into
  helper lemmas or split the determinant expansion.
* **Do NOT introduce `axiom` or `constant` declarations.**
* **Do NOT introduce sorries** — single-cycle-axiom-clean is the
  bar.
* **Do NOT attempt general-`n` thm:550A this cycle.** Per
  `.prover-state/issues/thm_550A_general_n.md`, this is multi-cycle
  infrastructure work (cofactor-expansion induction or
  eigenvalue-density argument). Cycle 141 cancelled an Aristotle
  general-`n` job at 6 %; the prover cannot solve it directly.
* **Do NOT chase Aristotle this cycle.** No outstanding jobs; do not
  submit new general-`n` jobs. Manual mechanical extension is
  faster and more reliable for n = 4.
* **Do NOT use `add_le_add_right (norm_add_le _ _) _`.** Per cycle
  144 dead end #2 + memory entry
  `feedback_add_le_add_left_dispatch.md`, the dispatch quirk
  produces the wrong-direction inequality. Use `linarith` over
  intermediate `have h1 / h2 / h3 : … := norm_add_le _ _` lemmas
  instead.
* **Do NOT use `mul_le_mul_of_nonneg_left h_inner (by positivity)`
  on `C * ‖y⁵‖` when the common factor is on the right.** Per cycle
  144 dead end #3, restructure with `calc … _ = (‖a‖+…) * ‖y⁵‖ := by
  ring` and apply `mul_le_mul_of_nonneg_left` against `‖y⁵‖` on the
  left.

## Aristotle policy this cycle

* No outstanding jobs. Do NOT submit new jobs — n = 4 is mechanical
  per the cycle 144 template, and Aristotle's general-`n`
  performance has been confirmed unreliable (cycle 141 cancellation).
* If the worker stalls past ~60 % of the cycle budget, pivot to
  Priority 2 (Backup A).

## Priority 2 (BACKUP A — if Priority 1 stalls): def:530A r = 3 heterogeneous-stages witness

If the n = 4 expansion blows up (e.g. `Matrix.det_fin_four` absent
AND cofactor expansion does not close cleanly), pivot to a smaller
single-cycle deliverable: strengthen `def:530A` non-vacuity with an
r = 3 heterogeneous-stages witness building on cycle 141's r = 2
design.

**Target**: add `nontrivialThreeStageGRK` (s = 3, b₀ ≠ 0),
`mixedStartingMethod3` (r = 3, distinct stages e.g. `1, 2, 3`),
plus the non-degeneracy + stage-distinctness theorems
`mixedStartingMethod3_isNonDegenerate`,
`mixedStartingMethod3_stages_pairwise_neq` — all axiom-clean.

**Location**: `OpenMath/Chapter5/Section530.lean`, after the cycle
141 r = 2 witnesses.

**Estimated**: ~80–100 LOC. The cycle 141 design is the template;
generalisation from r = 2 to r = 3 is mechanical.

## Priority 3 (BACKUP B — if Priorities 1 and 2 both stall): def:520F r = 2 negative L-stable witness

Lift cycle 137's r = 1 negative L-stable witness
`implicitMidpointGLM_not_isLStable` to r = 2 via the same
1-channel padding scheme as `padded2DBackwardEulerGLM` (cycle 143):

**Target**:
`padded2DImplicitMidpointGLM_not_isLStable`
in `OpenMath/Chapter5/Section520.lean`. The r = 2 lifted method is
A-stable but not L-stable (same as the r = 1 base), strengthening
the r = 2 negative-witness coverage.

**Estimated**: ~120 LOC.

## Hygiene checks (mandatory at end of cycle, regardless of priority)

1. `lake build OpenMath.Chapter5.Section550` (or
   `Section530`/`Section520` for backups) — must succeed.
2. `lean_verify` on the new theorem — must return only the standard
   axioms.
3. **Faithfulness check** (per CLAUDE.md):
   - Quote the textbook statement from
     `extraction/formalization_data/entities/thm_550A.json` (or
     `def_530A.json` / `def_520F.json`).
   - Confirm the Lean statement captures the same content at the
     specialised `n` / `r`.
   - Tautology check: conclusion not equal to any hypothesis.
   - Identity check: proof is multi-step, not `exact h`.
   - Hypothesis strength check: only the genuinely needed
     hypotheses (`α β : Fin 4 → ℂ` for Priority 1).
4. **Update `lean_status.json`**: bump cycle pointer for the
   touched entity.
5. **Update `plan.md`**: add a one-line note in the relevant entity
   row reflecting the new witness.
6. **Write `task_results/cycle_145.md`** documenting work done,
   approach taken, dead ends, and suggested next approach for
   cycle 146.
7. **Commit + push** to `Main/Experiments`. Verify
   `git rev-parse HEAD == git rev-parse origin/Main/Experiments`
   before declaring the cycle complete.

## Estimated cycle budget

* Priority 1 (n = 4 stepping stone): 150–250 LOC, ~60–90 min if
  paper algebra is correct on first attempt.
* Priority 2 (def:530A r = 3): 80–100 LOC, ~45–60 min.
* Priority 3 (def:520F r = 2 negative): ~120 LOC, ~60 min.
