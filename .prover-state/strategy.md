# Cycle 147 — strategy

## Snapshot

- Sorry count: **0** (clean).
- Last cycle (146): closed two axiom-clean negative non-vacuity witnesses
  (`padded2DEulerGLM_not_isAStable`, `padded2DEulerGLM_not_isLStable`)
  saturating four-corner coverage of `def:520E`/`def:520F` at r=2.
- No pending Aristotle results. The cycle-138 jobs (`7062c2a2-…`
  general-n, `70f26d67-…` n=2) are concluded; do NOT poll them again.
- Last worker's explicit suggestion: thm:550A n=5 stepping stone via
  Aristotle (deferred from cycle 146 due to the single-30-min-sleep
  budget rule and competing Priority 1 work).

## What to work on this cycle

**Priority 1 (mandatory): submit Aristotle batch for thm:550A n=5
stepping stone, then sleep 30 minutes.**

This continues the cycle 138/140/144/145 axiom-clean ladder
(n=1, 2, 3, 4 done) one rung. The submission is the *whole* cycle's
Aristotle compute window, per CLAUDE.md "Maximize Aristotle usage…
sleep 30 min, then process results. Do not poll repeatedly".

**Priority 2 (during the sleep, and after): attempt the manual closure
of `doublyCompanionMatrix_det_factorization_n_five` in
`OpenMath/Chapter5/Section550.lean`.**

Cycle 145 closed n=4 manually in one cycle (~90 LOC) using
`Matrix.det_succ_row_zero` once + four `Matrix.det_fin_three` calls.
n=5 follows the **same template** but with one extra Laplace
expansion (since Mathlib has no `Matrix.det_fin_four`). See "How to do
it" below for concrete recipes plus three fallbacks.

**Priority 3 (only if Priorities 1 and 2 are both delivered): update
the §5 row of `plan.md` and the `thm:550A` row of
`extraction/formalization_data/lean_status.json` to reference cycle
147 (status remains `partial` — n=5 is still a stepping stone, not
the general-n closure).** Also extend the `thm_550A_general_n.md`
issue file's status section to record n=5.

If only Priority 1 lands cleanly (Aristotle-supplied proof) but the
manual attempt stalls, that is still a successful cycle: a new
axiom-clean concrete-n witness committed.

If Aristotle returns a clean proof AND your manual work also closes,
**incorporate Aristotle's proof** ONLY if the manual one fails to
verify; otherwise prefer the **manual** version (provenance and
reproducibility), with a comment crediting the Aristotle return.
Aristotle's attempts have been brittle on this ladder (jobs A/B
from cycle 138 took ≥30 min for n=2; general-n jobs were
unbounded). Manual fallback is essential.

## Why not something else this cycle

- **General-n thm:550A closure**: Aristotle Job A (general-n) was
  cancelled at 6% after 24h in cycle 141. Manual cofactor-expansion
  induction is multi-cycle infrastructure scope (~300 LOC across
  2–3 cycles, per `.prover-state/issues/thm_550A_general_n.md`).
  Concrete-n stepping stones are the project's chosen forward
  direction until that infrastructure is funded.
- **`def:525A` substantive G-symplectic witness**: cycle 128 left a
  `√3` Butcher (525d) witness deferred. Plausible but requires
  bespoke G,D matrix arithmetic — not a single-cycle fit during a
  sleep window without prior preparation.
- **`thm:535A` (Underlying one-step method, GLM)**: requires
  rooted-tree-indexed solutions ξ(t), η(t), θ(t) that we have not
  built in §5. Multi-cycle infrastructure.
- **`def:530B` (Order relative to starting method)**: explicitly
  deferred per cycle 145; needs Taylor-expansion residual machinery.
- **`thm:521B`, `thm:541A`, `thm:553A`**: all unstarted but blocked
  on additional infrastructure (stability-order analysis, DIMSIM
  type machinery, IRK-stability derivation respectively).

The n=5 stepping stone is the highest-value target whose path is
**already proven** (cycles 144 and 145 are the templates).

---

## How to do it — step by step

### Step 0: Pre-flight checks

```bash
git status                                 # expect clean
sed -n '1,10p' .prover-state/heartbeat.json    # confirm cycle 147
```

### Step 1 (Priority 1): Build and submit the Aristotle batch

Create `.prover-state/aristotle_submissions/cycle_147/` with two
files (use the `Bash` tool to `mkdir -p`):

1. `n_five_factorization.lean` — a self-contained Lean snippet
   stating `doublyCompanionMatrix_det_factorization_n_five` with
   `sorry`. The stub statement is

   ```lean
   theorem doublyCompanionMatrix_det_factorization_n_five
       (α β : Fin 5 → ℂ) :
       Asymptotics.IsBigO (nhds (0 : ℂ))
         (fun z : ℂ =>
           (1 - z • doublyCompanionMatrix α β).det
             - alphaPoly α z * betaPoly β z)
         (fun z : ℂ => z ^ 6) := by
     sorry
   ```

   Include `import` headers, `open Asymptotics`, the namespace
   `OpenMath.Chapter5.Section550`, AND copies of `doublyCompanionMatrix`,
   `alphaPoly`, `betaPoly`, and the n=4 stepping stone proof (lines
   286–375 of `Section550.lean`) so the snippet is self-contained
   for Aristotle. Aristotle works best when given the full lemma
   landscape. Mirror cycle 138's `B_n_two_factorization.lean`
   structure.

2. `README.md` — short description and the cycle 145/144 attack
   recipe (Step-1 reduction to `!![…]` matrix, Step-2 nested
   `det_succ_row_zero` Laplace expansion to expose `Matrix.det_fin_three`,
   Step-3 `Asymptotics.IsBigO.of_bound` with explicit constant).

Submit via `mcp__aristotle__submit_directory`. **Submit ONLY the
n=5 file.** Do NOT also resubmit n=2/n=4/general-n; those are
concluded.

After submission, save the project ID at the top of
`.prover-state/aristotle_submissions/cycle_147/README.md` for the
post-sleep poll.

**Then call `Bash` with a 30-minute sleep, or proceed to Step 2
work that takes at least 30 minutes wall-clock and check status
afterwards. A single Aristotle poll afterwards. Do not re-poll if
still IN_PROGRESS.**

### Step 2 (Priority 2): Manual n=5 closure

The proof is a mechanical extension of cycle 145's n=4 template at
`OpenMath/Chapter5/Section550.lean:286–375`. Insert the new theorem
**immediately after** `doublyCompanionMatrix_det_factorization_n_four`
(line ~376) and **before** `end OpenMath.Chapter5.Section550`.

#### 2a — Step 1 of the proof: `h_diff` (residue factorisation)

```lean
have h_diff : (fun z : ℂ =>
    (1 - z • doublyCompanionMatrix α β).det
      - alphaPoly α z * betaPoly β z)
    = (fun z : ℂ => z ^ 6 *
        (-(α 0 * β 4) - α 1 * β 3 - α 2 * β 2 - α 3 * β 1 - α 4 * β 0
          + z * (-(α 1 * β 4) - α 2 * β 3 - α 3 * β 2 - α 4 * β 1)
          + z ^ 2 * (-(α 2 * β 4) - α 3 * β 3 - α 4 * β 2)
          + z ^ 3 * (-(α 3 * β 4) - α 4 * β 3)
          + z ^ 4 * (-(α 4 * β 4)))) := by
  funext z
  -- (i) Reduce X to a 5×5 !![…] matrix.
  have hX : doublyCompanionMatrix α β =
      !![-α 0, -α 1, -α 2, -α 3, -α 4 - β 4;
         1,     0,    0,    0,    -β 3;
         0,     1,    0,    0,    -β 2;
         0,     0,    1,    0,    -β 1;
         0,     0,    0,    1,    -β 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]
  rw [hX]
  -- (ii) Reduce 1 - z • X to !![…].
  have hmat :
      (1 - z • !![/* the matrix from (i) */] : Matrix (Fin 5) (Fin 5) ℂ)
        = !![1 + z * α 0,  z * α 1,  z * α 2,  z * α 3,  z * (α 4 + β 4);
             -z,           1,        0,        0,        z * β 3;
             0,            -z,       1,        0,        z * β 2;
             0,            0,        -z,       1,        z * β 1;
             0,            0,        0,        -z,       1 + z * β 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | (simp; ring) | simp
  rw [hmat]
  -- (iii) Expand 5×5 det via det_succ_row_zero, reduce 4×4 minors via
  --       det_succ_row_zero again, then 3×3 minors via det_fin_three.
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_five, Fin.sum_univ_four,
    Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
    alphaPoly, betaPoly,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.submatrix_apply, Fin.succ_zero_eq_one,
    Matrix.cons_val_fin_one, Fin.succAbove]
  ring
```

**Likely failure mode** for the simp set in (iii): the nested
`det_succ_row_zero` recursion may not collapse cleanly. If `simp`
times out or leaves residual goals, proceed to Fallback A below.

#### 2b — Step 2 of the proof: `IsBigO.of_bound`

Direct copy of the cycle 145 n=4 template, with one extra term `e`
for the `z^4` coefficient:

```lean
rw [h_diff]
refine Asymptotics.IsBigO.of_bound
    (‖-(α 0 * β 4) - α 1 * β 3 - α 2 * β 2 - α 3 * β 1 - α 4 * β 0‖
      + ‖-(α 1 * β 4) - α 2 * β 3 - α 3 * β 2 - α 4 * β 1‖
      + ‖-(α 2 * β 4) - α 3 * β 3 - α 4 * β 2‖
      + ‖-(α 3 * β 4) - α 4 * β 3‖
      + ‖-(α 4 * β 4)‖) ?_
rw [Metric.eventually_nhds_iff]
refine ⟨1, by norm_num, fun y hy => ?_⟩
rw [Complex.dist_eq, sub_zero] at hy
set a := -(α 0 * β 4) - α 1 * β 3 - α 2 * β 2 - α 3 * β 1 - α 4 * β 0 with ha_def
set b := -(α 1 * β 4) - α 2 * β 3 - α 3 * β 2 - α 4 * β 1 with hb_def
set c := -(α 2 * β 4) - α 3 * β 3 - α 4 * β 2 with hc_def
set d := -(α 3 * β 4) - α 4 * β 3 with hd_def
set e := -(α 4 * β 4) with he_def
have h_inner :
    ‖a + y * b + y ^ 2 * c + y ^ 3 * d + y ^ 4 * e‖
      ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  -- Five `‖y^k * x‖ ≤ ‖x‖` sub-bounds, then triangle-inequality cascade
  -- via norm_add_le, finally `linarith`. Direct extension of cycle 145
  -- (lines 350–369 in Section550.lean).
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
  have hye : ‖y ^ 4 * e‖ ≤ ‖e‖ := by
    rw [norm_mul, norm_pow]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    calc ‖y‖ ^ 4 ≤ 1 ^ 4 := by gcongr
      _ = 1 := one_pow _
  have h1 : ‖a + y * b + y ^ 2 * c + y ^ 3 * d + y ^ 4 * e‖
              ≤ ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖ + ‖y ^ 4 * e‖ :=
    norm_add_le _ _
  have h2 : ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
              ≤ ‖a + y * b + y ^ 2 * c‖ + ‖y ^ 3 * d‖ := norm_add_le _ _
  have h3 : ‖a + y * b + y ^ 2 * c‖
              ≤ ‖a + y * b‖ + ‖y ^ 2 * c‖ := norm_add_le _ _
  have h4 : ‖a + y * b‖ ≤ ‖a‖ + ‖y * b‖ := norm_add_le _ _
  linarith
rw [norm_mul]
calc ‖y ^ 6‖ * ‖a + y * b + y ^ 2 * c + y ^ 3 * d + y ^ 4 * e‖
    ≤ ‖y ^ 6‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖) :=
      mul_le_mul_of_nonneg_left h_inner (norm_nonneg _)
  _ = (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖) * ‖y ^ 6‖ := by ring
```

#### 2c — docstring

Mirror cycle 145's docstring on `_n_four` and adapt to n=5: list the
coefficient identities up through `z^9` (the `α(z)·β(z)` polynomial
goes up to `z^{2n-1} = z^9`) and the residue `-(convolution) z^k`
for k=5..9. Briefly mention this is the fifth concrete-n axiom-clean
stepping stone.

### Step 3 (post-sleep): process Aristotle

Run `mcp__aristotle__get_status` once on the cycle 147 project ID.
- If COMPLETE: pull the proof via `mcp__aristotle__extract_result`,
  compare with your manual attempt. If the manual attempt also
  closed, prefer the **manual** version (provenance and
  reproducibility) — but commit a comment crediting Aristotle. If
  only Aristotle closed, incorporate verbatim and verify axiom-clean.
- If still IN_PROGRESS at <50%: treat as a miss; rely on manual
  closure.
- If FAILED or returned a sorry-laden proof: rely on manual
  closure.

### Step 4: verification

```bash
lake env lean OpenMath/Chapter5/Section550.lean
# expected: clean compile, no errors, no warnings, no sorry messages
```

For axiom check, use `mcp__lean-lsp__lean_verify` with
`name = "OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_five"`.
Expected: `[propext, Classical.choice, Quot.sound]`.

Use `lake env lean` for the file, NOT `lake build`. (Per CLAUDE.md.)

### Step 5: commit

If n=5 lands axiom-clean, commit with message

```
Cycle 147 — add thm:550A n=5 stepping stone via det_succ_row_zero^2 + det_fin_three (axiom-clean)
```

If only Aristotle's proof landed, append `via Aristotle` to the
message.

### Step 6: write `.prover-state/task_results/cycle_147.md`

Use the standard CLAUDE.md format. Include the faithfulness section
listing the new theorem (it is *another* axiom-clean concrete-n
stepping stone, no new definitions).

---

## What NOT to try (failed approaches from prior cycles)

1. **DO NOT submit Aristotle for general-n thm:550A**. Cycle 138's
   Job A and cycle 140's Job A both stalled at 4–6%. Cycle 141
   cancelled the cycle-141 attempt at 6% after 24h. The general-n
   case requires multi-cycle Mathlib infrastructure
   (cofactor-expansion induction or eigenvalue-density argument);
   it is NOT an Aristotle-tractable single-shot.
2. **DO NOT attempt a fresh full build** with `lake build` to
   verify. Use `lake env lean OpenMath/Chapter5/Section550.lean`
   per CLAUDE.md (the GPFS olean cache is slow; single-file is
   the right granularity).
3. **DO NOT raise `maxHeartbeats`** if the n=5 proof times out.
   Decompose: introduce an explicit `det_fin_four`-style private
   helper inside `Section550.lean` (Fallback A below), then use it
   in the n=5 simp set. Per CLAUDE.md this is the canonical fix.
4. **DO NOT alter `doublyCompanionMatrix`'s definition** to make
   the n=5 case easier. The definition was carefully chosen to
   match the textbook block structure; n=1, 2, 3, 4 all rely on it
   verbatim and they must continue to compile unchanged.
5. **DO NOT poll Aristotle more than once after the 30-minute
   sleep.** CLAUDE.md is explicit. Single poll, then proceed.
6. **DO NOT introduce `axiom`/`constant`** for any leftover
   algebraic obstruction. If `ring` cannot close a polynomial
   identity in the residue, decompose via `linear_combination` or
   per-coefficient arguments.
7. **DO NOT cherry-pick a smaller n** (e.g. revisit n=4) to
   pad the cycle. Cycle 145 closed n=4 axiom-clean; the next rung
   is n=5.
8. **DO NOT touch `extraction/raw_text/` or
   `extraction/formalization_data/entities/`**. Both regenerate
   from the pipeline. Editing `lean_status.json` is fine
   (Step 5).
9. **DO NOT introduce new sorry's** in `Section550.lean`. Per
   CLAUDE.md sorry-first is for new structure; the n=5 proof is a
   pure proof-body addition. If the manual attempt stalls past the
   cycle budget, **commit nothing for n=5** and rely on Aristotle's
   result. (A cycle in which neither Priority 1 Aristotle nor
   Priority 2 manual lands cleanly is acceptable per CLAUDE.md if
   the strategy + Aristotle submission are committed — but
   score-wise it is at risk.)
10. **DO NOT reopen the cycle-141 cancelled general-n Aristotle
    project.** It was cancelled deliberately.
11. **DO NOT re-poll the cycle-138 Aristotle project IDs**
    (`7062c2a2-…`, `70f26d67-…`). The n=2 result already landed
    (cycle 140) and the general-n one was effectively abandoned at
    6% after 24h.

---

## Backup plan — if Step 2's `simp` recipe fails

If the `simp [Fin.sum_univ_five, Fin.sum_univ_four,
Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three, …]`
collapse from Step 2a (iii) does not close the polynomial identity
in 1–2 attempts (i.e. simp leaves goals or times out at default
heartbeats), pivot to **Fallback A** immediately:

### Fallback A — inline 4×4 determinant helper

State and prove a private helper inside `Section550.lean`,
**immediately after** the n=4 stepping-stone theorem (so it is
available to the n=5 proof):

```lean
private lemma det_fin_four_explicit
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℂ) :
    Matrix.det !![a₀, a₁, a₂, a₃;
                   b₀, b₁, b₂, b₃;
                   /* … */] = (closed-form polynomial) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, ...]
  ring
```

Or, more practically: prove a helper that handles **the specific
shape of the n=5 4×4 minors** that arise from the outer Laplace
expansion. There are five 4×4 minors (one per column of row 0); each
has a sub-diagonal of `-z`s and one column of α/β perturbations.
A unified helper can match them all by parameterising the
perturbation column.

Then in the n=5 proof's Step 2a (iii), invoke
`det_fin_four_explicit` (×5) instead of relying on simp to recurse
into 4×4 sub-determinants.

### Fallback B — fully manual Laplace expansion ×2

If Fallback A is also troublesome, do the Laplace expansion entirely
manually:

```lean
rw [Matrix.det_succ_row_zero]   -- 5×5 → five 4×4 minors
simp only [Fin.sum_univ_five]
-- For each 4×4 minor, apply Matrix.det_succ_row_zero and
-- Matrix.det_fin_three explicitly:
rw [show (the i-th 4×4 minor) =
        … explicit via Matrix.det_succ_row_zero + Matrix.det_fin_three]
-- (repeated 5 times)
ring
```

Verbose (~200 LOC) but mechanical. Each 4×4 minor expansion is the
cycle 145 n=4 inner determinant, repeatable.

### Fallback C — heartbeats/ring escape

If Fallback B's outer `ring` is heartbeats-heavy (>200000), split the
polynomial identity into per-coefficient comparisons via
`linear_combination` or do explicit
`Polynomial.coeff`-style arguments per power of `z`. Per CLAUDE.md,
do NOT raise `maxHeartbeats` — decompose instead.

---

## Backup plan — if cycle budget runs out before Step 2 lands

1. **DO** still commit the cycle 147 Aristotle submission directory
   (`.prover-state/aristotle_submissions/cycle_147/`) and
   `.prover-state/strategy.md` and any other housekeeping.
2. **DO NOT** commit a sorry-laden `Section550.lean`. If Step 2
   cannot land cleanly, leave `Section550.lean` unchanged (the n=5
   stepping stone simply does not appear this cycle).
3. **DO** write `.prover-state/task_results/cycle_147.md` honestly
   describing what was attempted, what blocked, and a concrete
   recommendation for cycle 148 (likely: poll the cycle 147
   Aristotle project once at the start of cycle 148, or commit to
   Fallback B's verbose manual proof).

The score floor for committing only the Aristotle submission +
strategy + task results is non-zero per CLAUDE.md ("a cycle with
zero changes is unacceptable; at minimum, decompose a sorry or
write an issue"). Submission infrastructure + task results document
plus an explicit cycle-148 plan satisfies that floor.

---

## Faithfulness reminder for the pre-commit checklist

The new theorem is a **stepping-stone witness for thm:550A**
(itself a `def`-and-statement entity in
`extraction/formalization_data/entities/thm_550A.json`). The
faithfulness check items that apply this cycle:

- **Tautology check**: the conclusion `IsBigO … (z ^ 6)` is NOT a
  hypothesis — it is the residue's actual asymptotic order at 0.
  No conclusion-equals-hypothesis bug.
- **Identity check**: the proof is decidedly not `exact h` — it is
  a multi-stage matrix-determinant calculation.
- **Hypothesis strength check**: the only hypotheses are the
  arbitrary `α β : Fin 5 → ℂ`. Cannot be weakened.
- **Absent theorem check**: no comments promising sorry'd content.

No new `def`/`structure`/`class` introduced. No new `theorem`
*statements* beyond the n=5 specialisation.
