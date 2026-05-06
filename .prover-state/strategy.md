# Cycle 148 — strategy

## Snapshot

- Sorry count: **0** (clean).
- Last cycle (147): closed `doublyCompanionMatrix_det_factorization_n_five`
  axiom-clean as the fifth concrete-`n` stepping stone for `thm:550A`.
  Manual proof landed before Aristotle progress (Aristotle project
  `9643742d-…` was IN_PROGRESS at 5% at the post-build poll; do NOT
  re-poll it — per CLAUDE.md, single-poll rule applies).
- The cycle 147 recipe (one-shot `simp […]; ring` after two-layer
  `Matrix.det_succ_row_zero` Laplace expansion) generalised cleanly
  from cycle 145's n=4 template **without** Fallback A. Five concrete
  data points (n = 1, 2, 3, 4, 5) now confirm the leading-coefficient
  pattern `−Σᵢ αᵢ · β_{n−i} z^{n+1}` of Theorem 550A.
- No pending Aristotle results awaiting incorporation.

## What to work on this cycle

**Priority 1 (mandatory): close
`doublyCompanionMatrix_det_factorization_n_six` axiom-clean in
`OpenMath/Chapter5/Section550.lean`** as the sixth concrete-`n`
stepping stone for `thm:550A`.

**Rationale.** Cycle 147 demonstrated that the cycle 145 template
generalises in *one cycle per rung* with a single-shot `simp […]; ring`
collapse (no Fallback A needed). The marginal cost of an additional
rung is minimal and continues to accumulate evidence for the eventual
general-`n` cofactor-expansion induction. After this rung, the
planner will judge whether to attempt general-`n` directly (cycle
149+) or pivot to other §5 work.

**Priority 2 (parallel, fire-and-forget): submit a single Aristotle
project for the *general-`n`* statement** with **all five n=1..5
proofs** included as in-context templates and a clear inductive
sketch in the prompt. This is a long-shot — cycle 141 cancelled an
Aristotle general-`n` job at 24h/6%, and cycle 147's general-`n`
adjacent attempt also stalled at 5% — but submission cost is zero
for the worker, and a hit would close out `thm:550A` entirely. **Do
NOT poll this job during the cycle**; just submit, record the project
ID in `.prover-state/aristotle_submissions/cycle_148/`, and let it
run.

**Priority 3 (only if Priorities 1 and 2 are both delivered):**
update the `thm:550A` row of `extraction/formalization_data/lean_status.json`
and the §5 row of `plan.md` to reference cycle 148. Status remains
`partial` (n=6 is still a stepping stone). Append a short n=6 status
update to `.prover-state/issues/thm_550A_general_n.md`.

## How to do Priority 1 (concrete recipe)

Open `OpenMath/Chapter5/Section550.lean`. Insert
`doublyCompanionMatrix_det_factorization_n_six` after
`doublyCompanionMatrix_det_factorization_n_five` (line 502, just before
`end OpenMath.Chapter5.Section550`). The template is the cycle 147
proof (lines 395–501) with **three** mechanical changes:

### Change 1: bump the matrix size from 5×5 to 6×6

Replace the explicit `!![…]` 5×5 matrix forms (cycle 147 lines 414–419
for `hX`, lines 425–434 for `hmat`) with their 6×6 analogues. The
sub-diagonal grows by one entry; the last column gets one more
`-β k` value; row 0 gets one more `-α k` entry. Concretely:

```lean
have hX : doublyCompanionMatrix α β =
    !![-α 0, -α 1, -α 2, -α 3, -α 4, -α 5 - β 5;
       1,     0,    0,    0,    0,    -β 4;
       0,     1,    0,    0,    0,    -β 3;
       0,     0,    1,    0,    0,    -β 2;
       0,     0,    0,    1,    0,    -β 1;
       0,     0,    0,    0,    1,    -β 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]
```

and the corresponding `1 - z • X` (sign flip on `-α k → +z·α k`,
and lower-triangle `1`s become `-z`):

```lean
have hmat :
    (1 - z • !![…6×6 explicit form…] : Matrix (Fin 6) (Fin 6) ℂ)
      = !![1 + z * α 0,  z * α 1,  z * α 2,  z * α 3,  z * α 4,  z * (α 5 + β 5);
           -z,           1,        0,        0,        0,        z * β 4;
           0,            -z,       1,        0,        0,        z * β 3;
           0,            0,        -z,       1,        0,        z * β 2;
           0,            0,        0,        -z,       1,        z * β 1;
           0,            0,        0,        0,        -z,       1 + z * β 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; ring) | simp
```

### Change 2: add `Matrix.det_succ_row_zero (n := 4)` to the simp set

Cycle 147's two-layer Laplace (`det_succ_row_zero` outer + `(n := 3)`
inner closing into `det_fin_three`) becomes a **three-layer** Laplace
for n=6 (since Mathlib has no `det_fin_four`):

* outer `det_succ_row_zero`: 6×6 → six 5×5 minors
* `det_succ_row_zero (n := 4)`: each 5×5 → five 4×4 minors
* `det_succ_row_zero (n := 3)`: each 4×4 → four 3×3 minors
* `Matrix.det_fin_three`: closes each 3×3 minor.

So the closing simp set is:

```lean
rw [Matrix.det_succ_row_zero]
simp [Fin.sum_univ_six, Fin.sum_univ_five, Fin.sum_univ_four,
  Matrix.det_succ_row_zero (n := 4),
  Matrix.det_succ_row_zero (n := 3),
  Matrix.det_fin_three,
  alphaPoly, betaPoly,
  Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.submatrix_apply, Fin.succ_zero_eq_one,
  Matrix.cons_val_fin_one, Fin.succAbove]
ring
```

If `Fin.sum_univ_six` is not in Mathlib (verify via
`mcp__lean-lsp__lean_local_search`; cycle 147 used `Fin.sum_univ_five`
and `Fin.sum_univ_four` successfully), expand the outer sum manually
via `Fin.sum_univ_succ` (six unfoldings) before the simp. **Do not
add this concern to the strategy unless verification fails.**

### Change 3: list **six** convolution coefficients in `IsBigO.of_bound`

The residue factors as `z^7 · (a + z·b + z²·c + z³·d + z⁴·e + z⁵·f)`
where, mirroring the cycle 147 convolution pattern (with a, b, c, d, e
as the cycle 147 coefficients shifted up by one β-index):

```
a := -(α 0 · β 5) - α 1 · β 4 - α 2 · β 3 - α 3 · β 2 - α 4 · β 1 - α 5 · β 0
b := -(α 1 · β 5) - α 2 · β 4 - α 3 · β 3 - α 4 · β 2 - α 5 · β 1
c := -(α 2 · β 5) - α 3 · β 4 - α 4 · β 3 - α 5 · β 2
d := -(α 3 · β 5) - α 4 · β 4 - α 5 · β 3
e := -(α 4 · β 5) - α 5 · β 4
f := -(α 5 · β 5)
```

The constant in `IsBigO.of_bound` is the sum of six norms;
the inner-factor bound becomes a five-step `norm_add_le` cascade
(plus `mul_le_of_le_one_left` for each `y^k * x` factor) ending with
`linarith`. The cycle 147 proof body lines 451–501 transcribe almost
verbatim — replace `‖y ^ 6‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖)` with
`‖y ^ 7‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖)` and add one more
`hyf : ‖y ^ 5 * f‖ ≤ ‖f‖` plus one more `norm_add_le` step.

### Sanity gate before closing

After `h_diff`'s `funext z; ... ; ring` step, **manually verify the
expected residue** by running `mcp__lean-lsp__lean_goal` mid-tactic if
the `ring` step fails. The most likely failure modes, ranked:

1. **Sign error in the explicit `!![…]` matrix `hX`.** The
   `doublyCompanionMatrix` definition's last column entry for `i ≥ 1`
   is `-β (n - i - 1)` (per the file preamble); double-check that
   row 1 column 5 is `-β 4` (not `-β 5` and not `-β 3`), row 2 column
   5 is `-β 3`, etc. The pattern: row `i` column `n-1` is `-β (n - i - 1)`,
   so for n=6 that is row 1 = `-β 4`, row 2 = `-β 3`, row 3 = `-β 2`,
   row 4 = `-β 1`, row 5 = `-β 0`. (The cycle 147 proof matches this
   pattern at n=5: row 1 = `-β 3`, …, row 4 = `-β 0`.)

2. **Convolution coefficient typo.** The cycle 147 coefficients are
   `a = -(α 0 · β 4) - α 1 · β 3 - α 2 · β 2 - α 3 · β 1 - α 4 · β 0`.
   For n=6, the `a` coefficient appends `- α 5 · β 0` and shifts
   each `β k → β (k+1)` for the existing terms. **Do this shift
   carefully** — a mistake here means `ring` fails at h_diff.

3. **`simp` doesn't close after Laplace.** If the three-layer simp
   set above leaves residual unfolded `Matrix.cons` cells, add
   `Fin.succAbove_succ`, `Fin.succAbove_zero`, or
   `Matrix.cons_val_succ` to the simp list. Cycle 147 did NOT need
   these (they were absorbed by the existing simp set), but with one
   more Laplace layer they may surface.

### If Priority 1 stalls (Fallback A)

Write a private helper `det_fin_four_explicit` of the shape

```lean
private lemma det_fin_four_explicit (M : Matrix (Fin 4) (Fin 4) ℂ) :
    M.det = ‹explicit 24-term formula in M i j› := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_succ_row_zero (n := 3),
        Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  ring
```

and add it to the simp set. This costs ~30 LOC but breaks the simp
tree depth into two more manageable layers. Recommended **only if**
the one-shot `simp […]; ring` times out (>200000 heartbeats) or
leaves residual goals.

### If Priority 1 still stalls (Fallback B)

Submit a focused **n=6** Aristotle batch separately from the
Priority 2 general-`n` job, with the cycle 147 n=5 proof included
as the in-context template. This is a fresh project; do NOT reuse
the Priority 2 project. Sleep 30 minutes; then incorporate. (Cycle
140 succeeded with this pattern at n=2, where Aristotle Job B
returned a clean proof while Job A on general-`n` stayed at 4%.)

## How to do Priority 2 (Aristotle parallel submission)

1. Create `.prover-state/aristotle_submissions/cycle_148/general_n.lean`
   as a self-contained snippet:
   - Imports: as in `Section550.lean` lines 1–6.
   - Definitions: `doublyCompanionMatrix`, `alphaPoly`, `betaPoly`
     verbatim from `Section550.lean`.
   - In-context templates: copy *all five* closed proofs
     (`_n_one`, `_n_two`, `_n_three`, `_n_four`, `_n_five`) verbatim.
     This gives Aristotle the n=1..5 closed forms to inductively
     extrapolate from.
   - Target: a single `theorem doublyCompanionMatrix_det_factorization
     {n : ℕ} (α β : Fin n → ℂ) : Asymptotics.IsBigO …` with body
     `sorry`, plus a comment block with a strong-induction sketch
     pointing at three plausible attack vectors:
     (a) cofactor expansion along row 0, recursive on the bottom-right
         (n−1)×(n−1) sub-block (which is itself a `doublyCompanionMatrix
         α' β'` for shifted indices);
     (b) eigenvalue-density argument (textbook proof) via
         continuity of charpoly coefficients in matrix entries; or
     (c) direct induction with `Fin.induction` and the cycle 145/147
         template instantiation as the inductive step.

2. Submit via `mcp__aristotle__submit_directory` on the cycle_148/
   directory. Record the project ID in
   `.prover-state/aristotle_submissions/cycle_148/README.md`.

3. **Do NOT poll the project during this cycle.** A future cycle (149
   or later) will check it once.

## What NOT to do

- Do **NOT** raise `maxHeartbeats` above 200000. If the three-layer
  `simp […]; ring` hits the budget, use Fallback A (`det_fin_four_explicit`
  helper) to break the proof tree.
- Do **NOT** try to close the **general-`n`** statement manually this
  cycle. Cycle 141 cancelled Aristotle's general-`n` attempt after 24h
  at 6%; the manual cofactor-expansion induction requires identifying
  the right inductive invariant (the residue's vector of convolution
  coefficients, indexed by k, satisfies a shift-by-one recurrence
  relative to the (n−1)×(n−1) sub-block — but encoding this cleanly is
  multi-cycle infrastructure work).
- Do **NOT** re-poll Aristotle project `9643742d-…` (cycle 147 n=5
  attempt). It is concluded from the worker's perspective; the manual
  proof landed.
- Do **NOT** re-attempt the Aristotle general-`n` jobs from cycles
  138/141 (`7062c2a2-…`, `70f26d67-…` first job) — both have been
  cancelled or stalled past usefulness. The Priority 2 submission
  this cycle is a **fresh** attempt with the n=1..5 templates as
  in-context evidence.
- Do **NOT** modify the existing axiom-clean proofs n=1..5. They
  are committed and stable; any "simplification" risks introducing
  regressions.
- Do **NOT** introduce new helpers or rewrite the cycle 147 template.
  The strategy is a verbatim three-mechanical-change extension; novelty
  is unwarranted at this rung.
- Do **NOT** edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/` (regenerated files; per
  CLAUDE.md and `extraction/EXTENSIBILITY.md`).
- Do **NOT** spend time on §513/§514/§515 cascade verification — the
  §550 work is structurally isolated from those files.
- Do **NOT** chase competing Chapter 5 priorities (e.g. `def:525A`
  G-symplectic substantive witness, `def:530B/C` order-relative-to-
  starting-method, `thm:521B` max stability order) this cycle. The
  n=6 deliverable is the focused single-cycle target.

## Pre-commit faithfulness check

For the new theorem `doublyCompanionMatrix_det_factorization_n_six`:

- Entity: `thm:550A`. Quote the textbook statement from
  `extraction/formalization_data/entities/thm_550A.json`:
  > "1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(z^{n+1})."
- Lean statement: specialisation at `n = 6`. The conclusion
  `(1 - z • doublyCompanionMatrix α β).det - alphaPoly α z * betaPoly β z
   =O[nhds 0] (z ^ 7)` matches the textbook `O(z^{n+1})` at `n = 6`
  (so `z^7`). **Faithful — same content as the textbook for the n=6 case.**
- Tautology check: the conclusion is an `IsBigO` claim; not present
  among the hypotheses (`α β : Fin 6 → ℂ` only). ✓
- Identity check: proof is a multi-stage matrix-determinant
  computation, not `exact h`. ✓
- Hypothesis strength: `α, β : Fin 6 → ℂ` are universal in the textbook
  too (no method-class restriction). ✓
- No new `def`/`structure`/`class` introduced.

## Acceptance criteria

A successful cycle 148 delivers ALL of:

1. `doublyCompanionMatrix_det_factorization_n_six` lands axiom-clean
   in `OpenMath/Chapter5/Section550.lean`.
2. `lake env lean OpenMath/Chapter5/Section550.lean` exits 0 (expect
   ~8–10 minutes wall-clock, similar to cycle 147).
3. `mcp__lean-lsp__lean_verify
   OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_six`
   returns `axioms = [propext, Classical.choice, Quot.sound]`.
4. Sorry count remains 0.
5. Aristotle Priority 2 job submitted (project ID recorded in
   `.prover-state/aristotle_submissions/cycle_148/README.md`).
6. Task results written to `.prover-state/task_results/cycle_148.md`.
7. `plan.md` and `lean_status.json` updated for Priority 3 (status
   stays `partial`).

A partial-success outcome (Priority 1 lands, Priority 2 not submitted,
or vice versa) is acceptable as a +1 cycle. A regression (any new
sorry, or any axiom change beyond the standard three) is a hard fail
and must be reverted before commit.
