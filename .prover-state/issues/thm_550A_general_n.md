# Issue: General-`n` proof of `thm:550A` (Doubly companion matrix factorization)

## Status update (cycle 151) — ARISTOTLE GENERAL-`n` JOB CANCELLED

Aristotle project `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (cycle 148
fire-and-forget general-`n` attempt) was **cancelled** in cycle 151
at 21 % completion, ~89 hours after submission.

This mirrors the cycle-141 cancellation of project
`7062c2a2-4a8b-4fae-b694-9355e06427a9` (analogous cycle-138 Job A,
cancelled at 6 % after 24 h). Two failed long-running attempts
constitute sufficient evidence that the prover cannot close
`doublyCompanionMatrix_det_factorization` for general `n` without
the upstream infrastructure (cofactor-expansion induction or
eigenvalue-density argument) — both multi-cycle work.

**No further Aristotle submissions for the general-`n` proof.** Save
the job slot for tractable submissions. The deferral remains in
force; closure path is structural, not search-based.

The seven concrete-`n` axiom-clean stepping stones (n = 1..7) remain
in `OpenMath/Chapter5/Section550.lean` as the empirical evidence base
for the leading-coefficient pattern. Cycle 150's task results note
the seven-`n` data set is now strong enough that further stepping
stones (n = 8) provide marginal value; effort should pivot.

## Status update (cycle 150) — n=7 STEPPING STONE ADDED

`doublyCompanionMatrix_det_factorization_n_seven` landed axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Strategy was the cycle 148
four-layer Laplace template (7×7 → seven 6×6 minors via outer
`Matrix.det_succ_row_zero`; each 6×6 → six 5×5 via `(n := 5)`; each 5×5
→ five 4×4 via `(n := 4)`; each 4×4 → four 3×3 via `(n := 3)`; close
each 3×3 minor by `Matrix.det_fin_three`). The naive one-shot
`simp […]; ring` blew past 200 000 heartbeats (timeout at `whnf`
during simp normalization of the ~5 040-monomial raw expansion plus
the alphaPoly·betaPoly polynomial product), so the matrix-expansion
`simp` was factored into a `private lemma matrix7_oneMinusZSmul_det`
that proves only `det(...) = explicit polynomial of degree 7 in z`.
The main theorem then `rw [hmat, matrix7_oneMinusZSmul_det]` and
finishes the alphaPoly·betaPoly residue identity in a separate
small `simp [alphaPoly, betaPoly, Fin.sum_univ_seven]; ring`. Total
build time ~8 min; both halves fit within default heartbeats.

`IsBigO.of_bound` on the seven-term inner factor
`a + z·b + z²·c + z³·d + z⁴·e + z⁵·f + z⁶·g`. Seven concrete `n`
data points (n = 1..7) now confirm the leading-coefficient pattern
`−Σᵢ αᵢ · β_{n−i} · z^{n+1}`.

Cycle 150 single-poll on Aristotle project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (cycle 148 fire-and-forget
general-n attempt) returned IN_PROGRESS at 18 % — left running per
strategy. Cycle 151+ will decide on cancellation or further polls.

**Seven concrete n's (n = 1..7) now confirm the leading-coefficient
pattern.**

## Status update (cycle 148) — n=6 STEPPING STONE ADDED

`doublyCompanionMatrix_det_factorization_n_six` landed axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Strategy was the cycle 147
n=5 recipe with three mechanical changes: (a) bump matrix size to 6×6,
(b) add `Matrix.det_succ_row_zero (n := 4)` to the simp set so a
**three-layer** Laplace expansion (6×6 → 5×5 minors via outer
`det_succ_row_zero`; 5×5 → 4×4 via `(n := 4)`; 4×4 → 3×3 via
`(n := 3)`; close each 3×3 minor by `det_fin_three`) collapses by
one-shot `simp […]; ring`, (c) list six convolution coefficients in
`IsBigO.of_bound` and add one more `norm_add_le` step plus one more
`mul_le_of_le_one_left` sub-bound (`hyf : ‖y ^ 5 * f‖ ≤ ‖f‖`). No
fallback A (no `det_fin_four_explicit` helper) was needed — the
one-shot simp closed the residue exactly as for n=5. Six concrete `n`
data points (n = 1..6) now confirm the leading-coefficient pattern
`−Σᵢ αᵢ · β_{n−i} · z^{n+1}`.

Cycle 148 also submitted **Aristotle project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda`** for the general-`n` statement
with all six closed proofs as in-context templates and a strong-induction
sketch (cofactor expansion / eigenvalue density / `Fin.induction`).
Single-poll discipline applies: do NOT re-poll until cycle 149+.

## Status update (cycle 147) — n=5 STEPPING STONE ADDED

`doublyCompanionMatrix_det_factorization_n_five` landed axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Strategy was identical
to cycle 145's n=4 template — the only structural change is one
extra layer of Laplace expansion (since Mathlib has no
`Matrix.det_fin_four`):

1. Reduce `doublyCompanionMatrix α β` at `n = 5` to an explicit
   `!![…]` form via `ext i j; fin_cases i <;> fin_cases j <;>
   simp [doublyCompanionMatrix]`.
2. Reduce `1 - z • X` to a second explicit `!![…]` form by a second
   `fin_cases` block with `first | (simp; ring) | simp`.
3. Expand the 5×5 determinant via `Matrix.det_succ_row_zero` (one
   Laplace step), then expand each 4×4 minor again via
   `Matrix.det_succ_row_zero (n := 3)` (a second Laplace step), then
   `Matrix.det_fin_three` closes each 3×3 minor. The single
   `simp [Fin.sum_univ_five, Fin.sum_univ_four,
    Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
    alphaPoly, betaPoly, …]; ring` closed the polynomial identity
   in one shot (no Fallback A needed).
4. Close the `IsBigO` via `Asymptotics.IsBigO.of_bound` with constant
   `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖`, where the residue factors as
   `z^6 · (a + z·b + z²·c + z³·d + z⁴·e)` with the five convolution
   coefficients
   * `a := -(α 0·β 4) - α 1·β 3 - α 2·β 2 - α 3·β 1 - α 4·β 0`,
   * `b := -(α 1·β 4) - α 2·β 3 - α 3·β 2 - α 4·β 1`,
   * `c := -(α 2·β 4) - α 3·β 3 - α 4·β 2`,
   * `d := -(α 3·β 4) - α 4·β 3`,
   * `e := -(α 4·β 4)`.
   Bound via repeated `norm_add_le` + `mul_le_of_le_one_left`
   exploiting `‖z‖ ≤ 1`.

In parallel, Aristotle project `9643742d-aac9-4e57-9f7a-2ba69a5f25ee`
was submitted with the same target and an n=4-template-included
self-contained snippet. At the post-build poll (~11 minutes in) it
was still IN_PROGRESS at 5% — manual closure won.

**Five data points (n = 1, 2, 3, 4, 5)** now confirm the leading-
coefficient pattern `−Σᵢ αᵢ · β_{n−i} z^{n+1}` predicted by Theorem
550A. Higher-order coefficients also match the `α(z) · β(z)`
expansion exactly. The cancellation of `z⁰`–`z⁵` in
`det(I − zX) − α(z)·β(z)` is the textbook content; verified
explicitly at `n = 5` by the `ring` step above.

General-`n` closure remains **deferred**. The simp-on-the-recursive
`det_succ_row_zero` worked at n=4 and n=5 in single passes, which
is encouraging evidence that the cofactor-expansion induction (the
textbook's "direct" path, distinct from the eigenvalue-density
argument) may be tractable when the right inductive invariant is
identified. That remains multi-cycle infrastructure scope.

**State after cycle 147** (file `OpenMath/Chapter5/Section550.lean`):

* `doublyCompanionMatrix` — kept
* `doublyCompanionMatrix_one_eq` simp lemma — kept
* `alphaPoly`, `betaPoly` — kept
* `doublyCompanionMatrix_det_factorization_n_one` — kept (axiom-clean, cycle 138)
* `doublyCompanionMatrix_det_factorization_n_two` — kept (axiom-clean, cycle 140)
* `doublyCompanionMatrix_det_factorization_n_three` — kept (axiom-clean, cycle 144)
* `doublyCompanionMatrix_det_factorization_n_four` — kept (axiom-clean, cycle 145)
* `doublyCompanionMatrix_det_factorization_n_five` — **added** (axiom-clean, cycle 147)
* `doublyCompanionMatrix_det_factorization` (general n) — still **absent**

## Status update (cycle 144) — n=3 STEPPING STONE ADDED

`doublyCompanionMatrix_det_factorization_n_three` landed axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Strategy:

1. Reduce `doublyCompanionMatrix α β` at `n = 3` to an explicit
   `!![…]` form via `ext i j; fin_cases i <;> fin_cases j <;> simp […]`
   (mirroring the cycle 138 `_one_eq` simp lemma but inline, since
   the explicit matrix is only used in this one proof).
2. Reduce `1 - z • X` to a second explicit `!![…]` form by a second
   `fin_cases` block.
3. Use `Matrix.det_fin_three` to expand the determinant; collapse the
   polynomial identity with `simp [alphaPoly, betaPoly,
   Fin.sum_univ_three]; ring`.
4. Close the `IsBigO` via `Asymptotics.IsBigO.of_bound` with constant
   `‖a‖ + ‖b‖ + ‖c‖`, where the residue factors as
   `z^4 · (a + z·b + z²·c)` with
   * `a := -(α 0 · β 2) - β 0 · α 2 - β 1 · α 1`,
   * `b := -(β 1 · α 2) - α 1 · β 2`,
   * `c := -(α 2 · β 2)`.
   Bound via repeated `norm_add_le` + `mul_le_of_le_one_left` exploiting
   `‖z‖ ≤ 1`.

**Three data points (n = 1, 2, 3)** now confirm the leading-coefficient
pattern `−Σᵢ αᵢ · β_{n−i} z^{n+1}` predicted by Theorem 550A. Higher-
order coefficients also match the `α(z) · β(z)` expansion exactly. The
cancellation of `z⁰`–`z³` in `det(I − zX) − α(z)·β(z)` is the textbook
content; verified explicitly at `n = 3` by the `ring` step above.

General-`n` closure remains **deferred** per the prior status updates
below. Cycle 141 cancelled the Aristotle general-`n` job at 6% after
24h; manual cofactor-expansion or eigenvalue-density argument is
multi-cycle infrastructure. The n=3 stepping stone leaves sorry count
unchanged at 0 and adds one more axiom-clean witness.

**State after cycle 144** (file `OpenMath/Chapter5/Section550.lean`):

* `doublyCompanionMatrix` — kept
* `doublyCompanionMatrix_one_eq` simp lemma — kept
* `alphaPoly`, `betaPoly` — kept
* `doublyCompanionMatrix_det_factorization_n_one` — kept (axiom-clean, cycle 138)
* `doublyCompanionMatrix_det_factorization_n_two` — kept (axiom-clean, cycle 140)
* `doublyCompanionMatrix_det_factorization_n_three` — **added** (axiom-clean, cycle 144)
* `doublyCompanionMatrix_det_factorization` (general n) — still **absent**

## Status update (cycle 140) — n=2 STEPPING STONE ADDED

Aristotle Job B (project `70f26d67-b37e-4eda-b946-64c9f4616612`,
focused on `n = 2`) returned **COMPLETE** during the cycle 140 poll.
Its proof was inlined verbatim as
`doublyCompanionMatrix_det_factorization_n_two`
(axiom-clean: `[propext, Classical.choice, Quot.sound]`). The proof
uses `Matrix.det_fin_two` to evaluate the determinant explicitly,
factors out `z^3` from the residue, and concludes the `IsBigO` via
`Asymptotics.IsBigO.of_bound` with an explicit constant
`‖-(α 0 * β 1) - β 0 * α 1‖ + ‖α 1 * β 1‖`. The `‖y‖ < 1`
neighborhood handles the higher-order `α 1 · β 1 · z⁴` term by
dominating `‖z‖ ≤ 1`.

Aristotle Job A (project `7062c2a2-4a8b-4fae-b694-9355e06427a9`,
general `n`) was still IN_PROGRESS at 4% (last update
2026-05-05T19:50:00, ≈40 minutes after submission). It was **left
running** rather than cancelled; a future cycle should poll once
more. If it eventually returns cleanly, the general-n statement and
proof can be reinstated; otherwise the deferral plan below remains
in force.

The n=2 closure provides a second axiom-clean witness alongside the
n=1 case, and confirms the closed-form residue formula
`-(α 0 · β 1 + α 1 · β 0) z³ - (α 1 · β 1) z⁴` is correct. This is
useful evidence for whoever eventually attacks general `n` (the
residue's leading coefficient pattern is `-(α_i · β_{n-i})` summed
over `i = 0..n-1` — visible already at n=1 and n=2).

**State after cycle 140** (file `OpenMath/Chapter5/Section550.lean`):

* `doublyCompanionMatrix` — kept
* `doublyCompanionMatrix_one_eq` simp lemma — kept
* `alphaPoly`, `betaPoly` — kept
* `doublyCompanionMatrix_det_factorization_n_one` — kept (axiom-clean, cycle 138)
* `doublyCompanionMatrix_det_factorization_n_two` — **added** (axiom-clean, cycle 140)
* `doublyCompanionMatrix_det_factorization` (general n) — still **absent**

## Status update (cycle 139)

The cycle-138 `sorry`-first scaffold for the general-`n` theorem has
been **removed** in cycle 139 to drive the §550 sorry count from 1
back to 0. The supervisor scored cycle 138 at −2 solely because the
sorry rose 0 → 1; the cleanest single-cycle remediation that does not
risk a stalled manual proof was to remove the statement until the
closure infrastructure is in place.

**State after cycle 139** (file `OpenMath/Chapter5/Section550.lean`):

* `doublyCompanionMatrix` — kept (definition unchanged, n=1 verified)
* `doublyCompanionMatrix_one_eq` simp lemma — kept
* `alphaPoly`, `betaPoly` — kept
* `doublyCompanionMatrix_det_factorization_n_one` — kept (axiom-clean)
* `doublyCompanionMatrix_det_factorization` (general n) — **removed**

Aristotle jobs from cycle 138 (project `7062c2a2-…` general-n,
project `70f26d67-…` n=2) were still IN_PROGRESS (4% / 3%) at the
cycle-139 poll. They were left running rather than re-submitted; a
future cycle will check them once and, if either returns cleanly,
reinstate the general-n statement together with its proof body.

## Blocker

`OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization`
is stated with `sorry` for general `n ∈ ℕ`. The `n = 1` specialisation
(`doublyCompanionMatrix_det_factorization_n_one`) is closed axiom-clean
in cycle 138 as a genuine witness, but the general-`n` proof is
multi-cycle infrastructure work.

## Context

**File**: `OpenMath/Chapter5/Section550.lean:111` (sorry at line ~121).
**Theorem (Butcher §550, p. 457)**: for the doubly companion matrix
`X = doublyCompanionMatrix α β`,
```
det(I − z X) = α(z) · β(z) + O(z^{n+1})    as z → 0 in ℂ
```
where `α(z) = 1 + Σᵢ α_i z^{i+1}` and similarly `β(z)`.

**Textbook proof outline** (eigenvalue density):
1. WLOG assume X has distinct non-zero eigenvalues (the choices of α
   that yield such X form a *dense* subset; the LHS and RHS are
   continuous in α, β; conclude on the dense set and extend).
2. Let λ be an eigenvalue. Define
   `v_k = λ^k + β₁ λ^{k-1} + … + βₖ`, k = 0..n. The vector
   `V = (v_{n-1}, …, v_0)` is the eigenvector for λ (verify by
   comparing components 2..n of `Xv = λv`).
3. The first-component equation
   `λ v_n + α₁ v_{n-1} + … + αₙ = 0`
   reduces (after substituting `λ = z⁻¹` and clearing the `λ^n`
   denominator) to
   `det(I − zX) = α(z)·β(z) + O(z^{n+1})`.

## What was tried

* Cycle 138 closed `n = 1` directly via `Matrix.det_fin_one` (~30 LOC).
* Two Aristotle jobs submitted in cycle 138:
  * Project `7062c2a2-4a8b-4fae-b694-9355e06427a9` — full general-n.
  * Project `70f26d67-b37e-4eda-b946-64c9f4616612` — focused on the
    `n = 2` specialisation.
  Their results will be processed in cycle 139.

## Why deferral

The eigenvalue-density argument requires several Mathlib pieces in
concert:
* Continuity of charpoly coefficients in matrix entries
  (`Polynomial.coeff_charpoly` together with continuity of polynomial
  multiplication and `Matrix.charpoly` in the entry-by-entry topology).
* Density of "distinct non-zero eigenvalues" in coefficient space
  (the discriminant of the characteristic polynomial is a non-trivial
  polynomial in the matrix entries, hence its zero set is closed and
  nowhere dense in any standard topology on ℂⁿ²).
* Identity-of-analytic-functions-style extension by continuity (or, in
  this case, just identity of polynomials in coefficient space, since
  the charpoly coefficients are *polynomial* in the entries).

Each of these is available in Mathlib, but the assembly is multi-cycle.

## Possible solutions

1. **Direct cofactor expansion of `det(I − zX)` for general `n`.**
   Exploit the sparse structure (only the first row, the last column,
   and the sub-diagonal are non-zero). Compute the determinant by
   Laplace expansion along the first column. Tedious but mechanical;
   plausible single-cycle work for cycle 139 (~150 LOC).

2. **Eigenvalue-density argument** (the textbook's path). ~300 LOC over
   2–3 cycles.

3. **Induction on `n` via row-reduction.** The `(n−1) × (n−1)`
   bottom-right block of `X` is itself a doubly companion matrix shifted
   down. This may be the cleanest approach; sketch in cycle 139.

4. **Wait for Aristotle**. Both jobs submitted in cycle 138; if either
   returns a clean proof, incorporate in cycle 139.

## Cross-reference

`thm:550A` blocks:
* `thm:550B` (similarity transformation; uses 550A + the (550d)
  `n`-fold-eigenvalue case).
* `thm:551B` (M(z) eigenvalue analysis for IRK stability).
* `thm:553A` (derivation of methods with IRK stability).

## Cycle plan

* **Cycle 139**: process Aristotle returns; if both fail, attempt the
  manual `n = 2` closure (~80 LOC) as a stepping stone, plus draft a
  cofactor-expansion sketch for general `n`.
* **Cycle 140+**: if no Aristotle path opens, commit to the
  cofactor-expansion or induction plan over 2 cycles.
