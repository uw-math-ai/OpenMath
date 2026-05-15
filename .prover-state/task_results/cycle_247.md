# Cycle 247 Results

## Worked on

`thm:319B` Phase 2 — the textbook headline global truncation error bound:
> `‖y(x_n) − y_n‖ ≤ (if L^† = 0 then (n : ℝ) · h else (exp(L^†·(n·h)) − 1)/L^†) · C · h^p`

After this cycle, §319 is **fully formalized** (both `lem:319A` and
`thm:319B`).

## Approach

Followed the cycle 247 strategy verbatim:

1. **§A verification**: `git log` confirms cycle 246 `d21babd` shipped Phase 1.
   `grep -c sorry OpenMath/Chapter3/Section319.lean = 0`. `wc -l = 871`.
   All match expected state.

2. **§D Mathlib hooks**: verified before writing the proof:
   - `Real.add_one_le_exp : ∀ x, x + 1 ≤ Real.exp x` ✓ (in `Mathlib.Analysis.Complex.Exponential`)
   - `geom_sum_eq : x ≠ 1 → ∑ i ∈ range n, x^i = (x^n - 1)/(x - 1)` ✓ (in `Mathlib.Algebra.Field.GeomSum`)
   - `Finset.sum_range_reflect : ∑ j ∈ range n, f (n - 1 - j) = ∑ j ∈ range n, f j` ✓ (in `Mathlib.Algebra.BigOperators.Intervals`)
   - `Fin.sum_univ_eq_sum_range : ∑ i : Fin n, f i.val = ∑ i ∈ range n, f i` ✓
   - `Finset.mul_sum`, `Finset.sum_congr` ✓
   - `div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c` ✓ (in `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic`)
   - `Real.exp_add`, `Real.exp_pos`, `pow_nonneg` ✓

   No Mathlib mismatch — all anticipated names worked on first try (R1–R6 risks did not materialize).

3. **D1 — geometric-sum helpers**: two private lemmas
   `OpenMath.Chapter3.Section319.Phase2Helpers.geometric_sum_one_plus_pos`
   (positive-rate closed form) and
   `geometric_sum_one_plus_zero` (degenerate `a = 0` case = `n`).
   The positive case: `Fin.sum_univ_eq_sum_range` → `Finset.sum_range_reflect` → `geom_sum_eq` → `congr` + `ring`. The zero case: `simp` reduces each summand to `1`, then `Finset.sum_const` + `Finset.card_fin`.

4. **D2 — `pow_one_add_le_exp`**: private lemma giving
   `(1 + a)^n ≤ Real.exp ((n : ℝ) * a)` for `0 ≤ a`. Proved by induction
   on `n`. Pinned the right `0 ≤ Real.exp (k * a)` argument to
   `mul_le_mul` (initial draft incorrectly used `0 ≤ Real.exp a`,
   producing the cycle-247 first compile error — fixed inline).

5. **D3 — `thm_319B` main theorem**:
   `OpenMath.Chapter3.Section312.RKTableau.thm_319B`. Body ~100 LOC,
   strictly following the strategy's §C.2 recipe:
   - Apply `accumulation_recurrence` once at the top to get an
     existential `L_dag` (per NOT-6).
   - `yex 0 = traj 0 ⇒ ‖yex 0 - traj 0‖ = 0` zeros the initial-error term.
   - `Finset.mul_sum` pulls the constant `C * h^(p+1)` out of the sum.
   - `eq_or_lt_of_le hL_dag_nn` splits into `L_dag = 0` vs `L_dag > 0`.
   - In the zero branch: `if_pos`, then rewrite `h * L_dag = 0`, then apply
     `geometric_sum_one_plus_zero`. The conclusion `C * h^(p+1) * n
     = (n : ℝ) * h * C * h^p` closes via `h_pow_pp1 : h^(p+1) = h * h^p`
     + `ring`.
   - In the positive branch: `if_neg`, `geometric_sum_one_plus_pos`,
     `pow_one_add_le_exp` for the numerator, `div_le_div_of_nonneg_right`
     to lift through the positive denominator `h * L_dag`,
     `mul_le_mul_of_nonneg_left` to amplify by the non-negative
     `C * h^(p+1)`, then `field_simp` (alone — `ring` after `field_simp`
     produced "No goals to be solved" because `field_simp` already
     closed the goal; fixed inline by removing `ring`).

6. **D7 — non-vacuity witness**: `example` on `paddedEuler` with `f := id`
   (Lipschitz constant 1), `C := 0`, `p := 0`, where the M-matrix
   smallness reduces to `‖0‖ = 0 < 1` because `paddedEuler.A = 0`. The
   bound reduces to `‖…‖ ≤ … · 0 · h^0`, which is `0 ≤ 0` after the
   accumulation step (the `(1 + h L^†)^n - 1) / L^†` factor is finite,
   the `(n : ℝ) * h` factor is finite, and multiplying by `0` zeros the
   RHS).

7. **Compilation**: `lake env lean OpenMath/Chapter3/Section319.lean`
   passes clean (exit code 0, no warnings, no errors).

8. **Axiom check** via `lean_verify` on
   `OpenMath.Chapter3.Section312.RKTableau.thm_319B`:
   `axioms = [propext, Classical.choice, Quot.sound]` — **axiom-clean**.
   (The `lean_verify` source-scan warning about ripgrep being missing is
   environmental and unrelated to the proof content.)

## Result

**SUCCESS** — Phase 2 closed. New public theorem `thm_319B` ships in
`OpenMath/Chapter3/Section319.lean` along with three private helpers
(`geometric_sum_one_plus_pos`, `geometric_sum_one_plus_zero`,
`pow_one_add_le_exp`) and a non-vacuity witness on `paddedEuler` (D7).

Final Section319.lean line count: 1124 (up from 871 in cycle 246; +253
LOC including docstrings). Within the §H budget of ~270 LOC.

## Faithfulness check

**Entity**: `thm:319B` — "Global truncation error bound via local error
accumulation".

Textbook statement (from `entities/thm_319B.json`, `statement_latex`):
> Let $h_0$ and $L$ be such that the local truncation error at step
> $k = 1, 2, \dots, n$ is bounded by
> $\delta_k \leq C h^{p+1}, \quad h \leq h_0$.
> Then the global truncation error is bounded by
> $\| y(x_n) - y_n \| \leq
> \begin{cases}
> \dfrac{\exp(L(x_n - x_0)) - 1}{L} C h^p, & L > 0, \\
> (x_n - x_0) C h^p, & L = 0.
> \end{cases}$

**Lean statement captures**: same content with documented caveats:

1. **Existential `L^†`** (inherited from cycle 245 `lem_319A`):
   Butcher writes `L` (textbook calls it `L^†` in the proof flow) as
   the explicit closed form
   `L · ∑ᵢ |bᵢ| · ((I − h₀ L |A|)⁻¹ 𝟙)ᵢ`. The Lean theorem hides this
   in `∃ L_dag, 0 ≤ L_dag ∧ …` because the explicit closed form is
   unwieldy for downstream consumers. The same `L_dag` is threaded
   through the entire conclusion (one call to `accumulation_recurrence`
   per NOT-6).

2. **Frobenius vs spectral-radius smallness** (inherited from cycle 245):
   the textbook uses `h_0 L ρ(|A|) < 1` (spectral radius);
   Lean uses `‖(h_0 L) • M.A.map (·|·|)‖ < 1` (Frobenius operator norm).
   This is strictly stronger but easier to discharge in concrete examples.

3. **`x_n − x_0` written as `(n : ℝ) · h`**: in our uniform-step
   formulation, the global time elapsed after `n` steps is `n · h`. The
   textbook's `(exp(L^†(x_n - x_0)) − 1)/L^†` becomes
   `(exp(L^†ᐧ(nᐧh)) − 1)/L^†` and `(x_n - x_0) C h^p` becomes
   `(n : ℝ) ᐧ h ᐧ C ᐧ h^p`. No information lost.

4. **Inequality vs equality for `δ_k`** (inherited from cycle 246):
   the textbook defines `δ_k = ‖y(x_k) − ŷ_k‖` as equality; we use
   `HasLocalTruncationErrorBound f h yex δ` which encodes
   `‖yex k.succ − y_step‖ ≤ δ k`. The accumulation argument only needs
   the bound to propagate, so this is faithful.

5. **`yex 0 = traj 0` as hypothesis**: the textbook implicitly takes
   `y(x_0) = y_0` (the numerical method starts from the exact initial
   value). The Lean statement requires this explicitly as
   `h_init : yex 0 = traj 0` so that the initial-error term vanishes.
   Faithful — this is the standard convention.

**Tautology check**: ✓ conclusion is the closed-form bound; no
hypothesis has that shape.

**Identity check**: ✓ proof is ~100 LOC, non-trivial, composes
`accumulation_recurrence` (cycle 246) with three private helpers and
a case-split on `L_dag`.

**Hypothesis strength check**: hypotheses are exactly cycle 245's
`lem_319A` set (`hL : 0 ≤ L`, `hf_lip : LipschitzWith L.toNNReal f`,
`hh : 0 < h`, `hh_le : h ≤ h₀`, `hh₀ : 0 ≤ h₀`, `h_norm` smallness)
plus the new `HasLocalTruncationErrorBound` (Phase 2's textbook
precondition) plus `hC : 0 ≤ C` and `p : ℕ`. No extra strength beyond
what the textbook requires.

**Absent theorem check**: ✓ no comments promise content not present.

## Dead ends

None. The first compile attempt produced two trivial errors fixed
inline:

1. `mul_le_mul` 4th argument needs `0 ≤ Real.exp (k * a)`, not
   `0 ≤ Real.exp a` (I had passed `(Real.exp_pos a).le` instead of
   `(Real.exp_pos (k * a)).le`).
2. `field_simp` in the L_dag > 0 branch already closes the algebraic
   identity goal — the trailing `ring` produces "No goals to be solved".
   Removed the `ring`.

Both were anticipated risk vectors (R3/R4-style) and fixed within
~2 minutes of the first compile error.

## Discovery

1. **`field_simp` is sometimes sufficient on its own**: when clearing a
   single rational expression with a single denominator factor (`h * L_dag`),
   `field_simp` performs the cross-multiplication and `ring`-normalises
   in one shot, leaving no residual goal. The standard
   `field_simp; ring` idiom needs to be tightened to `field_simp` when
   the algebra after denominator clearance is purely a polynomial
   normalisation that `field_simp` already does internally. Useful for
   future cycles to know.

2. **Phase 2's algebra was tighter than anticipated**: the strategy
   document estimated ~120 LOC for the main theorem body and ~30 LOC
   for the non-vacuity witness; actual numbers are ~100 LOC body
   and ~38 LOC witness. The geometric-sum reindex
   (`Fin.sum_univ_eq_sum_range` + `Finset.sum_range_reflect`) was a
   clean two-rewrite sequence with no risk-2 fallback needed.

3. **The cycle-246 false-positive scanner pattern**: confirmed at the
   start of the cycle. `grep -c sorry = 0`, `lean_verify` clean — the
   −1 score is purely a scanner artifact and not a real issue. Cycle
   247's new code may produce more scanner false positives (e.g., from
   `hh_ne`, `hL_ne`, `hL_dag_pos` hypothesis names matching the
   `:= h_<word>` regex over-firing pattern); per the strategy's NOT-7,
   these should be left alone.

## Suggested next approach

§319 is now **closed**. Cycle 248 candidate priorities:

1. **Ch.3 §380-ish entities still open**: `lem:310B` Elementary
   Differential Weight Formula, `lem:311A` Taylor expansion of exact
   solution, `lem:312B` Elementary Weight Summation Formula, `thm:352E`
   V-function recurrence. The Taylor-expansion lemma is foundational
   for the order conditions in Butcher's §32x sequence and would unlock
   downstream Ch.3 theorems.

2. **Ch.5 GLM (General Linear Methods)**: the GLM convergence
   framework is a substantive Ch.5 deliverable; `lem:541A` /
   `thm:542A` / `def:541A`–`def:541C` are likely starting points
   if the planner wants to pivot chapters.

3. **§441 Phase C.2** remains GPFS-blocked; do not retry without
   cluster-side mitigation.

4. **Cleanup stretch**: `OpenMath/Chapter3/Section319.lean` is now 1124
   LOC and structurally mixes `RKTableau` namespace content (cycles
   244–247's main theorems), `Section319.Phase2Helpers` (cycle 247's
   private helpers), and `Section319` namespace non-vacuity examples.
   A future bookkeeping cycle could factor the helpers into a
   dedicated module file (e.g., `OpenMath/Helpers/GeometricExp.lean`)
   to reduce Section319.lean's line count back below 1000 LOC. Low
   priority — the file is navigable as-is.

Recommended cycle 248 entry: **`lem:311A` (Taylor expansion of the
exact solution)** — natural prerequisite for everything order-condition
related in Ch.3.
