# Cycle 110 Results

## Worked on
Theorem 356C: AN-stability implies algebraic stability (`OpenMath/ANStability.lean`)

## Approach
1. Created `OpenMath/ANStability.lean` with sorry-first structure: definitions (Aℂ, bℂ, stabilityFnDiag, IsANStable), Part 1 (bⱼ ≥ 0), Part 2 (M PSD), and the main theorem `an_stable_implies_alg_stable`.
2. Submitted to Aristotle (project `95f3a6d4-c727-4482-9525-94f795041d07`). Still in progress at cycle end (13%).
3. Manually proved 3 of 4 sorry's while Aristotle ran.

## Result
PARTIAL SUCCESS — 3 of 4 sorry's closed, 1 remains.

### Closed sorry's:
- **`det_negTauBasis`**: For Z = -τ E_jj, det(I-AZ) = 1 + τ A_jj. Used `Matrix.mul_diagonal` to simplify AZ entry-wise, then `Matrix.det_one_add_replicateCol_mul_replicateRow` for the rank-1 determinant formula, then `Finset.sum_ite_eq'` for the dot product.

- **`stabilityFn_negTauBasis`**: R(Z) = (1+τ(A_jj-b_j))/(1+τA_jj). Key approach: set x = M⁻¹·𝟙, prove M·x = 𝟙 via `mulVec_mulVec` + `mul_nonsing_inv` + `one_mulVec`. Used `Finset.sum_eq_single j` to extract x_j from the matrix equation, getting (1+τA_jj)·x_j = 1. Then rewrote the stability function sum using `diagonal_mulVec` and `sum_ite_eq'` to collapse to one term. Final algebraic step via `linear_combination`.

- **`norm_stabilityFn_negTauBasis_gt_one`**: |R| > 1 when b_j < 0. Chose τ = 1/(2+2|A_jj|), showed 1+τA_jj > 0, cast num/denom to ℝ, used `Complex.ofReal_div`, `Complex.norm_real`, `one_lt_div₀`, and `nlinarith`.

### Remaining sorry:
- **`norm_stabilityFn_imagBasis_gt_one`**: For Z = iτ·diag(v) with v'Mv < 0, show |R(Z)| > 1 for small τ. Requires Taylor expansion |R(iτv)|² = 1 - τ²v'Mv + O(τ³) via Neumann series of (I±AZ)⁻¹. Genuinely hard — needs series expansion and careful coefficient tracking.

## Dead ends
- `nlinarith` over ℂ: doesn't work (ℂ not linearly ordered). Used `linear_combination` instead for complex algebraic identities.
- `if_pos rfl` in simp: sometimes Lean turns `j = j` into `True` first (via `eq_self_iff_true`), leaving `if True then ...`. Use `ite_true` instead.
- Direct `rw` with `← hx_def` after `← mulVec_mulVec`: the newly introduced `M⁻¹.mulVec ...` wasn't found by `rw`. Solution: prove the function-level equality first, then apply with `congr_fun`.

## Discovery
- `Matrix.mulVec_mulVec` is `@[simp]` and very useful for associativity: `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`
- `Matrix.mul_nonsing_inv` requires `IsUnit M.det`, obtained from `Ne.isUnit`
- `Matrix.mulVec_diagonal` gives `(diag v).mulVec w x = v x * w x`
- `Finset.sum_eq_single j` is the go-to tactic for reducing matrix sums when only one entry survives
- `Complex.ofReal_neg` needed to normalize `↑(-τ)` to `-(↑τ)` before `ring`/`linear_combination`

## Suggested next approach
1. Close `norm_stabilityFn_imagBasis_gt_one` via Neumann series expansion. The proof structure should be:
   - For small τ, show det(I - iτAV) ≠ 0 (polynomial in τ, value 1 at τ=0)
   - Expand R(iτv) = 1 + iτ·(Σ b_i v_i) - τ²·(Σ_{ij} b_i v_i A_{ij} v_j) + O(τ³) using truncated Neumann series
   - Compute |R|² and extract the τ² coefficient as -v'Mv
   - Use positivity of -v'Mv (given v'Mv < 0) to get |R|² > 1
2. If the Neumann series approach is too complex, consider a polynomial/rational function argument: |R|² · |det|² is a polynomial, compute its Taylor coefficients directly.
3. Alternatively, submit the single remaining sorry to Aristotle with a more detailed prompt.
