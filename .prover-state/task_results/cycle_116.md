# Cycle 116 Results

## Worked on
- `ANStability.lean`: replaced broken repo version with Aristotle d535dc15 result, extracted `continuousAt_imagBasis_inv` helper to eliminate `maxHeartbeats 800000`
- `BNStability.lean`: closed all 5 sorry's (Theorem 357C: algebraic stability implies BN-stability)

## Approach

### ANStability.lean (Priority 1)
1. Copied Aristotle d535dc15 result to replace the broken repo version
2. Fixed import to `import OpenMath.StiffEquations`
3. The Aristotle version used `set_option maxHeartbeats 800000` on `norm_stabilityFn_imagBasis_gt_one`
4. Extracted `continuousAt_imagBasis_inv` as a standalone lemma to decompose the proof
5. Removed `maxHeartbeats` override — compiles within default 200000

### BNStability.lean (Priority 2)
Closed all 5 sorry's:

1. **`rk_stage_difference_eq`** — Pure algebra: unfold `SatisfiesRKStep`, substitute, use `smul_sub`/`sum_sub_distrib`/`abel`
2. **`rk_output_difference_eq`** — Same pattern for output difference
3. **`algStabMatrix_inner_nonneg`** — Hardest lemma. Used Parseval identity in finite-dimensional span of {U_i}, swapped triple sums via `Finset.sum_comm`, applied `posdef_M` coordinate-by-coordinate
4. **`rk_step_norm_sq_identity`** — Norm-squared identity (357e). Structured as:
   - `h_lhs`: expand `‖d + h•w‖²` via `norm_add_sq_real`
   - `h_lem1`: stage inner product expansion `∑bᵢ⟨Yᵢ-Zᵢ, Fᵢ-Gᵢ⟩ = ⟨d,w⟩ + h*S`
   - `h_lem2`: M-matrix expansion `∑Mᵢⱼ⟨Fᵢ-Gᵢ, Fⱼ-Gⱼ⟩ = 2S - ‖w‖²` by expanding `algStabMatrix`, distributing, identifying T1=S (inner product comm), T2=S (index swap), T3=‖w‖² (sum_inner/inner_sum)
5. **`alg_stable_implies_bn_stable`** — Combined identity with dissipativity (nonpositive) and PSD form (nonneg), used `nlinarith` + `le_of_sq_le_sq`

## Result
**SUCCESS** — Both files compile with 0 sorry's. Entire project has 0 sorry's.

- `lean_verify ButcherTableau.alg_stable_implies_bn_stable`: only standard axioms (propext, Classical.choice, Quot.sound)
- `lean_verify ButcherTableau.an_stable_implies_alg_stable`: verified in earlier step

## Dead ends
- Aristotle job `8184d812` (initial BNStability submission): HTTP 500 errors, unusable
- Aristotle job `29f1dee7` (second BNStability submission): also HTTP 500, proved manually instead
- `congr/ext` approach for sum equalities in h_lem2 — over-closes goals; `Finset.sum_congr rfl` is more controlled
- `conv_lhs => ext i; ext j` for nested sum rewriting — fails because `conv_lhs` on `0 ≤ ∑...` targets `0`, not the sum

## Discovery
- `Finset.sum_comm` alone can close index-swap equalities when bound variable names align after the swap (hT2 proof)
- `real_inner_self_eq_norm_sq` + `sum_inner`/`inner_sum`/`real_inner_smul_left`/`real_inner_smul_right` is the right pipeline for expanding `‖∑ bᵢ • vᵢ‖²`
- For Parseval-style arguments, working in `Submodule.span ℝ (Set.range U)` with `stdOrthonormalBasis` avoids needing `FiniteDimensional` on the ambient space
- `set` abbreviations are definitionally transparent, so `rfl` can close goals where the only difference is folding/unfolding a `set` name

## Suggested next approach
- Project is at 0 sorry's. Focus on cleanup (Priority 3 from strategy): remove obsolete issue files
- Consider formalizing next textbook theorems per `plan.md`
