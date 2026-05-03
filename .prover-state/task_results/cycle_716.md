# Cycle 716 Results

## Worked on
§521 Steps D.10a + D.10b — `rowFAlphaPoly` evaluation specialisations
in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`. Both theorems were
landed inserted immediately before `end LMM` (now lines 1965–2000).

## Approach
Followed the strategy template exactly. Used the cycle 712 D.6/D.7
proof skeletons as drop-in templates:
- D.10a: `rw [rowFAlphaPoly_eq_residual_sum]; rw [Polynomial.eval_finset_sum];
  rw [Finset.sum_eq_single ⟨0, hs⟩]` then dispatch the three goals via
  `simp`, the `zero_pow hk'` simp set, and `Finset.mem_univ`.
- D.10b: `rw [rowFAlphaPoly_eq_residual_sum]; rw [Polynomial.eval_finset_sum]`
  then `Finset.sum_congr rfl` + per-summand `simp` with the
  `eval_mul/pow/X` set (every `1 ^ l` collapses, every `mul_one`
  collapses).

## Result
SUCCESS — both D.10a and D.10b compiled on first attempt under
`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` (empty
output). File grew from 1964 → 2000 lines, well under the 3000-line
cap. Zero `sorry`s introduced; the `rowFAlphaResidual` evaluation is
left abstract per the strategy.

## Dead ends
None — the proof skeletons in the strategy were copy-paste mirrors of
cycle 712 D.6/D.7 and worked verbatim.

## Discovery
Confirmed that the cycle 712 `Finset.sum_eq_single + zero_pow hk'`
shape generalises one-to-one from the
`(toGLM_stabilityMatrixPY m 0).charpoly` wrapper to the
`rowFAlphaPoly m` wrapper without any adjustment to the per-summand
`simp` lemma set. This means the same template should slot into any
future evaluation of an `f = ∑ l, residual l * X^l` decomposition.

## Suggested next approach
Per the strategy's "If both D.10a and D.10b land" note, the cheapest
next step is **D.11′**: substitute the new D.10a / D.10b right-hand
sides into the cycle 712/714 closed forms `D_mul_toGLM_charpoly_eval_zero_concrete`
(line 1892) and `D_mul_toGLM_charpoly_eval_one_concrete` (line 1913).
That is a pure `rw` chain layering D.10a onto D.8 and D.10b onto D.9,
no new lemma machinery required.

The genuinely hard step D.11 (pushing `Polynomial.eval 0` through
`Matrix.vecMul` against `charmatrix.adjugate * (PYHF).map C`) is best
saved for a dedicated cycle — it needs an `eval ∘ adjugate`
commutation argument and probably a local helper for matrix-entry
`eval` distribution.

A plausible D.12 candidate after D.11′ is the `rowYQuot` companion
evaluations (`rowYQuot.eval 0` and `rowYQuot.eval 1`) so the same
substitution tactic can fully concretise the `rowYQuot.eval ξ * z * β_last`
term still abstract in D.8/D.9.
