# Cycle 704 Results

## Worked on
§521 Step C.18 — `toGLM_charpoly_eval_zero_eq_zero_of_bdf`. The
boundary `ξ = 0` case excluded from Step C.17 (cycle 702): under BDF
and `D = 1 - z β_last ≠ 0` with `s ≥ 1`, the GLM stability matrix
charpoly vanishes at `ξ = 0`.

## Approach
Followed the strategy recipe verbatim. Appended the theorem inside the
existing `namespace LMM` (just before the file's final `end LMM`),
right after `toGLM_charpoly_eval_ne_zero_iff_stabilityPoly_of_bdf`.

Five-line proof:
```
have h := D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf m z hbdf hz
have heval := congrArg (Polynomial.eval (0 : ℂ)) h
simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
  Polynomial.eval_X] at heval
rw [zero_pow hs.ne', zero_mul] at heval
exact (mul_eq_zero.mp heval).resolve_left hz
```

## Result
SUCCESS — `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`
compiled cleanly on the first attempt with zero diagnostics.

`zero_pow hs.ne'` fired correctly without needing any of the proposed
fallback variants. `mul_eq_zero.mp heval` gave the disjunction in the
expected order (`D = 0 ∨ charpoly.eval 0 = 0`), so `.resolve_left hz`
closed it directly.

## Dead ends
None — the recipe worked verbatim.

## Discovery
The strategy's recipe was exact; the cycle 700/702 pattern of
`congrArg (Polynomial.eval ξ) + simp only [Polynomial.eval_*] + rw +
mul_eq_zero.mp _ |>.resolve_left _` extends cleanly to the `ξ = 0`
boundary case, with `zero_pow hs.ne'` collapsing the `X^s` factor.

## Suggested next approach
Cycle 705 should land the unifying iff combining C.17 + C.18:

```
((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0 ↔
  ξ = 0 ∨ (m.stabilityPolyPoly z).eval ξ = 0
```

(under BDF + `D ≠ 0` + `s ≥ 1`). Forward direction: case split on
`ξ = 0`; if zero, left disjunct; else apply C.17. Backward direction:
left disjunct uses C.18 directly; right disjunct uses C.17 backward.

After that, the file is positioned to start on the unit-disk
root-counting argument that feeds the `LMM.toGLM_isAStable_iff`
headline.

## Verification
- `git diff --stat`: only `OpenMath/LMMAsGLM/StabilityCharpoly.lean`
  modified, +22 lines (theorem body + docstring).
- `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`: 0 errors,
  0 warnings.
- `git status` clean after commit.
