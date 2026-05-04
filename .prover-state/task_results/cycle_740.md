# Cycle 740 Results

## Worked on

§521 Step L: general (non-BDF) LMM-to-GLM A-stability iff bridge.
Active file: `OpenMath/LMMAsGLM/StabilityCharpolyEval.lean` (now 1755
lines, up from 1662; well under the 3000-line cap).

Three new theorems landed sorry-free at end-of-file:

- `toGLM_charpoly_eval_eq_zero_iff` (Step L.1) — eval-form root iff
  for `(m.toGLM.stabilityMatrix z).charpoly` at `ξ`, no BDF hypothesis.
- `toGLM_charpoly_eval_ne_zero_iff` (Step L.2) — De Morgan dual.
- `toGLM_isAStable_iff` (Step L.3) — the §521 LMM iff bridge headline,
  no BDF restriction.

## Approach

Followed the strategy verbatim. L.1 evaluates the cycle 736 polynomial
identity K.1 (`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly`) at
`ξ` and casework-splits on `mul_eq_zero` / `pow_eq_zero_iff`. L.2 is a
one-liner via `Ne` + `not_or`. L.3 mirrors
`toGLM_isAStable_iff_of_bdf` (`OpenMath/LMMAsGLM/Stability.lean:1063`)
with K.1 in place of the BDF charpoly factorisation; the s = 0 (⇐)
boundary closes by `Matrix.det_isEmpty` showing the empty charpoly
is `1`.

## Result

SUCCESS. `lake env lean OpenMath/LMMAsGLM/StabilityCharpolyEval.lean`
returns clean. `lake build` returns clean (8087 jobs).

## Dead ends

- Initial transcription of L.1's reverse-direction `ξ = 0` branch used
  `rw [hξ0, ...] at heval` but left the goal still phrased in `ξ`.
  Fixed by `subst hξ0` before rewriting `heval`. Pattern lesson:
  when introducing an equation hypothesis, prefer `subst` over `rw …
  at` if the target also depends on the variable.
- L.3's (⇒) branch first attempted
  `rw [← Polynomial.IsRoot.def, Polynomial.IsRoot, ...]` to convert
  the goal `IsRoot charpoly ξ` to `charpoly.eval ξ = 0`. The `rw [←
  Polynomial.IsRoot.def]` direction was wrong and `Polynomial.IsRoot`
  is a `def` not a simp-rewrite. Replaced with `show … = 0` to leverage
  the definitional unfolding directly.

## Discovery

- The s = 0 (⇐) branch — flagged as the residual risk in the strategy
  — closes cleanly with `simp [Matrix.charpoly, Matrix.charmatrix,
  Matrix.det_isEmpty]`. No fallback / `Matrix.charpoly_zero_eq_one`
  search was needed.
- `m.toGLM` has shape `GeneralLinearMethod 1 (2 * s)`, so at `s = 0`
  the GLM stability matrix is `Fin 0 × Fin 0` (genuinely empty),
  cleanly making `Matrix.det_isEmpty` applicable. Note this is the
  GLM `r = 2 * s` convention (LMMAsGLM.lean:58), not `r = s`.

## Suggested next approach

Backlog item #7's iff-bridge sub-goal is closed; further §521 work is
either (a) §522 Butcher–Chipman conjecture outline (low priority,
mostly survey-shaped), (b) §523 algebraic / non-linear stability
(material gap), or (c) one-shot concrete LMM A-stability transports
that are now downstream of `toGLM_isAStable_iff`.

The natural next move is the next backlog item — Butcher §111 linear
ODE closed form `y = exp((x − x₀) A) y₀` — as scoped in the updated
`## Current Target` in `plan.md`. If §111 reveals a sizable Mathlib
gap on the matrix-exponential derivative side, the planner should
pivot to Backlog item #6 (Butcher §463 Milne device) and record the
§111 obstruction in `.prover-state/issues/`.
