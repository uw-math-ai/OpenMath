# Cycle 635 Results

## Worked on

Butcher §521 RK-side stability-defect bridge in `OpenMath/RKAsGLM.lean`.

## Approach

Followed the cycle 635 strategy and stayed away from the reverted LMM-side
parametric charpoly factorization. Added the new
`## §521 — Stability defect for RK as GLM` section immediately after
`ButcherTableau.toGLM_isAStable_iff`.

Each theorem was introduced sorry-first, checked with
`lake env lean OpenMath/RKAsGLM.lean`, then closed before moving on:

- `ButcherTableau.toGLM_qℂ_one`
- `ButcherTableau.toGLM_stabilityDefect_apply`
- `ButcherTableau.toGLM_stabilityDefect_zero`
- `ButcherTableau.toGLM_stabilityDefect_eq_zero_iff`

The closed-form defect proof unfolds
`GeneralLinearMethod.stabilityDefect`, rewrites with
`ButcherTableau.toGLM_stabilityMatrix`, and simplifies the singleton
`Fin 1` matrix-vector product. The zero-defect theorem is a direct
specialization of `GeneralLinearMethod.stabilityDefect_zero`.

## Result

SUCCESS. All three required deliverables landed sorry-free, and the
optional zero-iff theorem also landed sorry-free.

Verification passed:

- `lake env lean OpenMath/RKAsGLM.lean`
- `lake env lean OpenMath/LMMAsGLM.lean`
- `lake env lean OpenMath/GeneralLinearMethod.lean`

`plan.md` was updated in the §521 chapter list, cycle history block, and
backlog item #7.

## Dead ends

The first `RKAsGLM.lean` check could not see
`GeneralLinearMethod.qℂ` because the local compiled
`OpenMath.GeneralLinearMethod` import was stale relative to the live
source from cycle 633. Rebuilding that module once with
`lake build OpenMath.GeneralLinearMethod` fixed the import surface.

No Aristotle batch was submitted after the sorry-first checks because the
goals closed immediately by `simp` / direct specialization and there were
no remaining unresolved subgoals to hand off.

## Discovery

The RK GLM embedding makes the §521 defect literally
`R(z) - exp(z)` entrywise:

```lean
t.toGLM.stabilityDefect (fun _ => (1 : ℝ)) z k =
  t.stabilityFunction z - Complex.exp z
```

The function-level zero iff needs one explicit normalization of
`(0 : Fin 1 → ℂ) 0`; `simpa [toGLM_stabilityDefect_apply] using
congrFun h 0` is the clean route.

## Suggested next approach

Keep the next §521 cycle focused on a structured plan for the
`LMM.toGLM_isAStable_iff` bridge. Do not add more concrete LMM
A-stability transports before the general iff bridge lands.
