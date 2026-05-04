# Cycle 798 Results

## Worked on
Tier A from the cycle 798 strategy: the two missing main-method
`_toGLM_hasOrderGe1` witnesses for the embedded RK pairs RKF45 and DOPRI5
in `OpenMath/RKAsGLM.lean`.

## Approach
Direct copy of the BS32 main-method `_hasOrderGe1` template at
`OpenMath/RKAsGLM.lean:1511`:

```
theorem rk<X>_mainMethod_toGLM_hasOrderGe1 :
    rk<X>.mainMethod.toGLM.HasOrderGe1 :=
  rk<X>.mainMethod.toGLM_hasOrderGe1
    rk<X>_consistent.main_consistent
```

The two new theorems (`rkRKF45_mainMethod_toGLM_hasOrderGe1` and
`rkDOPRI5_mainMethod_toGLM_hasOrderGe1`) were placed immediately below
the existing `_hasOrderGe2` theorems for the corresponding methods, in
the §530 "main-method GLM order witnesses" cluster.

## Result
SUCCESS. `lake env lean OpenMath/RKAsGLM.lean` exits 0 with the new
theorems compiled. No new errors; only pre-existing simp-arg linter
warnings at lines 804 and 825 (untouched this cycle).

## Dead ends
None — the strategy template was correct as given. No edits were
needed beyond the two one-line term-mode proofs.

## Discovery
* The `rk<X>_consistent.main_consistent` projection is shared verbatim
  with the existing `_hasOrderGe2` proofs in the file (cycles 794, 796),
  so there is zero new infrastructure to land for the trivial rung.
* The §530 main-method witness table is now complete for every embedded
  RK pair currently in the project: HeunEuler21, BS32, RKF45, DOPRI5
  each have HasOrderGe1 through their respective max order witness.

## Suggested next approach
* Tier B (AM3 `_toGLM_hasOrderGe3`) was not attempted this cycle since
  the strategy designated Tier A as a sufficient cycle and the AM3
  shifted-Nordsieck template requires hand-computing the AM3 shift
  constant `C` from the AM3 β-coefficients. A future targeted cycle
  should: (a) compute `C` so that `(U q'')_0 = 0` for the AM3
  Nordsieck obligation; (b) clone the AM2 HasOrderGe3 proof shape at
  `OpenMath/LMMAsGLM.lean:1979` with the AM3 coefficients and the new
  `C`; (c) verify with `fin_cases`+`simp`+`norm_num`. If that lands,
  add `adamsMoulton3_toGLM_hasOrderGe2` as a `.toHasOrderGe2` corollary
  (mirroring the AM2 pattern at line 2014).
* The §530 witness table is now nearly saturated for the embedded RK
  pairs and BDF/AM/AB tables that fit under the s = 4/5 heartbeat
  ceiling. The next visible structural seam is either §531 (GLM
  stability matrix) or the LMM Nordsieck shifted-template extension to
  AM3+ — but the latter still needs the per-method shift constants.
