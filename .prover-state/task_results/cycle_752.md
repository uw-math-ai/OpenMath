# Cycle 752 Results

## Worked on

Butcher §542 — Runge–Kutta stability for general linear methods. Appended
to `OpenMath/DIMSIM.lean` immediately after the cycle 750 §54 RK-side
DIMSIM bridges.

## Approach

Sorry-first scaffold per the strategy:

1. Defined `GeneralLinearMethod.IsRungeKuttaStable` as the §542 design
   criterion encoded as "any two non-zero charpoly roots of `M(z)` are
   equal" — this avoids charpoly degree / multiplicity bookkeeping
   (an explicitly disproven path per the disproven-identities log).
2. Hoisted `ButcherTableau.charpoly_fin_one_const_isRoot_iff` from
   `private` to public in `OpenMath/RKAsGLM.lean` (single-token edit:
   removed the `private` modifier on line 94). This is the §520 helper
   that says "the only root of the `1×1` charpoly is the matrix
   entry"; the §542 RK-side proof needs it twice.
3. Proved `ButcherTableau.toGLM_isRungeKuttaStable` by rewriting both
   charpoly-root hypotheses through `toGLM_stabilityMatrix` then
   chaining `charpoly_fin_one_const_isRoot_iff` for `μ₁ = a` and
   `μ₂ = a` (where `a = t.stabilityFunction z`).
4. Concrete witnesses for `rkEuler`, `rkImplicitEuler`, `rkSDIRK2`
   plus a one-line conjunction `rkEuler_toGLM_type3_isRungeKuttaStable`
   demonstrating that the §542 predicate composes with §541 type 3.

## Result

**SUCCESS.** `lake env lean OpenMath/DIMSIM.lean` returns no errors.
`lake build` completes successfully (8087 jobs). All four new theorems
plus the helper hoist landed sorry-free.

## Dead ends

None encountered for the §542 work itself. One dependency surprise:
after editing `OpenMath/RKAsGLM.lean` to remove the `private` modifier,
the cached `.olean` made `charpoly_fin_one_const_isRoot_iff` look like
an unknown identifier from `OpenMath/DIMSIM.lean`. Fix was a one-shot
`lake build OpenMath.RKAsGLM` to refresh the export. Worth noting for
future cycles that change visibility modifiers in upstream files.

## Discovery

- The §542 "at most one non-zero eigenvalue" criterion has a clean
  encoding that completely sidesteps `Polynomial.degree` /
  `Matrix.charpoly_degree` reasoning: just quantify "any two
  non-zero roots are equal". This avoided the disproven-identities
  trap around charpoly bookkeeping.
- The RK-side §54 surface (DIMSIM type 1/2/3/4 + RK stability) is
  now mostly trivial corollaries of `r = 1` collapsing the GLM to a
  scalar. §543 ARK should be the same shape: anything sub-eigenstructure
  is vacuous when `r = 1`.

## Suggested next approach

Pivot to §543 Almost Runge–Kutta methods structural conditions:

- Define `IsAlmostRungeKutta` as `IsRungeKuttaStable ∧ <sub-eigenstructure>`
  with the sub-eigenstructure clause taken verbatim from Butcher §543
  Definition 540.
- Prove `ButcherTableau.toGLM_isAlmostRungeKutta` by the same `r = 1`
  pattern as cycle 752: the sub-eigenstructure condition is vacuous
  when the multivalue space is one-dimensional.
- Land witnesses for `rkEuler`, `rkImplicitEuler`, `rkSDIRK2`.

Avoid: any non-trivial GLM (LMM-as-GLM, DIMSIM with `r ≥ 2`). The
disproven-identities log records that LMM charpoly factorisation has
consumed dozens of cycles; the RK-side is the productive seam.

## Files touched

- `OpenMath/DIMSIM.lean` — appended §542 section (~60 lines).
- `OpenMath/RKAsGLM.lean` — removed `private` from
  `charpoly_fin_one_const_isRoot_iff` (one token).
- `plan.md` — marked §542 `[x]`, added cycle 752 to recent history,
  rotated `## Current Target` to §543 ARK.
