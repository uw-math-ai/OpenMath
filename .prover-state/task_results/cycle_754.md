# Cycle 754 Results

## Worked on
Butcher §543 — **Almost Runge–Kutta** (ARK) structural conditions.
Appended to `OpenMath/DIMSIM.lean` after the cycle 752 §542 block.

## Approach
Followed the cycle 754 strategy verbatim:

1. **Predicate** `GeneralLinearMethod.IsAlmostRungeKutta`: §542 RK
   stability **and** every charpoly root of `M(0)` other than `1`
   equals `0` (textbook example (505a) `σ(M(0)) = (1, 0, 0)`).
2. **RK-side bridge** `ButcherTableau.toGLM_isAlmostRungeKutta`: every
   RK-as-GLM is ARK because `M(0)` is the `1×1` matrix
   `!![stabilityFunction t 0] = !![1]`, whose sole charpoly root is
   `1`, so the spurious-eigenvalue clause is vacuous.
3. **Concrete witnesses** for `rkEuler`, `rkImplicitEuler`, `rkSDIRK2`
   (one-liners delegating to the bridge).

## Result
SUCCESS. `OpenMath/DIMSIM.lean` now 294 lines (from 237 in cycle 752),
zero sorry, compiles cleanly via `lake env lean OpenMath/DIMSIM.lean`.

The non-trivial seam — proving `stabilityFunction t (0 : ℂ) = 1` —
collapsed under `simp [ButcherTableau.stabilityFunction]` exactly as
the strategy predicted: at `z = 0` the second summand
`z * ∑ i j, b i * (...)` vanishes by `zero_mul`, leaving `1 + 0 = 1`.

## Dead ends
None encountered this cycle. The strategy's anticipated fallback path
(manual reduction `(1 - 0 • A) = 1`, `Matrix.inv_one`, `Matrix.one_mulVec`)
was not needed.

## Discovery
The §542 RK-side proof pattern from cycle 752 (re-use
`charpoly_fin_one_const_isRoot_iff` after `rw [toGLM_stabilityMatrix]`)
generalises cleanly to §543. The shape is:
1. unfold the RK→GLM stability matrix to a constant `1×1` matrix,
2. read off the unique charpoly root via the constant-matrix lemma,
3. compute the RK stability function at the requested `z`.
This will likely repeat for §544+ structural classes that constrain
`M(z)` at specific test values.

## Suggested next approach
Plan options for cycle 755:

* **§544 — order conditions for ARK.** The textbook follows §543 with
  order-conditions for the ARK class (analogous to RK trees but
  carrying the spurious-mode bookkeeping). On the RK side these
  collapse to standard tree conditions.
* **Lift `IsAlmostRungeKutta` to a non-trivial GLM example.** The
  cleanest target is a 1-step LMM whose `V` is `1×1`: it is RK stable
  and the spurious clause is vacuous. This would extend §543 beyond
  RK without re-opening the LMM charpoly factorisation chain that
  consumed cycles 641–732.
* **`stabilityFunction t 0 = 1` as a public lemma.** The proof is
  `simp [stabilityFunction]`, but lifting it to a named theorem in
  `OpenMath/RKAsGLM.lean` would let §544+ work avoid repeating the
  one-line reduction.

Avoid (per disproven.md / strategy hard constraints): LMM-side ARK
charpoly gymnastics with `r ≥ 2`, anything in `OpenMath/Hamiltonian.lean`,
§38 Butcher-group `bSeriesConvAug` `cut_assoc`.
