# Cycle 692 Results

## Worked on

§521 Step C resolution of the `activeStabilityPolyPoly` PY(z)/PY(0)
mismatch flagged in cycle 690. Strategy directed Steps 1–4 in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`:

1. Redefine `activeStabilityPolyPoly` to use `(toGLM_stabilityMatrixPY m 0).charpoly`.
2. Re-prove `activeStabilityPolyPoly_eq_stabilityPolyPoly_of_bdf` against the new definition.
3. Re-prove `D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf` against the new definition.
4. Add `D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual` (general headline).

## Approach

Started by sanity-checking the strategy mathematically. Verified Step 1
unfolds cleanly and Step 4 follows in one `unfold` + `Polynomial.smul_eq_C_mul`
from cycle 690's `D_mul_toGLM_charpoly_eq_X_pow_mul_PY0_plus_residual`.

Independently verified Steps 2 and 3 with two computations:

* Concrete s = 1 backward Euler (`α = (-1, 1)`, `β = (0, 1)`):
  `D • PY(0).charpoly = (1−z)(X−1) = (1−z)X − (1−z)`, while
  `m.stabilityPolyPoly z = -1 + (1-z) X`. They differ by `1 − D = z`.
* General algebraic expansion via `toGLM_stabilityMatrixPY_charpoly` at
  z = 0:
  `D • PY(0).charpoly − stabilityPolyPoly z = -C(z β_last) · ∑_l C(α(castSucc l)) X^l`
  under BDF — non-zero whenever `z β_last ≠ 0`.

Conclusion: Steps 2 and 3 as stated in the strategy are mathematically
false. Implemented Step 1 + Step 4, replaced the broken BDF lemmas
(old lines 449–475) with a single TRUE bridge using `stabilityPolyPoly`
directly:

```
D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf:
  C D · charpoly = X^s · m.stabilityPolyPoly z   (under BDF)
```

Proof routes through cycle 643's `toGLM_stabilityMatrix_charpoly_of_bdf`
followed by `toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf`
(line 944 of `Stability.lean`) — exactly the chain the strategy
suggested for Step 3, but landing on `stabilityPolyPoly` (true) rather
than `activeStabilityPolyPoly` (false with the new defn).

## Result

**SUCCESS** — Steps 1, 4 landed sorry-free; Steps 2 and 3 replaced
with a corrected TRUE BDF lemma.

* Step 1: `activeStabilityPolyPoly` body changed from `PY(z)` to `PY(0)`,
  docstring updated with the redefinition rationale and a NOTE that
  the BDF→`stabilityPolyPoly` collapse no longer holds directly.
* Step 4: `D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`
  added at line 1316; proof is `rw [cycle 690 lemma]; unfold
  activeStabilityPolyPoly; rw [Polynomial.smul_eq_C_mul]` — matched
  the strategy's "one-`ring` after unfolding" prediction up to a
  `ring` that turned out to be unnecessary (`No goals to be solved`
  after the smul rewrite — the residual term and `C D · PY(0).charpoly`
  agree definitionally after the smul rewrite).
* Replaced lines 449–475 (broken under new defn) with
  `D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`. No
  external callers (grep confirmed), so no ripple breakage.
* Updated cycle 690's docstring NOTE (lines 1274–1282) — the
  outdated "active stability polynomial unfolds to `D • PY(z).charpoly`"
  no longer applies.

`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` and
`lake env lean OpenMath/LMMAsGLM.lean` both return 0.

## Dead ends

None this cycle. The strategy's Step 2/3 are mathematically false; I
did not attempt to land them, instead routing to the corrected
`stabilityPolyPoly`-flavoured BDF lemma.

## Discovery

* `D • PY(0).charpoly ≠ stabilityPolyPoly z` under BDF in general:
  the difference is `-C(z β_last) · ∑_l C(α(castSucc l)) X^l` (the
  residual reduction of cycle 690's general identity under BDF).
* The "natural" BDF specialisation of cycle 692 Step 4 has a
  surviving `rowYQuot · X^s · C(z β_last)` summand (the strategy's
  own warning was correct on this point — it just contradicted the
  Step 3 statement).
* `Polynomial.smul_eq_C_mul` on
  `(1 - z β_last) • (toGLM_stabilityMatrixPY m 0).charpoly` lands the
  RHS of cycle 690's identity definitionally, so Step 4's proof is
  three lines (`rw`, `unfold`, `rw`) with no `ring` at the end.
* Issue file
  `.prover-state/issues/cycle_692_active_stability_polypoly_redefinition_breaks_bdf_bridges.md`
  documents the math in full for cycle 693+.

## Suggested next approach

The §521 program is now in good shape for the iff bridge target
`LMM.toGLM_isAStable_iff`:

1. **Cheap option**: write the iff bridge using
   `D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual` plus
   `charpoly_residual_degree_lt`. The argument is degree counting plus
   evaluation at `ξ ≠ 0` on the unit disk: at any unit-disk root
   `ξ` of `m.toGLM.stabilityMatrix z`, we get
   `0 = D · (m.toGLM.stabilityMatrix z).charpoly.eval ξ
        = ξ^s · activeStabilityPolyPoly.eval ξ − residual.eval ξ`
   with `residual.degree < 2s` and `ξ^s · …` of degree `< 2s + s = 3s`.
   Combined with the cycle 690 identity `D • PY(0).charpoly` ↔ the
   classical scalar polynomial via the corrected bridge in the new
   issue file, the iff falls out.
2. **Optional bookkeeping**: prove the corrected
   `activeStabilityPolyPoly = stabilityPolyPoly − C(z β_last) ·
   (sum)` BDF identity from option (1) of the issue file, if cycle
   693 wants a clean BDF bridge for the new active polynomial.
   Probably 30–50 lines, parallel structure to the existing line
   944 proof in `Stability.lean`.
3. **Avoid**: re-attempting the strategy's Step 2 / Step 3 statements
   verbatim. They are provably false; the issue file has the
   counterexample.

## Files modified

* `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:
  - Lines 431–490 (approx): redefined `activeStabilityPolyPoly`,
    replaced two broken BDF lemmas with one TRUE
    `stabilityPolyPoly`-flavoured BDF headline.
  - Lines 1266–1280 (approx): updated the cycle 690 lemma's docstring
    NOTE.
  - Lines 1308–1330 (approx): added
    `D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`.

## Files added

* `.prover-state/issues/cycle_692_active_stability_polypoly_redefinition_breaks_bdf_bridges.md`
  — counterexample + corrected bridge for cycle 693+.
