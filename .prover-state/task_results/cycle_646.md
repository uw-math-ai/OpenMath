# Cycle 646 Results

## Worked on

§521 PY-block entry simplifications in `OpenMath/LMMAsGLM.lean`. Added two
small entry-simp lemmas to support the next-cycle charpoly computation:

- `toGLM_stabilityMatrixPY_apply_shift` — non-final rows of the PY block
  are the pure shift indicator `if (l : ℕ) = (j : ℕ) + 1 then 1 else 0`.
- `toGLM_stabilityMatrixPY_apply_last_of_bdf` — the final row entry
  collapses to `(-α l) / (1 - z · β_s)` whenever the resolvent
  denominator is non-zero.

Both lemmas land immediately after `toGLM_stabilityMatrix_eq_fromBlocks`
and before the rank-one decomposition / BDF-specific `PYHF`/`PHF`
results, exactly as the strategy directed.

## Approach

1. Read `LMMAsGLM.lean` lines 940–1230 to confirm placement and the
   existing `toGLM_stabilityMatrixPY` definition shape.
2. Confirmed the file builds clean (`lake env lean OpenMath/LMMAsGLM.lean`
   exit 0).
3. Stated `toGLM_stabilityMatrixPY_apply_shift` with body
   `unfold; rw [if_neg hj]` — closed immediately, no sorry needed.
4. Stated `toGLM_stabilityMatrixPY_apply_last_of_bdf` with body
   `unfold; rw [if_pos hj]; field_simp`. The first build attempt left a
   pure ring obligation
   `α · (1 - z·β + z·β) = α`; closed with `ring`.
5. Re-built the file, confirmed exit 0, sorry count 0, line count 2477
   (well under the 3000 cap).

## Result

SUCCESS. Both lemmas land sorry-free, file rebuilds clean, no other
files touched.

## Dead ends

None this cycle. The proofs are essentially direct
`unfold + if_neg/if_pos + field_simp + ring`, exactly as the strategy
predicted. The only iteration was discovering that `field_simp` alone
does not close the last-row simplification — it normalises the fraction
but leaves the residual identity `α(1 - z·β + z·β) = α` which needs a
final `ring`.

## Discovery

- `field_simp` on a goal of the shape
  `a + z·β·(1/(1 − z·β))·a = a/(1 − z·β)` (with `1 − z·β ≠ 0` in scope
  via `hz`) clears the denominator using the local non-zero hypothesis
  even without an explicit `[hz]` argument; the residual is a pure ring
  identity, not a fresh denominator.
- The BDF hypothesis `hbdf` is **not** required by the last-row
  simplification — the PY-block last row in the definition does not
  branch on `m.β` for `l < s`. Naming retained `_of_bdf` only because
  the next-cycle charpoly proof will consume the lemma inside the BDF
  branch; this is consistent with the strategy's note that the lemma
  is reusable in the non-BDF setting.

## Suggested next approach

Compute `(toGLM_stabilityMatrixPY m z).charpoly` under the BDF
hypothesis using the two new entry simplifications, relating it to
`m.stabilityPoly` (defined at `OpenMath/MultistepMethods.lean:340`).

Concretely the PY block, post-simplification, is the companion-matrix
shape

```
[ 0   1   0   …   0 ]
[ 0   0   1   …   0 ]
[ …                 ]
[ 0   0   0   …   1 ]
[ -α₀/D  -α₁/D  …  -α_{s-1}/D ]
```

where `D = 1 − z · β_s`. Two natural Mathlib bridges to try first:

1. `Matrix.charpoly_companion` / `Polynomial.LinearRecurrence.charPoly`
   — search for an existing companion-matrix charpoly lemma. If a
   directly applicable form exists, the bridge is one rewrite.
2. If neither lands cleanly, expand `det (X • 1 − PYblock)` by induction
   on `s` along the shift columns (each non-final row contributes the
   single non-zero entry `−1` at column `j+1`, giving a Laplace
   expansion that recovers the standard companion-matrix charpoly
   formula `X^s + Σ (αᵢ/D) X^i` after sign tracking).

Either path should remain a single isolated cycle's worth of work; do
**not** combine it with `LMM.toGLM_isAStable_iff` in the same edit.

Aristotle remains in 429 territory (cycles 520, 521, 539, 543, 548–552,
558, 559, 565, 575–584, 588, 590, 645) so the next cycle should plan to
close the charpoly identity manually.
