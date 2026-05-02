# Cycle 644 Results

## Worked on

Re-landing the BDF-conditional §521 PHF charpoly chain (Steps 1–3) in
`OpenMath/LMMAsGLM.lean`. Cycles 642 and 643 both did this work and
were reverted because they committed sorry-headline scaffolds alongside
genuinely-proved helpers. This cycle lands all three lemmas
**sorry-free** and commits nothing else.

## Approach

Inserted three theorems immediately after
`toGLM_stabilityMatrix_eq_V_active_plus_rank_one` (around the old line
1175):

1. `toGLM_stabilityMatrixPHF_apply_of_bdf` — under
   `∀ l : Fin (s+1), l ≠ Fin.last s → m.β l = 0`, the PHF block entry
   reduces to `if (l : ℕ) = (j : ℕ) + 1 then 1 else 0`.
2. `toGLM_stabilityMatrixPHF_blockTriangular_of_bdf` — the BDF PHF
   block is `BlockTriangular id` (Mathlib's "upper triangular"
   convention: `M i j = 0` for `b j < b i`).
3. `toGLM_stabilityMatrixPHF_charpoly_of_bdf` — the BDF PHF block has
   characteristic polynomial `X^s`.

## Result

SUCCESS. All three lemmas closed sorry-free in one pass.
`lake env lean OpenMath/LMMAsGLM.lean` exits 0; `grep -c sorry
OpenMath/LMMAsGLM.lean` is `0`.

### Mathlib API names used

- `Matrix.BlockTriangular` (definition,
  `Mathlib/LinearAlgebra/Matrix/Block.lean:61`).
- `Matrix.charpoly_of_upperTriangular` (the headline,
  `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:199`). Returns
  `M.charpoly = ∏ i, (X - C (M i i))` for `M.BlockTriangular id`.

The strategy speculated that the upper-triangular charpoly lemma might
not exist; it does, with the exact shape needed.

### Hypothesis shape adjustment

Strategy wrote the BDF hypothesis as
`∀ l : Fin s, l ≠ Fin.last s → m.β l = 0`. That does not typecheck —
`Fin.last s : Fin (s+1)` while `l : Fin s`, and `m.β` has signature
`Fin (s+1) → ℝ`. The natural fix is to quantify over `Fin (s+1)`:

```
hbdf : ∀ l : Fin (s+1), l ≠ Fin.last s → m.β l = 0
```

This matches Butcher's BDF presentation and fits cleanly with
`Fin.castSucc` lifts in the proof.

### Step 1 proof shape

```
unfold toGLM_stabilityMatrixPHF
by_cases hj : (j : ℕ) + 1 = s
· rw [if_pos hj]
  -- l : Fin s ⇒ Fin.castSucc l ≠ Fin.last s via (l : ℕ) < s
  have hβ : m.β (Fin.castSucc l) = 0 := hbdf (Fin.castSucc l) hlne
  rw [hβ]; push_cast
  rw [if_neg (by intro hlj; have := l.isLt; omega)]
  ring
· rw [if_neg hj]   -- the closed form is exactly the if-branch already
```

### Step 2 proof shape

```
intro j l hlt
rw [toGLM_stabilityMatrixPHF_apply_of_bdf m z hbdf j l]
rw [if_neg]
intro h
simp [id] at hlt
omega
```

### Step 3 proof shape

```
rw [Matrix.charpoly_of_upperTriangular _
      (toGLM_stabilityMatrixPHF_blockTriangular_of_bdf m z hbdf)]
have hdiag : ∀ j, (X - C (M j j)) = X := by
  intro j
  rw [toGLM_stabilityMatrixPHF_apply_of_bdf m z hbdf j j]
  rw [if_neg (by omega)]; simp
simp [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
```

## Dead ends

None this cycle — every step closed first try after the hypothesis
type fix.

## Discovery

- `Matrix.charpoly_of_upperTriangular` (in `Charpoly/Basic.lean`) is
  the exact shape we needed. No need to fall back to expanding
  `Matrix.det_of_upperTriangular` over `charmatrix` by hand.
- `Matrix.BlockTriangular id` is the right flavour for "lower entries
  vanish in the natural Fin order"; the `intro j l hlt` pattern gives
  `hlt : (l : ℕ) < (j : ℕ)` after `simp [id]`.
- The natural BDF hypothesis must be quantified over `Fin (s+1)` (the
  domain of `m.β`), not `Fin s`. Future statements should use the
  `Fin (s+1)` form.

## Suggested next approach

Cycle 645 candidates, ranked:

1. **BDF stability defect bridge.** Combine
   `toGLM_stabilityMatrixPHF_charpoly_of_bdf` (this cycle) with the
   existing block decomposition
   `toGLM_stabilityMatrix_eq_fromBlocks` and the rank-one form
   `toGLM_stabilityMatrix_eq_V_active_plus_rank_one` (cycle 641) to
   land a BDF-specialised statement of the LMM-as-GLM stability
   matrix charpoly factorisation. Specifically, the charpoly of the
   full `stabilityMatrix z` should factor as
   `X^s * (BDF stability polynomial)` under BDF — a cycle 633-style
   bridge for the BDF case.

2. **Generalise Step 3 beyond BDF.** The shift-row branch of the PHF
   block is *always* the strict-shift companion (independent of
   `β`); only the last row picks up the resolvent term. A weaker
   hypothesis like "`m.β (Fin.castSucc l) = 0` for `(l : ℕ) =
   s - 1`" might suffice to keep the diagonal zero without forcing
   all but the last `β` to vanish. Worth exploring before committing
   to a name.

Do **NOT** recommend cycle 645 attempt the unconditional
`LMM.toGLM_isAStable_iff` headline — the general charpoly
factorisation still requires Mathlib infrastructure that does not
exist (see
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md`).

## Sorry count

`grep -c sorry OpenMath/LMMAsGLM.lean` → `0`. Project-wide invariant
preserved.
