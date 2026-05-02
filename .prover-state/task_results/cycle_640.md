# Cycle 640 Results

## Worked on

Strategy target: §521 — fully evaluate the LMM-as-GLM stability matrix
entries. Eight new theorems landed in `OpenMath/LMMAsGLM.lean` between the
cycle 639 row-projection block and the existing `toGLM_stageMap_eq`.

Concretely:

1. `toGLM_Aℂ_apply` (Step 1) — `m.toGLM.Aℂ 0 0 = ((m.β (Fin.last s) : ℝ) : ℂ)`.
2. `toGLM_resolvent_apply` (Step 2) — closed-form 1×1 resolvent
   `((1 - z • m.toGLM.Aℂ)⁻¹) 0 0 = 1 / (1 - z * β(last))`.
3. `toGLM_Uℂ_castAdd` and `toGLM_Uℂ_natAdd` (Step 3) — complex-lifted `U`
   row reads `((-α(castSucc k) : ℝ) : ℂ)` on past-`y` and
   `((β(castSucc k) : ℝ) : ℂ)` on past-`h*f`.
4. The four headline §521 closed scalar entries (Step 4):
   - `toGLM_stabilityMatrix_castAdd_last_castAdd_apply`
   - `toGLM_stabilityMatrix_castAdd_last_natAdd_apply`
   - `toGLM_stabilityMatrix_natAdd_last_castAdd_apply`
   - `toGLM_stabilityMatrix_natAdd_last_natAdd_apply`

## Approach

Sorry-first scaffold first: dropped all eight statements with `sorry` after
the cycle 639 block, verified `lake env lean OpenMath/LMMAsGLM.lean`
produced exactly seven `sorry` warnings (Step 1 closed inline because the
recipe collapses to `show … = _; rw [toGLM_A_apply]`).

Then closed each step in the planned order:

- **Step 1.** `show ((m.toGLM.A 0 0 : ℝ) : ℂ) = _; rw [toGLM_A_apply]`.
- **Step 2.** Built the literal `!![1 - z * β(last)]` via `ext`+`fin_cases`,
  rewrote `m.toGLM.Aℂ 0 0` through Step 1 inside the `show`, then
  `rw [hsub, Matrix.inv_def]; simp [Matrix.adjugate_fin_one]` — exactly the
  cycle 627 / 630 / 631 / 632 backwardEuler / trapezoidalRule / bdf2 recipe
  abstracted to general `s`.
- **Step 3.** Cycle 638 recipe verbatim:
  `show ((m.toGLM.U 0 … : ℝ) : ℂ) = _`, then `simp only [toGLM]`, then a
  `Fin.cast (Nat.two_mul s) (Fin.cast (Nat.two_mul s).symm (...)) = ...`
  rewrite via `ext; simp`, then `Fin.addCases_left` or
  `Fin.addCases_right`.
- **Step 4.** Each is a one-line `rw` chain on cycle 639 row projection +
  `toGLM_resolvent_apply` + the matching `Uℂ` simp lemma. The `castAdd_last_*`
  variants additionally need a local `hV : Vℂ … = …` projection (via
  `show ((m.toGLM.V … : ℝ) : ℂ) = _; rw [toGLM_V_castAdd_last_*_apply m j hj]`).
  The `natAdd_last_*` variants don't need the `hV` step because the cycle 620
  `toGLM_V_natAdd_last_apply` is already absorbed into the cycle 639 row
  projection.

## Result

SUCCESS — all eight theorems land sorry-free. `lake env lean
OpenMath/LMMAsGLM.lean` is silent (no warnings). `lake env lean
OpenMath/RKAsGLM.lean` and `lake env lean OpenMath/GeneralLinearMethod.lean`
also remain green; the new lemmas are additive and do not disturb the three
concrete §521 LMM A-stability theorems
(`backwardEuler_toGLM_isAStable`, `trapezoidalRule_toGLM_isAStable`,
`bdf2_toGLM_isAStable`).

## Dead ends

None of significance this cycle. The strategy's recipe transferred essentially
verbatim from cycles 627 / 638 / 639. One minor adjustment: in Step 2, the
literal-matrix construction needs `(1 : ℂ) - z * m.toGLM.Aℂ 0 0` (not
`(... : ℝ) : ℂ`) inside the `show` so the subsequent
`rw [toGLM_Aℂ_apply]; simp` fires cleanly.

The `hV` rewrite in the `castAdd_last_*` Step 4 lemmas closes by `rw`
alone (no trailing `simp` / `push_cast`); `Real.toComplex` of `-α` and
`β` projections matches the goal modulo definitional equality after the
simp lemma fires.

## Discovery

The four implicit-row entries split into two distinct algebraic shapes:

- **Past-`y` last row** (`castAdd_last_*`): a `Vℂ` term *plus* the
  resolvent contribution. Both addend terms share the column factor
  (`-α(castSucc l)` for past-`y`, `β(castSucc l)` for past-`h*f`),
  and the resolvent enters with a `z * β(last) * resolvent` prefactor.
- **Past-`h*f` last row** (`natAdd_last_*`): no `Vℂ` contribution
  (cycle 620 zeroes the row), so the entry is a pure
  `z * resolvent * column-factor`. Strictly simpler — these proofs are
  three-line `rw` chains.

This is the cleanest possible shape for the cycle 641 `Matrix.fromBlocks`
charpoly factorisation: when one factors out `1 / (1 - z * β(last))`, the
implicit-row block becomes
`(I - resolvent) [V_active | 0] + z * resolvent [α | β]` — i.e. a rank-1
correction over the cycle 619-era `V_active` block.

The cycle-619 simp lemmas for `V` are already at the right grain; the
matching `Uℂ` lemmas (Step 3) are the missing piece this cycle plugged.

## Suggested next approach

Cycle 641 should attempt the `Matrix.fromBlocks` factorisation of
`m.toGLM.stabilityMatrix z`:

- Past-`y` block: shift rows (cycle 639 `castAdd_shift`) plus the
  `castAdd_last` row from Step 4 above.
- Past-`h*f` block: shift rows (cycle 639 `natAdd_shift`) plus the
  `natAdd_last` row from Step 4 above.
- Use `Matrix.charpoly_fromBlocks_zero₂₁` (or symmetric variant) once the
  block-triangular structure is exposed. The denominator
  `1 - z * β(last)` lifts out of every row uniformly, which suggests
  factoring as `(1 - z β(last))^{-(s)} · (cycle-619 V_active contribution
  + z * rank-1 correction)`.

If `Matrix.charpoly_fromBlocks_*` is missing for the relevant block
structure, decompose: prove the determinant identity
`det(M - λ I) = denom⁻¹ * det(M̃ - λ̃ I)` directly.

The headline cycle 641 deliverable would be `LMM.toGLM_isAStable_iff`
(forward direction first via the rescaled charpoly; reverse direction via
the cycle-595-era Möbius-image bound on the unit disc).
