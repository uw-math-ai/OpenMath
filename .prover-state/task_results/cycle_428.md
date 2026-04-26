# Cycle 428 Results

## Worked on
Pilot refactor: rewire `LMM.ab2Vec_global_error_bound` in
`OpenMath/LMMAB2Convergence.lean` so its proof goes through the generic
`LMM.ab_global_error_bound_generic_vec` (cycle 427) instead of the inline
`lmm_error_bound_from_local_truncation` invocation.

Public statement of `ab2Vec_global_error_bound` is unchanged.
`OpenMath/LMMABGenericConvergence.lean` is untouched.

## Approach
1. Sorry-first refactor:
   - Added `import OpenMath.LMMABGenericConvergence`.
   - Introduced AB2 coefficient bridge `ab2GenericCoeff : Fin 2 → ℝ`
     with `α 0 = -1/2`, `α 1 = 3/2`, plus `@[simp]` evaluation lemmas.
   - Introduced three bridge lemmas (with `sorry` initially):
     - `abLip_ab2GenericCoeff : abLip 2 ab2GenericCoeff L = 2 * L`
     - `ab2IterVec_eq_abIterVec` : AB2 iteration equals generic AB iteration
       at `s = 2`, `α = ab2GenericCoeff`, starting samples `![y₀, y₁]`.
     - `ab2VecResidual_eq_abResidualVec` : AB2 residual equals generic
       residual at base point `t₀ + n·h`.
   - Rewrote `ab2Vec_global_error_bound` body around
     `ab_global_error_bound_generic_vec`, with `sorry` on the window-start
     bound `hstart` until the bridge was wired up. Other sub-pieces
     (Lipschitz scalar, residual cast bound, window-max ≥ pointwise error,
     `((N:ℝ)+1)*h ≤ T → (N:ℝ)*h ≤ T`) were proved inline.
2. Verified the sorry-first scaffold compiled. Discovered stale `.olean` for
   `LMMABGenericConvergence` after generic file was rebuilt; fixed by
   `lake build OpenMath.LMMABGenericConvergence` once.
3. Aristotle batch: submitted four jobs at 02:28 UTC for the four open
   sorries (one per bridge lemma + the window-start bound). Sleep + manual
   work in parallel.
4. Manual closures (all four sorries closed by hand before Aristotle
   reached >10% completion):
   - `abLip_ab2GenericCoeff`: `Fin.sum_univ_two`, fold absolute values
     for `|−1/2|` and `|3/2|`, then `ring`.
   - `ab2VecResidual_eq_abResidualVec`: `unfold ab2VecResidual abResidualVec`,
     `Fin.sum_univ_two`, then four time-coordinate equalities (`eA`–`eD`)
     to reshape `t₀ + n·h + 2h`, `+ h`, `+ ((n + ↑j) : ℕ)·h`. Used
     `Fin.val_zero` / `Fin.val_one` (via `simp`) to reduce Fin coercions.
     Closed the algebraic step with `neg_smul` + `abel`.
   - `hstart` (window start bound in `ab2Vec_global_error_bound`):
     `Finset.sup'_le` over `Fin 2`, `fin_cases j`, evaluated
     `abIterVec 2 α h f t₀ ![y₀, y₁] {0,1}` directly via the if-branch
     (`unfold abIterVec; simp` collapses to `![y₀, y₁] ⟨n, _⟩` and then
     `Matrix.cons_val_*`), then collapsed time arguments to `t₀` and
     `t₀ + h` to apply `he0_bd` / `he1_bd`.
   - `ab2IterVec_eq_abIterVec`: `Nat.strong_induction_on`, `match` on `n`:
     - `n = 0, 1`: `ab2IterVec_zero/one` + `unfold abIterVec; simp`.
     - `n = k + 2`: `ab2IterVec_succ_succ` on LHS, `abIterVec_step (s := 2)`
       on RHS, `Fin.sum_univ_two`, IH at `k` and `k+1`, cast
       `((k+1 : ℕ) : ℝ) = (k : ℝ) + 1`, then `neg_smul; abel`.
5. Cancelled all four Aristotle projects (still ≤8% complete) since the
   manual proofs were already in place and dwarfed the remaining wait.

## Result
SUCCESS — `OpenMath/LMMAB2Convergence.lean` now compiles cleanly with no
sorries; full `lake build` succeeds. The body of
`ab2Vec_global_error_bound` is now a thin specialisation of
`ab_global_error_bound_generic_vec`, with the AB2-specific shape carried
entirely by the three bridge lemmas. The constants in the theorem
statement (`Real.exp (2 * L * T)`, `K = T * Real.exp (2 * L * T) * C`)
are unchanged, since `abLip 2 ab2GenericCoeff L = 2 * L` matches the
inline-derived constant exactly.

## Dead ends
- `push_cast; ring` did not reduce `((0 : Fin 2) : ℕ)` / `((1 : Fin 2) : ℕ)`
  inside cast goals; had to explicitly add `Fin.val_zero`/`Fin.val_one`
  via `simp`. The Lean linter then flagged `Fin.val_one` as "unused" but
  removing it broke a downstream `rw` of `((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1`
  — the simp arg is load-bearing on the AB2 step case despite the linter
  hint. Left it in place.
- Aristotle was a sunk cost on this task: the four sorries were all
  short, mechanical, and within reach of hand-proof in less time than
  Aristotle's typical 20–40 min ceiling. Manual proofs were merged at
  ~10 minutes from submission.

## Discovery
- The generic vector AB scaffold from cycle 427 is sufficient for AB2
  with a tiny bridge layer (≤80 lines). Three bridge lemmas plus a
  coefficient definition are enough; no new helpers in the generic file
  were required. This is a positive signal for repeating the same
  refactor for AB3, AB4, AB5, AB6 vector chains in subsequent cycles.
- The window-max ≥ pointwise inequality (`abErrVec ... N ≤ abErrWindowVec
  ... N`) is reusable across all `s`-step bridges; same trick (sup over
  `j = 0`) generalises with `Fin.val_zero` and the rest of the lemma
  body unchanged. Worth extracting as a generic helper if more chains
  are bridged.

## Suggested next approach
- Replicate the same pilot refactor for AB3 (`OpenMath/LMMAB3VecChain.lean`
  or wherever the AB3 vector chain lives) using `s = 3`,
  `α : Fin 3 → ℝ = ![5/12, -16/12, 23/12]`. The Lipschitz bridge becomes
  `abLip 3 α L = (5+16+23)/12 · L = (44/12) L = (11/3) L`; check that
  this matches whatever constant the existing AB3 file uses.
- Consider hoisting `abErrVec_le_abErrWindowVec_at_top` as a one-line
  lemma in `LMMABGenericConvergence.lean` (window inequality at index `N`
  via `j = 0`) to avoid repeating the `Finset.le_sup'` step in every
  bridge.
- Optionally extract the coefficient-bridge boilerplate
  (`α : Fin s → ℝ`, `abLip_α`, `α_eval` simp lemmas) into a small helper
  pattern so AB3+ files keep the bridge layer minimal.
