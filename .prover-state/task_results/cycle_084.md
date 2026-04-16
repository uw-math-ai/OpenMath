# Cycle 084 Results

## Worked on
Removed both `set_option maxHeartbeats` overrides from `OpenMath/SpectralBound.lean`
(violations of the CLAUDE.md 200000 cap) by decomposing the two offending
Aristotle-generated proofs into helper lemmas.

Violations fixed:
- line 70: `set_option maxHeartbeats 800000 in` above `pow_apply_eq_sum_of_genEigenspace`
- line 201: `set_option maxHeartbeats 1600000 in` above `uniformly_bounded_iterates_of_spectral_bound`

## Approach
### Phase 1 — diagnose
Removed both `set_option` lines and ran `lake env lean OpenMath/SpectralBound.lean`.
Timeouts localized to three places:
1. `pow_apply_eq_sum_of_genEigenspace` induction step (line 92): the final
   `simp_all +decide [...]` with `h_expand_step` in context.
2. `uniformly_bounded_iterates_of_spectral_bound` inner `have h_bound_v` (line 236
   elaboration and lines 265/269/273): the whole per-μ case analysis.

### Phase 2 — decompose `pow_apply_eq_sum_of_genEigenspace`
Extracted the two `have h_expand_step` blocks into standalone lemmas above the
main theorem:

- `T_apply_binom_sum` : pure algebra — applying `T` to the binomial expansion
  gives two shifted sums.
- `pascal_recombination_genEigenspace` : pure algebra — Pascal recombination of
  the two shifted sums into `Finset.range (k + 1)` plus a boundary term.

The induction step of `pow_apply_eq_sum_of_genEigenspace` is now three lines
(`have := T_apply_binom_sum …`, `have := pascal_recombination_genEigenspace …`,
two `simp_all +decide` calls). Compiles comfortably under 200000 heartbeats.

### Phase 3 — decompose `uniformly_bounded_iterates_of_spectral_bound`
Extracted the entire `h_bound_v` block into a standalone lemma
`bound_on_maxGenEigenspace_component`, which takes `T`, `h_norm`, `h_simple`,
`μ`, `w`, `hw : w ∈ T.maxGenEigenspace μ` and returns
`∃ C, 0 ≤ C ∧ ∀ n, ‖T^n w‖ ≤ C * ‖w‖`.

**Rewrote the helper with clean mathlib-style structure** (the original
Aristotle proof relied on `simp_all +decide [Module.End.HasUnifEigenvector]`
repeatedly rewriting the input hypothesis `hw`, which broke once the lemma was
extracted because the rewrite chain was different). The clean proof:

1. Destructure via `Module.End.mem_maxGenEigenspace` to get explicit `k` with
   `((T - μ • 1)^k) w = 0`.
2. Case `μ` is an eigenvalue, `‖μ‖ = 1`: use `h_simple` to land in the
   eigenspace, then induct on `n` to show `T^n w = μ^n • w`; since `‖μ‖ = 1`
   the norm is preserved.
3. Case `μ` is an eigenvalue, `‖μ‖ < 1`: direct application of
   `norm_pow_le_on_maxGenEigenspace`.
4. Case `μ` is not an eigenvalue: `eigenspace μ = ⊥` hence `(T - μ • 1)` is
   injective, so `(T - μ • 1)^k` is injective (via `Module.End.coe_pow` and
   `Function.Injective.iterate`), so `w = 0`; bound is `0`.

Main theorem's `h_bound_v` then reduces to:
```lean
fun μ hμ => bound_on_maxGenEigenspace_component T h_norm h_simple μ (v μ) (hv₂ μ hμ)
```
and the subsequent combination step is a simple `calc` + `Finset.sum_le_sum`.

## Result
SUCCESS.

- `lake env lean OpenMath/SpectralBound.lean` passes with no errors and no
  heartbeat warnings.
- `grep "set_option maxHeartbeats" OpenMath/SpectralBound.lean` returns nothing.
- `lake build OpenMath.SpectralBound OpenMath.DahlquistEquivalence
  OpenMath.MultistepMethods` completes successfully.
- Sorry count unchanged: 2, both in `MultistepMethods.lean` (lines 1241, 1258,
  the Dahlquist barrier theorems that are off-limits this cycle).
- Issue file `.prover-state/issues/spectral_bound_heartbeat_decomposition.md`
  deleted.

## Dead ends
The direct "paste the original Aristotle proof into a lemma" approach failed
because `simp_all +decide [Module.End.HasUnifEigenvector]` had been rewriting
the outer-scope `hv₂ μ hμ` at a particular call site, but when the hypothesis
became a locally-bound `hw : w ∈ T.maxGenEigenspace μ` inside the extracted
lemma, `simp_all` rewrote `hw` into `T w = μ • w` (via the `‖μ‖ = 1` branch
rewriting), which then didn't match `(Module.End.mem_maxGenEigenspace ...).mpr`.
Rewriting the extracted lemma in direct style (no `simp_all`-as-rewriter tricks)
removed that fragility.

## Discovery
- `Module.End.mem_maxGenEigenspace T μ w : w ∈ maxGenEigenspace μ ↔ ∃ k, ((T - μ • 1)^k) w = 0`
  is the clean way to destructure maxGenEigenspace membership into an explicit
  `k : ℕ`.
- `Module.End.coe_pow : ⇑(f ^ n) = f^[n]` lets you reduce power-injectivity of
  a linear endomorphism to `Function.Injective.iterate`.
- `Module.End.eigenspace_def : eigenspace μ = LinearMap.ker (f - μ • 1)` — the
  definitional unfolding is exposed by a lemma, not a `rfl`.
- Aristotle-generated proofs that rely on `simp_all` rewriting outer-scope
  hypotheses are fragile to extraction. When decomposing, favor explicit
  `obtain`/`rw` with specific lemmas rather than blanket `simp_all`.

## Suggested next approach
Now that the heartbeat cap is honored across the project, cycle 85 can return
to the two Dahlquist barrier sorrys in `MultistepMethods.lean` (lines 1241,
1258) with Aristotle-only passes, or explore other unfinished textbook content
per `plan.md`. Consider running `lake build` in CI to catch heartbeat
regressions automatically.
