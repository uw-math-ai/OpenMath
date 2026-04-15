# Cycle 78 Results

## Worked on
Primary: `uniformly_bounded_tupleSucc_iterates` in `DahlquistEquivalence.lean` (blocked since cycle 35).
Specifically: the three Phase 1 foundation sub-lemmas plus Phase 2 decomposition skeleton.

## Approach
Followed the strategy exactly: prove 3 sub-lemmas that connect `LinearRecurrence.tupleSucc` to `LMM.rhoC`, then use them to set up the main theorem's proof structure.

### Sub-lemma 1: `aeval_tupleSucc_charPoly_eq_zero`
- **Strategy**: `LinearMap.ext` + `funext`, expand `aeval` on `charPoly`, convert `T^k` to iterates via `Module.End.coe_pow`, use `tupleSucc_iterate_eq_mkSol` to get `mkSol` form, then apply `is_sol_mkSol`.
- **Key difficulty**: Lean wouldn't unfold `(T^k) v j` through `Pi.sub_apply`/`Finset.sum_apply` until we introduced an intermediate `conv` lemma converting `((E.tupleSucc ^ k) v) j` to `E.mkSol v (k + ↑j)`.
- **Result**: SUCCESS

### Sub-lemma 2: `charPoly_eval_eq_rhoC`
- **Strategy**: Unfold both sides, use `Fin.sum_univ_castSucc` to split off leading term, apply `m.normalized` (α_s = 1), then `Finset.sum_neg_distrib` + `sub_neg_eq_add` + `add_comm`.
- **Key difficulty**: `abel` couldn't handle `-1 • ∑ x, -1 • (...)` normalization. Explicit rewrites worked.
- **Result**: SUCCESS

### Sub-lemma 3: `tupleSucc_eigenvalue_is_rhoC_root`
- **Strategy**: Get eigenvector from `hμ.exists_hasEigenvector`, apply `Module.End.aeval_apply_of_hasEigenvector`, combine with sub-lemma 1 to get `charPoly.eval μ • v = 0`, resolve with `v ≠ 0`, then rewrite via sub-lemma 2.
- **Result**: SUCCESS

### Phase 2: Main theorem decomposition
- Handled `s = 0` case (Subsingleton argument — needed explicit `Subsingleton` instance since Lean couldn't unfold `toLinearRecurrence.order` to `0` automatically).
- For `s > 0`: set up eigenvalue bound (`h_eigbound`), minpoly divisibility (`h_mp_dvd`), and generalized eigenspace decomposition (`h_decomp`). Left final sorry for the spectral bound argument.
- Submitted main theorem to Aristotle (project 086b0ae4, status: IN_PROGRESS at 12% when last checked).

## Result
**PARTIAL SUCCESS** — All 3 mandatory sub-lemmas proved and compiled. Main theorem sorry reduced from monolithic to well-structured with s=0 case closed and s>0 case having all key ingredients set up.

## Dead ends
- `ext v j` on `LinearMap` goals produces `LinearMap.single` terms that are hard to work with — use `LinearMap.ext (fun v => funext (fun j => ?_))` instead.
- `abel` fails on double-negation inside sums (`-1 • ∑ -1 • x`). Use explicit `Finset.sum_neg_distrib`.
- `omega` fails on `↑j + ↑i = ↑i + ↑j` with Fin.val coercions. Use `simp_rw [Nat.add_comm]`.
- The main theorem's spectral bound (s>0 case) requires proving that a linear operator with spectral radius ≤ 1 and semisimple unit eigenvalues has uniformly bounded powers. Mathlib has the Gelfand formula (`spectrum.gelfand_formula`) but NOT the power-boundedness result for semisimple unit eigenvalues. This needs either Jordan normal form or direct generalized eigenspace arguments.

## Discovery
- `Module.End.coe_pow` is the key bridge: `⇑(f ^ n) = (⇑f)^[n]` converts algebraic powers to functional iterates.
- `Module.End.aeval_apply_of_hasEigenvector` works cleanly for connecting polynomial evaluation to eigenvector action.
- `Module.End.iSup_maxGenEigenspace_eq_top` gives the generalized eigenspace decomposition over algebraically closed fields — this is the right starting point for Phase 2.
- After `subst` on `s = 0`, Lean doesn't automatically see `Fin m.toLinearRecurrence.order → ℂ` as `Subsingleton` — need to `simp only [toLinearRecurrence]` first to unfold `order` to `0`, then `infer_instance`.

## Suggested next approach
Phase 2 completion needs:
1. **Generalized eigenspace projection**: Show each `v` decomposes into generalized eigenvectors.
2. **Unit eigenvalue bound**: On `maxGenEigenspace μ` with `‖μ‖ = 1`, show the nilpotent part is zero (using `rootMultiplicity ≤ 1` from zero-stability + `minpoly ∣ charPoly`), so `T^n` acts as `μ^n · I`, giving `‖T^n v_μ‖ = ‖v_μ‖`.
3. **Interior eigenvalue bound**: On `maxGenEigenspace μ` with `‖μ‖ < 1`, use binomial formula on `(μI + N)^n` with nilpotent `N` to show `‖T^n v_μ‖ → 0` (polynomial × geometric decay).
4. **Combine**: Triangle inequality over the finite eigenspace decomposition.

Consider extracting step 2-3 as standalone lemmas and submitting to Aristotle. The key missing Mathlib infrastructure is connecting `rootMultiplicity` in `minpoly` to the nilpotency order of `T - μI` on generalized eigenspaces.

Check Aristotle project 086b0ae4 for possible progress on the full theorem.
