# Cycle 120 Results

## Worked on
- **Theorem 357D**: BN-stability implies AN-stability (`OpenMath/BNImpliesAN.lean`)
- Priority 2: Updated `lean_status.json` and `plan.md`
- Priority 4: Added GL2 order-star corollary

## Approach

### Theorem 357D (Priority 1)
The file `OpenMath/BNImpliesAN.lean` had a complete proof structure with 3 sorry's:
1. `inner_mul_self_re` (line 60): Real inner product identity `⟨g·d, d⟩_ℝ = Re(g)·‖d‖²`
2. `resolvedStages_eq` (line 89): Implicit stage equation for resolved stages
3. `stabilityFnDiag_eq_output` (line 97): Stability function equals RK output sum

All three were closed manually using algebraic manipulations:
- Sorry 1: `simp [Complex.inner, Complex.sq_norm, Complex.normSq_apply]; ring`
- Sorry 2: Extract the i-th component from `M * M⁻¹ * 1 = 1`, distribute sums, use `sub_eq_iff_eq_add`
- Sorry 3: Unfold definitions, swap ite condition with `@eq_comm`, simplify with `Finset.sum_comm`

The main theorem `bnStable_implies_anStable` was already proved assuming these lemmas. The proof constructs a dissipative field on ℂ (as a real inner product space) from the AN-stability test data, applies BN-stability with E = ℂ, and translates back.

### Status updates (Priority 2)
- Marked `thm:352C` and `thm:352D` as `done` in `lean_status.json`
- Marked `thm:357D` as `done` in `lean_status.json`
- Updated `plan.md`: marked 352C/352D completed, added 357D entry

### Order-star corollary (Priority 4)
- Added `gl2_imagAxis_not_orderStarPlus` to `OpenMath/OrderStars.lean` — one-liner using `aStable_imagAxis_not_orderStarPlus` and `gl2_aStable`

## Result
**SUCCESS** — All 3 sorry's in `OpenMath/BNImpliesAN.lean` closed. The full stability equivalence chain is now formalized:
- AN-stable ⟹ algebraically stable (Theorem 356C, `ANStability.lean`)
- Algebraically stable ⟹ BN-stable (Theorem 357C, `BNStability.lean`)
- BN-stable ⟹ AN-stable (Theorem 357D, `BNImpliesAN.lean`) [for irreducible non-confluent methods]

## Dead ends
None — all sorry's were closed on first approach.

## Discovery
- The real inner product on ℂ unfolds via `Complex.inner` and the norm via `Complex.sq_norm`/`Complex.normSq_apply` — these are the key simp lemmas.
- When dealing with `if a = x then ...` in Finset sums, use `@eq_comm _ a` to swap the condition to match `Finset.sum_ite_eq` / `Finset.sum_ite_eq'`.
- Matrix inverse equations `M * M⁻¹ = 1` can be extracted component-wise via `congr_fun` on `mulVec` form.

## Suggested next approach
- Priority 3 (Theorem 343A: reflected methods) is the next textbook-aligned target
- The full equivalence chain (AN ⟺ algebraic ⟺ BN for irreducible non-confluent methods) is complete
- Consider formalizing more order-star corollaries (GL3, RadauIIA3) in separate files that import the respective A-stability results
