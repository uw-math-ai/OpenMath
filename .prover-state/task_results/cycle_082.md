# Cycle 82 Results

## Worked on
- Sorry #2: `tupleSucc_pow_bounded_on_disk_eigenspace` in `DahlquistEquivalence.lean`
- Sorry #3: `uniformly_bounded_tupleSucc_iterates` (investigation only)
- Aristotle job status checks from cycle 81

## Approach

### Sorry #2 (`tupleSucc_pow_bounded_on_disk_eigenspace`)
Proved that on the disk eigenspace (|μ| < 1), T^n is uniformly bounded. The proof uses:

1. **Induction on nilpotency order k** of N = T - μ·1 (where N^k = 0 on the gen eigenspace).
2. **Key identity**: T^{n+1} w = μ(T^n w) + T^n(N w), using commutativity of T and N.
3. **Geometric recurrence bound** (new helper `geom_recurrence_bound`): if a_{n+1} ≤ r·a_n + K with r < 1, then a_n ≤ a_0 + K/(1-r) for all n.
4. **Inductive bound**: C_k = (1 + M/(1-‖μ‖))^k where M = ‖N‖ (operator norm).

Supporting lemmas added:
- `geom_recurrence_bound`: geometric recurrence ⟹ uniform bound
- `comm_tupleSucc_sub_smul`: T and N commute (T^n ∘ N = N ∘ T^n)
- `restrict_pow_coe`: (f.restrict h)^k coerced = f^k coerced

### Sorry #3 (`uniformly_bounded_tupleSucc_iterates`)
Investigated combining per-eigenspace bounds via eigenspace decomposition `⨆ μ V_μ = ⊤`. Would need projection construction from the direct sum or a basis argument. Deferred — too complex for remaining time.

### Aristotle
All 5 job status checks from cycle 81 returned HTTP 500 errors. Aristotle API appears to be down.

## Result
**PARTIAL SUCCESS**
- Sorry #2: CLOSED. Verified clean with `lean_verify` (only standard axioms: propext, Quot.sound, Classical.choice).
- Sorry #3: Still open. Investigation done, approach identified.
- Aristotle: Unavailable (HTTP 500).

DahlquistEquivalence.lean went from 3 sorrys → 1 sorry this cycle.

## Dead ends
- `div_add_eq_add_div` doesn't exist in current Mathlib; used `field_simp; ring` instead
- `Commute.pow_left` had wrong composition order; needed `hc.pow_right n` with explicit `show`
- `LinearMap.pow_apply` doesn't exist; used `pow_succ, Module.End.mul_apply` pattern
- `restrict_pow_coe` induction needed `generalizing v` to get universal IH
- `nlinarith` fails on division terms; worked around with `mul_le_mul_of_nonneg_right` + `mul_div_assoc` + `linarith`
- `one_le_pow_of_one_le_of_le` not found; `one_le_pow₀` works (no `MulLeftMono` needed)
- `lake env lean` fails with "unknown module prefix 'Mathlib'" — PATH issue on cluster. LSP verification works.

## Discovery
- `one_le_pow₀` is the right lemma for `1 ≤ x → 1 ≤ x^n` in current Mathlib
- `isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` gives nilpotency of N on gen eigenspace
- `LinearMap.restrict_coe_apply` is the key for coercion: `↑(f.restrict h x) = f ↑x`
- Operator norm bound: `LinearMap.toContinuousLinearMap` + `ContinuousLinearMap.le_opNorm`

## Suggested next approach
- **Sorry #3** (`uniformly_bounded_tupleSucc_iterates`): Use `Module.End.iSup_maxGenEigenspace_eq_top` to decompose any v into eigenspace components, apply per-eigenspace bounds, sum up. May need:
  - Finite sum of eigenspace projections (from `IsFinitelySemisimple` or explicit basis)
  - Or: argue via `Submodule.iSup_eq_top` + continuity of norm
  - Or: use `LinearMap.trace` / `Matrix.toLin` approach with Jordan normal form
- Aristotle API should be retried next cycle — may be a transient outage.
