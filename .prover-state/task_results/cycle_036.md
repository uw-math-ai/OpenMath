# Cycle 036 Results

## Worked on
`stableRecurrence_of_zeroStable` in `OpenMath/DahlquistEquivalence.lean` — the sorry for
"zero-stability implies stable recurrence" (the converse direction of the algebraic
Dahlquist equivalence).

## Approach
Connected LMM recurrence theory to Mathlib's `LinearRecurrence` infrastructure. Decomposed
the original monolithic sorry into a structured proof with clear sub-lemmas:

1. **`toLinearRecurrence`**: Converts LMM characteristic recurrence to Mathlib's
   `LinearRecurrence ℂ` (order = s, coeffs = -α_j).

2. **`satisfiesRecurrence_iff_isSolution`** (PROVED): Our `SatisfiesRecurrence` is
   equivalent to `LinearRecurrence.IsSolution`. Uses `Fin.sum_univ_castSucc` to decompose
   the sum over Fin (s+1), then algebraic manipulation.

3. **`tupleSucc_iterate_eq_mkSol`** (PROVED): The state vector at time n equals
   `tupleSucc^[n](init)`: `(tupleSucc^[n] init) i = mkSol init (n + i)`.
   Proved by induction on n, generalizing over i. Key insight: tupleSucc shifts the
   first s-1 components and applies the recurrence for the last.

4. **`uniformly_bounded_tupleSucc_iterates`** (SORRY): The spectral bound — under
   zero-stability, `‖tupleSucc^n(v)‖ ≤ M·‖v‖` for all n, v. This is the core
   hard step requiring Jordan normal form or generalized eigenspace decomposition.

5. **`stableRecurrence_of_zeroStable`** (PROVED modulo #4): Combines everything.
   Handles s=0 directly (only element in Fin 1 gives y_n = 0), and for s>0 uses
   the LinearRecurrence infrastructure to reduce to the spectral bound.

## Result
SUCCESS — Reduced the sorry from a vague "needs general solution theory" to a precise,
well-typed spectral bound statement. Proved 3 new lemmas fully. The remaining sorry
(`uniformly_bounded_tupleSucc_iterates`) is a clean mathematical statement about
operator norm bounds under spectral conditions.

Net sorry change: 1 → 1 (same count, but the sorry is now precisely scoped and the
surrounding proof structure is complete).

## Dead ends
- `linarith` doesn't work for ℂ — needed explicit `neg_eq_iff_eq_neg` manipulations.
- `Fin.sum_univ_one` doesn't match `Fin (0 + 1)` under `subst` — needed workaround.
- `neg_mul _ _` caused typeclass resolution issues — replaced with `ring`.

## Discovery
- Mathlib has `LinearRecurrence` in `Mathlib.Algebra.LinearRecurrence` with rich infrastructure:
  `IsSolution`, `mkSol`, `solSpace`, `toInit` (linear equiv), `tupleSucc` (companion map),
  `charPoly`, `geom_sol_iff_root_charPoly`.
- The `tupleSucc` linear map IS the companion matrix action, just expressed as a linear map
  on `Fin s → ℂ` rather than a matrix.
- `solSpace_rank` proves the solution space has dimension s.
- The Mathlib file explicitly notes that closed-form solutions await eigenvalue implementation.

## Suggested next approach
The remaining sorry `uniformly_bounded_tupleSucc_iterates` requires one of:
1. **Jordan normal form** over ℂ (not in Mathlib).
2. **Generalized eigenspace decomposition**: Mathlib has `Module.End.genEigenspace` in
   `Mathlib.LinearAlgebra.Eigenspace.Basic`. Could potentially decompose `tupleSucc` into
   generalized eigenspaces and bound each component.
3. **Cayley-Hamilton** + polynomial analysis: Use `aeval_self_charpoly` to express
   `tupleSucc^n` as a polynomial in `tupleSucc` of degree < s, then bound.
4. **Direct matrix norm bound**: Define companion matrix, relate its charpoly to ρ,
   use Gershgorin or similar.

Option 3 (Cayley-Hamilton) may be most tractable: `tupleSucc^n mod charpoly` gives
`tupleSucc^n = ∑_{k<s} c_{n,k} · tupleSucc^k`. The coefficients c_{n,k} are bounded
under the root condition, giving the uniform bound.

Alternatively, move to new material (Chapter 4: stiff equations) if the spectral bound
proves too costly.
