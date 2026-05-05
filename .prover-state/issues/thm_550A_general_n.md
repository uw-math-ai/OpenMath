# Issue: General-`n` proof of `thm:550A` (Doubly companion matrix factorization)

## Blocker

`OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization`
is stated with `sorry` for general `n ∈ ℕ`. The `n = 1` specialisation
(`doublyCompanionMatrix_det_factorization_n_one`) is closed axiom-clean
in cycle 138 as a genuine witness, but the general-`n` proof is
multi-cycle infrastructure work.

## Context

**File**: `OpenMath/Chapter5/Section550.lean:111` (sorry at line ~121).
**Theorem (Butcher §550, p. 457)**: for the doubly companion matrix
`X = doublyCompanionMatrix α β`,
```
det(I − z X) = α(z) · β(z) + O(z^{n+1})    as z → 0 in ℂ
```
where `α(z) = 1 + Σᵢ α_i z^{i+1}` and similarly `β(z)`.

**Textbook proof outline** (eigenvalue density):
1. WLOG assume X has distinct non-zero eigenvalues (the choices of α
   that yield such X form a *dense* subset; the LHS and RHS are
   continuous in α, β; conclude on the dense set and extend).
2. Let λ be an eigenvalue. Define
   `v_k = λ^k + β₁ λ^{k-1} + … + βₖ`, k = 0..n. The vector
   `V = (v_{n-1}, …, v_0)` is the eigenvector for λ (verify by
   comparing components 2..n of `Xv = λv`).
3. The first-component equation
   `λ v_n + α₁ v_{n-1} + … + αₙ = 0`
   reduces (after substituting `λ = z⁻¹` and clearing the `λ^n`
   denominator) to
   `det(I − zX) = α(z)·β(z) + O(z^{n+1})`.

## What was tried

* Cycle 138 closed `n = 1` directly via `Matrix.det_fin_one` (~30 LOC).
* Two Aristotle jobs submitted in cycle 138:
  * Project `7062c2a2-4a8b-4fae-b694-9355e06427a9` — full general-n.
  * Project `70f26d67-b37e-4eda-b946-64c9f4616612` — focused on the
    `n = 2` specialisation.
  Their results will be processed in cycle 139.

## Why deferral

The eigenvalue-density argument requires several Mathlib pieces in
concert:
* Continuity of charpoly coefficients in matrix entries
  (`Polynomial.coeff_charpoly` together with continuity of polynomial
  multiplication and `Matrix.charpoly` in the entry-by-entry topology).
* Density of "distinct non-zero eigenvalues" in coefficient space
  (the discriminant of the characteristic polynomial is a non-trivial
  polynomial in the matrix entries, hence its zero set is closed and
  nowhere dense in any standard topology on ℂⁿ²).
* Identity-of-analytic-functions-style extension by continuity (or, in
  this case, just identity of polynomials in coefficient space, since
  the charpoly coefficients are *polynomial* in the entries).

Each of these is available in Mathlib, but the assembly is multi-cycle.

## Possible solutions

1. **Direct cofactor expansion of `det(I − zX)` for general `n`.**
   Exploit the sparse structure (only the first row, the last column,
   and the sub-diagonal are non-zero). Compute the determinant by
   Laplace expansion along the first column. Tedious but mechanical;
   plausible single-cycle work for cycle 139 (~150 LOC).

2. **Eigenvalue-density argument** (the textbook's path). ~300 LOC over
   2–3 cycles.

3. **Induction on `n` via row-reduction.** The `(n−1) × (n−1)`
   bottom-right block of `X` is itself a doubly companion matrix shifted
   down. This may be the cleanest approach; sketch in cycle 139.

4. **Wait for Aristotle**. Both jobs submitted in cycle 138; if either
   returns a clean proof, incorporate in cycle 139.

## Cross-reference

`thm:550A` blocks:
* `thm:550B` (similarity transformation; uses 550A + the (550d)
  `n`-fold-eigenvalue case).
* `thm:551B` (M(z) eigenvalue analysis for IRK stability).
* `thm:553A` (derivation of methods with IRK stability).

## Cycle plan

* **Cycle 139**: process Aristotle returns; if both fail, attempt the
  manual `n = 2` closure (~80 LOC) as a stepping stone, plus draft a
  cofactor-expansion sketch for general `n`.
* **Cycle 140+**: if no Aristotle path opens, commit to the
  cofactor-expansion or induction plan over 2 cycles.
