# Issue: §521 — Charpoly factorisation for `LMM.toGLM_isAStable_iff`

## Blocker

The headline `LMM.toGLM_isAStable_iff (m : LMM s) : m.toGLM.IsAStable ↔ m.IsAStable`
in `OpenMath/LMMAsGLM.lean` (cycle 628) reduces to a charpoly
factorisation identity. The factorisation has been derived by hand
(see "Polynomial shape" below) but the polynomial-level proof has not
been mechanised. Cycle 628 lands the sorry-first headline plus a
direct `s = 1` concrete proof of `backwardEuler_toGLM_isAStable`; the
general-`s` factorisation is the cycle 629 follow-up.

## Context

- Live file: `OpenMath/LMMAsGLM.lean` line 678 (sorry).
- GLM A-stability definition:
  `OpenMath/GeneralLinearMethod.lean` lines 202–210.
- LMM A-stability definition:
  `OpenMath/MultistepMethods.lean` lines 340–353.
- LMM-as-GLM block layout:
  `OpenMath/LMMAsGLM.lean` lines 57–99 (V, A, U, B definitions).
- `toGLM_stabilityMatrix_apply`:
  `OpenMath/LMMAsGLM.lean` lines 656–667.
- Cycle 627 RK template (analogous bridge):
  `OpenMath/RKAsGLM.lean` lines 92–113.

## Polynomial shape (worked out by hand for `s = 1`)

For `m : LMM s` with `m.normalized` (so `m.α (Fin.last s) = 1`),
write `α_j := m.α j`, `β_j := m.β j`, and let
`c_z := 1 - z * (m.β (Fin.last s) : ℂ)`.

The GLM stability matrix is `M(z) = V_ℂ + z * (B_ℂ * (1 - z A_ℂ)⁻¹ * U_ℂ)`,
where `A_ℂ` is `1 × 1` with sole entry `c := β_s` (recall the GLM
stages count is `1`, register count is `2*s`). Hence
`((1 - z A_ℂ)⁻¹) 0 0 = 1 / c_z` when `c_z ≠ 0`, otherwise `0`.

### Rank-one structure

Because the GLM stage count is `1`, the matrix
`B_ℂ * (1 - z A_ℂ)⁻¹ * U_ℂ` is the rank-one outer product
`(1 / c_z) * (B_ℂ[·, 0]) * (U_ℂ[0, ·])`. Hence
`M(z)[k, l] = V_ℂ[k, l] + (z / c_z) * B_ℂ[k, 0] * U_ℂ[0, l]`.

### Block decomposition

Index `Fin (2*s) ≃ Fin s ⊕ Fin s` via `Fin.addCases`. Let
`P_y` and `P_f` be the embeddings of the two halves. Then:

* `B_ℂ[P_y j, 0] = β_s` if `j+1 = s`, else `0`;
  `B_ℂ[P_f j, 0] = 1`  if `j+1 = s`, else `0`. So `B_ℂ` has only two
  nonzero entries: at the last past-`y` slot and the last past-`f` slot.
* `U_ℂ[0, P_y j] = -α_j`,  `U_ℂ[0, P_f j] = β_j` for `j : Fin s`.
* `V_ℂ` block decomposes into:
  - `V_yy`: rows `j < s-1` are pure shift `[k,k+1] = 1`; row `s-1`
    has entries `-α_j` for `j : Fin s` (LMM α-coefficients).
  - `V_yf`: rows `j < s-1` are zero; row `s-1` has entries `β_j` for
    `j : Fin s`.
  - `V_fy = 0` everywhere.
  - `V_ff`: rows `j < s-1` are pure shift `[s+k, s+k+1] = 1`; row
    `s-1` is zero.

### Charpoly factorisation (s=1 case, derived)

For `s = 1` the matrix is `2 × 2` with `a := α_0`, `b := β_0`, `c := β_1`:
```
M(z) = (1/c_z) * !![-a, b; -a*z, b*z]   (when c_z ≠ 0).
```
Trace `= (b*z - a) / c_z`, determinant `= 0`. So
```
charpoly(M(z))(μ) = μ * (μ - (b*z - a) / c_z)
                  = μ * (μ * c_z + a - b*z) / c_z.
```
The LMM stability polynomial (for `s = 1`, with `α_1 = 1`) is
```
π(μ, z) = α_0 + μ - z * (β_0 + β_1 * μ) = μ * c_z + a - b*z.
```
So `charpoly(M(z))(μ) = (μ / c_z) * π(μ, z)`. Roots: `μ = 0`
together with the LMM stability roots.

### General-`s` charpoly factorisation (conjectured shape)

For general `s`, the charpoly should factor as
```
charpoly(M(z))(μ) = (μ^s / c_z^?) * π(μ, z) * (...?)
```
where `π(μ, z) = ρ(μ) - z * σ(μ)` is the standard LMM stability
polynomial of degree `s` in `μ`. The `μ^s` factor reflects the
nilpotent past-`h*f` block plus the shift component of the past-`y`
block above row `s-1`. Concretely the conjecture is that
```
charpoly(M(z)) = Polynomial.X^s * <some polynomial whose roots are
                                    exactly the LMM stability roots>.
```

The `μ^s` count comes from:
* `s - 1` zero eigenvalues from the past-`y` shift block (rows
  `0, ..., s-2` of `V_yy` are pure shift, contributing a Jordan block
  with zero eigenvalue but no contribution to actual root multiplicity
  via this argument alone — needs care);
* `s` zero eigenvalues from the past-`h*f` shift block (rows
  `0, ..., s-1` of `V_ff`, fully nilpotent: the last row is zero, the
  rest shift).

Actually the cleaner count: `r = 2*s` rows, so charpoly has degree
`2*s`. The past-`f` block alone is `s × s` strictly upper triangular
(nilpotent), contributing `μ^s`. The past-`y` block `V_yy` plus the
rank-one perturbation contributes a degree-`s` factor whose roots are
the LMM stability roots.

So the precise claim is:
```lean
theorem toGLM_stabilityMatrix_charpoly_eq (m : LMM s) (z : ℂ)
    (hz : 1 - z * (m.β (Fin.last s) : ℂ) ≠ 0) :
    (m.toGLM.stabilityMatrix z).charpoly =
      Polynomial.X ^ s *
      (∑ j : Fin (s + 1),
         Polynomial.C (((m.α j : ℂ) - z * (m.β j : ℂ)) /
                        (1 - z * (m.β (Fin.last s) : ℂ))) *
         Polynomial.X ^ (j : ℕ))
```
(modulo sign / scaling — the s=1 derivation gives this shape exactly).

### Iff bridge proof from charpoly identity

Once the charpoly identity is in hand:
* Forward (`m.toGLM.IsAStable → m.IsAStable`): for `z` with
  `z.re ≤ 0` and any LMM-stability root `ξ`, `ξ` is also a charpoly
  root via the factorisation, hence `‖ξ‖ ≤ 1` by GLM A-stability.
* Reverse (`m.IsAStable → m.toGLM.IsAStable`): for `z` with
  `z.re ≤ 0` and any charpoly root `μ`, the factorisation gives
  `μ = 0` (then `‖μ‖ ≤ 1` automatic) or `μ` is an LMM-stability
  root (then `‖μ‖ ≤ 1` by `m.IsAStable`).

The `c_z = 0` edge case (i.e., `z = 1 / β_s` when `z.re ≤ 0`) needs
a side argument. For `β_s ≥ 0` real (the standard normalised case)
this can only happen when `β_s = 0` and `z` is anything ⇒ no, wait,
if `β_s = 0` then `c_z = 1 ≠ 0`. So `c_z = 0` requires `β_s ≠ 0`
and `z = 1/β_s`. For `β_s > 0` real this gives `z.re > 0`, outside
the closed left half-plane, so doesn't apply. For `β_s < 0` real
this gives `z.re < 0`; the claim fails or needs an extra hypothesis.
Backward Euler has `β_1 = 1 > 0`, so this edge case never triggers.

## What was tried in cycle 628

- Sorry-first headline: lands at `OpenMath/LMMAsGLM.lean:678`.
- Concrete `s = 1` direct proof: `backwardEuler_toGLM_isAStable`
  lands at the bottom of `OpenMath/LMMAsGLM.lean`. Computed the 2×2
  stability matrix explicitly, then the charpoly via
  `Matrix.det_fin_two` and `Matrix.adjugate_fin_one` for the 1×1
  resolvent, then closed by checking both root values
  (`0` and `1/(1-z)`) lie in the closed unit disk for `z.re ≤ 0`.

## Possible solutions for cycle 629

1. **Direct general-`s` charpoly factorisation**. Prove
   `toGLM_stabilityMatrix_charpoly_eq` by:
   * Block-decompose `M(z)` over `Fin s ⊕ Fin s` via `Fin.addCases`.
   * The past-`f` block of `M(z)` differs from the past-`f` block of
     `V_ℂ` only at row `s-1` (which gets `(z/c_z) * U_ℂ[0, ·]`),
     and at all rows for the rank-one perturbation, so it does *not*
     remain block triangular in general — the rank-one perturbation
     mixes blocks. Refactor: pre-multiply by an appropriate similarity
     to expose the block structure.
   * Alternatively, use the **matrix determinant lemma**:
     `det(I + u v^T) = 1 + v^T u`. Here
     `μ I - M(z) = μ I - V_ℂ - (z/c_z) * (B_ℂ[·,0]) * (U_ℂ[0,·])`,
     a rank-one perturbation of `μ I - V_ℂ`. So
     `det(μ I - M(z)) = det(μ I - V_ℂ) - (z/c_z) * adj(μ I - V_ℂ)
                                          * (B_ℂ[·,0]) ⋅ U_ℂ[0,·]`
     ... or, more cleanly, the matrix determinant lemma gives
     `det(μ I - M(z)) = det(μ I - V_ℂ) * (1 - (z/c_z) * U_ℂ[0,·] *
                                          (μ I - V_ℂ)⁻¹ * B_ℂ[·,0])`.
   * Compute `det(μ I - V_ℂ) = μ^s * (μ^s + α_{s-1} μ^{s-1} + ... + α_0)`
     (from the block-shift structure). The first `μ^s` factor is the
     `V_ff` nilpotent block contribution; the second factor is
     `μ * ρ(μ)` ... no wait, the `V_yy` block has the LMM
     α-coefficients in its last row, so its charpoly should be the
     LMM ρ-polynomial. Need to verify carefully.
   * The rank-one correction term `1 - (z/c_z) * U^T (μI - V_ℂ)⁻¹ B`
     should evaluate to a rational expression in μ, z whose numerator
     is `(ρ(μ) - z * σ(μ)) / ρ(μ) * c_z` or similar — and the
     pole at `ρ(μ) = 0` cancels with the `μ^s * ρ(μ)` factor in
     `det(μ I - V_ℂ)`. Net result: charpoly is `μ^s * π(μ, z) / c_z`
     polynomial-equal up to constant scaling.

2. **Block-form lemma `toGLM_stabilityMatrix_block_form`**. Stop
   short of the full charpoly identity but expose the block structure
   in a reusable form. Strategy step 2 in cycle 628 strategy.

3. **Specialise to `s = 2`**, then `s = 3`, building intuition. The
   `s = 1` case (this cycle) confirms the conjectured shape.

## Cycle 628 status

- [x] `LMM.toGLM_isAStable_iff` headline lands sorry-first.
- [ ] `LMM.toGLM_stabilityMatrix_charpoly_eq` not yet attempted.
- [x] `backwardEuler_toGLM_isAStable` proved directly (does not use
      the iff bridge — independent concrete check).
