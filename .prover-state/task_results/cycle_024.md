# Cycle 024 Results

## Worked on
Dahlquist's second barrier — closing the remaining sorry in `order_ge_three_not_aStable_core` (OpenMath/MultistepMethods.lean). This is the core of the proof that A-stable + zero-stable LMMs have order ≤ 2.

## Approach
1. Analyzed the single monolithic sorry and designed the Gt construction:
   Gt(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w)) with removable singularity Gt(1) = 0.
2. Defined reversed polynomials σ̃, ρ̃ as Lean `let` bindings using `Fin.rev`.
3. Proved the key reversed polynomial identity: ∑ c(j.rev) · z^j = z^s · ∑ c(j) · z⁻¹^j,
   using `Fintype.sum_equiv Fin.revPerm` with a careful `pow_add`-based proof.
4. Proved `h_rho_rev` and `h_sigma_rev`: ρ̃(z) = z^s · ρ(1/z) and σ̃(z) = z^s · σ(1/z).
5. **Fully proved boundary non-negativity** (part c): Re(Gt(z)) ≥ 0 for |z| = 1.
   - z = 1 case: Gt(1) = 0 by definition.
   - z ≠ 1 case: σ̃/ρ̃ = σ(z⁻¹)/ρ(z⁻¹) via z^s cancellation (`mul_div_mul_left`),
     Re((z+1)/(2(1-z))) = 0 on unit circle (from `re_half_plus_inv_sub_one_eq_zero`),
     Re(σ/ρ) ≥ 0 from A-stability (`E_nonneg_re_unit_circle`, with by_cases for ρ=0).
6. Decomposed the remaining sorry into 2 focused sub-goals with detailed proof sketches.

## Result
PARTIAL SUCCESS — reduced 1 monolithic sorry to 2 focused sorrys with complete proof sketches.

### Fully proved
- `h_rev_identity`: reversed polynomial identity via `Fin.revPerm` + `pow_add`
- `h_rho_rev`, `h_sigma_rev`: ρ̃(z) = z^s · ρ(1/z) for z ≠ 0
- Part (b): Gt(1) = 0 by definition
- Part (c): boundary non-negativity — Re(Gt(z)) ≥ 0 for |z| = 1

### Remaining sorrys (2)
1. **DiffContOnCl ℂ Gt (Metric.ball 0 1)** (line 1024):
   - DifferentiableOn: straightforward (ρ̃ ≠ 0 for |w| < 1, w ≠ 1)
   - ContinuousOn: requires removable singularity at w = 1 (polynomial factoring + limits)
   - SUBTLETY: if ρ has unit-circle roots other than ζ = 1, Gt has boundary poles
     and DiffContOnCl fails. Needs additional hypothesis or different proof strategy.

2. **HasDerivAt Gt (1/12) 1** (line 1075):
   - Requires: N̄'''(1) = -ρ'(1), D̄''(1) = 4ρ'(1), giving G'(1) = -1/12, Gt'(1) = 1/12.
   - Uses order conditions C₀ through C₃ for the polynomial algebra.
   - Needs polynomial factoring: N̄ = (w-1)³Q, D̄ = (w-1)²·(-2R̃).

## Dead ends
- `Fin.revOrderIso` approach for sum re-indexing: invalid `α` argument, `_symm` not found.
  Solution: `Fintype.sum_equiv Fin.revPerm` with direct `pow_add`-based proof.
- `pow_sub₀` approach: order mismatch `(z^j.rev)⁻¹ * z^s` vs `z^s * (z^j.rev)⁻¹`.
  Solution: use `← h1, mul_assoc, mul_inv_cancel₀` chain.
- Trying to prove `rhoC z⁻¹ ≠ 0` for E_nonneg argument: approach via `h_rho_rev` + rewriting
  produced `h : 0 = 0 ⊢ False`. Solution: by_cases split (if ρ=0, div=0, Re=0≥0).
- DiffContOnCl with boundary poles: if ρ has unit-circle roots other than 1, the function
  σ̃/ρ̃ has poles on the boundary. exp(-Gt) analysis shows Re(Gt) → +∞ at these poles
  (from inside), so |exp(-Gt)| → 0, but continuity still fails at the boundary.

## Discovery
- `Fintype.sum_equiv Fin.revPerm` is the correct API for re-indexing sums with reversed indices.
- `Fin.val_rev` gives `(Fin.rev j).val = s - j.val`, closed with `omega`.
- The proof `z^j = z^s * z⁻¹^(j.rev)` is cleanest via: `pow_add` gives `z^j * z^(j.rev) = z^s`,
  then `mul_inv_cancel₀` converts to inverse form.
- For div-by-zero handling in boundary proofs: `by_cases hρ : m.rhoC z⁻¹ = 0` with
  `div_zero` lemma avoids the need to prove denominators are non-zero everywhere.
- **Critical mathematical insight**: The combined fraction N̄(w)/D̄(w) has a triple zero (N̄)
  vs double zero (D̄) at w = 1 for order ≥ 2. The triple zero uses C₀ (ρ(1)=0),
  C₁ (σ(1)=ρ'(1)), and C₂ (ρ''(1)=2σ'(1)-ρ'(1)). Order ≥ 3 then gives N̄'''(1)=-ρ'(1),
  which determines Gt'(1) = 1/12.
- **Potential issue**: DiffContOnCl requires no unit-circle roots of ρ other than ζ = 1.
  The textbook proof implicitly assumes this. For zero-stable A-stable methods, roots of ρ
  are in the closed disk (simple on boundary), but there could be other boundary roots.
  Analysis shows that at such roots, Re(σ·conj(ρ)) = 0 trivially and the E-function
  σ/ρ has a pole whose Re contribution is 0 at leading order. The proof may need
  either (a) an additional hypothesis, or (b) a stronger minimum principle that handles
  finitely many boundary singularities.

## Suggested next approach
1. **Easier path**: Prove HasDerivAt first. This is pure polynomial algebra:
   define the combined fraction, compute N̄'''(1) from order conditions C₀-C₃,
   factor out (w-1)³ from N̄, and derive HasDerivAt from the quotient.
   May need `HasDerivAt.div` from Mathlib.

2. **DiffContOnCl approach A**: Add hypothesis `∀ ζ, ‖ζ‖=1 → rhoC ζ=0 → ζ=1` to
   `order_ge_three_not_aStable_core`. Then ContinuousOn only needs the removable
   singularity at w=1. Provide hypothesis from zero-stability in calling theorem
   (may need a separate lemma or sorry).

3. **DiffContOnCl approach B**: Replace the minimum principle argument with a
   maximum principle on sub-balls B(0,r) for r < 1 (where Gt is DiffContOnCl),
   combined with a limiting argument as r → 1. This avoids boundary issues
   entirely but requires a custom limit argument.

4. **Alternative proof strategy**: Use Fourier analysis / Herglotz representation
   instead of the minimum principle. This works directly on the boundary and
   doesn't need DiffContOnCl. But requires Fourier machinery not in Mathlib.
