# Cycle 137 Results

## Worked on

- **Task 1**: `explicitEulerGLM_not_isLStable` — one-line negative L-stability
  witness for `def:520F`, follows directly from cycle 136's
  `explicitEulerGLM_not_isAStable` via `∧`-projection.
- **Task 2**: `implicitMidpointGLM_not_isLStable` — substantive negative
  L-stability witness for `def:520F`. Implicit midpoint *is* A-stable
  (cycle 135) but its stability function `R(z) = (1+z/2)/(1-z/2)` has
  `|R(z)| → 1` (not 0) at infinity, so it is not L-stable.

Both theorems land in `OpenMath/Chapter5/Section520.lean` immediately after
cycle 136's `explicitEulerGLM_not_isAStable`.

## Approach

### Task 1 (one-line)

```lean
theorem explicitEulerGLM_not_isLStable :
    ¬ explicitEulerGLM.IsLStable :=
  fun h => explicitEulerGLM_not_isAStable h.1
```

`IsLStable` is `IsAStable ∧ Tendsto … (𝓝 0)`; the projection `h.1` extracts
the A-stability conjunct, which cycle 136 refutes.

### Task 2 (substantive)

Three-stage proof:

1. **Private helper `spectralRadius_fin_one`**: `ρ(!![a]) = ‖a‖₊` (in
   ENNReal). Proved by recognising `(!![a] : Matrix (Fin 1) (Fin 1) ℂ)`
   as `algebraMap ℂ _ a` (since `1 : Matrix (Fin 1) (Fin 1) ℂ = !![1]`,
   `a • 1 = !![a]`), then applying `spectrum.scalar_eq` to get
   `spectrum ℂ !![a] = {a}`, and the `iSup` over a singleton collapses
   via `simp`.

2. **Witness sequence `g n = -((n : ℂ) + 2)` goes to cocompact**: applied
   `tendsto_cocompact_of_tendsto_dist_comp_atTop` with `x = 0`. The
   distance simplifies via `dist_zero_right`, `norm_neg`, and embedding
   `(n : ℂ) + 2 = (((n : ℝ) + 2) : ℝ : ℂ)` to apply `Complex.norm_real`.

3. **Lower bound on `ρ(M(g n))` for n ≥ 4**:
   - `(g n).re ≤ 0` so cycle 135's `implicitMidpointGLM_stabilityMatrix`
     applies: `M(g n) = !![(1 + g n /2) / (1 - g n /2)]`.
   - Algebraic simplification: `(1 + g n /2) / (1 - g n /2) = -n/(n+4)`
     (real-valued embedded in `ℂ`). Used `div_div_div_cancel_right₀` to
     cancel the common `/2` factor.
   - `‖real-valued ℂ‖ = |·|` via `Complex.norm_real`, `Real.norm_eq_abs`,
     `abs_div`, `abs_of_nonneg`.
   - For `n ≥ 4`: `n/(n+4) ≥ 1/2` in ℝ. Cast to NNReal via `NNReal.eq`,
     then to ENNReal via `ENNReal.coe_le_coe`. The `1/2` ENNReal value
     is brought into `(1/2 : NNReal) : ENNReal` form using
     `ENNReal.coe_div`.

4. **Contradiction**: composing `hRho` with `hg_cocompact` gives
   `Tendsto (n ↦ ρ(M(g n))) atTop (𝓝 0)`. By `ENNReal.tendsto_atTop_zero`
   with `ε = 1/4`, eventually `ρ(M(g n)) ≤ 1/4`. But the lower bound
   gives `ρ(M(g n)) ≥ 1/2` for `n ≥ 4`. Picking `n = max N 4` yields
   `1/2 ≤ 1/4`, refuted by `norm_num`.

## Result

**SUCCESS** — both theorems compile cleanly. Verified axiom-clean
(`propext, Classical.choice, Quot.sound`) via
`mcp__lean-lsp__lean_verify` for both
`explicitEulerGLM_not_isLStable` and
`implicitMidpointGLM_not_isLStable`.

`lake env lean OpenMath/Chapter5/Section520.lean` exits 0.

## Faithfulness check

### Task 1 — `explicitEulerGLM_not_isLStable`
- Entity ID: `def:520F` non-vacuity (auxiliary witness; not a textbook-named
  theorem).
- Statement: `¬ explicitEulerGLM.IsLStable`.
- Tautology check: conclusion is `¬ IsLStable …`, no hypothesis matches.
- Identity check: proof is `fun h => …_not_isAStable h.1`. The `h.1` is
  ∧-projection (selects the A-stability conjunct from L-stability), then
  feeds it to a *non-trivial* prior theorem. This does real mathematical
  work: it instantiates the implication "L-stable ⇒ A-stable" at a specific
  method and chains with the A-stability refutation.
- Hypothesis strength: zero hypotheses.
- No new structures.

### Task 2 — `implicitMidpointGLM_not_isLStable`
- Entity ID: `def:520F` non-vacuity (auxiliary substantive witness).
- Statement: `¬ implicitMidpointGLM.IsLStable`.
- Captures the textbook contrast (Butcher §520, p. 419): the canonical
  Padé(1,1) approximant of `exp(z)` is A-stable but not L-stable.
- Tautology / identity check: conclusion is `¬ IsLStable …`; proof is
  >70 lines of genuine spectral-radius/cocompact reasoning, not a
  re-export of any hypothesis.
- Hypothesis strength: zero hypotheses.
- Definition smuggling check: `IsLStable` was defined in cycle 088 as
  `IsAStable ∧ Tendsto (ρ ∘ M) cocompact (𝓝 0)`, faithfully encoding
  the textbook `ρ(M(∞)) = 0` via the universal stiff-ODE convention
  (cf. Hairer–Wanner) of using the cocompact-filter limit. We are
  *negating* this faithful definition for a specific GLM.
- No new structures or classes.

### Private helper — `spectralRadius_fin_one`
- Generic helper: `spectralRadius ℂ !![a] = ‖a‖₊`. No textbook identity;
  it is an instance of the standard fact "spectrum of a 1×1 matrix is
  its single entry". Proved via `algebraMap` + `spectrum.scalar_eq`
  rather than re-deriving the spectrum-of-singleton lemma.

## Dead ends

- **`spectrum_diagonal` direct rewrite**: planner suggested using
  `spectrum_diagonal` to reduce `Matrix.diagonal` of `Fin 1` to a
  singleton range. The lemma exists (`spectrum_diagonal` in
  `Mathlib.LinearAlgebra.Eigenspace.Matrix`) but the import path was
  unclear and the resulting `Set.range (fun _ : Fin 1 => a)` simplification
  to `{a}` was awkward. Switched to the cleaner
  `algebraMap` + `spectrum.scalar_eq` route.
- **`field_simp; ring` on the ratio simplification**: my first attempt
  on `(1 + g n / 2) / (1 - g n / 2) = ↑(-n/(n+4))` after `push_cast`
  produced a normalised form that `ring` rejected. Switched to a
  cleaner pre-decomposition: prove the numerator equals `-n/2` and
  denominator equals `(n+4)/2` separately by `ring` (no field
  operations), then apply `div_div_div_cancel_right₀` to cancel the
  `/2`.
- **`div_le_div_iff` deprecated**: not the current Mathlib name. Used
  `le_div_iff₀` then `field_simp; linarith` for the `1 ≤ n/(n+4) * 2`
  bound.
- **NNReal `⟨...⟩` constructor mismatch**: writing `(⟨1/2, _⟩ : NNReal)`
  to coerce a NNReal value sometimes elaborates as `{r // 0 ≤ r}`
  rather than `NNReal`. Worked around by splitting `(1/2 : NNReal)`
  through `(1/2 : NNReal) = (⟨1/2, _⟩ : NNReal)` after `apply NNReal.eq`.

## Discovery

- **`tendsto_cocompact_of_tendsto_dist_comp_atTop`**: clean Mathlib
  bridge from `Tendsto (dist ∘ f · x) atTop atTop` to
  `Tendsto f atTop cocompact`. Reusable for any future "subsequence
  diverges to ∞" → cocompact-filter argument.
- **`spectrum.scalar_eq`**: cleaner than `spectrum_diagonal` for the
  1×1 case, since `algebraMap ℂ A · a = a • 1` and unfolds without
  rangefolding.
- **ENNReal arithmetic friction**: `(1/2 : ENNReal)` and
  `(1/4 : ENNReal)` are not `norm_num`-positive directly; the cleanest
  path is to show they equal a `(NNReal : ENNReal)` coercion via
  `ENNReal.coe_div`, then apply `ENNReal.coe_pos.mpr` with `norm_num`
  on the NNReal side.
- **Cycle 135's private helper `norm_pow_fin_one`** was *not* needed
  here because we directly compute the spectral radius (a single
  application), not iterated powers. The 1×1 powers infrastructure
  remains specific to A-stability proofs.

## Suggested next approach

Per the planner's suggested cycle 138 direction: the non-vacuity
strengthening cadence (cycles 128–137) has run its course for the
five definitions `def:520E`, `def:520F`, `def:525A`, `def:542A`,
`def:551A`. Time to attack a real theorem. Concrete options:

1. **`thm:551B` Single Non Zero Eigenvalue Stability** — small
   statement, builds on cycle 131/133's `def:551A` infrastructure.
   The natural follow-on to having two `IsIRKStable` witnesses.
2. **`thm:521B` Maximum stability order for given steps** — small
   statement, builds on `def:521A` (cycle 089). Note: planner cycle
   137 strategy mentioned this requires the deferred `Polynomial`
   representation of `stabilityFunction`; verify before starting.
3. **`thm:550A` Doubly companion matrices** — pure linear algebra,
   potentially Mathlib-light. Independent of Chapter 5 stability
   apparatus.

Cycle 138 planner should pick one. The new Mathlib bridges discovered
this cycle (`tendsto_cocompact_of_tendsto_dist_comp_atTop`,
`spectrum.scalar_eq`, `spectralRadius_fin_one`) are reusable for any
spectral-radius / cocompact-filter argument that arises during
`thm:551B` or related work.
