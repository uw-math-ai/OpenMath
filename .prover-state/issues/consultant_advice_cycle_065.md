# Consultant Advice: Breaking the 6-Cycle Stall — Cycle 65

## Executive Summary

Three sorrys remain, unchanged since cycle 58. The last 6 cycles (59–64) produced zero mathematical progress due to context window saturation / pre-work timeout. This advice provides **maximally concrete, copy-paste-ready proof strategies** for each sorry, designed to be actionable in a single cycle.

**Priority order:**
1. `uniformly_bounded_tupleSucc_iterates` (DahlquistEquivalence.lean:284) — freshest approach, most impact
2. `hasDerivAt_Gtilde_one` (MultistepMethods.lean:1166) — self-contained polynomial algebra
3. `continuousOn_Gtilde_closedBall` (MultistepMethods.lean:1183) — depends on (2)

---

## Part 1: `uniformly_bounded_tupleSucc_iterates` — The Spectral Bound

### The Goal

```lean
theorem uniformly_bounded_tupleSucc_iterates (m : LMM s) (hzs : m.IsZeroStable) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : Fin s → ℂ),
      ‖(m.toLinearRecurrence.tupleSucc^[n]) v‖ ≤ M * ‖v‖
```

### Why Previous Approaches Failed

Cycles 35–43 tried to connect `LinearRecurrence.charPoly` to `LinearMap.charpoly` for `tupleSucc`. This requires computing `det(XI - companion matrix)` for general `s` — a massive, unnecessary computation. **Don't do this.**

### The Right Approach: Direct Annihilation + Coprime Splitting

**Key insight**: You do NOT need `LinearMap.charpoly tupleSucc = E.charPoly`. You only need `aeval tupleSucc E.charPoly = 0`, which follows trivially from the recurrence relation.

#### Step 1: `aeval tupleSucc charPoly = 0` (the foundation)

```lean
lemma aeval_tupleSucc_charPoly_eq_zero (E : LinearRecurrence ℂ) :
    Polynomial.aeval E.tupleSucc E.charPoly = 0 := by
  ext v
  simp only [LinearMap.zero_apply]
  ext j
  simp only [Pi.zero_apply]
  -- Need: ((aeval E.tupleSucc E.charPoly) v) j = 0
  -- charPoly = X^order - ∑ coeffs_i * X^i
  -- aeval T (X^k) v = T^k v = tupleSucc^[k] v  (LinearMap.pow_apply)
  -- (T^k v) j = mkSol v (k + j)  (tupleSucc_iterate_eq_mkSol)
  -- So the sum equals mkSol v (order + j) - ∑ coeffs_i * mkSol v (i + j)
  -- = 0 by E.is_sol_mkSol v j
  sorry -- Fill in: expand aeval on charPoly, convert T^k to iterate,
        -- use tupleSucc_iterate_eq_mkSol, then is_sol_mkSol
```

**Critical tactic chain**: The main challenge is connecting `aeval T (X^k)` to `T^[k]`.

```lean
-- Key identity: (f ^ k) = f^[k] for LinearMap
-- Use: LinearMap.pow_apply or prove by induction
-- Then: (aeval T (monomial k c)) v = c • (T ^ k) v  (Polynomial.aeval_monomial + smul)
-- Then: (T ^ k) v j = tupleSucc^[k] v j  (by pow_apply + function.iterate)
-- Then: tupleSucc^[k] v j = mkSol v (k + j)  (tupleSucc_iterate_eq_mkSol)
```

**Verified Mathlib lemmas**:
- `Polynomial.aeval_monomial` — `aeval f (monomial k c) = c • f ^ k` (Module.End algebra)
- `LinearMap.pow_apply` — for iterating linear maps
- `LinearRecurrence.is_sol_mkSol` — `mkSol init` satisfies the recurrence
- `tupleSucc_iterate_eq_mkSol` — already proved at line 239

#### Step 2: `charPoly.eval = rhoC` (algebraic identity)

```lean
theorem charPoly_eval_eq_rhoC (m : LMM s) (μ : ℂ) :
    m.toLinearRecurrence.charPoly.eval μ = m.rhoC μ := by
  simp only [LinearRecurrence.charPoly, toLinearRecurrence, rhoC]
  -- Both expand to μ^s + ∑_{j<s} (α_j : ℂ) μ^j
  -- charPoly = X^s - ∑ (-(α_i : ℂ)) X^i = X^s + ∑ α_i X^i
  -- rhoC μ = ∑_{j≤s} α_j μ^j = α_s μ^s + ∑_{j<s} α_j μ^j = μ^s + ∑ α_j μ^j
  sorry -- Expand both sides, use m.normalized (α_s = 1), Fin.sum_univ_castSucc, ring
```

#### Step 3: Eigenvalue → ρ-root (using the killer lemma)

**Verified Mathlib lemma** (this is the key!):
```
Module.End.aeval_apply_of_hasEigenvector :
  f.HasEigenvector μ x → aeval f p x = p.eval μ • x
```

So if `T v = μ v` with `v ≠ 0`, then `0 = (aeval T charPoly) v = charPoly.eval μ • v`, giving `charPoly.eval μ = 0`, hence `rhoC μ = 0`.

```lean
theorem tupleSucc_eigenvalue_implies_rhoC_root (m : LMM s) (μ : ℂ)
    (hμ : m.toLinearRecurrence.tupleSucc.HasEigenvalue μ) : m.rhoC μ = 0 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h1 := aeval_tupleSucc_charPoly_eq_zero m.toLinearRecurrence
  have h2 := Module.End.aeval_apply_of_hasEigenvector hv (p := m.toLinearRecurrence.charPoly)
  rw [show (aeval m.toLinearRecurrence.tupleSucc m.toLinearRecurrence.charPoly) v = 0
    from by rw [h1]; rfl] at h2
  -- h2 : 0 = charPoly.eval μ • v
  rw [← charPoly_eval_eq_rhoC]
  exact (smul_eq_zero.mp h2.symm).resolve_right hv.2
```

#### Step 4: The Coprime Splitting (the core argument)

Factor `charPoly` into unit-circle roots and disk roots:

```lean
-- Let S = set of distinct unit-circle roots of charPoly
-- p_unit = ∏_{μ ∈ S} (X - C μ)    (squarefree by construction)
-- p_disk = charPoly / p_unit       (remaining factors)

-- Key properties:
-- 1. charPoly = p_unit * p_disk  (since zero-stability: unit-circle roots are simple)
-- 2. IsCoprime p_unit p_disk     (disjoint root sets)
-- 3. p_unit is Squarefree        (each root appears once)
```

**Verified Mathlib infrastructure for coprime splitting**:
- `Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime` : `IsCoprime p q → ker(p(T)) ⊔ ker(q(T)) = ker((p*q)(T))`
- `Polynomial.disjoint_ker_aeval_of_isCoprime` : `IsCoprime p q → Disjoint ker(p(T)) ker(q(T))`
- `Polynomial.sup_aeval_range_eq_top_of_isCoprime` : `IsCoprime p q → range(p(T)) ⊔ range(q(T)) = ⊤`
- `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` : over algebraically closed fields, coprime iff no common root
- `Polynomial.pairwise_coprime_X_sub_C` : distinct linear factors are pairwise coprime

Since `aeval T charPoly = 0`, we have `ker(charPoly(T)) = ⊤`. The coprime splitting gives `ker(p_unit(T)) ⊕ ker(p_disk(T)) = ⊤`.

#### Step 5: Bound the unit-circle component (semisimple)

On `ker(p_unit(T))`: `aeval T p_unit = 0` restricted to this kernel.

Since `p_unit` is squarefree:
```
Module.End.isSemisimple_of_squarefree_aeval_eq_zero :
  Squarefree p → aeval f p = 0 → f.IsSemisimple
```

Then:
```
Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace :
  f.IsFinitelySemisimple → f.maxGenEigenspace μ = f.eigenspace μ
```

Combined with `iSup_maxGenEigenspace_eq_top`, eigenspaces span the restricted space. On each eigenspace, `T v = μ v` with `|μ| = 1`, so `‖T^n v‖ = |μ|^n ‖v‖ = ‖v‖`. Bounded!

#### Step 6: Bound the disk component (spectral decay)

All eigenvalues of `T` restricted to `ker(p_disk(T))` have `|μ| < 1`.

**Verified Mathlib lemma**:
```
tendsto_pow_const_mul_const_pow_of_abs_lt_one :
  |r| < 1 → Tendsto (fun n => n^k * r^n) atTop (𝓝 0)
```

On each generalized eigenspace (`maxGenEigenspace μ`), `T - μ` is nilpotent (by `isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`), so `(T - μ)^d = 0` for some `d ≤ s`. Then:
```
T^n v = ∑_{k<d} C(n,k) μ^{n-k} (T-μ)^k v
```
Each term has `‖C(n,k) μ^{n-k} (T-μ)^k v‖ ≤ n^k |μ|^{n-k} ‖(T-μ)^k‖ ‖v‖ → 0`.

So `T^n → 0` on this component, hence bounded.

#### Step 7: Combine

```
‖T^n v‖ = ‖T^n(P₁v + P₂v)‖ ≤ C₁‖P₁v‖ + C₂‖P₂v‖ ≤ (C₁‖P₁‖ + C₂‖P₂‖)‖v‖
```

### Recommended Decomposition

Break `uniformly_bounded_tupleSucc_iterates` into focused sub-lemmas:

```lean
-- Sub-lemma 1: charPoly annihilates tupleSucc
lemma aeval_tupleSucc_charPoly_eq_zero (E : LinearRecurrence ℂ) :
    Polynomial.aeval E.tupleSucc E.charPoly = 0

-- Sub-lemma 2: charPoly.eval = rhoC
theorem charPoly_eval_eq_rhoC (m : LMM s) (μ : ℂ) :
    m.toLinearRecurrence.charPoly.eval μ = m.rhoC μ

-- Sub-lemma 3: eigenvalue → ρ-root
theorem tupleSucc_eigenvalue_implies_rhoC_root (m : LMM s) (μ : ℂ)
    (hμ : m.toLinearRecurrence.tupleSucc.HasEigenvalue μ) : m.rhoC μ = 0

-- Sub-lemma 4: bounded powers of semisimple operator with unit eigenvalues
-- (This is the hardest piece — consider submitting to Aristotle)
lemma bounded_pow_of_semisimple_unit_eigenvalues
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hs : T.IsSemisimple)
    (h_unit : ∀ μ, T.HasEigenvalue μ → ‖μ‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (v : V), ‖(T ^ n) v‖ ≤ C * ‖v‖

-- Sub-lemma 5: bounded powers when all eigenvalues in open disk
lemma bounded_pow_of_eigenvalues_in_disk
    [FiniteDimensional ℂ V] (T : Module.End ℂ V)
    (h_disk : ∀ μ, T.HasEigenvalue μ → ‖μ‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (v : V), ‖(T ^ n) v‖ ≤ C * ‖v‖
```

### Single-Cycle Realistic Plan

In one cycle, prove sub-lemmas 1–3. These are mechanical and provide immediate value. Then decompose the main theorem using the coprime splitting, leaving sub-lemmas 4–5 as focused sorrys. Net result: 1 opaque sorry → 2 well-understood sorrys with clear proof paths.

**If blocked on sub-lemma 1**: The `aeval` ↔ `iterate` connection is the technical bottleneck. Try:

```lean
-- Prove by showing: ∀ v j, ((aeval T charPoly) v) j = 0
-- Expand charPoly as X^order - ∑ coeffs_i * X^i
-- aeval distributes: aeval T (X^n) = T^n (as LinearMap.pow)
-- (T^k v) j = tupleSucc^[k] v j (need Function.iterate_eq_pow or induction)
-- tupleSucc^[k] v j = mkSol v (k + j) (tupleSucc_iterate_eq_mkSol)
-- The sum equals the recurrence, which is 0 (is_sol_mkSol)
```

### Alternative: Accept as Documented Sorry

The mathematical content is standard and correct. If blocked after sub-lemmas 1–3, leaving the main theorem as a documented sorry is acceptable — the Dahlquist equivalence IS correctly formalized modulo this one well-understood spectral theory fact. Move to Chapter 4 material.

---

## Part 2: `hasDerivAt_Gtilde_one` — Derivative = 1/12

### The Goal

```lean
theorem hasDerivAt_Gtilde_one (m : LMM s) (p : ℕ) (hp : m.HasOrder p) (hp3 : 3 ≤ p)
    (ha : m.IsAStable) (hρ_simple : m.rhoCDeriv 1 ≠ 0) :
    HasDerivAt (fun w : ℂ => if w = 1 then (0 : ℂ) else
      m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w))) (1/12 : ℂ) 1
```

### Why Previous Approaches Failed (Cycles 19–34)

All cycles tried to prove `HasDerivAt` of the piecewise function directly. This requires limit arguments at the removable singularity — which is hard in Lean because `w = 1` is NOT in `ball(0,1)` (so the "ρ̃ ≠ 0" guarantee doesn't apply there).

### The Right Approach: Polynomial Cancelled Form + `HasDerivAt.congr_of_eventuallyEq`

**Key insight**: Define a polynomial cancelled form `Gt_cancelled`, prove `HasDerivAt Gt_cancelled (1/12) 1` using the quotient rule, then transfer to the piecewise function via `HasDerivAt.congr_of_eventuallyEq`.

#### Step 1: Build `Polynomial ℂ` objects

```lean
-- Reversed polynomials as Polynomial ℂ
let ρ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
  Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)
let σ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
  Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)

-- Connection to function-level definitions:
-- ∀ w, ρ_rev_poly.eval w = m.rhoCRev w
-- ∀ w, σ_rev_poly.eval w = m.sigmaCRev w
-- These are definitional after simp with eval lemmas.
```

#### Step 2: Factor ρ̃ as `(X - 1) * R_poly`

```lean
-- ρ̃(1) = ρ(1) = 0  (consistency, C₀)
have hρ_root : ρ_rev_poly.IsRoot 1 := by
  rw [Polynomial.IsRoot]; -- eval 1 ρ_rev_poly = rhoCRev 1 = rhoC 1 = 0
  sorry

-- Factor:
let R_poly := ρ_rev_poly /ₘ (Polynomial.X - Polynomial.C 1)
have h_ρ_factor : ρ_rev_poly = (Polynomial.X - Polynomial.C 1) * R_poly :=
  (Polynomial.mul_divByMonic_eq_iff_isRoot _).mpr hρ_root |>.symm

-- R_poly.eval 1 ≠ 0 (from zero-stability: ρ̃'(1) ≠ 0)
-- Key identity: if p = (X - a) * q then p.derivative.eval a = q.eval a
-- So R_poly.eval 1 = ρ_rev_poly.derivative.eval 1 = ρ̃'(1) ≠ 0
have hR1_ne : R_poly.eval 1 ≠ 0 := by sorry
```

**Verified Mathlib lemma**:
```
Polynomial.mul_divByMonic_eq_iff_isRoot :
  (X - C a) * (p /ₘ (X - C a)) = p ↔ p.IsRoot a
```

#### Step 3: Build P_poly and show triple root at 1

```lean
-- P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)
let P_poly := 2 • σ_rev_poly * (Polynomial.X - Polynomial.C 1) +
              ρ_rev_poly * (Polynomial.X + Polynomial.C 1)

-- Show rootMultiplicity 1 P_poly ≥ 3
-- Requires: P(1) = 0, P'(1) = 0, P''(1) = 0
-- These follow from order conditions C₀, C₁, C₂
```

**Verified Mathlib lemma**:
```
Polynomial.eval_iterate_derivative_rootMultiplicity :
  (derivative^[rootMultiplicity t p] p).eval t =
    (rootMultiplicity t p)! • (p /ₘ (X - C t)^(rootMultiplicity t p)).eval t
```

For showing rootMultiplicity ≥ 3, use:
```
-- CharZero instance for ℂ:
-- n < rootMultiplicity t p ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t
```

**P(1) = 0**: `2σ̃(1)·0 + ρ̃(1)·2 = 0 + 0 = 0` (from C₀: ρ(1) = 0)

**P'(1) = 0**: By product rule, `P'(1) = 2σ̃(1) + 2ρ̃'(1) = 2σ(1) - 2ρ'(1) = 0` (from C₁: σ(1) = ρ'(1), and reversed derivative identity ρ̃'(1) = -ρ'(1))

**P''(1) = 0**: Uses C₂ (order ≥ 3 guarantees this)

#### Step 4: Factor and define cancelled form

```lean
-- Factor P_poly = (X-1)^3 * Q_poly (or at least (X-1)^2 * P2_poly with P2_poly(1) = 0)
-- Then Gt_cancelled(w) = (w-1)*Q.eval w / (2*R.eval w)

-- Define:
let Gt_cancelled : ℂ → ℂ := fun w =>
  (w - 1) * Q_poly.eval w / (2 * R_poly.eval w)
```

#### Step 5: Prove `HasDerivAt Gt_cancelled (1/12) 1`

Using the quotient rule:

**Verified Mathlib lemma**:
```
HasDerivAt.div :
  HasDerivAt c c' x → HasDerivAt d d' x → d x ≠ 0 →
  HasDerivAt (c/d) ((c'*d x - c x*d') / d x^2) x
```

```lean
-- numerator: n(w) = (w-1) * Q.eval w
-- n(1) = 0, n'(1) = Q(1)  (product rule: 1·Q(1) + 0·Q'(1))
-- denominator: d(w) = 2 * R.eval w
-- d(1) = 2*R(1) ≠ 0
-- Gt'(1) = (Q(1)·2R(1) - 0·2R'(1)) / (2R(1))² = Q(1)/(2R(1))
```

Computing `Q(1)/(2R(1))`:
- `Q(1) = P'''(1)/6` (from `eval_iterate_derivative_rootMultiplicity`)
- `R(1) = ρ̃'(1) = -ρ'(1) = -σ(1)` (reversed derivative identity + C₁)
- `P'''(1) = -σ(1)` (from C₃ order condition)
- `Gt'(1) = (-σ(1)/6) / (2·(-σ(1))) = 1/12` ✓

**Verified Mathlib lemmas for HasDerivAt**:
```
Polynomial.hasDerivAt : HasDerivAt (fun x => eval x p) (eval x (derivative p)) x
-- (in Mathlib.Analysis.Calculus.Deriv.Polynomial, listed as Polynomial.differentiableAt_aeval)
HasDerivAt.mul : HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (f*g) (f'*g x + f x*g') x
HasDerivAt.div : quotient rule (verified above)
hasDerivAt_id : HasDerivAt id 1 x
hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
```

#### Step 6: Transfer to piecewise function

**Verified Mathlib lemma**:
```
HasDerivAt.congr_of_eventuallyEq :
  HasDerivAt f f' x → f₁ =ᶠ[𝓝 x] f → HasDerivAt f₁ f' x
```

The piecewise function and `Gt_cancelled` agree on a neighborhood of `w = 1`. Since ρ̃ is a non-identically-zero polynomial, its zeros near 1 are isolated (only at 1 itself, since ρ̃(1) = 0 and ρ̃'(1) ≠ 0). So there exists `δ > 0` such that for `w ∈ ball(1, δ) \ {1}`, `ρ̃(w) ≠ 0`, and the piecewise function equals `σ̃/ρ̃ - (w+1)/(2(1-w))` = `Gt_cancelled(w)` (algebraic identity). At `w = 1`, both equal 0. So they agree on `ball(1, δ)`.

To prove the neighborhood exists: use the fact that a nonzero polynomial has finitely many roots (`Polynomial.card_roots_le_degree` or `Set.Finite.of_surjOn`), so the roots of ρ̃ form a finite set, and there exists a ball around 1 containing no other root.

### Recommended Single-Cycle Approach for `hasDerivAt_Gtilde_one`

1. Define `ρ_rev_poly`, `σ_rev_poly` as `Polynomial ℂ`
2. Prove `eval` connection to `rhoCRev`, `sigmaCRev`
3. Factor `ρ_rev_poly = (X-1) * R_poly`, show `R_poly.eval 1 ≠ 0`
4. Build `P_poly`, show `P_poly.IsRoot 1`, `(derivative P_poly).IsRoot 1`, `(derivative (derivative P_poly)).IsRoot 1`
5. Factor out `(X-1)^2` from `P_poly` to get `P2_poly`, show `P2_poly.IsRoot 1`
6. Factor out another `(X-1)` to get `Q_poly`
7. Define `Gt_cancelled`, prove `HasDerivAt` via quotient rule
8. Compute `Q(1)/(2R(1)) = 1/12` from order conditions
9. Transfer via `congr_of_eventuallyEq`

**If short on time**: Steps 1–6 are the infrastructure. Steps 7–9 are the payoff. If you only complete 1–6, you've reduced the sorry to a well-defined computational remainder.

---

## Part 3: `continuousOn_Gtilde_closedBall` — Continuity on Closed Disk

### The Goal

```lean
theorem continuousOn_Gtilde_closedBall (m : LMM s) (p : ℕ) (hp : m.HasOrder p)
    (hp3 : 3 ≤ p) (ha : m.IsAStable) (hρ_simple : m.rhoCDeriv 1 ≠ 0) :
    ContinuousOn (fun w : ℂ => if w = 1 then (0 : ℂ) else
      m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w)))
      (closure (Metric.ball 0 1))
```

### The Fundamental Difficulty: Boundary Roots of ρ̃

**The hard problem previous cycles never resolved**: If `ρ̃(w₀) = 0` for some `|w₀| = 1` with `w₀ ≠ 1`, then:
- In Lean, `σ̃(w₀)/ρ̃(w₀) = σ̃(w₀)/0 = 0` (junk division)
- The piecewise function gives `Gt(w₀) = 0 - (w₀+1)/(2(1-w₀))` (wrong value)
- The true limit is `σ̃'(w₀)/ρ̃'(w₀) - (w₀+1)/(2(1-w₀))`
- These don't match → `Gt` is NOT continuous at `w₀`

### Resolution: Add Hypothesis or Prove No Other Unit-Circle Roots

**Option A (recommended — fastest)**: Add hypothesis to both sorry lemmas:

```lean
(hρ_no_other : ∀ w : ℂ, ‖w‖ = 1 → w ≠ 1 → m.rhoCRev w ≠ 0)
```

Then derive it in `order_ge_three_not_aStable` from A-stability + zero-stability.

**Option B**: Prove it as a standalone lemma. The argument: if `ρ(ζ₀) = 0` with `|ζ₀| = 1`, `ζ₀ ≠ 1`, then A-stability forces the perturbed root `ζ(z) ≈ ζ₀ + z·σ(ζ₀)/ρ'(ζ₀)` to stay in the disk for ALL `z` in the left half-plane. This requires `Re(e^{iφ} · σ(ζ₀)·conj(ζ₀)/ρ'(ζ₀)) ≤ 0` for all `φ ∈ [π/2, 3π/2]`, which forces `σ(ζ₀) = 0`. But even with `σ(ζ₀) = 0`, the piecewise Lean function still has the wrong junk value at `w₀ = ζ₀⁻¹`.

So **Option A is strictly necessary** unless you redefine `Gt` using the cancelled polynomial form everywhere.

### Proof with `hρ_no_other`

Once you have `hρ_no_other`, the proof uses the cancelled polynomial form from Part 2:

```lean
-- With the polynomial infrastructure from hasDerivAt_Gtilde_one:
-- Gt_cancelled(w) = (w-1)*Q.eval w / (2*R.eval w)

-- R_poly.eval w ≠ 0 on closedBall(0,1):
--   w = 1: R(1) = ρ̃'(1) ≠ 0  (zero-stability)
--   |w| < 1, w ≠ 1: ρ̃(w) ≠ 0 (A-stability), w-1 ≠ 0, so R(w) = ρ̃(w)/(w-1) ≠ 0
--   |w| = 1, w ≠ 1: ρ̃(w) ≠ 0 (hρ_no_other), w-1 ≠ 0, so R(w) ≠ 0

-- Gt_cancelled is continuous: ratio of polynomial evals with nonzero denominator
-- Use: ContinuousOn.div (Polynomial.continuous.continuousOn) (Polynomial.continuous.continuousOn)
--      (fun w hw => R_poly_ne_zero w hw)

-- Gt_cancelled = piecewise Gt on closedBall(0,1)
-- Use: ContinuousOn.congr
```

**Verified Mathlib lemmas**:
```
ContinuousOn.div : ContinuousOn f s → ContinuousOn g s → (∀ x ∈ s, g x ≠ 0) → ContinuousOn (f/g) s
ContinuousOn.congr : ContinuousOn f s → EqOn g f s → ContinuousOn g s
Polynomial.continuous : Continuous (fun x => eval x p)  (via Polynomial.differentiable)
```

### Propagating `hρ_no_other`

In `order_ge_three_not_aStable_core`, the hypothesis `hρ_no_other` needs to be added. Then in `order_ge_three_not_aStable` (line 1448), derive it from `hzs : m.IsZeroStable` and `ha : m.IsAStable`:

```lean
have hρ_no_other : ∀ w : ℂ, ‖w‖ = 1 → w ≠ 1 → m.rhoCRev w ≠ 0 := by
  -- Proof: ρ̃(w) = 0 with |w| = 1 means ρ(w⁻¹) = 0 with |w⁻¹| = 1.
  -- Combined with A-stability perturbation argument: σ(w⁻¹) = 0 too.
  -- But even if we can't prove σ = 0 here, we can prove no such w exists:
  -- For zero-stable A-stable methods of order ≥ 3, ρ has no unit-circle roots
  -- other than 1.
  sorry -- This is a separate mathematical lemma, OK to leave as sorry initially
```

---

## Part 4: Recommended Cycle Plan

### Option A: Focus on `uniformly_bounded_tupleSucc_iterates` (highest impact)

1. Prove `aeval_tupleSucc_charPoly_eq_zero` (~30 min)
2. Prove `charPoly_eval_eq_rhoC` (~15 min)
3. Prove `tupleSucc_eigenvalue_implies_rhoC_root` (~15 min)
4. Decompose main theorem into coprime splitting + 2 sub-sorrys (~30 min)
5. Write task result (~5 min)

**Net result**: 1 opaque sorry → 3 infrastructure lemmas + 2 focused sorrys

### Option B: Focus on `hasDerivAt_Gtilde_one` (most self-contained)

1. Build `ρ_rev_poly`, `σ_rev_poly` as `Polynomial ℂ` (~15 min)
2. Factor `ρ_rev_poly = (X-1)*R_poly` (~15 min)
3. Show `P_poly` has triple root at 1 (~30 min)
4. Define `Gt_cancelled`, prove `HasDerivAt` via quotient rule (~30 min)
5. Transfer to piecewise, compute `1/12` (~15 min)
6. Write task result (~5 min)

**Net result**: Close 1 sorry completely (lines 1166)

### Option C: Submit all three to Aristotle

Frame each as a standalone problem with the relevant Mathlib lemma names. This is the fastest path if the worker keeps timing out.

---

## Part 5: Key Mathlib Lemma Reference (Verified)

### Polynomial Factorization
| Lemma | Type |
|-------|------|
| `Polynomial.mul_divByMonic_eq_iff_isRoot` | `(X - C a) * (p /ₘ (X - C a)) = p ↔ p.IsRoot a` |
| `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq` | `(X - C a)^m * (p /ₘ (X - C a)^m) = p` |
| `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` | `p ≠ 0 → eval a (p /ₘ (X - C a)^m) ≠ 0` |
| `Polynomial.eval_iterate_derivative_rootMultiplicity` | Iterated derivative at root = factorial * quotient eval |

### Eigenvalue Theory
| Lemma | Type |
|-------|------|
| `Module.End.aeval_apply_of_hasEigenvector` | `HasEigenvector f μ x → aeval f p x = p.eval μ • x` |
| `Module.End.iSup_maxGenEigenspace_eq_top` | Generalized eigenspaces span V (AlgClosed + FinDim) |
| `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` | `Squarefree p ∧ aeval f p = 0 → f.IsSemisimple` |
| `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` | Semisimple → genEigenspace = eigenspace |

### Coprime Polynomial Splitting
| Lemma | Type |
|-------|------|
| `Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime` | `IsCoprime p q → ker(p(T)) ⊔ ker(q(T)) = ker((pq)(T))` |
| `Polynomial.disjoint_ker_aeval_of_isCoprime` | `IsCoprime p q → Disjoint ker(p(T)) ker(q(T))` |
| `Polynomial.sup_aeval_range_eq_top_of_isCoprime` | `IsCoprime p q → range(p(T)) ⊔ range(q(T)) = ⊤` |
| `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` | Coprime iff no common root (AlgClosed) |

### Complex Analysis / Calculus
| Lemma | Type |
|-------|------|
| `HasDerivAt.div` | Quotient rule for derivatives |
| `HasDerivAt.congr_of_eventuallyEq` | Transfer HasDerivAt across locally equal functions |
| `ContinuousOn.div` | Quotient of continuous functions (nonzero denominator) |
| `ContinuousOn.congr` | Transfer continuity via EqOn |
| `DiffContOnCl.mk` | Construct from DifferentiableOn + ContinuousOn closure |
| `Complex.norm_le_of_forall_mem_frontier_norm_le` | Maximum modulus principle |

### Convergence / Bounds
| Lemma | Type |
|-------|------|
| `tendsto_pow_const_mul_const_pow_of_abs_lt_one` | `|r| < 1 → n^k * r^n → 0` |
| `minpoly.dvd` | `aeval x p = 0 → minpoly ∣ p` |

---

## Part 6: What NOT to Do

1. **Do NOT try to compute `det(XI - companion matrix)`** for general `s`. Use `aeval T charPoly = 0` directly.
2. **Do NOT try to prove `LinearMap.charpoly tupleSucc = E.charPoly`**. The whole approach works without this.
3. **Do NOT try to prove limits of the piecewise G̃ function directly**. Use polynomial cancellation + `congr_of_eventuallyEq`.
4. **Do NOT try to build the reversed polynomial derivative infrastructure again** (cycles 29–32 did this). Use `Polynomial ℂ` objects and `divByMonic`.
5. **Do NOT spend more than 10 minutes on any single tactic step**. If stuck, leave a focused sorry and move on.
6. **Do NOT attempt all three sorrys in one cycle**. Pick one and make concrete progress.
