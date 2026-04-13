# Consultant Advice: Closing `uniformly_bounded_tupleSucc_iterates`

## Executive Summary

The sole remaining sorry in `DahlquistEquivalence.lean` (line 284) requires proving that under zero-stability, `‖tupleSucc^n(v)‖ ≤ M·‖v‖` uniformly in `n` and `v`. This is the classical **power-bounded operator** result for the companion matrix under the root condition.

**The critical insight previous cycles missed**: You do NOT need to prove `LinearMap.charpoly tupleSucc = E.charPoly`. Instead, proving `aeval tupleSucc E.charPoly = 0` directly (via the recurrence relation) gives everything you need. Combined with coprime polynomial factoring and Mathlib's semisimplicity infrastructure, the proof decomposes into clean, independent sub-lemmas.

---

## Part 1: Why Previous Approaches Failed

Cycles 35–37 identified three gaps:
1. **Gap 1**: Connecting `LinearRecurrence.charPoly` to `LinearMap.charpoly` for `tupleSucc`
2. **Gap 2**: From eigenvalue bounds to operator power bounds
3. **Gap 3**: Relating `IsZeroStable` (roots of `rhoC`) to eigenvalues

**The key realization**: Gap 1 is a red herring. You never need `LinearMap.charpoly tupleSucc = E.charPoly`. The proof only needs `aeval tupleSucc E.charPoly = 0`, which follows trivially from the recurrence relation. This bypasses the determinant computation for the companion matrix entirely.

---

## Part 2: The Mathematical Argument

Let `T = tupleSucc : Module.End ℂ (Fin s → ℂ)`, `V = Fin s → ℂ`.

### Step A: charPoly annihilates T

`E.charPoly = X^s - ∑_{i<s} c_i X^i`, so `charPoly(T) = T^s - ∑ c_i T^i`.

For any `v : V`, by `tupleSucc_iterate_eq_mkSol`:
```
(T^k v)(j) = mkSol v (k + j)
```

So `(charPoly(T) v)(j) = mkSol v (s + j) - ∑ c_i · mkSol v (i + j)`.

Since `mkSol v` IS a solution of the recurrence: `mkSol v (n + s) = ∑ c_i · mkSol v (n + i)` for all `n`. Taking `n = j` gives `charPoly(T) v = 0`. ∎

### Step B: charPoly.eval = rhoC

Direct computation:
```
E.charPoly.eval μ = μ^s + ∑_{i<s} α_i μ^i = rhoC μ
```

This holds because `E.coeffs i = -(α_i : ℂ)` (from `toLinearRecurrence`), so:
```
E.charPoly = X^s - ∑ (-(α_i : ℂ)) X^i = X^s + ∑ α_i X^i = rhoC (as polynomial)
```

### Step C: Eigenvalue bounds from zero-stability

If `T.HasEigenvalue μ`, then `Tv = μv` for some `v ≠ 0`. Since `charPoly(T) = 0`:
```
0 = charPoly(T) v = charPoly(μ) v = rhoC(μ) · v
```
Since `v ≠ 0`, `rhoC(μ) = 0`. By zero-stability: `‖μ‖ ≤ 1`, and if `‖μ‖ = 1` then `rhoCDeriv μ ≠ 0` (μ is a simple root).

### Step D: Coprime factoring

Factor `E.charPoly` over ℂ (using `IsAlgClosed.splits`):
```
E.charPoly = ∏_i (X - r_i)
```

Partition roots: `R_unit = {μ : ‖μ‖ = 1}`, `R_disk = {μ : ‖μ‖ < 1}`.

Define:
- `p_unit = ∏_{μ ∈ R_unit, distinct} (X - μ)` — squarefree, one factor per unit-circle root
- `p_disk = E.charPoly / p_unit` — remaining factors

Properties:
- `E.charPoly = p_unit * p_disk` (since each unit-circle root has multiplicity 1 by zero-stability)
- `p_unit` is squarefree (each root appears once)
- `IsCoprime p_unit p_disk` (no common roots: unit-circle roots ≠ disk roots)

### Step E: Projections via Bézout

By `IsCoprime.exists`: `∃ a b : ℂ[X], a * p_unit + b * p_disk = 1`.

Define:
```
P₁ = aeval T (b * p_disk)   -- projection onto unit-circle component
P₂ = aeval T (a * p_unit)   -- projection onto disk component
```

Since `aeval` is an algebra homomorphism:
- `P₁ + P₂ = aeval T 1 = id`
- `P₁ ∘ P₂ = aeval T (a * b * p_unit * p_disk) = aeval T (a * b * E.charPoly) = a(T) ∘ b(T) ∘ 0 = 0`
- `P₁² = P₁` (idempotent), `P₂² = P₂`
- `range P₁ ⊕ range P₂ = V` (internal direct sum)

### Step F: Bound on unit-circle component

On `range P₁`:
```
p_unit(T) ∘ P₁ = p_unit(T) ∘ (b * p_disk)(T) = (b * p_unit * p_disk)(T)
               = (b * charPoly)(T) = b(T) ∘ charPoly(T) = 0
```

So `aeval (T.restrict to range P₁) p_unit = 0`. Since `p_unit` is squarefree, by `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`:

**T restricted to range(P₁) is semisimple.**

By `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`: generalized eigenspaces = eigenspaces on this component. Since all eigenvalues have `‖μ‖ = 1`:

For any `v ∈ range P₁`, decompose `v = ∑ v_μ` where `T v_μ = μ v_μ`. Then:
```
T^n v = ∑ μ^n v_μ
‖T^n v‖ ≤ ∑ |μ|^n ‖v_μ‖ = ∑ ‖v_μ‖ ≤ C₁ · ‖v‖
```

where `C₁` depends only on the eigenspace projections (finite-dimensional constant).

### Step G: Bound on disk component

On `range P₂`:
```
p_disk(T) ∘ P₂ = (a * p_unit * p_disk)(T) = (a * charPoly)(T) = 0
```

All eigenvalues of `T|_{range P₂}` are roots of `p_disk`, which have `‖μ‖ < 1`.

The spectral radius of `T|_{range P₂}` is `max{‖μ‖ : μ root of p_disk} < 1`.

By the Gelfand formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`):
```
‖T^n|_{range P₂}‖^{1/n} → spectral radius < 1
```

Therefore `‖T^n|_{range P₂}‖` is eventually < 1 and hence bounded by some `C₂`.

### Step H: Combine

For any `v ∈ V`:
```
‖T^n v‖ = ‖T^n P₁ v + T^n P₂ v‖ ≤ C₁ ‖P₁ v‖ + C₂ ‖P₂ v‖
         ≤ (C₁ ‖P₁‖ + C₂ ‖P₂‖) · ‖v‖ =: M · ‖v‖
```

---

## Part 3: Concrete Sub-Lemma Decomposition

Break the proof into 6 self-contained lemmas.

### Lemma 1: `aeval_tupleSucc_charPoly_eq_zero`

```lean
lemma aeval_tupleSucc_charPoly_eq_zero (E : LinearRecurrence ℂ) :
    Polynomial.aeval E.tupleSucc E.charPoly = 0 := by
```

**Proof sketch**: `ext v; ext j; simp` reduces to showing `(T^s v)(j) = ∑ c_i (T^i v)(j)`. By `tupleSucc_iterate_eq_mkSol`, this is `mkSol v (s + j) = ∑ c_i mkSol v (i + j)`, which is `E.is_sol_mkSol v j`.

**Key Mathlib**: `LinearRecurrence.is_sol_mkSol`, `tupleSucc_iterate_eq_mkSol`, `Polynomial.aeval`, `LinearMap.ext_iff`, `funext`.

**Difficulty**: Medium. The main challenge is connecting `aeval T p` (algebra evaluation) to `T^[n]` (function iteration). Need to show `(aeval T (X^k)) v = T^[k] v`, i.e., `(T : Module.End)^k = T^[k]` as functions. This follows from `LinearMap.pow_apply` or similar.

**Critical tactic**: To evaluate `aeval T charPoly`, expand charPoly as `X^s - ∑ c_i X^i`, then use:
```lean
simp [LinearRecurrence.charPoly, map_sub, map_sum, map_mul, Polynomial.aeval_monomial]
```

Then `Polynomial.aeval_monomial` gives `aeval T (monomial k c) = c • T^k`, and `T^k` applied to `v` gives `tupleSucc^[k] v` by `Function.iterate_eq_pow` (or similar).

### Lemma 2: `charPoly_eval_eq_rhoC`

```lean
theorem charPoly_eval_eq_rhoC (m : LMM s) (μ : ℂ) :
    m.toLinearRecurrence.charPoly.eval μ = m.rhoC μ := by
```

**Proof**: Direct unfolding. Both equal `μ^s + ∑_{i<s} (α_i : ℂ) μ^i`.

```lean
  simp only [LinearRecurrence.charPoly, toLinearRecurrence, rhoC,
    Polynomial.eval_sub, Polynomial.eval_monomial, Polynomial.eval_finset_sum,
    one_mul]
  rw [Fin.sum_univ_castSucc]
  simp [m.normalized, Fin.val_castSucc, Fin.val_last]
  ring
```

### Lemma 3: `tupleSucc_eigenvalue_implies_rhoC_root`

```lean
theorem tupleSucc_eigenvalue_implies_rhoC_root (m : LMM s) (μ : ℂ)
    (hμ : m.toLinearRecurrence.tupleSucc.HasEigenvalue μ) :
    m.rhoC μ = 0 := by
```

**Proof**: From `hμ`, get eigenvector `v ≠ 0` with `T v = μ v`. Then `charPoly(T) v = charPoly(μ) · v = 0` (from Lemma 1). Since `v ≠ 0`, `charPoly(μ) = 0`. By Lemma 2, `rhoC μ = 0`.

**Key Mathlib**: `Module.End.HasEigenvalue`, `Module.End.HasEigenvector`, `Polynomial.aeval_apply_of_hasEigenvector` (may not exist directly — may need to prove that `aeval T p` applied to an eigenvector equals `p.eval μ · v`).

**Alternative**: Use `Module.End.hasEigenvalue_iff_isRoot` with `minpoly`. Since `aeval T charPoly = 0`, `minpoly ∣ charPoly`, so roots of minpoly are roots of charPoly. `hasEigenvalue_iff_isRoot` gives μ is root of minpoly, hence root of charPoly.

### Lemma 4: `bounded_poly_times_geom`

```lean
lemma bounded_poly_times_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ k * r ^ n ≤ C := by
```

**Proof**: `tendsto_pow_const_mul_const_pow_of_lt_one k hr0 hr1` gives `n^k * r^n → 0`. A convergent sequence is bounded.

**Key Mathlib**:
- `tendsto_pow_const_mul_const_pow_of_lt_one` — convergence to 0
- `Filter.Tendsto.isBounded` or extract bound from `Filter.Tendsto.eventually`
- `Metric.tendsto_atTop` gives ∀ ε, ∃ N, ∀ n ≥ N, |f n| < ε. Take ε = 1, then C = max of finitely many values and 1.

### Lemma 5: `uniformly_bounded_of_semisimple_unit_eigenvalues`

```lean
lemma uniformly_bounded_of_semisimple_unit_eigenvalues
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (hs : T.IsSemisimple)
    (h_unit : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (v : V), ‖(T ^ n) v‖ ≤ C * ‖v‖ := by
```

**Proof sketch**: Semisimple over ℂ ⟹ diagonalizable. The generalized eigenspaces = eigenspaces, and they span V. On each eigenspace, `T^n v = μ^n v`, so `‖T^n v‖ = |μ|^n ‖v‖ ≤ ‖v‖`. Combine via eigenspace projections.

**Key Mathlib**:
- `Module.End.IsSemisimple.isFinitelySemisimple` → `IsFinitelySemisimple`
- `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` → eigenspaces = generalized eigenspaces
- `Module.End.iSup_maxGenEigenspace_eq_top` — eigenspaces span V
- `Module.End.independent_maxGenEigenspace` — eigenspaces are independent
- In finite dim: independent + span V → internal direct sum → projections exist

**Difficulty**: HARD. This is the main technical challenge. Getting explicit projections with norm bounds from the abstract direct sum requires finite-dimensional linear algebra (choosing a basis from the eigenspaces, computing projection norms).

**Alternative (pragmatic)**: In finite dimensions, every sequence of linear maps `T^n` that is pointwise bounded is uniformly bounded (by Banach-Steinhaus / uniform boundedness principle). So it suffices to show: for each `v`, `sup_n ‖T^n v‖ < ∞`.

For semisimple T with unit eigenvalues and eigenvector decomposition `v = ∑ v_μ`:
```
‖T^n v‖ = ‖∑ μ^n v_μ‖ ≤ ∑ |μ|^n ‖v_μ‖ ≤ ∑ ‖v_μ‖
```
This is independent of n, so bounded. Then Banach-Steinhaus gives uniform bound.

**Mathlib for Banach-Steinhaus**: `banach_steinhaus` or `isCoercive_of_forall_le_norm` might help. In finite dim, it may be simpler to use `ContinuousLinearMap.opNorm_le_bound`.

### Lemma 6: `uniformly_bounded_of_spectral_radius_lt_one`

```lean
lemma uniformly_bounded_of_spectral_radius_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (h : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (v : V), ‖(T ^ n) v‖ ≤ C * ‖v‖ := by
```

**Proof sketch**: All eigenvalues in the open disk → spectral radius < 1 → Gelfand formula gives `‖T^n‖^{1/n} → ρ < 1` → eventually `‖T^n‖ < 1` → bounded.

**Key Mathlib**:
- `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` — Gelfand formula
- Need to convert between `Module.End` (LinearMap) and `ContinuousLinearMap` (for the normed algebra structure)
- `Module.End.hasEigenvalue_iff_mem_spectrum` — eigenvalues = spectrum (finite dim)
- In finite dim, spectrum = eigenvalues, so spectral radius = max|eigenvalue|

**Issue**: The Gelfand formula in Mathlib works for Banach algebras, using `spectralRadius` and `NNNorm`. The type `V →ₗ[ℂ] V` (Module.End) is NOT a normed algebra. Need to use `V →L[ℂ] V` (ContinuousLinearMap) instead, and convert.

In finite dimensions: `LinearMap.toContinuousLinearMap : (V →ₗ[ℂ] V) ≃ₗ (V →L[ℂ] V)` exists. The operator norm of the ContinuousLinearMap version bounds the LinearMap version.

---

## Part 4: Recommended Approach — Bypassing Most Infrastructure

The full approach above (Lemmas 1-6) requires 4-5 cycles. For a **single cycle**, here is a dramatically simpler approach:

### The "minpoly divides charPoly" shortcut

**Key observation**: We can avoid coprime factoring, Gelfand formula, and spectral radius entirely by using a more direct argument:

1. Prove `aeval T charPoly = 0` (Lemma 1)
2. Therefore `minpoly ℂ T ∣ charPoly` (since charPoly annihilates T)
3. For each eigenvalue μ: `rootMultiplicity μ (minpoly T) ≤ rootMultiplicity μ (charPoly)`
4. For unit-circle eigenvalues: `rootMultiplicity μ (charPoly) = 1` (zero-stability + Lemma 2)
5. So `rootMultiplicity μ (minpoly T) = 1` for unit-circle eigenvalues
6. The squarefree part of `minpoly T` annihilates T (it divides minpoly by construction)

Wait, step 6 doesn't work. The squarefree part of minpoly doesn't annihilate T in general.

**Better shortcut**: Construct a squarefree polynomial that annihilates T directly:

Let `q = ∏_{μ eigenvalue of T} (X - μ)` (product over distinct eigenvalues). This is squarefree by construction. Does `q` annihilate T? Only if `q ∣ minpoly T`, which is true iff `minpoly T` is squarefree. This holds iff every eigenvalue has `rootMultiplicity 1` in `minpoly T`.

From step 5: unit-circle eigenvalues have `rootMultiplicity 1` in `minpoly T`.

For disk eigenvalues: we don't know. The `rootMultiplicity` in `minpoly T` could be > 1 for disk eigenvalues.

So the squarefree approach doesn't work for the WHOLE operator, but it works for the UNIT-CIRCLE PART.

### Recommended single-cycle approach: Coprime splitting (simplified)

Here is the minimal version:

1. **Prove Lemma 1**: `aeval T charPoly = 0`
2. **Factor charPoly**: Let `S` be the set of distinct roots of `charPoly` with `‖μ‖ = 1`. Define:
   ```
   p_unit = ∏_{μ ∈ S} (X - C μ)     -- squarefree, unit circle roots only
   p_rest = charPoly / p_unit          -- remaining factors
   ```
   Since zero-stability gives multiplicity 1 for unit-circle roots, `charPoly = p_unit * p_rest`.
3. **Coprimality**: `IsCoprime p_unit p_rest` (distinct roots sets)
4. **Bézout**: Get `a, b` with `a * p_unit + b * p_rest = 1`
5. **Projections**: `P₁ = aeval T (b * p_rest)`, `P₂ = aeval T (a * p_unit)`
6. **Unit part**: `p_unit(T)|_{range P₁} = 0`, squarefree → semisimple → `T|_{range P₁}` bounded
7. **Disk part**: `p_rest(T)|_{range P₂} = 0`, all eigenvalues `|μ| < 1` → `T^n → 0` → bounded
8. **Combine**: `M = C₁ ‖P₁‖ + C₂ ‖P₂‖`

Steps 1-5 are mechanical. Steps 6-7 are where the math happens.

---

## Part 5: Key Mathlib Lemmas (Verified to Exist)

### Polynomial annihilation
- **`LinearMap.aeval_self_charpoly`**: `aeval f f.charpoly = 0` — Cayley-Hamilton for `LinearMap.charpoly`
- **`Polynomial.aeval`**: algebra homomorphism `R[X] →ₐ[R] Module.End R M`
- **`Polynomial.aeval_monomial`**: `aeval f (monomial k c) = c • f ^ k`

### Eigenvalue theory
- **`Module.End.hasEigenvalue_iff_isRoot_charpoly`**: `f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ` (for `LinearMap.charpoly`)
- **`Module.End.hasEigenvalue_iff_isRoot`**: `f.HasEigenvalue μ ↔ (minpoly K f).IsRoot μ`
- **`Module.End.iSup_maxGenEigenspace_eq_top`** `[IsAlgClosed K] [FiniteDimensional K V]`: generalized eigenspaces span V
- **`Module.End.independent_maxGenEigenspace`**: generalized eigenspaces are independent
- **`Module.End.exists_eigenvalue`** `[IsAlgClosed K] [Nontrivial V]`: eigenvalue exists

### Semisimplicity
- **`Module.End.isSemisimple_of_squarefree_aeval_eq_zero`**: `Squarefree p ∧ aeval f p = 0 → f.IsSemisimple`
- **`Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`**: semisimple → generalized = ordinary eigenspaces
- **`Module.End.IsSemisimple.isFinitelySemisimple`**: IsSemisimple → IsFinitelySemisimple

### Nilpotent / generalized eigenspace
- **`Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`**: `f - μ` nilpotent on `maxGenEigenspace μ`
- **`Module.End.isNilpotent_restrict_genEigenspace_nat`**: explicit: `(f - μ)^k = 0` on `genEigenspace μ k`

### Polynomial factoring
- **`IsAlgClosed.splits`** / **`IsAlgClosed.factors`**: every polynomial splits over ℂ
- **`Polynomial.roots`**: multiset of roots with multiplicities
- **`IsCoprime`**: `∃ a b, a * p + b * q = 1` (Bézout)

### Root multiplicity
- **`Polynomial.rootMultiplicity`**: multiplicity of a root
- **`Polynomial.dvd_iff_isRoot`**: `(X - C a) ∣ p ↔ p.IsRoot a`
- **`LinearMap.finrank_maxGenEigenspace_eq`**: `finrank(maxGenEigenspace μ) = rootMultiplicity μ (charpoly f)`

### Spectral radius / decay
- **`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`**: Gelfand formula
- **`tendsto_pow_const_mul_const_pow_of_lt_one`**: `n^k * r^n → 0` for `0 ≤ r < 1`
- **`summable_norm_pow_mul_geometric_of_norm_lt_one`**: `∑ ‖n^k * r^n‖` summable for `‖r‖ < 1` (implies bounded)

### Polynomial / minpoly
- **`minpoly.dvd`**: if `aeval f p = 0` then `minpoly K f ∣ p`
- **`minpoly.monic`**: minpoly is monic
- **`Polynomial.rootMultiplicity_le_of_dvd`**: divisibility implies multiplicity ≤

### Linear recurrence
- **`LinearRecurrence.charPoly`**: `X^s - ∑ c_i X^i`
- **`LinearRecurrence.charPoly_monic`**: charPoly is monic
- **`LinearRecurrence.geom_sol_iff_root_charPoly`**: `(IsSolution (q^·)) ↔ charPoly.IsRoot q`
- **`LinearRecurrence.tupleSucc`**: companion operator
- **`LinearRecurrence.is_sol_mkSol`**: `mkSol init` is a solution

---

## Part 6: Critical Connection — `charPoly.eval = rhoC`

This is essential and straightforward. The two polynomials are identical:

```
E.charPoly.eval μ
  = μ^s - ∑_{i<s} E.coeffs(i) · μ^i          -- definition of charPoly
  = μ^s - ∑_{i<s} (-(α_i : ℂ)) · μ^i         -- toLinearRecurrence: coeffs = -α
  = μ^s + ∑_{i<s} (α_i : ℂ) · μ^i            -- sign cancellation
  = ∑_{j≤s} (α_j : ℂ) · μ^j                  -- since α_s = 1 (normalized)
  = m.rhoC μ                                   -- definition of rhoC
```

This is a purely algebraic identity. Prove it by:
```lean
simp [LinearRecurrence.charPoly, toLinearRecurrence, rhoC, Polynomial.eval_sub,
      Polynomial.eval_monomial, Polynomial.eval_finset_sum, m.normalized]
rw [Fin.sum_univ_castSucc]; ring
```

---

## Part 7: Concrete Implementation Plan

### Phase 1 (Priority: Highest, ~1 cycle)

**Lemma 1**: `aeval_tupleSucc_charPoly_eq_zero`

This is the foundation. Everything else depends on it.

```lean
lemma aeval_tupleSucc_charPoly_eq_zero (E : LinearRecurrence ℂ) :
    Polynomial.aeval E.tupleSucc E.charPoly = 0 := by
  ext v
  simp only [LinearMap.zero_apply]
  -- Goal: (aeval E.tupleSucc E.charPoly) v = 0
  -- Expand aeval on charPoly = monomial s 1 - ∑ monomial i (coeffs i)
  simp only [LinearRecurrence.charPoly, map_sub, map_sum, Polynomial.aeval_monomial,
    one_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  -- Goal: tupleSucc^s v - ∑ coeffs(i) • tupleSucc^i v = 0
  -- Show this is zero by extensionality on Fin E.order
  ext j
  simp only [Pi.sub_apply, Pi.zero_apply, Finset.sum_apply]
  -- Use tupleSucc_iterate_eq_mkSol to convert to mkSol
  -- Then use E.is_sol_mkSol
  sorry  -- detailed proof using tupleSucc_iterate_eq_mkSol and is_sol_mkSol
```

**Key issue**: Converting between `LinearMap.pow` and `Function.iterate`. For `f : Module.End R M`:
- `(f ^ n) v = f^[n] v` as functions (need to verify this in Lean/Mathlib)
- Look for `LinearMap.pow_apply` or `Function.iterate_eq_pow`

**Lemma 2**: `charPoly_eval_eq_rhoC`

Straightforward algebraic identity, prove in the same cycle.

### Phase 2 (~1-2 cycles)

**Lemma 3**: Eigenvalue → rhoC root (using Lemmas 1-2)

**The coprime factoring infrastructure**:
- Construct `p_unit` and `p_rest` from the roots of `charPoly`
- Prove coprimality
- Construct projections

This is mostly algebraic manipulation with Mathlib's `Polynomial` API.

### Phase 3 (~1-2 cycles)

**Lemma 5**: Semisimple + unit eigenvalues → bounded (using eigenspace decomposition)
**Lemma 6**: All eigenvalues in open disk → bounded (using Gelfand or direct nilpotent+decay argument)
**Combine**: Put everything together

---

## Part 8: Alternative Simpler Approach — Direct Nilpotent Bound

Instead of the full coprime factoring, use a more direct argument:

### Observation: `minpoly T ∣ charPoly`, and charPoly = rhoC

1. `aeval T charPoly = 0` → `minpoly ℂ T ∣ charPoly`
2. Every eigenvalue μ of T is a root of `minpoly`, hence of `charPoly = rhoC`
3. By zero-stability: `‖μ‖ ≤ 1`, unit-circle μ are simple roots of charPoly
4. `rootMultiplicity μ (minpoly T) ≤ rootMultiplicity μ (charPoly) = 1` for unit-circle μ

Now use `iSup_maxGenEigenspace_eq_top` to decompose V into generalized eigenspaces.

On `maxGenEigenspace μ`:
- `T - μ` is nilpotent: `(T - μ)^d = 0` where `d ≤ finrank(maxGenEigenspace μ)`
- `T^n v = ∑_{k=0}^{d-1} C(n,k) μ^{n-k} (T-μ)^k v`

**Case |μ| = 1**: `rootMultiplicity μ (minpoly) = 1` implies `(T - μ)` restricted to `maxGenEigenspace μ` is zero. (Because: the restriction of `T` to `maxGenEigenspace μ` satisfies `(T-μ)^{rootMult} = 0` where `rootMult ≤ rootMultiplicity μ (minpoly) = 1`.) So `T v = μ v` on this eigenspace, giving `‖T^n v‖ = ‖v‖`.

Wait, I need to be more careful. `maxGenEigenspace μ = genEigenspace μ ⊤ = ⋃_k ker((T-μ)^k)`. The isNilpotent result says `(T-μ)^d = 0` on `maxGenEigenspace μ` for `d = maxGenEigenspaceIndex`. The key question is: does `rootMultiplicity μ (minpoly T) = 1` imply `d = 1`?

Yes! Here's why: the minimal polynomial of the restriction of `T` to `maxGenEigenspace μ` divides `(X - μ)^d` (nilpotent). It also divides `minpoly T` (because `minpoly T` annihilates the restriction). So it divides `gcd((X-μ)^d, minpoly T)`. Since `rootMultiplicity μ (minpoly T) = 1`, the power of `(X - μ)` in `minpoly T` is exactly 1. So `gcd((X-μ)^d, minpoly T)` has `(X - μ)^1` as its `(X - μ)` component. Therefore the minimal polynomial of the restriction divides `(X - μ)^1 = X - μ`. So `(T - μ)|_{maxGenEigenspace μ} = 0`, i.e., `T = μ · id` on this eigenspace.

**Formally**: `minpoly T` annihilates `T|_{maxGenEigenspace μ}`. If we write `minpoly T = (X - μ) · q` where `q(μ) ≠ 0`, then `0 = minpoly(T)|_{V_μ} = (T - μ) · q(T)|_{V_μ}`. Since `q(μ) ≠ 0` and all eigenvalues on `V_μ` equal `μ`, `q(T)|_{V_μ}` is invertible (because the eigenvalues of `q(T)|_{V_μ}` are `q(μ) ≠ 0`). Therefore `(T - μ)|_{V_μ} = 0`.

**Making this rigorous in Lean**: Need `Module.End.isUnit_of_forall_hasEigenvalue_ne_zero` or similar (showing that if no eigenvalue is zero, the operator is invertible). In finite dimensions over algebraically closed fields, this is equivalent to the operator being injective.

**Case |μ| < 1**: `T^n v = ∑_{k<d} C(n,k) μ^{n-k} (T-μ)^k v`. Each term has norm:
```
‖C(n,k) μ^{n-k} (T-μ)^k v‖ ≤ C(n,k) |μ|^{n-k} ‖(T-μ)^k‖ ‖v‖
```

Since `|μ| < 1` and `k < d ≤ s`: `C(n,k) |μ|^{n-k} ≤ n^k |μ|^{n-k} / k!`. The term `n^k |μ|^n / |μ|^k` is bounded by `bounded_poly_times_geom` times `|μ|^{-k}`. So each term is bounded, and there are finitely many (at most d ≤ s).

**Combining**: Use the projection from `iSup_maxGenEigenspace_eq_top`. The problem is extracting explicit projections from the abstract supremum.

In finite dimensions over an algebraically closed field with independent subspaces spanning V:
```
V = ⊕_μ maxGenEigenspace μ  (internal direct sum)
```

The projection onto each eigenspace can be constructed using the complement from the direct sum. In a normed finite-dimensional space, every subspace has a closed complement, and the projection is continuous (bounded).

**Concrete Lean approach**: Use `Submodule.isInternal_of_independent_of_iSup_eq_top` to get the internal direct sum structure, then use `DirectSum.component` or similar to get projections.

### Issue: Getting norm bounds on projections

The main obstacle in Lean is: extracting continuous (bounded) projections from an abstract direct sum decomposition and bounding their norms.

In finite dimensions, all linear maps are continuous, so the projections automatically have finite operator norm. The bound `‖P_μ‖ < ∞` follows from `Module.Finite` + `NormedSpace` + linearity.

To get a concrete bound, one approach is:
```lean
-- In finite dim, every linear map is continuous
have h := LinearMap.continuous_of_finiteDimensional (projection_μ)
-- Therefore it has finite operator norm
have := ContinuousLinearMap.opNorm_lt_top h.toContinuousLinearMap
```

But expressing the sum `‖v‖ ≤ ∑ ‖P_μ v‖ ≤ (∑ ‖P_μ‖) ‖v‖` requires working with the finite set of eigenvalues.

---

## Part 9: Recommended Single-Cycle Plan

Given the complexity, here is the most achievable plan for ONE cycle:

### Option A: Prove Lemmas 1-3 + decompose the main theorem (1 cycle)

1. Prove `aeval_tupleSucc_charPoly_eq_zero` ✓
2. Prove `charPoly_eval_eq_rhoC` ✓
3. Prove `tupleSucc_eigenvalue_implies_rhoC_root` ✓
4. Decompose `uniformly_bounded_tupleSucc_iterates` into:
   - `bounded_on_unit_eigenspaces`: T acts as scalar μ on unit-circle eigenspaces
   - `bounded_on_disk_eigenspaces`: T^n → 0 on disk eigenspaces
   - `combine_eigenspace_bounds`: using decomposition V = ⊕ V_μ

This reduces the sorry count from 1 (opaque) to 2-3 (focused, well-understood).

### Option B: Submit to Aristotle

Frame the Aristotle submission as:
```
Prove: For T : Module.End ℂ (Fin s → ℂ), if (aeval T p = 0) for a monic
polynomial p of degree s whose roots satisfy |root| ≤ 1 with simple unit-circle
roots, then ∃ M, ∀ n v, ‖T^n v‖ ≤ M * ‖v‖.

Hint: Use Module.End.iSup_maxGenEigenspace_eq_top for eigenspace decomposition,
isSemisimple_of_squarefree_aeval_eq_zero for unit-circle part,
tendsto_pow_const_mul_const_pow_of_lt_one for disk part.
```

### Option C: Accept as documented sorry

Leave the sorry with full mathematical documentation. The Dahlquist equivalence theorem is correctly formalized modulo this standard spectral theory fact. Move to Chapter 4 (stiff equations).

---

## Part 10: Concrete Tactic Suggestions

### For `aeval_tupleSucc_charPoly_eq_zero`:

The key technical challenge is converting between `aeval T (monomial k c)` and `T^[k]`:

```lean
-- aeval for monomial
have : ∀ (k : ℕ) (c : ℂ) (v : Fin E.order → ℂ),
    (Polynomial.aeval E.tupleSucc (Polynomial.monomial k c)) v =
    c • (E.tupleSucc ^ k) v := by
  intro k c v
  simp [Polynomial.aeval_monomial]

-- Power vs iterate for LinearMap
have : ∀ (k : ℕ) (v : Fin E.order → ℂ),
    (E.tupleSucc ^ k) v = E.tupleSucc^[k] v := by
  intro k v
  induction k with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp [pow_succ, LinearMap.mul_apply, Function.iterate_succ', Function.comp, ih]
```

### For eigenvalue → root:

```lean
-- If T v = μ v and p(T) = 0, then p(μ) v = 0
lemma aeval_eigenvector {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) (p : R[X]) (μ : R) (v : M)
    (hv : f v = μ • v) : (Polynomial.aeval f p) v = p.eval μ • v := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq => simp [map_add, LinearMap.add_apply, hp, hq, add_smul]
  | h_monomial n c =>
    simp [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, LinearMap.mul_apply, ih, ← smul_assoc, smul_comm, smul_assoc]
      congr 1
      rw [← hv]
      rfl  -- or ring
```

### For bounded_poly_times_geom:

```lean
lemma bounded_poly_times_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ k * r ^ n ≤ C := by
  have htend := tendsto_pow_const_mul_const_pow_of_lt_one k hr0 hr1
  -- Convergent sequences are bounded
  have hbound := Filter.Tendsto.isBounded htend
  rw [Metric.isBounded_iff_nnnorm_le] at hbound  -- or similar
  -- Extract C from the bound
  sorry -- details depend on exact Mathlib API
```

---

## Part 11: What NOT to Do

1. **Do NOT try to compute `det(XI - companion matrix)` for general s.** This is a massive determinant computation. Use `aeval T charPoly = 0` directly instead.

2. **Do NOT try to prove `LinearMap.charpoly tupleSucc = E.charPoly`.** This is equivalent to computing the determinant above. The whole approach works without this.

3. **Do NOT use the Gelfand formula for the unit-circle part.** The Gelfand formula gives asymptotic behavior (`spectralRadius = 1`), not a bound. Use semisimplicity instead.

4. **Do NOT try to prove the bound by induction on n using the recurrence.** The recurrence `‖T^{n+s}‖ ≤ ∑|c_i| ‖T^{n+i}‖` gives exponential growth, not a uniform bound.

5. **Do NOT spend more than 2 cycles on this.** If blocked after Phase 1 (Lemmas 1-3), either submit to Aristotle or accept as documented sorry and move to new material.

---

## Summary

| Phase | What to prove | Difficulty | Cycle estimate |
|-------|--------------|-----------|----------------|
| 1 | `aeval T charPoly = 0` + `eval = rhoC` + eigenvalue→root | Medium | 1 cycle |
| 2 | Coprime factoring + projections | Medium-Hard | 1-2 cycles |
| 3 | Bounded powers (semisimple + decay) | Hard | 1-2 cycles |
| 4 | Combine | Easy | 0.5 cycle |

**Start with Phase 1.** It's self-contained, provides immediate value (closes Gap 1 and Gap 3 from the issue file), and unlocks all subsequent phases.

**If Phase 1 completes quickly**, proceed to Phase 2. The coprime factoring is algebraically mechanical and well-suited to Lean's `Polynomial` API.

**If blocked**, submit to Aristotle with the Phase 1 lemmas as context, or accept as documented sorry.
