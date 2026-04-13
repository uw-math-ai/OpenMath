# Consultant Advice: Closing `uniformly_bounded_tupleSucc_iterates`

## Executive Summary

The sole remaining sorry in `DahlquistEquivalence.lean` (line 284) is the **spectral bound**: under zero-stability, the companion operator `tupleSucc` has uniformly bounded iterates. This is the classical result that a linear recurrence whose characteristic polynomial has all roots in the closed unit disk (with simple unit-circle roots) produces only bounded solutions.

**Three approaches are described below, in order of recommended priority.**

---

## The Sorry Statement

```lean
theorem uniformly_bounded_tupleSucc_iterates (m : LMM s) (hzs : m.IsZeroStable) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : Fin s → ℂ),
      ‖(m.toLinearRecurrence.tupleSucc^[n]) v‖ ≤ M * ‖v‖
```

**Available hypotheses** (from `hzs : m.IsZeroStable`):
- `hzs.roots_in_disk : ∀ ξ : ℂ, m.rhoC ξ = 0 → ‖ξ‖ ≤ 1`
- `hzs.unit_roots_simple : ∀ ξ : ℂ, m.rhoC ξ = 0 → ‖ξ‖ = 1 → m.rhoCDeriv ξ ≠ 0`

**Key infrastructure already proved**:
- `toLinearRecurrence` converts LMM to `LinearRecurrence ℂ`
- `tupleSucc_iterate_eq_mkSol` connects companion iteration to solutions
- `geom_sol_iff_root_charPoly` (Mathlib) connects geometric solutions to charPoly roots

---

## Part 1: The Mathematical Argument

Let T = `tupleSucc` acting on V = `Fin s → ℂ` (dimension s).

### Step A: Eigenvalues of T = roots of ρ

**Direct proof (avoids charpoly connection)**:

**Forward** (`T.HasEigenvalue μ → m.rhoC μ = 0`):
If Tv = μv with v ≠ 0, the shift structure of tupleSucc forces v_i = μ^i · v_0 (from entries 0 through s-2). Since v ≠ 0, v_0 ≠ 0. The last entry gives:
```
μ · v_{s-1} = ∑_{j<s} (-α_j) v_j = ∑_{j<s} (-α_j) μ^j v_0
```
Dividing by v_0: μ^s + ∑_{j<s} α_j μ^j = 0, i.e., ρ(μ) = 0.

**Backward** (`m.rhoC μ = 0 → T.HasEigenvalue μ`):
Define v_i = μ^i. Then Tv = μv:
- For i < s-1: (Tv)_i = v_{i+1} = μ^{i+1} = μ · v_i ✓
- For i = s-1: (Tv)_{s-1} = ∑(-α_j)μ^j = -(∑α_j μ^j - μ^s) = μ^s = μ · v_{s-1} ✓
And v ≠ 0 (v_0 = μ^0 = 1).

### Step B: The bound

By zero-stability: every eigenvalue μ satisfies |μ| ≤ 1, and unit-circle eigenvalues are simple roots of ρ (hence algebraic multiplicity 1).

**Split via coprime polynomial factoring**:
- Let p_circle = ∏_{|μ|=1, ρ(μ)=0} (X - μ) — unit-circle roots, all simple
- Let p_disk = ρ / p_circle — interior roots (all |μ| < 1)
- p_circle · p_disk = ρ, and gcd(p_circle, p_disk) = 1 (no common roots)

**By Bézout**: ∃ a, b ∈ ℂ[X] with a · p_circle + b · p_disk = 1.

**Projections**:
- P₁ = b(T) · p_disk(T) — projects onto circle eigenspaces
- P₂ = a(T) · p_circle(T) — projects onto disk eigenspaces
- P₁ + P₂ = Id (evaluating Bézout at T, using ρ(T) = 0 from Cayley-Hamilton)
- P₁ · P₂ = 0 (since p_circle · p_disk = ρ annihilates T)

**On Im(P₁)** (circle part):
- T satisfies p_circle, which is squarefree (all roots simple)
- By semisimplicity: T is diagonalizable on Im(P₁)
- All eigenvalues have |μ| = 1, so T^n is a linear combination of μ^n (bounded since |μ^n| = 1)
- ‖T^n|_{Im(P₁)}‖ ≤ C₁ for all n

**On Im(P₂)** (disk part):
- T satisfies p_disk, all roots have |μ| < 1
- Spectral radius of T|_{Im(P₂)} < 1
- By Gelfand formula: ‖T^n|_{Im(P₂)}‖^{1/n} → spectral radius < 1
- Therefore ‖T^n|_{Im(P₂)}‖ is eventually < 1, hence bounded
- ‖T^n|_{Im(P₂)}‖ ≤ C₂ for all n

**Combine**:
‖T^n v‖ = ‖T^n P₁v + T^n P₂v‖ ≤ ‖T^n P₁v‖ + ‖T^n P₂v‖ ≤ C₁ ‖P₁v‖ + C₂ ‖P₂v‖ ≤ (C₁ ‖P₁‖ + C₂ ‖P₂‖) ‖v‖

Set M = C₁ ‖P₁‖ + C₂ ‖P₂‖. ✓

---

## Part 2: Approach A — Coprime Polynomial Splitting (Recommended)

This is the most practical approach. It decomposes the proof into well-isolated sub-lemmas.

### Phase 1: Connecting charPoly to ρ

**Key infrastructure lemma**:

```lean
-- LinearRecurrence.charPoly matches rhoC up to evaluation
theorem charPoly_eval_eq_rhoC (m : LMM s) (ξ : ℂ) :
    m.toLinearRecurrence.charPoly.eval ξ = m.rhoC ξ
```

**Proof**: Both equal `ξ^s + ∑_{j<s} α_j ξ^j`. By definition:
- `charPoly = X^s - ∑_{i<s} coeffs_i · X^i = X^s - ∑_{i<s} (-α_i) · X^i = X^s + ∑_{i<s} α_i · X^i`
- `rhoC ξ = ∑_{j≤s} α_j ξ^j = α_s ξ^s + ∑_{j<s} α_j ξ^j = ξ^s + ∑_{j<s} α_j ξ^j` (since α_s = 1)

In Lean: unfold both, use `Polynomial.eval_sub`, `Polynomial.eval_monomial`, `Polynomial.eval_finset_sum`, then show the sums match via `Fin.sum_univ_castSucc`.

### Phase 2: Cayley-Hamilton for tupleSucc

The critical gap: we need `aeval tupleSucc (charPoly) = 0`, i.e., ρ(T) = 0. This is the **companion matrix Cayley-Hamilton theorem**.

**Two options**:

**Option A (use Mathlib's Cayley-Hamilton directly)**:
If we can show `LinearMap.charpoly tupleSucc = LinearRecurrence.charPoly` (as polynomials), then `LinearMap.aeval_self_charpoly` gives `aeval tupleSucc (charPoly) = 0`.

Proving `LinearMap.charpoly tupleSucc = charPoly` requires computing the determinant of (XI - companion matrix), which is standard but tedious for general s.

**Option B (prove aeval directly)**:
Show `aeval T p = 0` directly for p = charPoly, by induction on s or by showing it holds on each basis vector. For the standard basis vector e_i:
- `p(T) e_i = T^s e_i + ∑_{j<s} α_j T^j e_i`
- `T^k e_i` = e_{i+k} for i+k < s (shift), and involves the recurrence for higher indices
- The sum telescopes to 0 by the recurrence relation

This might be cleaner in Lean than the charpoly determinant approach.

**Concrete tactic sketch for Option B**:
```lean
-- Show aeval tupleSucc charPoly = 0
-- Equivalently: ∀ v, (∑ j, α_j • T^j) v = 0
-- This follows from: T^j applied to v gives state shifted by j steps,
-- and the sum ∑ α_j (state at j) = 0 by the recurrence relation.
-- Key lemma: tupleSucc_iterate_eq_mkSol gives (T^n v)_i = mkSol v (n+i)
-- The recurrence: ∑ α_j · mkSol v (n+j) = 0 (since mkSol is a solution)
```

### Phase 3: Factor ρ and construct projections

```lean
-- Factor rhoC into circle and disk parts
-- p_circle : Polynomial ℂ — product of (X - μ) for unit-circle roots
-- p_disk : Polynomial ℂ — rhoC / p_circle
-- h_factor : p_circle * p_disk = rhoC (or charPoly)
-- h_coprime : IsCoprime p_circle p_disk

-- Bézout: ∃ a b, a * p_circle + b * p_disk = 1
obtain ⟨a, b, hab⟩ := h_coprime.exists  -- or IsCoprime.exists

-- Projections
let P₁ := aeval T (b * p_disk)
let P₂ := aeval T (a * p_circle)
-- P₁ + P₂ = Id
have h_sum : P₁ + P₂ = LinearMap.id := by
  have := congr_arg (aeval T) hab
  simp [map_add, map_mul, aeval_one] at this
  exact this

-- P₁ · P₂ = 0
have h_prod : P₁.comp P₂ = 0 := by
  show aeval T (b * p_disk) ∘ₗ aeval T (a * p_circle) = 0
  rw [← map_mul]
  -- b * p_disk * a * p_circle = (a * b) * (p_circle * p_disk) = (a * b) * charPoly
  -- aeval T charPoly = 0
  sorry -- algebraic manipulation
```

**Constructing p_circle and p_disk in Lean**:

This is a key difficulty. We need to *construct* the factorization as `Polynomial ℂ` objects. Options:

**Option 1 (explicit construction for specific methods)**: For each concrete LMM, the roots are known explicitly. But we need a general proof.

**Option 2 (use Polynomial.roots)**: Mathlib's `Polynomial.roots` gives a multiset of roots. Filter by norm to get circle vs. disk roots. Then construct `p_circle = ∏ μ in circle_roots, (X - C μ)` and `p_disk = charPoly /ₘ p_circle`.

```lean
-- Get roots of charPoly
let roots := charPoly.roots  -- Multiset ℂ (with multiplicities)

-- Split into circle and disk roots
let circle_roots := roots.filter (fun μ => ‖μ‖ = 1)
let disk_roots := roots.filter (fun μ => ‖μ‖ < 1)
-- Note: by zero-stability, all roots satisfy ‖μ‖ ≤ 1, so these partition roots

-- p_circle = ∏ μ in circle_roots, (X - C μ)
let p_circle := (circle_roots.map (fun μ => Polynomial.X - Polynomial.C μ)).prod
-- p_disk similarly
```

The coprimality follows from the roots being disjoint.

**IMPORTANT**: This construction requires `charPoly.Splits` (it splits over ℂ). Since ℂ is algebraically closed and charPoly is monic, this holds via `IsAlgClosed.splits`.

### Phase 4: Bound the circle part

```lean
-- On Im(P₁): T satisfies p_circle
-- p_circle is squarefree (all unit-circle roots are simple by zero-stability)
have h_sf : Squarefree p_circle := by
  -- Each root appears once (simple by zero-stability)
  sorry

-- Restriction of T to Im(P₁) is semisimple
-- Use: Module.End.isSemisimple_of_squarefree_aeval_eq_zero
-- Need: aeval (T.restrict ...) p_circle = 0
-- And: p_circle is squarefree

-- Once semisimple: T^n on Im(P₁) is bounded
-- Use: eigenvectors span (semisimplicity), eigenvalues have |μ| = 1
-- Each eigenvector: ‖T^n v_μ‖ = |μ|^n ‖v_μ‖ = ‖v_μ‖
-- By triangle inequality + finite dimensionality: bounded
```

**Semisimple + unit eigenvalues → bounded powers**:

This sub-lemma is worth extracting:
```lean
-- Helper: semisimple operator with unit eigenvalues has bounded powers
lemma bounded_powers_of_semisimple_unit_eigenvalues
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hs : T.IsSemisimple)
    (h_unit : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖T ^ n‖ ≤ C
```

**Proof sketch**: Semisimple over ℂ + finite-dimensional → diagonalizable → T = ∑ μ P_μ where P_μ are idempotent projections summing to Id. Then T^n = ∑ μ^n P_μ. Since |μ^n| = 1 and the sum is finite:
‖T^n‖ ≤ ∑ |μ^n| ‖P_μ‖ = ∑ ‖P_μ‖ := C.

In Lean, the diagonal decomposition for a semisimple operator follows from:
- `Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace` — generalized = ordinary eigenspaces
- `Module.End.iSup_maxGenEigenspace_eq_top` — eigenspaces span V
- `Module.End.independent_maxGenEigenspace` — eigenspaces are independent

These give the direct sum decomposition V = ⊕_μ eigenspace(μ). On each eigenspace, T acts as μ·Id, so T^n acts as μ^n·Id. The projection onto each eigenspace is a continuous linear map (finite-dim), hence bounded. QED.

### Phase 5: Bound the disk part

```lean
-- On Im(P₂): all eigenvalues have |μ| < 1
-- spectral radius < 1
-- By Gelfand formula: ‖T^n‖^{1/n} → spectralRadius < 1
-- Therefore bounded

-- Helper:
lemma bounded_powers_of_spectral_radius_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →L[ℂ] V) (h : spectralRadius ℂ T < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖T ^ n‖ ≤ C
```

**Proof**: By the Gelfand formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`):
`‖T^n‖^{1/n} → spectralRadius ℂ T < 1`

So there exists N such that for all n ≥ N, `‖T^n‖^{1/n} < 1`, hence `‖T^n‖ < 1`.
For n < N, `‖T^n‖` is a finite set of values.
Set C = max({‖T^n‖ : n < N} ∪ {1}). Then ‖T^n‖ ≤ C for all n.

**Mathlib lemmas needed**:
- `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` — Gelfand formula
- `Filter.Tendsto.eventually` — eventually less than 1
- `Finset.sup` — max over finite set

**Connecting spectral radius to eigenvalue norms**:
In finite dimensions over ℂ (algebraically closed):
```
spectralRadius ℂ T = sup {‖μ‖ : μ ∈ spectrum ℂ T} = max {|μ| : μ eigenvalue of T}
```
If all eigenvalues have |μ| < 1 and the spectrum is finite (finite dim), then spectralRadius < 1.

Mathlib should have `spectrum.isCompact` in finite dimensions, plus `spectrum = eigenvalues` for finite-dimensional algebras. The key connection is:
- `Module.End.hasEigenvalue_iff_isRoot_charpoly` — eigenvalue ↔ root of charpoly
- In finite dim over algebraically closed: spectrum = eigenvalues = roots of charpoly

### Phase 6: Combine

```lean
-- ‖T^n v‖ = ‖T^n (P₁ v + P₂ v)‖
-- = ‖T^n P₁ v + T^n P₂ v‖  (since P₁, P₂ commute with T)
-- ≤ ‖T^n P₁ v‖ + ‖T^n P₂ v‖
-- ≤ C₁ ‖P₁ v‖ + C₂ ‖P₂ v‖
-- ≤ C₁ ‖P₁‖ ‖v‖ + C₂ ‖P₂‖ ‖v‖
-- = (C₁ ‖P₁‖ + C₂ ‖P₂‖) ‖v‖
-- =: M ‖v‖
```

---

## Part 3: Approach B — Generalized Eigenspace Decomposition (More Direct)

This approach uses the generalized eigenspace decomposition directly, without coprime factoring.

### Step 1: Decompose

By `Module.End.iSup_maxGenEigenspace_eq_top` (ℂ is algebraically closed, V is finite-dimensional):
```
V = ⊕_μ maxGenEigenspace(T, μ)
```

### Step 2: Connect eigenvalues to ρ-roots

Prove the eigenvector↔root correspondence (Part 1, Step A).

### Step 3: Bound on each generalized eigenspace

**Case |μ| = 1 (unit-circle eigenvalue)**:

Zero-stability gives: μ is a simple root of ρ. If we prove ρ = charpoly of T, then rootMultiplicity(μ, charpoly) = 1. This means:
- `finrank(maxGenEigenspace T μ) = 1` (the generalized eigenspace is 1-dimensional)
- On a 1-dimensional eigenspace: T acts as scalar μ
- ‖T^n v‖ = |μ|^n ‖v‖ = ‖v‖

**Why 1-dimensional**: The sum of all generalized eigenspace dimensions = dim V = s = degree of charpoly. Each generalized eigenspace has dimension ≥ 1 (since it contains the eigenspace). And the sum of root multiplicities also = s. With `independent_maxGenEigenspace` giving the direct sum, each dim ≤ its root multiplicity. For simple roots, dim = 1.

In Lean, this argument uses:
- `Module.End.independent_maxGenEigenspace` — independence
- `Module.End.iSup_maxGenEigenspace_eq_top` — spans V
- `Submodule.finrank_iSup_eq_of_independent` (or similar) — dimensions add up
- Root multiplicity 1 → generalized eigenspace dimension = 1

**Case |μ| < 1 (interior eigenvalue)**:

On `maxGenEigenspace(T, μ)`, the operator `(T - μ·Id)` is nilpotent (by `isNilpotent_restrict_genEigenspace_nat`). So (T - μ·Id)^k = 0 for some k ≤ dim(eigenspace).

Then: T^n = (μ·Id + (T - μ·Id))^n = ∑_{j=0}^{k-1} C(n,j) μ^{n-j} (T-μ·Id)^j

Each term: ‖C(n,j) μ^{n-j} (T-μ·Id)^j v‖ ≤ C(n,j) |μ|^{n-j} ‖(T-μ·Id)^j‖ ‖v‖

**Bound on C(n,j) |μ|^{n-j}** for |μ| < 1, j < k ≤ s:
- C(n,j) ≤ n^j / j!
- n^j |μ|^{n-j} = |μ|^{-j} (n |μ|)^j |μ|^n
- Since |μ| < 1: n |μ|^{n/j} → 0, so n^j |μ|^n → 0
- Therefore C(n,j) |μ|^{n-j} is bounded (continuous function of n going to 0)
- sup_n {C(n,j) |μ|^{n-j}} < ∞

**Concrete bound**: for |μ| < 1 and j ≥ 0:
sup_n n^j |μ|^n = (j / (e · ln(1/|μ|)))^j (attained at n = j/ln(1/|μ|))

This is finite. Set M_j = sup_n C(n,j) |μ|^{n-j}. Then:
‖T^n v‖ ≤ (∑_{j=0}^{k-1} M_j ‖(T-μ)^j‖) ‖v‖ on this eigenspace.

### Step 4: Combine

As in Approach A: ‖T^n v‖ ≤ ∑_μ ‖T^n P_μ v‖ ≤ M ‖v‖.

The projections P_μ : V → maxGenEigenspace(T, μ) exist as continuous linear maps in finite dimensions.

---

## Part 4: Approach C — Submit to Aristotle

The sorry statement is clean and self-contained. Frame the Aristotle submission as:

```
Prove: For a linear recurrence E : LinearRecurrence ℂ, if all roots of E.charPoly
satisfy ‖root‖ ≤ 1, and unit-circle roots are simple (rootMultiplicity = 1),
then ∃ M, ∀ n v, ‖(E.tupleSucc^[n]) v‖ ≤ M * ‖v‖.

Available Mathlib tools:
- Module.End.iSup_maxGenEigenspace_eq_top (generalized eigenspace decomposition)
- Module.End.isSemisimple_of_squarefree_aeval_eq_zero
- isNilpotent_restrict_genEigenspace_nat
- LinearMap.aeval_self_charpoly (Cayley-Hamilton)
- spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (Gelfand formula)
```

---

## Part 5: Key Mathlib Lemmas (Verified Locations)

### Eigenspace decomposition
- **`Module.End.iSup_maxGenEigenspace_eq_top`** — `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean:75`
  `[IsAlgClosed K] [FiniteDimensional K V] → ⨆ μ, f.maxGenEigenspace μ = ⊤`
- **`Module.End.independent_maxGenEigenspace`** — `Mathlib/LinearAlgebra/Eigenspace/Basic.lean:687`
  Independence of generalized eigenspaces for distinct eigenvalues
- **`Module.End.isNilpotent_restrict_genEigenspace_nat`** — `Mathlib/LinearAlgebra/Eigenspace/Basic.lean:376`
  `(f - μ • 1)` restricted to genEigenspace is nilpotent

### Eigenvalue characterization
- **`Module.End.hasEigenvalue_iff_isRoot_charpoly`** — `Mathlib/LinearAlgebra/Eigenspace/Charpoly.lean:38`
  `f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ` (IsDomain required)
- **`Module.End.exists_eigenvalue`** — existence over algebraically closed fields
- **`LinearRecurrence.geom_sol_iff_root_charPoly`** — `Mathlib/Algebra/LinearRecurrence.lean:214`
  `IsSolution (fun n => q^n) ↔ charPoly.IsRoot q`

### Semisimplicity
- **`Module.End.isSemisimple_of_squarefree_aeval_eq_zero`** — `Mathlib/LinearAlgebra/Semisimple.lean:220`
  `Squarefree p → aeval f p = 0 → f.IsSemisimple`
- **`Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace`** — `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean:56`
  Semisimple ⟹ generalized eigenspace = eigenspace

### Cayley-Hamilton
- **`LinearMap.aeval_self_charpoly`** — Cayley-Hamilton: `aeval f f.charpoly = 0`

### Spectral radius
- **`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`** — Gelfand formula
  `‖f^n‖^{1/n} → spectralRadius`

### Polynomial coprimality
- **`IsCoprime`** — `∃ a b, a * p + b * q = 1` (Bézout)
- **`Polynomial.IsCoprime.of_isCoprime_of_eval`** — coprimality from root disjointness
- **`Polynomial.roots`** — multiset of roots with multiplicities
- **`IsAlgClosed.splits`** — every polynomial splits over algebraically closed field

### Linear recurrence
- **`LinearRecurrence.charPoly`** — `X^order - ∑ coeffs_i * X^i`
- **`LinearRecurrence.charPoly_monic`** — charPoly is monic
- **`LinearRecurrence.tupleSucc`** — companion operator

---

## Part 6: Infrastructure Lemmas to Prove First

Before tackling the main theorem, prove these standalone lemmas:

### Lemma 1: Eigenvalue ↔ ρ-root correspondence

```lean
theorem hasEigenvalue_iff_rhoC_root (m : LMM s) (hs : 0 < s) (μ : ℂ) :
    (m.toLinearRecurrence.tupleSucc.toLinearMap).HasEigenvalue μ ↔ m.rhoC μ = 0 := by
  constructor
  · -- Eigenvalue → root (from shift structure of companion)
    sorry
  · -- Root → eigenvalue (construct eigenvector v_i = μ^i)
    sorry
```

### Lemma 2: charPoly evaluates to ρ

```lean
theorem charPoly_eval_eq_rhoC (m : LMM s) (ξ : ℂ) :
    m.toLinearRecurrence.charPoly.eval ξ = m.rhoC ξ := by
  simp only [LinearRecurrence.charPoly, toLinearRecurrence, rhoC]
  -- Both expand to ξ^s + ∑_{j<s} α_j ξ^j
  sorry
```

### Lemma 3: Cayley-Hamilton for tupleSucc

```lean
theorem aeval_charPoly_tupleSucc (m : LMM s) :
    Polynomial.aeval m.toLinearRecurrence.tupleSucc m.toLinearRecurrence.charPoly = 0 := by
  -- Option A: prove charpoly(tupleSucc as LinearMap) = charPoly, use aeval_self_charpoly
  -- Option B: direct verification using tupleSucc_iterate_eq_mkSol + recurrence
  sorry
```

### Lemma 4: Polynomial growth times geometric decay is bounded

```lean
-- For |r| < 1 and k : ℕ, n^k * ‖r‖^n is bounded
lemma bounded_poly_times_geom (r : ℂ) (hr : ‖r‖ < 1) (k : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, (n : ℝ)^k * ‖r‖^n ≤ C := by
  -- n^k * r^n → 0 as n → ∞ (polynomial growth vs geometric decay)
  -- A bounded sequence that converges to 0 is bounded
  sorry
```

---

## Part 7: Recommended Implementation Order

### Priority 1: Prove Lemmas 1-3 (infrastructure)

These are the foundation. Lemma 2 is likely straightforward (definitional unfolding). Lemma 1 is the most important mathematical insight. Lemma 3 is needed for Cayley-Hamilton.

**Estimated difficulty**: Medium. Main challenge is Lean bookkeeping with `Fin`, `Finset.sum`, casts.

### Priority 2: Prove the main theorem via Approach A or B

**If using Approach A** (coprime splitting):
1. Construct p_circle and p_disk from the roots
2. Show coprimality
3. Define projections via Bézout
4. Bound circle part (semisimple + unit eigenvalues)
5. Bound disk part (spectral radius < 1)
6. Combine

**If using Approach B** (generalized eigenspaces directly):
1. Decompose via `iSup_maxGenEigenspace_eq_top`
2. Show each eigenvalue is a ρ-root (Lemma 1)
3. Bound each component
4. Combine

### Priority 3: If blocked, submit to Aristotle

Frame as: "Prove uniformly_bounded_tupleSucc_iterates given the infrastructure lemmas and the Mathlib API listed above."

---

## Part 8: Alternative Simpler Approach — Direct Scalar Reduction

There's a potentially simpler approach that avoids the operator theory entirely:

**Observation**: By `tupleSucc_iterate_eq_mkSol`, the i-th component of `T^n v` equals `mkSol v (n + i)`. So we need to bound `|mkSol v (n + i)|` for all n, i.

Since `mkSol v` is a solution of the recurrence (by construction), and it has initial values v₀, ..., v_{s-1}, we need: **every solution of the scalar recurrence is bounded**.

The scalar problem: given the recurrence y_{n+s} + ∑_{j<s} α_j y_{n+j} = 0 with all roots of ρ in the closed unit disk and simple on the unit circle, show every solution is bounded.

**Key fact**: Every solution is a linear combination of generalized geometric solutions:
y(n) = ∑_{μ root of ρ} ∑_{j=0}^{m_μ-1} c_{μ,j} · C(n,j) · μ^{n-j}

where m_μ = multiplicity of μ and c_{μ,j} are determined by initial conditions.

This reduces to showing:
- For |μ| < 1: C(n,j) |μ|^{n-j} is bounded (Lemma 4)
- For |μ| = 1, m_μ = 1: |μ^n| = 1 is bounded ✓

**In Lean**: This approach requires proving the explicit solution formula for linear recurrences, which is substantial but self-contained. Mathlib's `LinearRecurrence.mkSol` might already contain some of this structure.

The advantage: no operator theory, no eigenspace decomposition, no spectral radius. Just polynomial roots and explicit bounds.

The disadvantage: proving the explicit solution formula is essentially proving a baby version of Jordan normal form for the companion matrix.

---

## Part 9: Concrete Tactic Suggestions

### For Fin/Finset sum manipulations:
```lean
-- Split sum over Fin (s+1) into Fin s + last term
rw [Fin.sum_univ_castSucc]
simp [Fin.val_castSucc, Fin.val_last, m.normalized]

-- Reindex a sum
rw [Finset.sum_bij (fun i _ => f i) ...]
-- Or use Fintype.sum_equiv
```

### For connecting polynomial evaluations:
```lean
-- Unfold polynomial evaluation
simp [Polynomial.eval_sub, Polynomial.eval_monomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
```

### For eigenvector construction:
```lean
-- Define eigenvector for companion matrix
let v : Fin s → ℂ := fun i => μ ^ (i : ℕ)
have hv_ne : v ≠ 0 := by
  intro h
  have : v ⟨0, hs⟩ = 0 := congr_fun h ⟨0, hs⟩
  simp [v] at this
```

### For the norm bound on T^n:
```lean
-- Use norm_le_pi_norm for Fin s → ℂ
calc ‖(T^[n] v) i‖ ≤ ‖T^[n] v‖ := norm_le_pi_norm _ _
   _ ≤ M * ‖v‖ := hM n v
```

---

## Part 10: What NOT to Do

1. **Do NOT try to prove Jordan normal form from scratch.** Use Mathlib's generalized eigenspace decomposition instead.

2. **Do NOT try to compute the companion matrix determinant for general s.** Use the Cayley-Hamilton theorem for linear maps instead, or prove `charPoly_eval_eq_rhoC` by evaluation.

3. **Do NOT try to bound ‖T^n‖ by induction on n using the recurrence ‖T^{n+s}‖ ≤ ∑ |α_j| ‖T^{n+j}‖.** This gives an exponentially growing bound, not a constant bound.

4. **Do NOT try to use C*-algebra or self-adjoint spectral theory.** The companion matrix is generally not normal, so the spectral theorem for normal operators doesn't apply. Use the general Gelfand formula or generalized eigenspace decomposition.

5. **Do NOT spend more than 2 cycles on this.** If blocked after Lemmas 1-3, submit to Aristotle immediately.

---

## Summary

| Approach | Difficulty | Key Mathlib Deps | Recommended? |
|----------|-----------|------------------|-------------|
| A: Coprime splitting | Medium-Hard | IsCoprime, Squarefree, spectralRadius | ✓ Primary |
| B: GenEigenspace | Hard | iSup_maxGenEigenspace_eq_top, isNilpotent | ✓ Fallback |
| C: Aristotle | Easy to submit | N/A | ✓ If blocked |
| D: Scalar reduction | Hard | Explicit solution formula | Not recommended |

**Start with**: Lemmas 1-3 (infrastructure), then Approach A phases 3-6.
