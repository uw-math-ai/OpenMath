# Strategy — Cycle 82

## Current sorry inventory (5 total)

| # | File | Line | Theorem | Status |
|---|------|------|---------|--------|
| 1 | DahlquistEquivalence.lean | 405 | `tupleSucc_eq_smul_on_unit_eigenspace` | **THIS CYCLE** |
| 2 | DahlquistEquivalence.lean | 413 | `tupleSucc_pow_bounded_on_disk_eigenspace` | **THIS CYCLE** |
| 3 | DahlquistEquivalence.lean | 454 | `uniformly_bounded_tupleSucc_iterates` (tail) | THIS CYCLE if 1+2 close |
| 4 | MultistepMethods.lean | 1241 | `hasDerivAt_Gtilde_one` | Do NOT touch |
| 5 | MultistepMethods.lean | 1258 | `continuousOn_Gtilde_closedBall` | Do NOT touch |

## Infrastructure already proved (from cycles 78+81)

These are in `DahlquistEquivalence.lean` and available for use:

- `aeval_tupleSucc_charPoly_eq_zero` — charPoly annihilates tupleSucc
- `charPoly_eval_eq_rhoC` — charPoly.eval = rhoC
- `tupleSucc_eigenvalue_is_rhoC_root` — eigenvalue → ρ-root
- `charPoly_derivative_eval_eq_rhoCDeriv` — derivative connection
- `charPoly_rootMultiplicity_of_unit_root` — unit-circle roots are simple in charPoly
- `tupleSucc_minpoly_rootMultiplicity_eq_one_of_unit_eigenvalue` — rootMult μ (minpoly ℂ T) = 1 for unit-circle eigenvalues
- `bounded_pow_geom_decay` — n^k * r^n is bounded for r < 1
- Inside `uniformly_bounded_tupleSucc_iterates` (s > 0 branch): `h_eigbound`, `h_mp_dvd`, `h_decomp` already established

## PHASE 0: Check Aristotle results (first 5 minutes)

Five Aristotle jobs from cycle 81 are IN_PROGRESS (7–14% at last check). Check their status:

```
65e4e237  — tupleSucc_eq_smul_on_unit_eigenspace
668684f8  — tupleSucc_pow_bounded_on_disk_eigenspace
9b831aee  — uniformly_bounded_tupleSucc_iterates
b9b81468  — minpoly/restriction route for unit eigenspace
4d573da6  — final combination step
```

**Action:** Call `mcp__aristotle__get_status` on each. If any are COMPLETE, download with `mcp__aristotle__download_result` and `mcp__aristotle__extract_result`, then incorporate the proof. If still IN_PROGRESS, continue to Phase 1 and re-check after 30 minutes.

Also try downloading these older completed results that previously failed:
- `086b0ae4` (main theorem, from cycle 78)
- `32aa0177` (sdirk3_poly_ineq)

## PHASE 1: Prove `tupleSucc_eq_smul_on_unit_eigenspace` (line 405)

### Goal

```lean
private lemma tupleSucc_eq_smul_on_unit_eigenspace
    (m : LMM s) (hzs : m.IsZeroStable) (μ : ℂ) (hroot : m.rhoC μ = 0) (hunit : ‖μ‖ = 1)
    (v : Module.End.maxGenEigenspace m.toLinearRecurrence.tupleSucc μ) :
    m.toLinearRecurrence.tupleSucc v = μ • v
```

### Approach: minpoly coprime factoring

The proof has three steps:

**Step 1: Factor minpoly at μ.**

We have `rootMult μ (minpoly ℂ T) = 1` (from `tupleSucc_minpoly_rootMultiplicity_eq_one_of_unit_eigenvalue`). So:
- `(X - C μ) ∣ minpoly ℂ T` (μ is a root)
- `(X - C μ)² ∤ minpoly ℂ T` (rootMult = 1)

Define `q := minpoly ℂ T /ₘ (X - C μ)`. Then `minpoly ℂ T = (X - C μ) * q` and `q.eval μ ≠ 0`.

Use: `Polynomial.mul_divByMonic_eq_iff_isRoot` to get the factoring. Use `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` to get `q(μ) ≠ 0`.

**Step 2: Show `Polynomial.aeval T q` is injective on `maxGenEigenspace T μ`.**

Since `q(μ) ≠ 0` and `X - C μ` is irreducible (degree 1), `IsCoprime (X - C μ) q`. Use:

```
Polynomial.isCoprime_of_isUnit_of_isUnit  -- or derive from EuclideanDomain
```

Or more directly: `X - C μ` is irreducible, and `(X - C μ) ∤ q` (since `q(μ) ≠ 0`), so they're coprime.

Then use `Polynomial.disjoint_ker_aeval_of_isCoprime` to get:
```
Disjoint (ker (aeval T (X - C μ))) (ker (aeval T q))
```

Since `maxGenEigenspace T μ ⊆ ker (aeval T (X - C μ)^k)` for large k, and `ker (aeval T (X - C μ)^k) ∩ ker (aeval T q)` is contained in `ker(aeval T ((X - C μ)^k * q))`. But `(X - C μ)^k * q` is divisible by `(X - C μ) * q = minpoly`, which annihilates T, so the kernel is everything... Hmm, this doesn't directly give disjointness.

**Better approach for Step 2:** Use the direct argument:

`minpoly(T) = (T - μ) ∘ q(T) = 0` on all of V. So `range(q(T)) ⊆ ker(T - μ) = eigenspace(T, μ)`.

For `v ∈ maxGenEigenspace T μ` with `q(T) v = 0`: v is in both `maxGenEigenspace T μ` AND `ker(q(T))`. But `IsCoprime (X - C μ) q` gives `Disjoint (ker(aeval T (X - C μ))) (ker(aeval T q))`. And `maxGenEigenspace T μ = ⨆_k ker((T-μ)^k)`. Since each `ker((T-μ)^k)` is disjoint from `ker(q(T))` (by IsCoprime of `(X-C μ)^k` and `q`, which holds since they share no roots), we get `maxGenEigenspace T μ` is disjoint from `ker(q(T))`.

Actually, the cleanest way: `IsCoprime ((X - C μ)^k) q` for any k (since X - C μ is irreducible and doesn't divide q). Then `disjoint_ker_aeval_of_isCoprime` gives `Disjoint (ker(aeval T (X-Cμ)^k)) (ker(aeval T q))`. Taking the sup over k: `maxGenEigenspace T μ` is disjoint from `ker(aeval T q)`.

So `q(T)` is injective on `maxGenEigenspace T μ`.

**Step 3: Conclude T = μ on maxGenEigenspace.**

For any `v ∈ maxGenEigenspace T μ`:
- `(T - μ)(q(T) v) = minpoly(T) v = 0` (since minpoly annihilates T)
- `q(T) v ∈ maxGenEigenspace T μ` (since `maxGenEigenspace` is T-invariant, hence q(T)-invariant)
- Wait — we need `q(T) v` to be in `maxGenEigenspace T μ`, not just in V.

Actually, `maxGenEigenspace T μ` IS `T`-invariant (it's an invariant subspace for T). So `q(T)` maps `maxGenEigenspace T μ` to itself. And `q(T)` is injective there (Step 2). Since `maxGenEigenspace` is finite-dimensional, `q(T)` is bijective on it.

Now: for any `w ∈ maxGenEigenspace T μ`, there exists `v` with `q(T) v = w` (surjectivity). Then `(T - μ) w = (T - μ)(q(T) v) = 0`. So `T w = μ w`.

### Concrete Lean sketch

```lean
private lemma tupleSucc_eq_smul_on_unit_eigenspace
    (m : LMM s) (hzs : m.IsZeroStable) (μ : ℂ) (hroot : m.rhoC μ = 0) (hunit : ‖μ‖ = 1)
    (v : Module.End.maxGenEigenspace m.toLinearRecurrence.tupleSucc μ) :
    m.toLinearRecurrence.tupleSucc v = μ • v := by
  set T := m.toLinearRecurrence.tupleSucc
  -- Step 1: Get HasEigenvalue (needed for the minpoly helper)
  have hμ_eig : T.HasEigenvalue μ := by
    -- v is in maxGenEigenspace, so μ is an eigenvalue (if v ≠ 0)
    -- Or: derive from hroot using the converse of tupleSucc_eigenvalue_is_rhoC_root
    sorry -- may need to construct an eigenvector from hroot
  -- Step 2: rootMult μ (minpoly ℂ T) = 1
  have hrm := tupleSucc_minpoly_rootMultiplicity_eq_one_of_unit_eigenvalue m hzs μ hμ_eig hunit
  -- Step 3: Factor minpoly = (X - C μ) * q with q(μ) ≠ 0
  let mp := minpoly ℂ T
  have hmp_root : mp.IsRoot μ := Module.End.isRoot_of_hasEigenvalue hμ_eig
  let q := mp /ₘ (Polynomial.X - Polynomial.C μ)
  have hmp_factor : (Polynomial.X - Polynomial.C μ) * q = mp :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot _).mpr hmp_root
  -- q(μ) ≠ 0 (from rootMult = 1)
  have hq_ne : q.eval μ ≠ 0 := by
    -- Use Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
    -- after showing rootMult = 1 means q = mp /ₘ (X - C μ)^1
    sorry
  -- Step 4: (T - μ) ∘ q(T) = 0 (from minpoly annihilation)
  have h_annihilate : (T - algebraMap ℂ _ μ) ∘ₗ (Polynomial.aeval T q) = 0 := by
    -- minpoly(T) = 0, and minpoly = (X - C μ) * q
    -- aeval T minpoly = aeval T ((X - C μ) * q) = (T - μ) ∘ q(T) = 0
    sorry
  -- Step 5: q(T) injective on maxGenEigenspace T μ
  -- (because IsCoprime (X - C μ)^k q for each k, giving disjointness)
  -- Step 6: q(T) surjective on maxGenEigenspace (finite-dim + injective)
  -- Step 7: For any w ∈ maxGenEigenspace, w = q(T) v' for some v',
  --         so (T - μ) w = (T - μ)(q(T) v') = 0
  sorry
```

### Alternative simpler approach (try this FIRST)

Instead of the coprime factoring, use the following observation directly:

Since `v ∈ maxGenEigenspace T μ`, there exists `k` such that `(T - μ)^k v = 0`. The smallest such k is the nilpotency order at v. If we can show `k = 1` for all v, we're done (because `(T - μ)^1 v = 0` means `T v = μ v`).

**Claim**: `(T - μ)^1 = 0` on `maxGenEigenspace T μ`.

**Proof**: `minpoly ℂ T = (X - C μ) * q` with `q(μ) ≠ 0`. Apply `aeval T` to both sides: `0 = (T - μ) ∘ q(T)`. Now `q(T)` restricted to `maxGenEigenspace T μ` is an endomorphism. If we show it's injective (hence bijective in finite dim), then `(T - μ) = 0` on the range of `q(T)|_{V_μ}` = all of `V_μ`.

To show injectivity of `q(T)|_{V_μ}`: suppose `q(T) v = 0` for `v ∈ V_μ`. Since `v ∈ V_μ = maxGenEigenspace T μ`, also `(T - μ)^k v = 0` for some k. So v is in `ker((T-μ)^k) ∩ ker(q(T))`. But `IsCoprime ((X-Cμ)^k, q)` (because they share no roots: `(X-Cμ)^k` has only μ as root, `q(μ) ≠ 0`). By `Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`: `ker((T-μ)^k) ⊕ ker(q(T)) ↪ ker((T-μ)^k * q(T))`. Disjointness gives `ker((T-μ)^k) ∩ ker(q(T)) = 0`, so v = 0.

### Key Mathlib lemmas to use

- `Polynomial.mul_divByMonic_eq_iff_isRoot` — factor out root
- `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` — quotient nonzero
- `Polynomial.IsCoprime` — for the coprime argument
- `Polynomial.disjoint_ker_aeval_of_isCoprime` — disjoint kernels
- `Module.End.isRoot_of_hasEigenvalue` — eigenvalue is root of minpoly
- `minpoly.aeval` — `aeval T (minpoly ℂ T) = 0`
- `Submodule.eq_bot_iff` — for v = 0 from intersection = 0
- For the `IsCoprime` proof: `X - C μ` is irreducible (degree 1 polynomial over a field), `q(μ) ≠ 0` means `(X - C μ) ∤ q`, so `IsCoprime`. Use `EuclideanDomain.isCoprime_of_dvd` or `Polynomial.isCoprime_of_isUnit_of_isUnit`.

### How to get `HasEigenvalue T μ` from `hroot : rhoC μ = 0`

The sorry lemma takes `hroot` but needs `HasEigenvalue` for the minpoly helper. Two options:

**Option A**: Change the lemma signature to take `HasEigenvalue` directly instead of `hroot`. This is cleaner since the caller (`uniformly_bounded_tupleSucc_iterates`) can derive it from `hroot`.

**Option B**: Construct an eigenvector from `hroot`. Since `rhoC μ = 0` means `charPoly.eval μ = 0`, and `charPoly = minpoly * q` (up to associates), μ is a root of charPoly. The vector `v = (1, μ, μ², ..., μ^{s-1})` is an eigenvector of the companion matrix with eigenvalue μ (standard result). Define this vector explicitly and verify `T v = μ v` by checking each component.

**Recommendation**: Use Option A — modify the signature to take `HasEigenvalue` directly. The `hroot` argument is redundant given `HasEigenvalue` (by `tupleSucc_eigenvalue_is_rhoC_root`).

## PHASE 2: Prove `tupleSucc_pow_bounded_on_disk_eigenspace` (line 413)

### Goal

```lean
private lemma tupleSucc_pow_bounded_on_disk_eigenspace
    (m : LMM s) (hzs : m.IsZeroStable) (μ : ℂ) (hroot : m.rhoC μ = 0) (hdisk : ‖μ‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ)
      (v : Module.End.maxGenEigenspace m.toLinearRecurrence.tupleSucc μ),
      ‖(m.toLinearRecurrence.tupleSucc ^ n) v‖ ≤ C * ‖v‖
```

### Approach: Nilpotent binomial expansion + geometric decay

On `maxGenEigenspace T μ`, `N := T - algebraMap ℂ _ μ` is nilpotent: `N^d = 0` for some `d`. Then:

```
T^n = (μ + N)^n = ∑_{k=0}^{d-1} C(n,k) μ^{n-k} N^k
```

For each term:
```
‖C(n,k) μ^{n-k} N^k v‖ ≤ C(n,k) ‖μ‖^{n-k} ‖N^k‖ ‖v‖
                        ≤ n^k ‖μ‖^{n-k} ‖N^k‖ ‖v‖
                        = (n^k ‖μ‖^n / ‖μ‖^k) ‖N^k‖ ‖v‖
```

Since `‖μ‖ < 1`, `n^k ‖μ‖^n` is bounded by `bounded_pow_geom_decay` (already proved). And `‖N^k‖ / ‖μ‖^k` is a constant (k < d ≤ s, so finitely many terms).

Sum over k = 0, ..., d-1: total bound is a finite sum of bounded terms.

### Key Lean challenges

1. **Getting the nilpotency**: Use `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` to get `IsNilpotent N`. Extract `d` from `IsNilpotent.eq_pow_zero_of_pow_eq_zero` or similar.

2. **Binomial expansion for non-commutative ring**: `T = μ·1 + N` where `μ·1` and `N` commute (they're both polynomials in T). Use `Commute.add_pow` from Mathlib.

3. **Norm bounds**: Triangle inequality on the finite sum, then `bounded_pow_geom_decay` for each term.

4. **Type coercions**: `v` has type `maxGenEigenspace T μ` (subtype). Need to carefully handle coercions between submodule elements and ambient vectors.

### Lean sketch

```lean
-- Get nilpotent N = (T - μ) restricted to maxGenEigenspace
have hN : IsNilpotent ((T - algebraMap ℂ _ μ).restrict h_inv) :=
  Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap T μ
obtain ⟨d, hd⟩ := hN
-- Binomial: T^n = Σ C(n,k) μ^{n-k} N^k
-- Bound each term using bounded_pow_geom_decay
-- Sum finitely many bounded terms
```

## PHASE 3: Prove the combination step (line 454)

This is the hardest sorry. Only attempt if Phases 1 and 2 are done.

The goal: combine per-eigenspace bounds with `iSup_maxGenEigenspace_eq_top` to get a global bound.

### Approach

The abstract direct sum `V = ⨆ μ, maxGenEigenspace T μ` gives:
- For each v, there exist projections v = Σ v_μ with v_μ ∈ maxGenEigenspace T μ
- `‖T^n v‖ ≤ Σ_μ ‖T^n v_μ‖ ≤ Σ_μ C_μ ‖v_μ‖ ≤ (Σ C_μ ‖π_μ‖) ‖v‖`

**The main obstacle**: extracting norm-bounded projections from the abstract supremum.

In finite dimensions, the eigenspace decomposition gives continuous projections. Use:
- `Submodule.isInternal` from `independent_maxGenEigenspace` + `iSup_maxGenEigenspace_eq_top`
- `DirectSum.IsInternal.submodule_iSup_eq_top` → projections exist
- In `FiniteDimensional`, all linear maps are continuous, so projections are bounded

**If this is too hard**: Leave as a focused sorry with `tupleSucc_eq_smul_on_unit_eigenspace` and `tupleSucc_pow_bounded_on_disk_eigenspace` proved. This is still progress (3 sorrys → 1 sorry in DahlquistEquivalence).

## What NOT to try

- **Do NOT touch MultistepMethods.lean** — the Dahlquist barrier sorrys (lines 1241, 1258) need dedicated polynomial-algebra infrastructure that is orthogonal to this cycle's work
- **Do NOT compute `det(XI - companion matrix)`** or prove `LinearMap.charpoly = charPoly` — not needed
- **Do NOT use Gelfand formula** for the unit-circle eigenvalue bound — use minpoly + coprime instead
- **Do NOT try induction on n** using the recurrence — gives exponential, not constant, bound
- **Do NOT spend more than 15 minutes on any single tactic** — leave a focused sorry and move on
- **Do NOT repeat the approaches from cycles 35-43** (charpoly matching, determinant computation)
- **Do NOT try to build the full Jordan normal form** — the coprime/nilpotent approach is sufficient

## Mandatory deliverables

1. Check all 5 Aristotle jobs (and re-check after 30 min if still running)
2. Close at least `tupleSucc_eq_smul_on_unit_eigenspace` (sorry #1)
3. All modified files verified with `lake env lean OpenMath/DahlquistEquivalence.lean`
4. Task result written to `.prover-state/task_results/cycle_082.md`
5. Commit and push

## Rules reminder

- Sorry-first: write full structure with sorry, verify compilation, then close
- Aristotle-first: check the 5 in-progress jobs, sleep 30 min, check again
- Do NOT increase maxHeartbeats above 200000
- A cycle with zero changes is UNACCEPTABLE
- Prefer `lake env lean OpenMath/DahlquistEquivalence.lean` over `lake build`
