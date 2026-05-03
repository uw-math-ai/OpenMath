# Cycle 097 Results

## Worked on

* **Priority 0a**: Updated `.prover-state/issues/u_prime_equals_u_bridge.md`
  to reflect cycle 096's analysis — `U·u' = 𝟙` is provably **NOT
  extractable from `def:512A`**, formally closing off option (b) and
  reframing the open paths as (i)–(iii) + (a)/(c). The issue is now
  flagged as a major open problem to be addressed after Path B
  mean-ergodic infrastructure lands.

* **Priority 1**: Closed sub-lemma C of Path B for
  `exists_inverse_of_cesaro_zero` — the inner-product orthogonality
  step:

  ```
  cesaro_orthogonal_to_VT_fixed
    {V : Matrix (Fin r) (Fin r) ℝ}
    (hCes : Tendsto (fun n => (1/n) • Σ_{k<n} V^k *ᵥ w) atTop (𝓝 0))
    {u : Fin r → ℝ} (hu : V.transpose *ᵥ u = u) :
    dotProduct w u = 0
  ```

  Proof structure (~70 LOC, matches the planner's outline):
    1. Inductive helper `V.transpose ^ k *ᵥ u = u` for all `k`.
    2. Per-`k` identity `dotProduct (V^k *ᵥ w) u = dotProduct w u`
       via `dotProduct_comm` → `Matrix.dotProduct_mulVec` →
       `Matrix.mulVec_transpose` → `Matrix.transpose_pow` → step 1.
    3. Finite sum identity ⟹ `n * dotProduct w u`.
    4. Bridge `sum_dotProduct`.
    5. Bridge `smul_dotProduct` + `field_simp` cancellation.
    6. Lift via `Continuous.dotProduct` of `hCes`.
    7. Eventually-constant-then-tendsto via `Filter.tendsto_congr'`
       on `tendsto_const_nhds`.
    8. `tendsto_nhds_unique`.

  Axioms: `[propext, Classical.choice, Quot.sound]` only.

* **Priority 2**: Closed `exists_inverse_of_cesaro_zero` itself —
  the finite-dim Fredholm-alternative step:

  ```
  exists_inverse_of_cesaro_zero
    {V : Matrix (Fin r) (Fin r) ℝ}
    (_hPB : ∃ K, ∀ n, ‖V^n‖ ≤ K)
    {w : Fin r → ℝ}
    (hCes : Tendsto (fun n => (1/n) • Σ_{k<n} V^k *ᵥ w) atTop (𝓝 0)) :
    ∃ v, (1 - V) *ᵥ v = w
  ```

  Proof structure (~80 LOC):
    1. Embed `M := 1 - V` as `T : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] _`
       via `Matrix.toEuclideanLin`. Embed `w` as `w_E := WithLp.toLp 2 w`.
    2. Show `LinearMap.adjoint T = Matrix.toEuclideanLin M.transpose`
       via `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` +
       `Matrix.conjTranspose_eq_transpose_of_trivial` (over ℝ).
    3. Show `w_E ∈ (adjoint T).kerᗮ`: take `u_E ∈ ker(adjoint T)`,
       extract `u := u_E.ofLp`, derive `V.transpose *ᵥ u = u` via
       `Matrix.toEuclideanLin_apply` + `WithLp.toLp_injective` +
       `Matrix.transpose_sub` + `Matrix.transpose_one` + `sub_eq_zero`.
    4. Apply Priority 1 (`cesaro_orthogonal_to_VT_fixed`) to get
       `dotProduct w u = 0`.
    5. Bridge to `inner ℝ u_E w_E = 0` via
       `EuclideanSpace.inner_eq_star_dotProduct` + `star_trivial` over ℝ.
    6. Prove `(LinearMap.range T)ᗮ = LinearMap.ker (adjoint T)`
       directly via `LinearMap.adjoint_inner_right` + `ext_inner_left`
       (because `LinearMap.orthogonal_ker` doesn't actually exist in
       this Mathlib — only `ContinuousLinearMap.orthogonal_ker` does;
       Loogle returned a hallucinated name).
    7. `Submodule.orthogonal_orthogonal` (finite-dim has
       `HasOrthogonalProjection`) ⟹ `(adjoint T).kerᗮ = T.range`.
    8. Extract `v_E ∈ preimage` via `LinearMap.mem_range`. Set
       `v := v_E.ofLp`. Convert via `Matrix.toEuclideanLin_apply` +
       `WithLp.toLp_injective`.

  Axioms: `[propext, Classical.choice, Quot.sound]` only.

## Approach

* **Aristotle-first** (CLAUDE.md mandate): submitted three jobs at
  cycle entry (12:03 UTC):
    - Job A — `V.transpose ^ k *ᵥ u = u` (induction).
    - Job B — per-`k` identity `dotProduct (V^k *ᵥ w) u = dotProduct w u`.
    - Job C — the full orthogonality theorem (Priority 1 statement).

  Worked on Priority 0a in parallel; ran one status check after the
  manual implementations were complete (~30 min later). Job A came
  back `COMPLETE_WITH_ERRORS`; jobs B + C came back `COMPLETE`. By
  the time jobs returned, the manual implementations were already
  axiom-verified (`[propext, Classical.choice, Quot.sound]` only),
  so no need to incorporate Aristotle output. **Aristotle did not
  produce a useful artifact this cycle**, but the policy mandate was
  honored and the ONE-CHECK rule respected.

* **Manual implementation** for Priority 1 followed the planner's
  outline almost verbatim. Key Mathlib name-correction discovered
  via build feedback:
    - `Matrix.dotProduct` does NOT exist (the function is in the
      root namespace, just `dotProduct`); `Matrix.dotProduct_mulVec`
      etc DO exist (they're inside `namespace Matrix`).
    - `Matrix.zero_dotProduct`, `Matrix.smul_dotProduct`,
      `Matrix.sum_dotProduct` — all in root namespace, NOT in
      `Matrix.*`. With `open Matrix` in effect, the bare names work.

* **Manual implementation** for Priority 2 hit one Mathlib gap
  beyond the planner's outline: `LinearMap.orthogonal_ker` is NOT
  in Mathlib — Loogle returned a hallucinated name. Only the
  `ContinuousLinearMap` variant exists at
  `Adjoint.lean:182`. Worked around by proving the LinearMap
  `(range T)ᗮ = ker(adjoint T)` direction inline using
  `ext_inner_left` + `LinearMap.adjoint_inner_right`, then
  applying `Submodule.orthogonal_orthogonal` to flip.

  Side note: deprecation warning on `Matrix.toEuclideanLin_apply`
  ("use `Matrix.toLpLin_apply` instead") — the new API has a
  different generic type (`WithLp p (n → R)` instead of
  `EuclideanSpace 𝕜 n`) so it's not a drop-in replacement; left as
  warning for future cleanup.

## Result

**SUCCESS** — both Priority 1 (`cesaro_orthogonal_to_VT_fixed`) and
Priority 2 (`exists_inverse_of_cesaro_zero`) closed cleanly in one
cycle. Sorry count went from **2 → 1** (the remaining sorry is
`cesaro_residual_tendsto_zero` at line ~159, gated on the `u' = u`
bridge per `u_prime_equals_u_bridge.md`). The main theorem
`convergent_preconsistent_isConsistent` still has `sorryAx` (transitively
via `cesaro_residual_tendsto_zero`), but the only remaining gap is
that one bridge.

Files modified:
* `OpenMath/Chapter5/Section514.lean` — added 2 imports
  (`Mathlib.Topology.Instances.Matrix`,
  `Mathlib.Analysis.InnerProductSpace.Adjoint`),
  added `cesaro_orthogonal_to_VT_fixed` (private), filled in
  `exists_inverse_of_cesaro_zero` body.
* `.prover-state/issues/u_prime_equals_u_bridge.md` — Priority 0a
  rewrite to mark option (b) closed off and reframe paths.

Build status: `lake build OpenMath.Chapter5.Section514` succeeds
(2 deprecation warnings + 1 sorry warning, no errors).

## Faithfulness check

Both new sub-lemmas are pure linear-algebra helpers of the abstract
Lean-side helper `exists_inverse_of_cesaro_zero` (which is itself a
non-textbook-entity helper for thm:514A's proof). Neither corresponds
to a Butcher entity directly, so there's no `formalization_data` JSON
to compare against. No `def`, `structure`, `class`, or
textbook-named theorem was introduced.

Tautology check: ✓ (neither lemma's conclusion appears in its
hypotheses).
Identity check: ✓ (proofs are 70-80 LOC each, doing real work).
Hypothesis strength check: `_hPB` (power-boundedness) is unused in
`exists_inverse_of_cesaro_zero` — flagged as `_hPB` per planner
guidance; the hypothesis is genuinely needed for the OTHER sorry
(`cesaro_residual_tendsto_zero`), which is why it stays in the
signature.
Definition smuggling check: ✓ (no `def`s introduced).
Absent theorem check: ✓ (no comments promise content not present).

## Dead ends

* **`LinearMap.orthogonal_ker` does not exist**: Loogle returned a
  result naming this lemma in `Mathlib.Analysis.InnerProductSpace.Adjoint`,
  but the actual file only contains `ContinuousLinearMap.orthogonal_ker`
  (line 182). Worked around by writing an inline proof of
  `(range T)ᗮ = ker(adjoint T)` using `LinearMap.adjoint_inner_right`
  + `ext_inner_left`. Took ~10 LOC.

* **`Matrix.dotProduct` namespace confusion**: First build failed with
  `Unknown constant Matrix.dotProduct`. The function `dotProduct` is
  in the root namespace, not `Matrix`. Same for `zero_dotProduct`,
  `smul_dotProduct`, `sum_dotProduct`. Once corrected via global
  replace `Matrix.dotProduct → dotProduct`, the build went through.

* **`Filter.Tendsto.congr'` argument-inference issue**: The original
  `(tendsto_const_nhds (x := dotProduct w u)).congr' ?_` form failed
  because Lean couldn't infer the target function. Fixed by binding
  the `EventuallyEq` separately and using `Filter.tendsto_congr'.mp`
  on the bare `tendsto_const_nhds`.

## Discovery

* **Mathlib's `LinearMap.adjoint` exists** (in
  `Mathlib.Analysis.InnerProductSpace.Adjoint:467`, in finite-dim
  Euclidean), with full `adjoint_inner_left/right`, `adjoint_adjoint`,
  etc. — but the `LinearMap.orthogonal_ker` companion is **NOT
  present**, only the `ContinuousLinearMap` version at line 182. If
  this lemma is needed elsewhere in the project, factor out the
  ~10 LOC inline proof from `exists_inverse_of_cesaro_zero` into a
  shared helper.

* **`star_trivial`** + `Matrix.conjTranspose_eq_transpose_of_trivial`
  are the two key bridges from complex/RCLike-flavored API to ℝ for
  inner-product/adjoint work. `EuclideanSpace.inner_eq_star_dotProduct`
  has a `star`-on-the-other-component twist; over ℝ this collapses
  via `star_trivial` per-component.

* **Aristotle's batch return time was ~25 min for jobs B + C**
  (12:04→12:25 / 12:28); job A failed (`COMPLETE_WITH_ERRORS`) in
  ~10 min. The manual implementations were faster end-to-end than
  waiting for and incorporating Aristotle output.

## Suggested next approach

Cycle 098 priority list (planner's preview also says these):

1. **Pivot to `cesaro_residual_tendsto_zero`** — the last
   §514 sorry. This is gated on the `u' = u` bridge
   (`u_prime_equals_u_bridge.md`), which cycle 097 confirmed is a
   genuine major open problem. The most viable remaining options
   are (per the updated issue):

   * **(iii)** strengthen `IsConvergent` (def:512A) to expose
     stages — paralleled by the LMM `is_convergent_strengthened.md`
     issue. Requires modifying the GLM convergence definition and
     re-proving §513 + the cycle-096 partial bridge against the
     new signature. Estimated 1 cycle of plumbing.

   * **(ii)** reformulate `thm:514A`'s conclusion to use `u'`
     itself (drop the textbook `IsPreconsistent` connection in the
     witness). Smaller code change but textbook-divergence
     debt; requires a separate equivalence lemma to recover the
     textbook statement.

   * **(c)** prove preconsistency-vector uniqueness (potentially
     up to scalar) as a separate lemma. Smaller scope but still
     requires `U·u' = something extractable`, which (i) blocks.

   Recommend **(iii)** as the next cycle's target — it's the
   cleanest mathematical fix and parallels work already on the
   table.

2. If `(iii)` stalls, pivot to **§515** (`lem:515A`–`lem:515C`,
   `thm:515D`). The "stability + consistency ⇒ convergence"
   theorems are independent of `thm:514A` and may surface
   infrastructure (e.g. a cleaner GLM iterate framework) that
   simplifies `cesaro_residual_tendsto_zero` retroactively.

3. Cleanup: replace deprecated `Matrix.toEuclideanLin_apply` with
   `Matrix.toLpLin_apply` if a clean API switch is feasible (the
   new API uses `WithLp p (n → R)` instead of `EuclideanSpace`,
   and may require coercion plumbing).

4. Cleanup: extract the inline `(range T)ᗮ = ker(adjoint T)` proof
   from `exists_inverse_of_cesaro_zero` into a shared helper
   `LinearMap.orthogonal_range_eq_ker_adjoint` if used elsewhere
   (it's a reasonable "Mathlib gap" upstream candidate too).
