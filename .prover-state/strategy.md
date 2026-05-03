# Cycle 097 Strategy — Build Path B mean-ergodic infrastructure for `exists_inverse_of_cesaro_zero`

## Status snapshot

* `OpenMath/Chapter5/Section514.lean` has **2 sorries**:
  - Line 157 — `cesaro_residual_tendsto_zero` (gated on the
    `u' = u` bridge: see `u_prime_equals_u_bridge.md`).
  - Line 180 — `exists_inverse_of_cesaro_zero` (gated on
    finite-dim mean-ergodic infrastructure: see
    `cesaro_inverse_I_minus_V.md`).
* Cycle 096 closed half of the `u' = u` bridge
  (`convergence_witness_isVfixed`, `V·u' = u'`). The other half
  (`U·u' = 𝟙`) is **not extractable from `def:512A` directly**
  because `IsConvergent`'s conclusion only constrains `Y n n` (the
  output sequence), not the per-step internal stages `Y_i` where
  `U` actually appears in the recurrence (verified by re-reading
  `Section512.lean:89-96`).
* No pending Aristotle results.
* Sorry count must not regress (cycles 092/094/095 reverted on
  sorry-count regression; cycles 091/096 hit +2 with focused, small,
  clean wins).

## Decision: target the `exists_inverse_of_cesaro_zero` sorry, not the bridge

The supervisor explicitly directs us toward infrastructure work
when an issue reports a blocker. `cesaro_inverse_I_minus_V.md`
lays out **Path B (finite-dim mean ergodic)** as a feasible
2–3 cycle program. We start that program in cycle 097.

We do **NOT** attempt `U·u' = 𝟙` this cycle. The cycle 096 task
results' analysis (option (b) in `u_prime_equals_u_bridge.md`)
suggested a "smarter φ" approach, but `U` does not appear in the
*output* recurrence `y_seq (n+1) = h·B𝟙 + V·y_seq n` for any
choice of `f`, `y₀`, `yex`, or φ — it appears only in the
existential *stage* equation. The convergence conclusion is on
`y_seq` alone, so no choice of `(f, y₀, yex, φ)` constrains `U·u'`
through `IsConvergent`'s output. Document this in
`u_prime_equals_u_bridge.md` (Priority 0a below) and pivot.

## Mathematical plan for `exists_inverse_of_cesaro_zero`

### Goal (verbatim from `Section514.lean:170-180`)

```
exists_inverse_of_cesaro_zero {r : ℕ}
  {V : Matrix (Fin r) (Fin r) ℝ}
  (_hPB : ∃ K : ℝ, ∀ n, ‖V ^ n‖ ≤ K)
  {w : Fin r → ℝ}
  (_hCes : Filter.Tendsto
    (fun n : ℕ => (1 / (n : ℝ)) •
      (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w))
    Filter.atTop (nhds 0)) :
  ∃ v : Fin r → ℝ,
    ((1 : Matrix (Fin r) (Fin r) ℝ) - V) *ᵥ v = w
```

### Argument (Path B from the issue, expanded)

**Claim**: `w ∈ range((I - V).mulVecLin)`. Equivalently
(in finite-dim Euclidean space) `w ⊥ ker((I - V)ᵀ.mulVecLin)`.

**Step 1 — orthogonality**: For every `u` with `Vᵀ *ᵥ u = u`,
show `⟪w, u⟫ = 0` (equivalently `Matrix.dotProduct w u = 0`).

Computation: For any such `u` and any `k ≥ 0`,
```
dotProduct (V^k *ᵥ w) u = dotProduct w ((V^k)ᵀ *ᵥ u)
                        = dotProduct w ((Vᵀ)^k *ᵥ u)
                        = dotProduct w u
```
(using `Matrix.dotProduct_mulVec`, `Matrix.transpose_pow`, and
the fact that `(Vᵀ)^k · u = u` follows from `Vᵀ·u = u` by
induction on `k`).

So
```
dotProduct ((1/n) • Σ_{k<n} V^k *ᵥ w) u
  = (1/n) · Σ_{k<n} dotProduct (V^k *ᵥ w) u
  = (1/n) · (n · dotProduct w u)
  = dotProduct w u.
```
The LHS sequence tends to `dotProduct 0 u = 0` (by `hCes` and
continuity of `dotProduct · u`). Hence `dotProduct w u = 0`.

**Step 2 — bridge orthogonality to range**: In finite-dim
Euclidean space, for `T = (I - V).toEuclideanLin` (continuous
linear map),
```
range T = (ker Tᵀ_adjoint)ᗮ
```
(applying `ContinuousLinearMap.orthogonal_ker` to `T†` and using
that finite-dim subspaces are closed). Step 1 shows
`w ∈ (ker T†)ᗮ`, hence `w ∈ range T`. Extract `v`.

### Mathlib infrastructure (verified available; verify exact names with `lean_local_search` before relying)

| Goal | Lemma | File |
|---|---|---|
| Matrix adjoint = `conjTranspose` (= `transpose` over ℝ) | `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` | `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:894` |
| `range = (ker adjoint)ᗮ` (over ℝ via closure) | `ContinuousLinearMap.orthogonal_ker` | `Adjoint.lean:182` |
| `(M^k)ᵀ = (Mᵀ)^k` | `Matrix.transpose_pow` | `Mathlib/Data/Matrix/Basic.lean:911` |
| `EuclideanSpace ℝ (Fin r)` ↔ `Fin r → ℝ` | `EuclideanSpace.equiv` (linear isometry) | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:249` |
| Inner product as dot product | `EuclideanSpace.inner_eq_star_dotProduct` (or via `PiLp.inner_apply`) | `PiL2.lean` |
| `dotProduct (A *ᵥ x) y = dotProduct x (Aᵀ *ᵥ y)` | `Matrix.dotProduct_mulVec` | `LinearAlgebra/Matrix/DotProduct.lean` |
| Finite-dim subspaces are closed | `Submodule.closed_of_finiteDimensional` | std |

## Cycle 097 deliverables (in priority order)

### Priority 0 — Quick win (~10 min)

**0a.** Update `.prover-state/issues/u_prime_equals_u_bridge.md`
to record cycle 096's analysis: `U·u' = 𝟙` is provably **NOT
extractable from `def:512A`** because `U` appears only in the
existential stage equation. State the only viable paths now: (i)
prove a GLM analog of LMM's `thm:405B` (`convergent_isPreconsistent`)
by an ergodic-style argument that bypasses the stage equation —
needs invention; (ii) reformulate `thm:514A`'s conclusion to use
`u'` itself (drop the textbook `IsPreconsistent` connection in the
witness) — requires changing the textbook signature; (iii)
strengthen `IsConvergent` to also expose stages — also a textbook
deviation. Mark as a major open problem to be addressed after
Path B mean-ergodic lands.

### Priority 1 — orthogonality lemma (the core sub-lemma)

Add to `OpenMath/Chapter5/Section514.lean`, **above**
`exists_inverse_of_cesaro_zero` (around line 165):

```lean
/-- Inner-product orthogonality: under the Cesàro-zero hypothesis
on `V` and `w`, every fixed point `u` of `Vᵀ` is orthogonal
(in the dotProduct sense) to `w`. -/
private lemma cesaro_orthogonal_to_VT_fixed {r : ℕ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    {w : Fin r → ℝ}
    (hCes : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w))
      Filter.atTop (nhds 0))
    {u : Fin r → ℝ} (hu : V.transpose *ᵥ u = u) :
    Matrix.dotProduct w u = 0 := by
  sorry
```

Proof outline (worker should manualize, ~80 LOC):

1. Inductive helper `∀ k : ℕ, (V.transpose ^ k) *ᵥ u = u`.
   Use `pow_zero`/`Matrix.one_mulVec` for base case, and
   `pow_succ` + `Matrix.mulVec_mulVec` for the step. Should
   close in ~10 LOC.
2. Per-`k` identity:
   `Matrix.dotProduct ((V ^ k) *ᵥ w) u = Matrix.dotProduct w u`.
   Chain: `dotProduct (V^k *ᵥ w) u = dotProduct w ((V^k)ᵀ *ᵥ u)`
   via `Matrix.dotProduct_mulVec` (verify exact statement —
   may be `Matrix.dotProduct_mulVec` or
   `Matrix.mulVec_dotProduct`; use `lean_local_search "dotProduct
   mulVec"`). Then `(V^k)ᵀ = (Vᵀ)^k` via
   `Matrix.transpose_pow`. Then apply step 1.
3. Sum identity:
   `∑ k ∈ Finset.range n, dotProduct ((V^k) *ᵥ w) u
     = (n : ℝ) * dotProduct w u`.
   Use `Finset.sum_const` + `Finset.card_range` after rewriting
   each summand by step 2.
4. Bridge sum-into-dotProduct:
   `dotProduct (∑ k, (V^k) *ᵥ w) u = ∑ k, dotProduct ((V^k) *ᵥ w) u`
   via `Matrix.sum_dotProduct` (verify name).
5. Bridge smul-into-dotProduct:
   `dotProduct ((1/n) • s) u = (1/n) * dotProduct s u`
   via `Matrix.smul_dotProduct` (verify name).
6. Combine 3+4+5: for every `n`,
   `dotProduct ((1/n) • ∑ k, (V^k) *ᵥ w) u = dotProduct w u`
   (when `n > 0`; the `(1/n) * n = 1` cancellation is `field_simp`
   or explicit).
7. Apply `Filter.Tendsto.const_dotProduct` (or build the
   `Continuous` variant manually via
   `(continuous_id.dotProduct continuous_const).tendsto`) to lift
   `hCes` to
   `dotProduct ((1/n) • ∑ k, (V^k) *ᵥ w) u → dotProduct 0 u = 0`.
8. By `tendsto_nhds_unique` (or `tendsto_const_nhds.unique`)
   applied to step 6's eventually-constant sequence and step 7's
   convergence to 0: `dotProduct w u = 0`.

If step 7's `Continuous` lift is unfamiliar API, an explicit
proof: `dotProduct ·ᵥ u : (Fin r → ℝ) → ℝ` is a finite linear
combination of components, hence continuous. For each `n > 0`
the LHS sequence equals the constant `dotProduct w u`, and the
RHS converges to `0`. Two limits of the same eventually-constant
sequence must agree.

**Verification**: `lake env lean OpenMath/Chapter5/Section514.lean`
must succeed, and `lean_verify
OpenMath.Chapter5.Section510.cesaro_orthogonal_to_VT_fixed` must
show only `[propext, Classical.choice, Quot.sound]`.

### Priority 2 — close `exists_inverse_of_cesaro_zero`

Replace the body of `exists_inverse_of_cesaro_zero`
(`Section514.lean:170-180`):

```lean
theorem exists_inverse_of_cesaro_zero {r : ℕ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (_hPB : ∃ K : ℝ, ∀ n, ‖V ^ n‖ ≤ K)
    {w : Fin r → ℝ}
    (hCes : Filter.Tendsto ...)
    : ∃ v : Fin r → ℝ,
        ((1 : Matrix (Fin r) (Fin r) ℝ) - V) *ᵥ v = w := by
  -- See proof outline below.
  sorry
```

Proof outline (~120 LOC):

1. Set `M := (1 : Matrix _ _ ℝ) - V`. The goal becomes
   `∃ v, M *ᵥ v = w`.
2. Equivalent in `LinearMap.range` form: `w ∈ Set.range M.mulVec`.
   Bridge via `Matrix.mulVec_eq` if needed; the cleanest formal
   statement is `w ∈ LinearMap.range (Matrix.mulVecLin M)`, then
   `LinearMap.mem_range` extracts `v`.
3. To show `w ∈ LinearMap.range (Matrix.mulVecLin M)` over `ℝ`
   in finite dim, work in `EuclideanSpace ℝ (Fin r)` via
   `Matrix.toEuclideanLin M`:
   - This gives a `ContinuousLinearMap`.
   - Goal becomes `(EuclideanSpace.equiv).symm w ∈
     (Matrix.toEuclideanLin M).range`.
4. By `ContinuousLinearMap.orthogonal_ker (Matrix.toEuclideanLin M)†`,
   ```
   ((Matrix.toEuclideanLin M)†).range.topologicalClosure
     = (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ
   ```
   We want `range T = (ker T†)ᗮ`. This is **the dual statement**:
   apply `orthogonal_ker` to `T†` instead of `T`, using
   `T†.adjoint = T` (the adjoint is involutive: see
   `ContinuousLinearMap.adjoint_adjoint`):
   ```
   (LinearMap.ker T†)ᗮ = T.range.topologicalClosure = T.range
   ```
   (last step: `Submodule.closed_of_finiteDimensional` makes
   `topologicalClosure = id`).
5. Suffices: `w ⊥ ker (Matrix.toEuclideanLin M)†`. Take `u` in
   that kernel, i.e. `(Matrix.toEuclideanLin M)† u = 0`. Bridge
   to matrix form via `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`:
   the adjoint of `M.toEuclideanLin` is `M.conjTranspose.toEuclideanLin`,
   and over ℝ `conjTranspose = transpose`. So `u` satisfies
   `M.transpose *ᵥ u = 0`, i.e.
   `((1 - V).transpose) *ᵥ u = 0`. Unfold:
   `(1.transpose - V.transpose) *ᵥ u = 0`, hence
   `u - V.transpose *ᵥ u = 0`, i.e. `V.transpose *ᵥ u = u`.
6. Apply `cesaro_orthogonal_to_VT_fixed hCes hu` →
   `Matrix.dotProduct w u = 0`.
7. Bridge `dotProduct w u = 0` to
   `⟪w, u⟫_(EuclideanSpace ℝ (Fin r)) = 0` via
   `EuclideanSpace.inner_eq_star_dotProduct` (or
   `PiLp.inner_apply` and `IsROrC.star_def` over ℝ where
   `star = id`).
8. Conclude `w ∈ T.range` from step 4. Apply `LinearMap.mem_range`
   (or the `ContinuousLinearMap.mem_range` analog) to extract a
   `v_E : EuclideanSpace ℝ (Fin r)` with
   `(Matrix.toEuclideanLin M) v_E = w_E`.
9. Set `v := EuclideanSpace.equiv v_E` (transport back to
   `Fin r → ℝ`). Show `M *ᵥ v = w` by unfolding `toEuclideanLin`'s
   `mulVec`-action. This is `rfl` modulo the equiv.

**If step 4's adjoint-involution + `topologicalClosure = id`
combo is fiddly**, an alternative: use
`Submodule.eq_orthogonal_orthogonal_of_isClosed` directly,
combined with `(LinearMap.range L)ᗮ = LinearMap.ker L†` (the dual
direction of `orthogonal_ker`). The two-`ᗮ`-trick is standard.

### Priority 3 — verification + cleanup (~15 min)

* `lake env lean OpenMath/Chapter5/Section514.lean` — clean.
* `lake build OpenMath.Chapter5.Section514` — refresh `.olean`
  (per the cycle 072 stale-cache lesson).
* `lean_verify` on both new sub-lemmas:
  `OpenMath.Chapter5.Section510.cesaro_orthogonal_to_VT_fixed` and
  `OpenMath.Chapter5.Section510.exists_inverse_of_cesaro_zero` —
  axioms must be `[propext, Classical.choice, Quot.sound]` only.
* Verify the **whole §514 file** has only ONE remaining sorry
  (line ~157, `cesaro_residual_tendsto_zero`).
* If Priority 2 closes, also `lean_verify
  OpenMath.Chapter5.Section510.GeneralLinearMethod.convergent_preconsistent_isConsistent`
  to confirm the main theorem still has just the 1 cesaro_residual
  gating sorry.

## Aristotle batch (start at cycle entry, before Priority 1)

CLAUDE.md mandates Aristotle-first. Submit **three** small,
self-contained sub-lemmas to Aristotle (free compute, max ~5
jobs, 30-minute sleep, ONE check per CLAUDE.md):

* **Job A — VT power preserves fixed point**:
  ```
  ∀ {r : ℕ} {V : Matrix (Fin r) (Fin r) ℝ} {u : Fin r → ℝ},
    V.transpose *ᵥ u = u → ∀ k : ℕ, V.transpose ^ k *ᵥ u = u
  ```
  (~10 LOC; pure induction. Aristotle should one-shot this.)

* **Job B — per-`k` orthogonality (the heart of step 2)**:
  ```
  ∀ {r : ℕ} {V : Matrix (Fin r) (Fin r) ℝ} {w u : Fin r → ℝ},
    V.transpose *ᵥ u = u → ∀ k : ℕ,
      Matrix.dotProduct (V^k *ᵥ w) u = Matrix.dotProduct w u
  ```
  (~15 LOC. Tests Aristotle's premise selection on
  `Matrix.transpose_pow` + `Matrix.dotProduct_mulVec`.)

* **Job C — sum of constant**:
  ```
  ∀ {n : ℕ} (c : ℝ),
    (∑ _k ∈ Finset.range n, c) = (n : ℝ) * c
  ```
  (Trivial via `Finset.sum_const` + `Finset.card_range` +
  `nsmul_eq_mul`. Submit only if jobs A, B leave room — this
  one closes manually in 1 line.)

Submit batch via `mcp__aristotle__submit_prompt` with each job's
statement and request `[propext, Classical.choice, Quot.sound]`-only
proofs. Sleep 30 min via `Bash sleep 1800` (run in background while
working on Priority 0a). After 30 min, ONE check via
`mcp__aristotle__get_status`. Incorporate any returned proofs;
manualize the rest.

## Hypothesis adaptation rules

* `_hPB` (power-boundedness) is currently underscored (unused).
  **For Path B's argument as written, `_hPB` is genuinely
  unused** — the inner-product orthogonality argument doesn't
  need power-boundedness. Keep the underscore. (Power-boundedness
  IS needed by the OTHER sorry, `cesaro_residual_tendsto_zero`,
  which we are not touching this cycle.)
* `dotProduct` over ℝ is symmetric (`Matrix.dotProduct_comm`);
  use this if direction-of-arguments mismatches Mathlib lemma
  signatures.
* The `dotProduct ↔ inner` bridge over `EuclideanSpace ℝ (Fin r)`:
  `EuclideanSpace.inner_eq_star_dotProduct` gives
  `⟪x, y⟫ = star (dotProduct (star x) y)` or similar. Over ℝ,
  `star = id`, so `⟪x, y⟫ = dotProduct x y`. Verify exact form
  via `lean_hover_info` on the lemma.
* `Matrix.toEuclideanLin` vs `Matrix.toLin'` vs `Matrix.mulVecLin`:
  use `Matrix.toEuclideanLin` for the InnerProductSpace structure
  (it's `Matrix.toLin'` post-composed with `EuclideanSpace.equiv`).

## What NOT to try

* **Do NOT attempt `U·u' = 𝟙`**. Cycle 096's analysis confirms `U`
  is unreachable from `IsConvergent`'s output-only conclusion.
  Documented in Priority 0a.
* **Do NOT touch `cesaro_residual_tendsto_zero`** (Section514:148).
  It is gated on the `u' = u` bridge which we are NOT closing
  this cycle. Leave the sorry in place.
* **Do NOT raise `maxHeartbeats`**. The orthogonality argument is
  finite-dim and should not be slow.
* **Do NOT introduce `axiom` or `constant`**. If you hit a
  Mathlib API gap (e.g., `Submodule.closed_of_finiteDimensional`
  with the wrong typeclass), prove it as a private helper or use
  a known-equivalent lemma.
* **Do NOT modify `def:512A` (`IsConvergent`)**. The strengthening
  question is open (per `is_convergent_strengthened.md`'s parallel
  for LMMs); we are NOT addressing that this cycle.
* **Do NOT use `Mathlib.MeasureTheory.Ergodic`** — that's the
  unitary mean-ergodic theorem, which doesn't apply to general
  power-bounded `V`. Path B is finite-dim Euclidean, derived from
  scratch via the inner-product argument above.
* **Do NOT attempt a Schur or Jordan decomposition** (per the
  `jordan_canonical_form_missing.md` issue, neither is in
  Mathlib). Path B is exactly the "avoid Jordan/Schur" workaround.
* **Do NOT cherry-pick a different theorem** from `plan.md`.
  §514 is the active target; deviating will be flagged as
  strategy_deviation.
* **Do NOT poll Aristotle more than once**. CLAUDE.md is
  explicit. Submit batch → sleep 30 min → ONE check → proceed.

## Acceptance criteria

* **Sorry count must not regress**: currently **2**, must end at
  **2** or fewer. Closing only Priority 1 keeps it at 2 — that's
  a successful cycle. Closing Priorities 1 + 2 brings it to 1.
* New lemmas must have axiom check `[propext, Classical.choice,
  Quot.sound]` only.
* `lake build OpenMath.Chapter5.Section514` must succeed.
* Faithfulness check: both new lemmas are pure linear-algebra
  sub-lemmas of the abstract `exists_inverse_of_cesaro_zero`
  (which is itself a Lean-side helper, not a textbook entity), so
  no textbook entity is at risk of definition smuggling. Document
  in `task_results/cycle_097.md` per CLAUDE.md.

## Backup plan (if Priority 1 stalls > 90 min)

If the inner-product orthogonality argument hits a Mathlib API
gap (e.g., the `Continuous.dotProduct` lift is unexpectedly
non-trivial, or the smul/sum/dotProduct bridge lemmas are
named differently than expected):

1. Decompose Priority 1 into smaller `private lemma`s (one per
   step 1–8 in the outline above) and close as many as possible.
   Each closed lemma is a deliverable; even closing steps 1+2 is
   meaningful progress.
2. Skip Priority 2 for cycle 097 (defer to cycle 098).
3. Write `task_results/cycle_097.md` documenting the specific
   API gap encountered, with reproducer snippets via
   `lean_multi_attempt`, and recommend the next-cycle plan.

A cycle that lands the orthogonality lemma cleanly + scaffolds
`exists_inverse_of_cesaro_zero` (with its body still `sorry` but
the orthogonality plumbing wired up) is still a **positive**
cycle by CLAUDE.md's "minimum: decompose a sorry or write an
issue" rule.

## Suggested cycle-098 follow-up (planner preview, do NOT execute)

* Close Priority 2 of cycle 097 if it slipped.
* Once `exists_inverse_of_cesaro_zero` is fully closed, the
  remaining gating sorry is `cesaro_residual_tendsto_zero` →
  pivot to the `u' = u` bridge problem with a fresh attack.
* If the bridge stays blocked, pivot to §515 (`lem:515A`,
  `lem:515B`, `lem:515C`, `thm:515D`) — these are the
  "stability + consistency ⇒ convergence" theorems and may
  surface infrastructure that simplifies the §514 closure.
