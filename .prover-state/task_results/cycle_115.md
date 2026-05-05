# Cycle 115 Results

## Worked on

`OpenMath/Chapter5/Section515.lean` — Phase 1 of Solution A: localize the
`M_bound` hypothesis in the `localStepError_bound` helper chain. This refactor
unblocks cycle 116's planned strengthening of `GeneralLinearMethod.IsConvergent`
in `Section512.lean` by making the helper-chain compatible with §514's
`yex = id` consumer (`id` IS bounded on a compact interval but not globally).

## Approach

Steps 1–3 fully landed; Step 4 deferred per strategy backup plan (capstone
keeps global hypothesis, derives localized forms inline). Plus an additional
"Step 2b" for `aux_T3'_bound` which the strategy didn't explicitly list but
which had to be refactored as a transitive consumer of `aux_y_diff_norm_bound`.

### Step 1 (`aux_y_diff_norm_bound`, line 129–187)

Replaced `(hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)` with
`(hf_y_bound : ∀ t ∈ Set.uIoc x (x + h * ξ), |f (y t)| ≤ L * M_bound)`.
Reordered parameters so `(x h hh ξ)` are introduced before `hf_y_bound`
(the bound now depends on them). Updated the internal `hC` block to consume
the membership directly (one-line change: drop the `_` for `ht`, pass it
to `hf_y_bound`).

### Step 2 (`aux_T3_bound`, line 296)

Replaced global `hf_y_bound` with
`(hf_y_bound : ∀ t ∈ Set.uIcc x (x + h * c_i), |f (y t)| ≤ L * M_bound)`.
At the `aux_y_diff_norm_bound` call site (formerly line 320), inserted
inclusion `Set.uIcc x (x + h * ξ) ⊆ Set.uIcc x (x + h * c_i)` (proved via
`Set.uIcc_of_le` + `Set.Icc_subset_Icc_right` + `nlinarith`) and used
`Set.uIoc_subset_uIcc` to bridge `uIoc → uIcc`.

### Step 2 (`aux_T4_bound`, line 384)

Replaced global `hf_y_bound` with the per-`j` form
`(hf_y_bound : ∀ j : Fin s, ∀ t ∈ Set.uIcc x (x + h * c j), |f (y t)| ≤ L * M_bound)`.
At the `aux_y_diff_norm_bound` call site (formerly line 415), invoked
`hf_y_bound j` and applied `Set.uIoc_subset_uIcc` to get the per-`ξ`
form needed by Step 1.

### Step 2b (`aux_T3'_bound`, line 470 — not in strategy)

Discovered as a transitive consumer of `aux_y_diff_norm_bound`. Refactored
similarly to take
`(hf_y_bound : ∀ t ∈ Set.uIcc x (x + h), |f (y t)| ≤ L * M_bound)`.
The internal `aux_y_diff_norm_bound` invocation is at `ξ = 1`, so the
relevant interval is `Set.uIoc x (x + h * 1) = Set.uIoc x (x + h)`; bridged
via `ring_nf` rewriting plus `Set.uIoc_subset_uIcc`.

### Step 3 (`localStageError_bound_a`, line 580–667)

Replaced `(_hy_M : ∀ t, |yex t| ≤ M_bound)` and
`(_hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)` with the per-`j` localized forms
```
(_hy_M_local  : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j), |yex t| ≤ M_bound)
(_hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j), |deriv yex t| ≤ L * M_bound)
```
positioned after `_hc_def` (since they reference `c`). Updated the `hf_yex_bound`
derivation to per-`j` form (one-line: introduce `j t ht`, apply pointwise).
T3 invocation passes `hf_yex_bound i` (since `aux_T3_bound`'s `c_i` matches
this stage's `c i`); T4 invocation passes the full per-`j` `hf_yex_bound`.

### Step 3 (`localStageError_bound_b`, line 711–820)

Same per-`j` localization as `_a`, PLUS additional endpoint hypotheses needed
because the b-case T3 (at `c_i := 1`) and T3' both evaluate over
`Set.uIcc xn1 (xn1 + h)`, which is not naturally indexed by any `j ∈ Fin s`:
```
(_hy_M_endpoint  : ∀ t ∈ Set.uIcc xn1 (xn1 + h), |yex t| ≤ M_bound)
(_hy'_LM_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h), |deriv yex t| ≤ L * M_bound)
```
The "ring_nf" rewrite handles the `(h * 1)` ↔ `h` simplification at the T3
invocation site.

### Step 4 (`localStepError_bound`, line 1355) — DEFERRED to cycle 116

Per strategy's backup plan, the capstone retains its global `_hy_M` and
`_hy'_LM` hypotheses, with localized forms derived inline before the
`localStageError_bound_a/b` invocations:
```
have _hy_M_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
    |yex t| ≤ M_bound := fun _ t _ => _hy_M t
have _hy'_LM_local : ... := fun _ t _ => _hy'_LM t
have _hy_M_endpoint : ... := fun t _ => _hy_M t
have _hy'_LM_endpoint : ... := fun t _ => _hy'_LM t
```
This is a clean intermediate state — the helper chain is fully localized,
and cycle 116 can strengthen the capstone signature plus `IsConvergent`
together (which is the natural unit, since both flow into `Section513.lean`
and `Section514.lean`).

## Result

SUCCESS. Steps 1, 2, 2b, 3 all landed. Step 4 deferred to cycle 116 per
strategy.

* `lake env lean OpenMath/Chapter5/Section515.lean` — clean (only pre-existing
  warnings on unused `hβ_nn` / `Finset.sum_Ico_succ_top` simp arg, plus the
  expected `sorry` warning at `aux_515D_output_tendsto` line 1836).
* `lake env lean OpenMath/Chapter5/Section513.lean` — clean.
* `lake env lean OpenMath/Chapter5/Section514.lean` — clean (only pre-existing
  `Matrix.toEuclideanLin_apply` deprecation warnings).
* Axiom check via scratch `import OpenMath.Chapter5.Section515` + `#print axioms`:
  - `aux_y_diff_norm_bound` → `[propext, Classical.choice, Quot.sound]`
  - `GeneralLinearMethod.localStageError_bound_a` → `[propext, Classical.choice, Quot.sound]`
  - `GeneralLinearMethod.localStageError_bound_b` → `[propext, Classical.choice, Quot.sound]`
  - `GeneralLinearMethod.localStepError_bound` → `[propext, Classical.choice, Quot.sound]`
  - (Private helpers `aux_T3_bound` / `aux_T3'_bound` / `aux_T4_bound` cannot
    be probed externally, but their sole consumers — the
    `localStageError_bound_*` / `localStepError_bound` chain — being
    sorry-free transitively confirms they are too.)

## Faithfulness check

No new `def` or `theorem` introduced this cycle — only signature refactors of
existing helpers. The faithfulness obligation is **strict-weakening**:

* The new compact-interval bound `∀ t ∈ Set.uIcc x ..., |f (y t)| ≤ L M`
  is **implied by** the old global bound `∀ t, |f (y t)| ≤ L M`.
  All existing consumers in §513 / §514 (which feed into `localStepError_bound`
  via the unrefactored capstone) continue to compile by trivial restriction.
* The textbook (Butcher 2008, p. 412, `lem_515A.json` `context_latex`) actually
  hypothesizes `‖y(x)‖ ≤ M` for `x` in a "closed set S containing the trajectory" —
  which is morally exactly the compact interval, so this refactor moves the
  Lean statement *closer* to the textbook, not further. No faithfulness
  divergence is introduced.
* Tautology check: N/A (no new theorems).
* Identity check: N/A (no new theorems).
* Definition smuggling check: N/A (no new structures or definitions).
* Hypothesis strength check: PASSES — each refactored helper now takes a
  *weaker* hypothesis than before.
* Absent theorem check: confirmed no proof comments promise content lost in
  the refactor; the only commented "promise" (line 1836 `sorry` at
  `aux_515D_output_tendsto`) was already there from cycle 114 and is the
  cycle-117 deliverable.

The faithfulness divergence at the `IsConvergent` layer (the `M_bound`
strengthening overall) is documented in
`.prover-state/issues/is_convergent_strengthened.md` (LMM precedent) and will
be extended in cycle 116 alongside Phase 2.

## Dead ends

None this cycle. The scratch-file-first workflow caught all signature mismatches
before transplant.

## Discovery

* **`aux_T3'_bound` was a hidden Step 2b**: not listed in the strategy, but its
  internal use of `aux_y_diff_norm_bound` (at `ξ = 1`) forced a refactor.
  Future cycles refactoring helper-chain hypotheses should `rg` for ALL
  consumers of the changed helper before scoping the work.
* **The b-case needs an extra `_endpoint` hypothesis** beyond the strategy's
  per-`j` form, because `aux_T3_bound` is invoked with `c_i := 1` (not any
  `c j`) and `aux_T3'_bound` evaluates at the same endpoint. The simplest
  encoding is a parallel pair `_hy_M_endpoint` + `_hy'_LM_endpoint` over
  `Set.uIcc xn1 (xn1 + h)`. Cycle 116 will need to handle this in the
  `IsConvergent`-strengthening flow — likely by combining all evaluation
  points into a single `Set.uIcc xn1 (xn1 + h * cmax)` bound where
  `cmax := max 1 (max_j c j)`.
* **`Set.uIoc_subset_uIcc` is the workhorse**: every helper that uses
  `aux_y_diff_norm_bound` (which internally uses `Set.uIoc`) had to bridge
  via this lemma to the helper's exterior `Set.uIcc` hypothesis. Worth
  remembering for similar localization passes elsewhere.
* **Linter warnings on the new locals at cycle 115 sites**: Lean 4's
  `unusedVariables` linter does NOT flag the new `_hy_M_local` /
  `_hy_M_endpoint` even though they are unused in the body, because they
  start with underscore. This matches the existing `_hy_M` convention and
  is the right name choice for parallel-hypothesis design.

## Suggested next approach

**Cycle 116**: Phase 2 of Solution A. Strengthen
`GeneralLinearMethod.IsConvergent` in `Section512.lean` to require the
localized hypotheses (replace the global `M_bound`-style hypothesis with
`∀ t ∈ Set.Icc x₀ x, ...` per the strategy's blocker doc), then verify §513
(`yex = 0` case: trivially bounded by `M_bound := 0`) and §514 (`yex = id`
case: bounded by `M_bound := |x|` on `Set.Icc 0 x`). Also strengthen
`localStepError_bound`'s capstone signature to take the localized forms
directly (Step 4 deferred from cycle 115); the inline derivation block
in cycle 115's commit is the migration pattern.

Specifically, `localStepError_bound` should take:
```
(_hy_M_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j), |yex t| ≤ M_bound)
(_hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j), |deriv yex t| ≤ L * M_bound)
(_hy_M_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h), |yex t| ≤ M_bound)
(_hy'_LM_endpoint : ∀ t ∈ Set.uIcc xn1 (xn1 + h), |deriv yex t| ≤ L * M_bound)
```
in place of the global `_hy_M` / `_hy'_LM`.

**Cycle 117**: Compose the `aux_515D_output_tendsto` body using the cycle 110–
114 deliverables (`aux_515D_construct_ell_U_phi_A`, `aux_515D_per_step_recurrence`,
`aux_515D_gronwall_bound`, `aux_515D_squeeze`, `aux_515D_stage_eventually_bounded`)
plus the cycle-116 `IsConvergent` strengthening. This is where Aristotle
compute should be deployed.
