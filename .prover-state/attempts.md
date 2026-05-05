
### Cycle 8
Cycle 008: Claimed to add ode_solution_unique, ode_solution_exists, ode_existence_uniqueness to OpenMath/Chapter1/Section110.lean and update lean_status.json for thm:110C, but git diff is empty — same commit-not-reaching-repo failure as cycles 005–007.

### Cycle 12
thm:141A (cycle 012): Sum-swap approach for constant-coefficient recurrence closed form succeeded. Key pattern: extend variable-bound inner sum to fixed bound via Finset.sum_filter + conditional, then Finset.sum_comm to swap, factor out initial-data/forcing term, close with theta_recurrence_at. Finset.sum_Icc_succ_top exposes the missing ψ_n top term. k=0 case requires separate handling (theta degenerates to δ_{m,0}). Aristotle jobs on sub-lemmas landed too late to contribute — manual proofs finished first.

(Cycle 010 Section112.lean:74 entry resolved by cycle 015's `h_inner → hinner`
rename. Cycle 013 Section212.lean:138/144 entries resolved by cycle 014's
inline refactor. Both removed 2026-04-28 to stop propagating into next
cycle's prompt.)

### Cycle 35
Cycle 035 Section404.lean: Worker reports creating LinearMultistepMethod structure, IsPreconsistent predicate, and two concrete witnesses (explicit/implicit Euler) with clean compile and full lake build. However, git diff shows only heartbeat.json changed — no Lean files committed. Same commit-not-reaching-repo failure as cycle 008.

### Cycle 50
Cycle 050: `Finset.sum_le_sum_nbij'` does not exist in Mathlib; use `← Finset.sum_image hinj` + `Finset.sum_le_sum_of_subset_of_nonneg` instead (Approach B). Also: after `intro a ha b hb hab` in a `Set.InjOn` proof, a bare `simp only` is needed to beta-reduce `(fun i => i - c) a = (fun i => i - c) b` before `omega` can close it.

### Cycle 71
Cycle 071: Worker staged infrastructure for convergent_isStable (runningMaxAbs def + 6 helpers, Section405 scaffold) but did not commit — git diff shows heartbeat.json only, same failure as cycles 008/035. A tautological proof was introduced at Section404.lean:4695 (proof is `exact <hypothesis>`), bumping semantic sorry count 0→1.

### Cycle 72
Cycle 072 confirmed cycle-071 staged work was sound and committed it together with the cycle-072 closure of `hstart_tendsto`/`thm:405A` in a single commit. The line-4695 "tautology" was a scanner false positive (sum-head inside a theorem statement, not a proof body) per `tautology_scanner_false_positives.md`. Faithfulness/axiom check clean. Note: `lake env lean <file>` does NOT update the .olean cache — use `lake build OpenMath.Chapter4.Section405` before `#print axioms` to avoid stale-cache `sorryAx` false positives.

### Cycle 73
Cycle 073: Authored the §410 generating-function infrastructure (`αPoly`, `βPoly`, `C`, `expNegPS`, 5 Aristotle helpers including the load-bearing `coeff_aeval_C_X_pow`, 7 manually-closed sub-lemmas) in `OpenMath/Chapter4/Section410.lean`, but left `thm_410A`'s general-`j` case as `sorry` and committed nothing — supervisor REVERTED with score −2 (commit-not-reaching-repo). Cycle 074 closes the sorry (via `map_sub`/`map_one`/`map_sum` push-throughs + `coeff_aeval_C_X_pow` + `rfl` against the `C M (j+1)` pattern-match) and lands the cycle-073 infrastructure together in one zero-sorry commit.

### Cycle 78
Cycle 078 lem:383A: planner's Path B sketch proposed a trivial pointwise multiplicativity statement — rejected as definition smuggling (Butcher's lemma is about the convolution product, not pointwise). Faithful implementation required building Multiset.powerset_add (missing from Mathlib) and sum_mul_sum_eq_sum_product as private helpers. DecidableEq for RootedTree required Classical.decEq workaround (nested-inductive deriving failure). Multiset.mul_sum does not exist — correct name is Multiset.sum_map_mul_left.

### Cycle 97
Cycle 097: `LinearMap.orthogonal_ker` does not exist in Mathlib — Loogle returned a hallucinated name; only `ContinuousLinearMap.orthogonal_ker` exists at Adjoint.lean:182. Worked around with ~10 LOC inline proof of `(range T)ᗮ = ker(adjoint T)` via `LinearMap.adjoint_inner_right + ext_inner_left`. `dotProduct` and `smul_dotProduct`/`sum_dotProduct` live in root namespace, not `Matrix.*` — bare names work under `open Matrix`. Aristotle jobs A/B/C completed during cycle but manual proofs were already axiom-clean before results returned; Aristotle output not incorporated.

### Cycle 99
Cycle 099: unicode `𝟙` as an identifier suffix (e.g. `B𝟙`) breaks the Lean parser — use ASCII identifiers (`B1`, etc.) and reserve `𝟙` for operators/notation only. For `V^(k+1) *ᵥ u' = u'` induction after `rw [pow_succ, ← Matrix.mulVec_mulVec]`, the goal becomes `V^k *ᵥ (V *ᵥ u') = u'`; `ih` does not match the inner `V *ᵥ u'` subterm, so rewrite `hVu'` first (reducing `V *ᵥ u'` to `u'`) then apply `ih`: correct order is `rw [pow_succ, ← Matrix.mulVec_mulVec, hVu', ih]`.

### Cycle 112
Cycle 112 sub-lemma B (`aux_515D_gronwall_bound`): calling `Section404.discrete_gronwall_exp_bound` directly did not fit cleanly (parameter/shape mismatch with `k` stride vs. the `α*h` form); worker instead built `aux_515D_discrete_gronwall_raw` from scratch via `Nat.strong_induction_on` + `Finset.sum_Ico_succ_top` + `nlinarith`, then wrapped with `aux_515D_one_add_pow_le_exp` to convert the `(1+αh)^n` base to `exp(α·n·h)` form. Section404 helper remains unused.
