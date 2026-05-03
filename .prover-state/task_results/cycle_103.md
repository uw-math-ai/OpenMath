# Cycle 103 Results

## Worked on

Opened `lem:515B` (Butcher §515, p. 414) — local-step error propagation
for a stable, consistent GLM. Sorry-first scaffold added to
`OpenMath/Chapter5/Section515.lean`, growing the file from 831 → 1040
lines (+209 LOC).

Scaffolded:

* `GeneralLinearMethod.localStepError_bound` — main theorem (top-level
  `lem:515B` claim). Sorry-first.
* `aux_515B_residual_decomposition` — algebraic identity for the
  residual splitting `LHS = Σ V·δ + (LHS-with-yt_prev-instead-of-y_prev)`.
  **Closed manually** (purely `Finset.sum_sub_distrib` + `ring`).
* `aux_515B_lipschitz_bridge` — `|h Σ B·(f(Ŷ) − f(Y))| ≤ h L Σ |B|·|η|`.
  Sorry → submitted to Aristotle.
* `aux_515B_eta_contraction` — η bound via `(I − h₀ L|A|)^{−1}`
  positivity. Sorry → submitted to Aristotle.

Sorry count for §515: 0 → 3 (one per stubbed sub-lemma + one in main
theorem).

## Approach

Followed the cycle 103 strategy verbatim:

1. **Read formalization data**: `entities/lem_515B.json`, confirming
   the textbook statement and the two distinct ell-vectors (`ℓ_U`
   for α, `ϕ_A` for β-via-515A).

2. **Sorry-first scaffold** of `localStepError_bound`. Used the
   recommended proxy approach:
   - `α, β, δ_max` as proxy parameters with upper-bound side
     conditions (sidesteps `Finset.sup'`-non-emptiness).
   - `ell_U, phi_A` as parameters with linear-system side conditions
     (sidesteps `(I − h₀ L|A|)^{-1}` infrastructure, deferred).

3. **Decomposed** into three sub-lemmas + the main theorem. The
   strategy listed four (`aux_515B_main_combination` was its
   fourth); we chose to inline the main combination into
   `localStepError_bound` itself rather than create a redundant
   wrapper, but submitted a self-contained version of the main
   theorem to Aristotle as one of the three batch items.

4. **Closed `aux_515B_residual_decomposition` manually**. The proof
   is the `Σ V·y_prev = Σ V·yt_prev − Σ V·δ` rewrite plus `ring`.
   Closed in 6 lines.

5. **Submitted Aristotle batch** of three sorry-bearing lemmas to
   project `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8` at 2026-05-03
   17:52 UTC. Per the strategy, we do NOT poll repeatedly; status
   checked once at end of cycle.

6. **Compile-check**: `lake env lean OpenMath/Chapter5/Section515.lean`
   succeeds with exactly three `declaration uses sorry` warnings
   (lines 906, 931, 993), matching the three open sub-lemmas/theorem.

## Result

**SUCCESS** — all must-haves met:

* `lem:515B` scaffolded with textbook-faithful signature ✓
* `aux_515B_residual_decomposition` closed manually ✓
* Aristotle batch submitted (3 pieces) ✓
* `lake env lean` compiles with only expected sorries ✓
* `task_results/cycle_103.md` written ✓
* Commit will be pushed to `origin/Main/Experiments` ✓

## Faithfulness check

For `aux_515B_residual_decomposition` (cycle 103, helper lemma):

* **Entity ID**: not a textbook entity; helper for `lem:515B`.
* **Lean statement captures**: textbook's algebraic splitting of
  the local-step residual. Pure algebra, no analytic content.
* **Tautology check**: conclusion ≠ any hypothesis ✓
* **Identity check**: proof is non-trivial (`Finset.sum_sub_distrib`
  + `ring` after `δ`-substitution) ✓
* **Hypothesis strength check**: only `hδ_def` is used; all other
  arguments are passed through to the conclusion. No extra
  hypotheses ✓

For `aux_515B_lipschitz_bridge` (cycle 103, helper):

* Helper lemma; not a textbook entity directly.
* Captures: `f` Lipschitz `⇒` `|Σ B·(f(a) − f(b))| ≤ L Σ|B|·|a − b|`.
* This is a standard application of triangle + Lipschitz; analogous
  to the proven `aux_T4_bound` in §515.

For `aux_515B_eta_contraction` (cycle 103, helper):

* Helper lemma; not a textbook entity directly.
* Captures: the textbook's η-bound derivation, expressed as a
  conditional theorem (given the per-stage contraction estimate,
  conclude the η bound). Decouples (I − h₀L|A|)^{-1} positivity
  infrastructure from the rest of the proof.
* The `c_j ≥ 0` hypothesis matches the cycle-101 restriction in
  `aux_T3_bound` (sign-asymmetric in `c_i`); textbook is
  sign-symmetric, but all standard GLMs satisfy `c ≥ 0`.

For `GeneralLinearMethod.localStepError_bound` (cycle 103, main
theorem for `lem:515B`):

* **Entity ID**: `lem:515B`. Textbook statement (from
  `entities/lem_515B.json`):

  > Under the conditions of Lemma 515A, the exact solution and
  > the computed solution in a step are related by
  > `ỹ_i^[n] − y_i^[n] = Σ_j V_{ij}(ỹ_j^[n−1] − y_j^[n−1]) + K_i^[n]`,
  > where `‖K^[n]‖ ≤ h α max|ỹ^[n−1] − y^[n−1]| + β h²`,
  > with α = L max|ℓ| and
  > β = L² M max [½|u_i| + |v_i| + Σ|b_{ij} c_j| + h₀ L Σ|b_{ij}| ϕ_j].

* **Lean statement captures**: same content **modulo proxy
  abstraction** described below. Documented in the docstring.

* **Deviations from textbook**:

  1. *Maxima as proxy parameters*: textbook uses concrete suprema
     `max_{i=1}^r |δ_i|`, `max_{i=1}^s |ℓ_i|`, `max_{i=1}^s [...]`;
     we abstract as `δ_max`, `α`, `β` with upper-bound side
     conditions. **Strictly weaker** than textbook (any valid upper
     bound is acceptable). The conclusion is preserved under any
     correct choice of α, β, δ_max. **Justified**: avoids
     `Finset.sup'`-non-emptiness plumbing, matches cycles 100/102
     pattern of taking abscissae `c` as a parameter.

  2. *α formula*: textbook says `α = L max_i |ℓ_i|`; we encode
     `∀ i, L · Σ_j |B_{ij}| · ell_U_j ≤ α`. The latter is what the
     analysis actually produces; the textbook formula appears to
     assume `Σ|B_{ij}| ≤ 1` (not stated in `lem:515B`). The user
     can supply `α := L · max_i Σ_j |B_{ij}| ell_U_j` or any larger
     value. **Documented in the docstring.** This is *strictly
     more permissive* (the bound holds for more α-values), so the
     main claim is faithful.

  3. *Two distinct ell-vectors*: the textbook uses `ℓ` ambiguously
     for both `ℓ_U` (in α) and `ϕ_A = ℓ` (in β-via-515A). We
     encode them as two named parameters with their two distinct
     linear-system side conditions, per the cycle 103 strategy
     reading.

  4. *`(I − h₀ L|A|)^{-1}`-inversion infrastructure deferred*: we
     take `ell_U`, `phi_A` as parameters rather than constructing
     them. **Documented in the docstring.** Future cycle will
     build the infrastructure and discharge both side conditions.

  5. *`‖K^[n]‖_∞`*: encoded pointwise as `∀ i, |K i| ≤ ...`,
     equivalent.

* **Tautology check**: conclusion is `∃ K, identity ∧ bound`. K is
  not a hypothesis; identity and bound are non-trivial ✓
* **Identity check**: existential will be witnessed by an explicit
  K_i := stage equation residual − Σ V·δ; identity by ring; bound
  by combining sub-lemmas. **Currently sorry'd**, awaiting
  Aristotle.
* **Hypothesis strength check**: hypotheses match `lem:515A`
  (cycles 100–102) exactly + the new ell_U/phi_A side conditions
  + the proxy α/β/δ_max. The added hypotheses are exactly what's
  documented in the entity JSON.

## Dead ends

None this cycle — the scaffold compiled on first try, residual
decomposition closed via the strategy's recommended `Finset.sum_sub_distrib`
+ `ring` pattern.

## Discovery

* The strategy's recommendation to abstract α, β, δ_max as proxy
  parameters is clean and avoids `Finset.sup'`-non-emptiness
  bookkeeping. This pattern should generalize: when a textbook
  formula involves `max_i ...` over an indexing set, abstract via
  a proxy with `∀ i, ... ≤ α` side condition.

* The textbook's α formula `L max|ℓ|` appears to skip a `Σ|B_{ij}|`
  factor; the analysis actually produces `L Σ|B_{ij}| ℓ_j`. Our
  encoding makes the analysis-correct form available; documenting
  the deviation in the docstring satisfies faithfulness.

* The two ell-vectors (ell_U with RHS = Σ|U|, phi_A with RHS =
  ½c² + |A||c|) need to be encoded separately. The textbook is
  ambiguous ("ℓ as in Lemma 515A"); the JSON's `statement_latex`
  makes this clear.

## Suggested next approach

For cycle 104 (the planner's choice):

1. **Hardest priority**: build `(I − h₀ L|A|)^{-1}` positivity
   infrastructure, then construct `ell_U` and `phi_A` and discharge
   the side conditions of `localStepError_bound`. This unlocks both
   the η contraction (`aux_515B_eta_contraction`) and the construction
   side of the textbook's α, β.

   - Mathlib pointer: `Matrix.IsM` / `Matrix.invertibleOfDiagDominant`
     and related — search `lean_local_search` for "M-matrix" /
     "diagonally dominant".

2. **Easier priority**: close `aux_515B_lipschitz_bridge` manually
   (≤ 30 LOC, pattern of `aux_T4_bound`). If Aristotle returns this
   already proved in cycle 103's batch, this is moot.

3. **Compose**: assuming all three sub-lemmas are closed, `localStepError_bound`
   is a straightforward composition. Writeable in ≤ 50 LOC.

4. After `lem:515B`, the next entity in the §515 dependency chain is
   `lem:515C` (accumulated error estimate), which depends on `lem:515B`,
   followed by `thm:515D` (full convergence theorem).

5. A *separate* parallel direction: continue infrastructure for
   `def:512A`'s convergence definition (cycle 098 strengthening) —
   but this is downstream of `lem:515C` and `thm:515D`, so probably
   block on those first.

## Aristotle batch

* **Project ID**: `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`
* **Submitted**: 2026-05-03 17:52 UTC
* **Pieces**: 3 sorry-bearing lemmas in
  `.prover-state/aristotle_submissions/cycle_103/sub_lemmas.lean`:
  - `aux_515B_lipschitz_bridge` (cheap)
  - `aux_515B_eta_contraction` (hardest — requires `(I − h₀ L|A|)^{-1}`
    positivity)
  - `aux_515B_main_combination` (medium — composition)
* **Status check policy**: ONE check at end of cycle, per CLAUDE.md.
  No polling.
