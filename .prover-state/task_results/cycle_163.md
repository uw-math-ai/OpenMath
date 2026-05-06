# Cycle 163 Results

## Worked on
`def:530B` / `def:530C` Path A — r-parametric refactor Phase B.1 +
Phase B.2.

Specifically: introduced two parametric `HasOrderRelativeTo_explicit`
witnesses (`paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)`
and `_hasOrderOne_padCompatStartingR (r : ℕ)`) plus the two
parametric `HasOrder_explicit` wrappers
(`paddedREulerGLM_hasOrderZero (r : ℕ)` and `_hasOrderOne (r : ℕ)`)
that subsume the four hand-written `r ∈ {1, 2, 3, 4}` × `p ∈ {0, 1}`
pairs from cycles 153/155/156/157/159/161. Phase B.3 (reconciliation
lemmas / retirement of hand-written instances) was *not* attempted
this cycle; deferred to cycle 164 per strategy's "ship only if clean"
rule.

## Approach
Followed cycle 163 strategy verbatim. The closure recipe for the
parametric `HasOrderRelativeTo_explicit` witnesses is structurally
identical to the cycle 156/159/161 hand-written templates, but with
two key adjustments forced by the parametric `r`:

1. **Case-split on `i : Fin (r + 1)`**: `fin_cases i` only fires at
   concrete `r`, so the proof uses `by_cases hi : i.val = 0` (the
   same shape established by cycle 162's
   `padCompatStartingMethodR_applyExplicit`).

2. **Closed-form helper extraction**: rather than inline the
   `padded2DEulerGLM`/`padded3DEulerGLM`/`padded4DEulerGLM`-style
   `simp [...]; Matrix.mulVec, dotProduct, Fin.sum_univ_…, ring`
   computations (which collapse cleanly only at concrete `r`), I
   extracted seven private helper lemmas:
   - **Three `paddedREulerGLM_{U,B,V}_apply (r : ℕ) …`** lemmas
     reducing the `Matrix.of fun i j => if …` bodies to indicator
     form by `rfl`.
   - **Two `paddedREulerGLM_{U,V}_mulVec_*` lemmas** collapsing the
     indicator-weighted finite sums via
     `Finset.sum_eq_single (0 : Fin (r + 1))`: for `U`, the row-0
     dot product equals `v 0`; for `V`, the row-`i` dot product
     equals `v 0` when `i.val = 0` and `0` otherwise.
   - **`paddedREulerGLM_explicitStageValue_zero (r : ℕ) …`**
     evaluates the GLM stage recursion at the single stage
     `0 : Fin 1`, where the empty `Fin 0` sum kills the recursive
     step and the body collapses to `(U *ᵥ y_input) 0 = y_input 0`.
   - **`paddedREulerGLM_applyStartingThenStep_explicit_apply`** —
     the SM[i] closed form: `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)`
     when `i.val = 0`, else `0`.
   - **`paddedREulerGLM_applyExactThenStarting_explicit_apply`** —
     the ES[i] closed form: `yex(x₀ + h) + h·f(yex(x₀ + h))` when
     `i.val = 0`, else `0`.

3. **Witness closure**: with these helpers in place, each of the
   parametric witnesses follows the same shape as the hand-written
   ones but is now `r`-uniform:
   - `i.val = 0` channel: rewrite SM[i] − ES[i] using the two
     closed-form helpers, simp away the `if i.val = 0` clauses
     (positive branch), collapse `h ^ (p + 1)` to `h` / `h ^ 2`,
     then one-line invoke the cycle 158/160 Taylor + Lipschitz
     helpers.
   - `i.val ≠ 0` channel: rewrite SM[i] − ES[i] using the same two
     closed-form helpers, simp away the `if i.val = 0` clauses
     (negative branch) leaving `Diff = 0`, then close via
     `Asymptotics.isBigO_zero`.

4. **Phase B.2 wrappers**: each `HasOrder_explicit` wrapper is a
   one-line `refine ⟨padCompatStartingMethodR r, …⟩` exhibiting
   the parametric starting family as the existential witness, with
   non-degeneracy / explicit-constituent clauses supplied by the
   cycle 162 Phase A helpers and the
   `HasOrderRelativeTo_explicit` component supplied by Phase B.1.

5. **Verification**: `lake env lean OpenMath/Chapter5/Section530.lean`
   and `lake env lean OpenMath/Chapter5.lean` both exit 0; sorry
   count remained 0; tautology-scanner regex returns only the
   pre-existing `OpenMath/Chapter5/Section514.lean:601` hit.
   `mcp__lean-lsp__lean_verify` on each of the four new theorems
   returned axioms `[propext, Classical.choice, Quot.sound]` only.

Aristotle was **not** invoked, per the strategy's anti-pattern list
(historical Aristotle weakness on parametric `Fin`-indexed sums and
decidable-equality case splits). The closure was a mechanical port
of the cycle 156/159/161 templates with parametric matrix-entry
helpers, so manual proof was the right call.

Phase B.3 (reconciliation lemmas) was *not* attempted: cycle 163
shipped the cleaner Phase B.1 + B.2 closure first, leaving
reconciliation as a clean incremental cycle 164 deliverable.

## Result
SUCCESS — Phase B.1 and Phase B.2 land axiom-clean. Four new
theorems plus seven new private helper lemmas; Sorry count remains
at 0 in both `Section520.lean` and `Section530.lean`. Section530
file LOC: 2599 → 2901 (+302 LOC, within the strategy's "expected
case" budget of 200–350 LOC).

## Faithfulness check

For each new theorem this cycle:

### `theorem paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ) …`
- Entity: `def:530B` (Path A non-vacuity, parametric).
- Textbook statement (`extraction/formalization_data/entities/def_530B.json`):
  > Consider a general linear method M and a non-degenerate
  > starting method S. The method M has order p relative to S
  > if the results found from SM and ES agree to within
  > O(h^{p+1}).
- Lean statement captures: **same content** (parametric over `r`
  with the explicit Euler family + passive-zero starting family;
  `p = 0`). The hypothesis pack (`LipschitzWith L f`,
  `yex x₀ = y₀`, `HasDerivAt yex (f y₀) x₀`) matches the cycle
  153/156/159/161 hand-written instances exactly. The conclusion
  is the substantive `O(h^(0+1))` agreement between SM and ES.

### `theorem paddedREulerGLM_hasOrderOne_padCompatStartingR (r : ℕ) …`
- Entity: `def:530B` (Path A non-vacuity, parametric, `p = 1`).
- Same textbook quote as above.
- Lean statement captures: **same content** (parametric over `r`,
  `p = 1`). Hypothesis pack (`LipschitzWith L f`,
  `ContDiff ℝ 2 yex`, full ODE relation, `yex x₀ = y₀`) matches
  cycles 154/157/159/161 exactly. Conclusion is the substantive
  `O(h^(1+1))` SM−ES agreement.

### `theorem paddedREulerGLM_hasOrderZero (r : ℕ) …`
- Entity: `def:530C` (Path A non-vacuity wrapper, parametric, `p = 0`).
- Textbook statement (`extraction/formalization_data/entities/def_530C.json`):
  > A general linear method M has order p if there exists a
  > non-degenerate starting method S such that M has order p
  > relative to S.
- Lean statement captures: **same content** under the explicit
  restriction (Path A). The existential is supplied by
  `padCompatStartingMethodR r`; non-degeneracy via
  `padCompatStartingMethodR_isNonDegenerate r`; the
  `HasOrderRelativeTo_explicit` component via Phase B.1 above.

### `theorem paddedREulerGLM_hasOrderOne (r : ℕ) …`
- Entity: `def:530C` (Path A non-vacuity wrapper, parametric, `p = 1`).
- Same textbook quote.
- Lean statement captures: **same content** (parametric, `p = 1`).
  Same existential witness shape as `_hasOrderZero` above.

### Tautology / identity / hypothesis-strength checks
- **Tautology check**: clean. None of the four conclusions appears
  as a hypothesis. The conclusions are substantive
  `=O[nhds 0] (h^(p+1))` claims (Phase B.1) or substantive
  existentials (Phase B.2).
- **Identity check**: clean. The Phase B.1 proofs do real algebraic
  work (closed-form rewrites + Taylor + Lipschitz invocations +
  zero-collapse). The Phase B.2 proofs are one-line existential
  closures, but the witness (`padCompatStartingMethodR r`) and the
  three component proofs are all genuinely substantive
  (cycle 162 + cycle 163 Phase B.1 work).
- **Hypothesis strength check**: clean. The hypothesis packs match
  cycles 153/154/156/157/159/161 exactly; the parametric `(r : ℕ)`
  argument is a free variable, not an extra constraint.
- **Definition smuggling check**: N/A — no new `def`s land this
  cycle. Phase A's `paddedREulerGLM`, `padCompatStartingMethodR`,
  etc. are already in place from cycle 162.
- **Absent theorem check**: clean. Phase B.1 / B.2 do not promise
  any sorry'd follow-up content within the file.

## Dead ends
None encountered substantively. The first compilation attempt of
the closed-form helper
`paddedREulerGLM_applyStartingThenStep_explicit_apply` had a single
algebraic ordering issue at the `i.val = 0` branch (`simp [hi]`
left `h * f(y₀ + h*f y₀) + (y₀ + h*f y₀)` not matching the goal's
`(y₀ + h*f y₀) + h * f(y₀ + h*f y₀)`); resolved by appending `ring`
to that one branch. Total iteration cost: one re-compile.

## Discovery
- The five-helper unfolding pattern
  (`paddedREulerGLM_{U,B,V}_apply` + the two `_mulVec_*` lemmas) is
  the right shape for working with `Matrix.of fun i j => if …`
  matrices at parametric size. Every dot product collapses via
  `Finset.sum_eq_single` against the indicator's apex index. This
  pattern likely generalizes to any future `Matrix.of`-bodied
  family with a single-active-row/column structure.
- `by_cases hi : i.val = 0` paired with `simp [hi]` cleanly
  threads the case split through long calc-style proofs that mix
  `if i.val = 0`-conditioned closed forms — the cycle 162
  `padCompatStartingMethodR_applyExplicit` precedent ports
  beautifully.
- Phase B.1's i = 0 channel proof is now ~30 LOC per witness
  (down from ~70 LOC for each cycle 161 hand-written instance):
  the closed-form helper extraction does most of the work, leaving
  only a `funext h; rw [...closed-form...]; simp [hi]; ring` glue
  before the cycle 158/160 helper invocation.
- The `Phase B.2` `HasOrder_explicit` wrappers stayed at the
  same trivial one-line shape established by cycle 156/157/159/161,
  validating that the Phase A `padCompatStartingMethodR_isNonDegenerate`
  and `_constituents_isExplicit` helpers were the right interface.

## Suggested next approach
Cycle 164 candidates (in rough preference order):

1. **Phase B.3 reconciliation lemmas** — the four
   `paddedREulerGLM 0 = explicitEulerGLM`,
   `paddedREulerGLM 1 = padded2DEulerGLM`,
   `paddedREulerGLM 2 = padded3DEulerGLM`,
   `paddedREulerGLM 3 = padded4DEulerGLM` reconciliations (and
   analogous starting-family reconciliations). Likely close by
   `ext + decide` / `ext + simp` since the `Matrix.of`-body and
   `!![..]`-body forms unfold differently. If they close cleanly,
   cycle 165 can begin retiring the hand-written
   `padded{2,3,4}DEulerGLM` and `pad{N}CompatStartingMethod`
   instances (and their cycle 156/157/159/161 witnesses), shrinking
   Section520 + Section530 by a substantial LOC delta. If
   reconciliation requires non-trivial plumbing, defer further.

2. **Pivot to a fresh `def`/`thm` entity** — natural candidates:
   - `def:451A` G-stable
   - `def:422B` underlying one-step method
   - `def:442A` principal sheet
   - `thm:535A` underlying one-step method (GLM)
   - `thm:541A` types of DIMSIM methods

3. **Path B (implicit branch)** of `def:530B`/`def:530C` —
   continues to require multi-cycle infrastructure work
   (`ContractingWith` / `Function.IsFixedPt` setup); not a
   single-cycle deliverable. Defer until a multi-cycle Path B
   campaign is explicitly authorized.

4. **Long-range targets** (multi-cycle, *do not* take on solo):
   - `thm:550A` general-n (cancelled twice; needs cofactor-expansion
     induction or eigenvalue density).
   - `aux_515D_construct_ell_U_phi_A` `_hc_nn`/`_hc_le_one` removal.
