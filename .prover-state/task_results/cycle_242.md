# Cycle 242 Results

## Worked on

`thm:523B` — Butcher §523 (p. 428) non-linear stability **inequality**:
`‖y_next‖²_G ≤ ‖y_prev‖²_G` whenever the algebraic-stability block
matrix `M(D, G)` is PSD, `D` is symmetric, and the step is
dissipative (`⟨hF, Y⟩_D ≤ 0`).

Public symbol added:
`OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_inequality`
in `OpenMath/Chapter5/Section523.lean`, immediately after cycle 241's
`algebraicStability_identity` and before its non-vacuity example block.

A companion non-vacuity `example` was added at `(s, r) = (1, 1)`
`explicitEulerGLM` with `D, G = Matrix.diagonal …`, taking `hPSD`,
`hStage`, `hOut`, `hDiss` as hypotheses — mirroring cycle 241's
pattern.

## Approach

The planner's recipe was followed verbatim:

1. **Identity application**: `algebraicStability_identity` (cycle 241)
   rewrites
   `y_next ⬝ᵥ (G *ᵥ y_next) = y_prev ⬝ᵥ (G *ᵥ y_prev) + 2·⟨hF,Y⟩_D − M_quad`
   as an algebraic equality.

2. **PSD ⇒ M-quad ≥ 0**: `Matrix.PosSemidef.dotProduct_mulVec_nonneg`
   (verified present at
   `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:298`)
   gives `0 ≤ star x ⬝ᵥ (M *ᵥ x)` for any `x`. The `star x` collapses
   to `x` via `simpa` because `ℝ` has `TrivialStar` and `star_trivial`
   is a default simp lemma — no manual `funext`/`Pi.star_apply`
   bridging needed.

3. **Combine via `linarith`**: With the identity, `hDiss ≤ 0`, and
   `hMq ≥ 0` all named, `linarith` closes the inequality in one
   tactic call.

Total proof body: 6 lines of tactics. Total content (theorem +
docstring + non-vacuity example + docstring section): ~50 LOC.

## Result

**SUCCESS** — axiom-clean ship.

* `mcp__lean-lsp__lean_diagnostic_messages` returns no errors and no
  warnings.
* `mcp__lean-lsp__lean_verify` on
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_inequality`
  returns exactly `[propext, Classical.choice, Quot.sound]` — no new
  axioms.
* `grep -c sorry OpenMath/Chapter5/Section523.lean` returns 0.

## Faithfulness check

### `theorem GeneralLinearMethod.algebraicStability_inequality`

Entity ID and textbook statement (quoted from
`extraction/formalization_data/entities/thm_523B.json`):

> If $M$ given by \eqref{eq:523b} is positive semi-definite, then
> $$\|y^{[n]}\|_G^2 \leq \|y^{[n-1]}\|_G^2.$$

(The bulk of the JSON `statement_text` is a §524 LMM-reduction
digression that is **not** part of the 523B theorem proper — it
discusses a downstream construction. The actual theorem is the
single-line displayed inequality above.)

Lean statement captures: **same content, with surfaced hypotheses**.

The textbook PSD-on-`M` hypothesis maps directly to `hM_psd :
(M.algebraicStabilityMatrix D G).PosSemidef`. The displayed
inequality `‖y^[n]‖²_G ≤ ‖y^[n-1]‖²_G` maps to `y_next ⬝ᵥ (G *ᵥ
y_next) ≤ y_prev ⬝ᵥ (G *ᵥ y_prev)` — the standard `‖x‖²_G := x ᵀ G x`
encoding (also used in cycle 241).

**Surfaced (vs. textbook implicit) hypotheses**:

* `hDiss : (fun i => h * F i) ⬝ᵥ (D *ᵥ Y) ≤ 0` — dissipativity.
  Butcher's §357/§523 framing assumes this implicitly via the
  monotone-ODE setup (same convention as B-stability and algebraic
  stability throughout §357). Cycle 241's identity treats `Y` and
  `F` as pure algebraic variables, so dissipativity has to be a
  separate hypothesis at the Lean level. The textbook is unambiguous
  that this hypothesis is in force: without it the inequality is
  false (one can pick `F` with `⟨hF, Y⟩_D > 0`, making `M_quad`
  the only sign-determined term and forcing `‖y_next‖²_G > ‖y_prev‖²_G`).

* `hStage`, `hOut` — explicit step equations decoupled from
  `IsGLMSolution`, inherited from cycle 241. (Cycle 241 already
  documents this divergence and our reuse is faithful.)

* `hD : D.IsSymm` — symmetry of `D`. The textbook says
  "PSD diagonal `D`", which trivially implies `D.IsSymm`. We use
  the weaker symmetry hypothesis (inherited from cycle 241's
  identity, where the M-quad expansion uses `Dᵀ = D` to collapse
  cross-terms but does *not* use PSD-of-`D` for any sign argument).
  This is a **strict generalisation** along `D`, and consistent
  with cycle 241's already-documented faithfulness divergence.

**Not strengthened**: we do NOT require `D.PosSemidef`. The planner
flagged this explicitly as a "DO NOT" — adding `D.PosSemidef` would
be redundant (doesn't unlock anything in the proof body) and would
break the symmetry-only generalisation established in cycle 241.

### Tautology / Identity / Smuggling / Hypothesis-strength checks

* **Tautology check** — the conclusion `y_next ⬝ᵥ (G *ᵥ y_next) ≤
  y_prev ⬝ᵥ (G *ᵥ y_prev)` does NOT appear verbatim in any
  hypothesis. The hypotheses are: structural symmetry/PSD of two
  matrices, an equality identity (decomposed via `hId`), and a
  scalar inequality `⟨hF, Y⟩_D ≤ 0`. None of these reduce to the
  conclusion. ✓

* **Identity check** — the proof is `have hId := …; have hMq …;
  linarith` (three tactic steps). It is NOT `exact h` for any
  hypothesis. Real mathematical work happens at `linarith`, which
  combines three named facts algebraically. ✓

* **Smuggling check** — no `class`/`structure` is introduced this
  cycle. The single new declaration is a `theorem`. ✓

* **Hypothesis strength check** — `D.IsSymm` is weaker than the
  textbook's "PSD diagonal" (justified above as a strict
  generalisation inherited from cycle 241). `hM_psd` matches the
  textbook PSD hypothesis exactly. `hDiss` is implicit in the
  textbook setting and faithfully surfaced. `hStage`/`hOut` are
  cycle 241's decoupling pattern; documented. No hypothesis is
  *stronger* than the textbook requires. ✓

* **Absent theorem check** — no comments promise content that is
  not present. The theorem body and its docstring are self-contained. ✓

## Dead ends

None. The planner's recipe worked on the first attempt:

1. `lean_diagnostic_messages` showed zero errors after the initial
   edit (no need to iterate).
2. `simpa using hM_psd.dotProduct_mulVec_nonneg _` collapsed the
   `star x = x` step on its first try (`TrivialStar` + default
   simp set, as the planner predicted). No fallback to
   `simpa [star_trivial]` or manual `funext` was needed.
3. `linarith` closed the final inequality from `hId`, `hDiss`,
   `hMq` without hints.

## Discovery

* The `simpa using hM_psd.dotProduct_mulVec_nonneg (Sum.elim α y_prev)`
  collapse for `star x = x` over reals is robust enough that it
  needs no manual bridging — confirming the planner's analysis of
  Mathlib's `TrivialStar` instance for `ℝ` and `Pi`. This is a
  reusable pattern for any future Lean lemma that needs to apply
  a real-valued PSD bound through `dotProduct_mulVec_nonneg`.

* Cycle 241's deliberate decoupling of the identity from
  `IsGLMSolution` (taking step equations as explicit hypotheses)
  pays off cleanly in cycle 242: no `IsGLMSolution` unpacking or
  existential threading was needed. The inequality form inherits
  the same explicit step equations and just adds the dissipativity
  hypothesis on top.

* The textbook JSON `statement_text` for `thm:523B` bundles in
  ~80% irrelevant §524 content (LMM-reducibility to a
  `k`-input GLM, Butcher & Hill 2006 reference). Future workers on
  Butcher entities with proof-following preambles should treat the
  *first sentence with a display equation* as the actual statement
  and ignore the trailing context — the extractor doesn't always
  cleanly trim §-boundary spillover.

## Suggested next approach

§523 is now fully closed (`thm:523A` ✓ cycle 241, `thm:523B` ✓ cycle 242).
Reasonable next targets in increasing order of risk:

1. **`thm:521B`** (Maximum stability order for given steps, §521) —
   the only remaining `[ ]` row in §521. Single-cycle candidate if
   the proof reduces to a degree-counting argument on the stability
   polynomial; needs preliminary inspection of the JSON statement to
   confirm.

2. **`thm:535A`** (Underlying one-step method, §535) — flagged `[ ]`
   in plan.md. Likely needs §530-§534 infrastructure first; check
   `topo_order.json` for prerequisites.

3. **Stretch on §523**: the planner's optional (a) variant — a
   *residual* form helper `algebraicStability_residual`:
   `‖y_next‖²_G − ‖y_prev‖²_G = 2·⟨hF,Y⟩_D − ‖hF ⊕ y_prev‖²_M`
   (without any sign hypotheses). Direct `linarith` from cycle 241's
   identity, ~10 LOC. Lowest-risk add-on if a future cycle has
   spare budget after a primary ship.

4. **DO NOT** touch §441 / GPFS-slow paths (44 consecutive timeouts
   per issue `.prover-state/issues/cycle_182_gpfs_slowness.md`).

5. **DO NOT** attempt §302 (Cayley) or §324 (RK order theorems)
   in single-cycle scope — both need rooted-tree combinatorial
   infrastructure not yet in `Section310.lean`.
