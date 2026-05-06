# Cycle 157 Results

## Worked on
- `def:530B` Path A r=2 × p=1 witness:
  `padded2DEulerGLM_hasOrderOne_padCompatStarting`
  (`OpenMath/Chapter5/Section530.lean`).
- `def:530C` Path A r=2 × p=1 existential closure:
  `padded2DEulerGLM_hasOrderOne` (same file).

## Approach
Followed the cycle 157 strategy verbatim — a mechanical port of cycle
154's `explicitEulerGLM_hasOrderOne_trivialStarting` to the padded
`(s, r) = (1, 2)` setting:

* **i=0 channel** — Verbatim port of cycle 154 lines 918–1086 with the
  three name swaps:
  - `explicitEulerGLM` → `padded2DEulerGLM`
  - `trivialStartingMethod` → `padCompatStartingMethod`
  - constituents-explicit and `_isExplicit` proof arguments swapped to
    the cycle-156 padCompat counterparts.
  - The hES sub-proof uses cycle 156's manual `show … = …` +
    `rw [padCompatStartingMethod_applyExplicit]` + `rfl` pattern (no
    padCompat-side analog of `trivialStartingMethod_applyExactThenStarting_explicit`
    exists, but the closed form is identical).
  - The hSM sub-proof mirrors cycle 156's i=0 hSM: `show` exposes the
    GLM index `0 : Fin 2`, then `rw` + `unfold explicitStageValue` +
    `simp [padded2DEulerGLM, Matrix.mulVec, dotProduct]` + `ring`.
  - All Taylor + Lipschitz machinery (htaylor, hT_eval, hderiv_x0,
    htend, hres, hT1_eq, hconst, hT1, hT2 calc-block) transfers
    verbatim because the closed forms `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)`
    and `yex(x₀+h) + h·f(yex(x₀+h))` match exactly between cycles
    154 and 157.
* **i=1 channel** — Verbatim port of cycle 156 lines 1296–1335 with
  one replacement: `h ^ (0 + 1)` → `h ^ (1 + 1)`. SM[1] = ES[1] = 0
  collapses Diff to identically zero, closed by
  `Asymptotics.isBigO_zero`.
* **def:530C wrapper** — One-line `refine ⟨padCompatStartingMethod,
  padCompatStartingMethod_constituents_isExplicit,
  padCompatStartingMethod_isNonDegenerate, ?_⟩` followed by `exact`
  of the witness theorem (mirrors `padded2DEulerGLM_hasOrderZero`).

## Result
**SUCCESS — axiom-clean.** Both new theorems compile under default
heartbeats and `lean_verify` returns
`[propext, Classical.choice, Quot.sound]` for each:

```
OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne_padCompatStarting
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne
  → [propext, Classical.choice, Quot.sound]
```

Cycle 156's regression check passes:
`padded2DEulerGLM_hasOrderZero_padCompatStarting` remains
`[propext, Classical.choice, Quot.sound]`.

`OpenMath/Chapter5/Section530.lean`: 1361 → 1600 LOC (+239, within
target +210–260, below ceiling 320). Sorry count: 0 → 0 (invariant
preserved). `lake env lean OpenMath/Chapter5/Section530.lean` and
`lake env lean OpenMath/Chapter5.lean` both exit 0 with no output.

## Faithfulness check

### `padded2DEulerGLM_hasOrderOne_padCompatStarting`
- Entity ID: `def:530B` (witness; Path A, `r = 2`, `p = 1`).
- Textbook statement (quoted from `entities/def_530B.json`):
  > Consider a general linear method $\mathcal{M}$ and a non-degenerate
  > starting method $\mathcal{S}$. The method $\mathcal{M}$ has order
  > $p$ relative to $\mathcal{S}$ if the results found from
  > $\mathcal{S}\mathcal{M}$ and $\mathcal{E}\mathcal{S}$ agree to within
  > $O(h^{p+1})$.
- Lean statement captures: **same content**. The Lean theorem instantiates
  `HasOrderRelativeTo_explicit` (the predicate proved in cycle 153 to
  faithfully unfold to the textbook's componentwise `O(h^{p+1})` agreement
  on the SM−ES diff) at `M = padded2DEulerGLM`, `S = padCompatStartingMethod`
  (non-degenerate via `padCompatStartingMethod_isNonDegenerate`),
  `p = 1`. Hypothesis pack matches cycle 154 verbatim
  (`LipschitzWith L f`, `ContDiff ℝ 2 yex`, full ODE relation,
  `yex x₀ = y₀`); these are exactly the Lipschitz + smoothness
  requirements that justify the `O(h²)` bound for explicit Euler in
  Butcher's textbook treatment of order-1 methods.
- No divergence.

### `padded2DEulerGLM_hasOrderOne`
- Entity ID: `def:530C` (witness; Path A, `r = 2`, `p = 1`).
- Textbook statement (quoted from `entities/def_530C.json`):
  > A general linear method $\mathbf{M}$ has order $p$ if there exists
  > a non-degenerate starting method $\mathbf{S}$ such that
  > $\mathbf{M}$ has order $p$ relative to $\mathbf{S}$.
- Lean statement captures: **same content**. The Lean theorem produces
  the existential closure `HasOrder_explicit padded2DEulerGLM
  padded2DEulerGLM_isExplicit 1 f yex x₀ y₀` by exhibiting
  `padCompatStartingMethod` as the witness `S`, supplying
  `padCompatStartingMethod_constituents_isExplicit` for the
  Path-A explicit-constituents constraint,
  `padCompatStartingMethod_isNonDegenerate` for the non-degeneracy
  clause, and the cycle-157 witness theorem above for the
  `HasOrderRelativeTo_explicit` component.
- No divergence.

## Pre-commit faithfulness checklist
- TAUTOLOGY CHECK: ✓ No conclusion appears verbatim as a hypothesis.
  The `HasOrderRelativeTo_explicit` and `HasOrder_explicit` predicates
  state asymptotic-agreement properties; hypotheses are Lipschitz +
  smoothness + ODE conditions, none of which contain the conclusion.
- IDENTITY CHECK: ✓ Neither proof is a single `exact h_*` identity.
  The witness theorem performs nontrivial Taylor + Lipschitz analysis;
  the existential closure does packaging via `refine ⟨…, ?_⟩` + `exact`
  of the witness, but the witness itself does the mathematical work.
- DEFINITION SMUGGLING: ✓ No new structures or `Prop` fields introduced.
- HYPOTHESIS STRENGTH: ✓ Hypothesis pack is identical to cycle 154's
  (the cycle-154 strategy already established that `ContDiff ℝ 2` +
  full ODE relation are exactly what Taylor's theorem at order 2
  requires for the closed-form expansion of `yex(x₀+h)`); no new
  hypotheses introduced relative to the established pattern.
- ABSENT THEOREM: ✓ No `sorry` or "will be proved below" comments.
- The `h_<name>` / `h_inner` idiom is avoided (cf. tautology scanner
  false positives D1/D2). All hypothesis identifiers use `hname` form.

## Dead ends
None. The mechanical port executed cleanly on the first compile —
the cycle 154 Taylor + Lipschitz machinery transfers verbatim because
the i=0 channel's closed forms are identical between trivialStartingMethod
and padCompatStartingMethod. The only adaptation needed beyond name
swaps was switching the hES tactic from cycle 154's
`trivialStartingMethod_applyExactThenStarting_explicit` lemma to the
manual `show + rw + rfl` pattern from cycle 156, which the strategy
flagged in advance.

## Discovery
- The Path A non-vacuity four-corner grid `(r ∈ {1, 2}) × (p ∈ {0, 1})`
  is now saturated. Future cycles can rely on
  `HasOrderRelativeTo_explicit` and `HasOrder_explicit` being
  well-defined non-vacuous predicates at multiple sizes (small r=1
  baseline + non-trivial r=2 baseline) and at both small (p=0) and
  textbook-standard (p=1, matching Butcher's classification of
  explicit Euler as order 1) orders.
- The cycle 154 Taylor + Lipschitz closure is genuinely portable
  across multi-channel padded GLMs as long as the row-0 channel's
  closed form matches explicit Euler's (and inactive rows collapse
  to zero). This is reassuring for any future thm:532A work that
  proves order properties for higher-order Runge-Kutta-type GLMs:
  the closure pattern is structurally robust to padding.
- The i=0 T1/T2 closure block is now duplicated across cycles
  153/154/156/157 with only minor structural variations. A
  parameterized helper that abstracts over `(M, S, hSM_closed,
  hES_closed, p)` would recover roughly 140 LOC. (Strategy flagged
  this as orthogonal to cycle 157's witness goal — defer to a
  dedicated refactoring cycle 158+.)

## Suggested next approach
Two viable directions for cycle 158:

1. **Pivot to `thm:532A` (Algebraic analysis of order)** — the next
   textbook entity in §53. This needs multi-cycle infrastructure
   (rooted-tree elementary differentials from §31x or a polynomial
   test-function reformulation), so the planner should consider
   either a sorry-first scaffold (with full acceptance that sorry
   count will go 0 → N for several cycles, distinct from the cycle
   138/139 / 149/150 rollback precedents because thm:532A is a new
   target rather than a re-attempt) or a cautious series of
   prerequisite cycles building rooted-tree machinery. The strategy
   should explicitly state which mode it is in.

2. **Refactor cycles 153/154/156/157 i=0 T1/T2 closures** into a
   shared helper. Net LOC: roughly −140. This is *appealing* because
   it would make any future Path A r ≥ 3 or higher-p witness
   one-line corollaries. It is also *risky* because the four call
   sites have subtle differences (hypothesis packs vary slightly:
   cycle 153 uses `HasDerivAt yex (f y₀) x₀` only, cycles 154/156/157
   use the full ODE relation; cycle 153's T1 is `o(h)`, cycles
   154/157's T1 is `O(h²)`). A clean refactor needs to parametrize
   over the Taylor degree `n` and the smoothness assumption
   `ContDiff ℝ n yex`, which means the helper signature is non-trivial.
   Recommended structure: extract a single `taylor_lipschitz_closure`
   lemma taking `(M, S, hSM_closed, hES_closed, n, hf_lip, hyex_x₀,
   hyex_Cn, hyex_ode)` → asymptotic O(h^n) bound on the diff. The
   four existing witnesses then reduce to one-line applications.
   Suggested as cycle 158 if the Aristotle queue is empty.

Either is acceptable; the planner's call. Direction 1 advances the
textbook pipeline; direction 2 reduces technical debt before the
file gets larger.

## LOC delta
+239 LOC (1361 → 1600). Within target (+210–260), below ceiling (320).

## Sorry count
0 → 0 (invariant preserved).

## Aristotle usage
None this cycle. Per strategy, the proof is mechanical and manual
closure beats Aristotle on this kind of port (cf. cycle 154 closing
while Aristotle was IN_PROGRESS). No new pending Aristotle jobs.
