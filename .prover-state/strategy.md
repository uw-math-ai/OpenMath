# Cycle 163 Strategy — def:530B/C Path A r-parametric refactor Phase B

## Context

Cycle 162 landed **Phase A** of the r-parametric refactor for
`def:530B`/`def:530C` Path A: a parametric padded GLM family
`paddedREulerGLM (r : ℕ) : GeneralLinearMethod 1 (r + 1)` (Section520),
a parametric starting family
`padCompatStartingMethodR (r : ℕ) : StartingMethod (r + 1)` (Section530),
and four axiom-clean structure lemmas. Sorry count remains 0 in both
files. The hand-written `r ∈ {1, 2, 3, 4}` instances coexist with
the parametric family.

Cycle 162's task results explicitly enumerate **Phase B** as the natural
cycle 163 deliverable. Phase B replaces the four hand-written pairs of
`HasOrderRelativeTo_explicit` / `HasOrder_explicit` witnesses (cycles
156/157/159/161 at r ∈ {2, 3, 4} × p ∈ {0, 1}, plus cycle 153/155 at
r = 1) with **two** parametric pairs of theorems indexed by `r : ℕ`.

Cycle 158 (p = 1) and cycle 160 (p = 0) helpers
(`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` and
`taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`) are already
validated at four call sites each — they are the load-bearing primitives
for the i = 0 channel of the parametric closure.

## Priority 1 — Phase B.1: parametric `HasOrderRelativeTo_explicit` witnesses

### Goal

Land two new theorems in `OpenMath/Chapter5/Section530.lean`:

```lean
theorem paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit
      (paddedREulerGLM r) (padCompatStartingMethodR r)
      (padCompatStartingMethodR_constituents_isExplicit r)
      (paddedREulerGLM_isExplicit r)
      0 f yex x₀ y₀
```

```lean
theorem paddedREulerGLM_hasOrderOne_padCompatStartingR (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit
      (paddedREulerGLM r) (padCompatStartingMethodR r)
      (padCompatStartingMethodR_constituents_isExplicit r)
      (paddedREulerGLM_isExplicit r)
      1 f yex x₀ y₀
```

### Closure recipe

Both proofs follow the **same structural template** (port of cycle
156/159/161's r = 2 / r = 3 / r = 4 closures, with the per-r constants
replaced by parametric `r`):

1. **Setup**: `intro i`, then `by_cases hi : i.val = 0`. Note the
   cycle 162 `padCompatStartingMethodR_applyExplicit` lemma uses
   exactly this `by_cases` shape, so it ports cleanly. Do NOT use
   `fin_cases i` — that only fires at concrete `r` values.

2. **i.val = 0 channel** (the substantive part):
   - **SM closed form**: rewrite `applyStartingThenStep_explicit` at
     index 0. Should reduce to
     `(y₀ + h * f y₀) + h * f (y₀ + h * f y₀)` after unfolding
     `paddedREulerGLM` (its `U`, `B`, `V` row-0 entries are all 1)
     and citing `padCompatStartingMethodR_applyExplicit r f y₀ h`
     plus a `simp [hi]` collapse.
   - **ES closed form**: `applyExactThenStarting_explicit` at index 0
     reduces to `yex(x₀ + h) + h * f (yex(x₀ + h))` via
     `padCompatStartingMethodR_applyExplicit` applied to
     `yex(x₀ + h)` instead of `y₀`.
   - **Power collapse**: `h^(p+1)` → `h` (p=0) or `h^2` (p=1) via
     `simp` or `ring`.
   - **Helper invocation**: one-liner
     `exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
       hf_lip hyex_x₀ hyex_deriv` (p=0) or
     `exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
       hf_lip hyex_x₀ hyex_C2 hyex_ode` (p=1).

3. **i.val ≠ 0 channel** (the zero-collapse):
   - SM at `i ≥ 1`: `applyStartingThenStep_explicit` reduces to 0
     because `paddedREulerGLM`'s `B[i]` and `V[i]` rows for `i ≥ 1`
     are all-zero, AND `padCompatStartingMethodR_applyExplicit` returns
     0 at `i.val ≠ 0`.
   - ES at `i ≥ 1`: `applyExactThenStarting_explicit` reduces to 0
     by the same `padCompatStartingMethodR_applyExplicit` clause.
   - Conclude `Diff = 0` and close with `Asymptotics.isBigO_zero`.

### Sanity-check the SM closed form first

Before diving into the full proof, run a small `lean_multi_attempt` /
`lean_goal` exploration to confirm the parametric closed form matches
the cycle-156/159/161 hand-written form. The key risk is that
`paddedREulerGLM`'s `Matrix.of fun (...) => if ... then 1 else 0`
body unfolds slightly differently from
`padded{2,3,4}DEulerGLM`'s `!![..]` body. If `simp` doesn't collapse
cleanly, you may need to add small unfolding helpers (e.g.
`paddedREulerGLM_U_zero_zero (r : ℕ)`,
`paddedREulerGLM_B_zero_zero (r : ℕ)`,
`paddedREulerGLM_V_zero_zero (r : ℕ)` proving the row-0/col-0 entries
explicitly, plus row-i (i ≥ 1) zero entries). Submit this triage to
`lean_multi_attempt` early; if the closed form is awkward, **introduce
the unfolding helpers as private sub-lemmas before the main witnesses**.

### Estimated LOC

- ~150–250 LOC total for both witnesses (cycle 162's projection).
- If unfolding helpers are needed: +30–50 LOC.

## Priority 2 — Phase B.2: parametric `def:530C` wrappers

After Phase B.1 lands, add two trivial corollaries (~30 LOC total):

```lean
theorem paddedREulerGLM_hasOrderZero (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit (paddedREulerGLM r) (paddedREulerGLM_isExplicit r)
      0 f yex x₀ y₀ :=
  ⟨padCompatStartingMethodR r,
   padCompatStartingMethodR_constituents_isExplicit r,
   padCompatStartingMethodR_isNonDegenerate r,
   paddedREulerGLM_hasOrderZero_padCompatStartingR r
     hf_lip hyex_x₀ hyex_deriv⟩
```

(and the analogous `_hasOrderOne` wrapper.)

These should be one-line existential closures using the cycle-162
`padCompatStartingMethodR_isNonDegenerate r` and
`padCompatStartingMethodR_constituents_isExplicit r` helpers.

## Priority 3 (stretch) — Phase B.3: reconciliation lemmas

If Phase B.1 and B.2 close with budget remaining (i.e. file LOC delta
under ~250 by mid-cycle), **try** the four reconciliation lemmas:

```lean
theorem paddedREulerGLM_zero_eq_explicitEulerGLM :
    paddedREulerGLM 0 = explicitEulerGLM
theorem paddedREulerGLM_one_eq_padded2DEulerGLM :
    paddedREulerGLM 1 = padded2DEulerGLM
theorem paddedREulerGLM_two_eq_padded3DEulerGLM :
    paddedREulerGLM 2 = padded3DEulerGLM
theorem paddedREulerGLM_three_eq_padded4DEulerGLM :
    paddedREulerGLM 3 = padded4DEulerGLM
```

(and analogous reconciliations for `padCompatStartingMethodR`.)

These likely close by `ext + decide` or `ext + simp` since
`Matrix.of`-bodies vs `!![..]`-bodies unfold differently.

**SHIP ONLY IF CLEAN**: if the first reconciliation attempt requires
non-trivial `Matrix.of`-vs-`!![..]` plumbing, defer to cycle 164. Do
NOT block cycle 163 on these — they are infrastructure cleanup, not a
critical-path item.

## Priority 4 — state updates (mandatory at end of cycle)

1. **Update `lean_status.json`**: bump `cycle` to 163 for both
   `def:530B` and `def:530C` rows. Append a brief one-line note (the
   `plan.md` row already serves as the long-form notes destination).
2. **Update `plan.md`**: append cycle 163 notes to the `def:530B` and
   `def:530C` rows describing the parametric Phase B closure. Mention
   that the four hand-written `r ∈ {1, 2, 3, 4}` pairs are now
   subsumed by the parametric family (but coexist; their retirement
   is downstream cleanup).
3. **Update `def_530B_scaffold_strategy.md`**: append a "Cycle 163
   update" section documenting Phase B.1, B.2 (and B.3 if landed).
   Mark Phase A and Phase B status; if reconciliation lemmas land,
   note that retirement of hand-written instances becomes a future
   cleanup option (do NOT actually retire them this cycle).
4. **Write `.prover-state/task_results/cycle_163.md`** per the CLAUDE.md
   format.

## Things NOT to try

These are explicit anti-patterns from prior cycles:

- **Do NOT submit to Aristotle.** Cycle 162's strategy correctly
  flagged historical Aristotle weakness on parametric `Fin`-indexed
  sums and decidable-equality case splits. The closure here is a
  mechanical port of cycle 156/159/161 templates plus cycle 158/160
  helper invocations. Manual proof wins.
- **Do NOT pursue Path B (implicit method via `ContractingWith` /
  `Function.IsFixedPt`).** Per `def_530B_scaffold_strategy.md`, this
  is multi-cycle infrastructure scope and remains deferred. Phase A
  + B saturate the *explicit* branch of `def:530B`/`def:530C`.
- **Do NOT add r = 5 or higher concrete-r hand-written witnesses.**
  Cycle 161 saturated the four-corner grid through r = 4. The
  parametric refactor (Phase A + B) is the systematic answer; further
  concrete instances are diminishing returns.
- **Do NOT attack `thm:550A` general-n.** Cycle 151 cancelled the
  second long-running Aristotle attempt at 21% (after the cycle-141
  cancellation at 6%). Closure requires structural infrastructure
  (cofactor-expansion induction or eigenvalue density), which is
  multi-cycle work. Stay clear unless a planner explicitly assigns it.
- **Do NOT touch `aux_515D_construct_ell_U_phi_A`** to remove
  `_hc_nn`/`_hc_le_one`. Per
  `stable_consistent_isConvergent_hc_nn.md`, this is multi-cycle
  refactor work and not on the critical path.
- **Do NOT use `fin_cases i`** for the parametric `i : Fin (r + 1)`
  case-split. It only fires at concrete `r`. Use
  `by_cases hi : i.val = 0` (validated by cycle 162's
  `padCompatStartingMethodR_applyExplicit`).
- **Do NOT introduce `axiom`/`constant`** for any helper.
- **Do NOT raise `maxHeartbeats` above 200000.** If the i.val = 0
  channel's closed-form simp blows past, factor a private unfolding
  helper (per the cycle 150 n=7 precedent in §550).
- **Do NOT modify `scripts/autonomous_loop.py`.** Worker is forbidden
  per CLAUDE.md and the standing
  `tautology_scanner_false_positives.md` issue. If the scanner flags
  any new `:= h_*` / `exact h_*` closer in your new lemmas, apply
  the cosmetic `h_<name>` → `h<name>` rename workaround.
- **Do NOT pivot to a fresh entity yet** (e.g. `def:451A`,
  `def:422B`, `def:442A`, `thm:535A`, `thm:541A`). Phase B closure
  is the higher-confidence single-cycle deliverable. The pivot is
  cycle 164 work.

## Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
2. `lake env lean OpenMath/Chapter5.lean` exits 0.
3. `grep -c sorry OpenMath/Chapter5/Section530.lean` returns 0
   (sorry count must NOT increase from cycle 162's 0).
4. `mcp__lean-lsp__lean_verify` on each new theorem returns axioms
   `[propext, Classical.choice, Quot.sound]` only. NO `sorryAx`.
5. Tautology-scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` clean against
   `OpenMath/`.
6. Cycle 153/155/156/157/159/161 theorems still axiom-clean (no
   regression). Spot-check `paddedREulerGLM_isExplicit` and the
   four cycle 162 lemmas to confirm Phase A is undisturbed.

## Faithfulness checklist

For each new theorem this cycle (Phase B.1 + B.2):

- **Tautology check**: clean. Conclusion is a substantive
  `HasOrderRelativeTo_explicit` / `HasOrder_explicit` claim, not a
  hypothesis re-export.
- **Identity check**: clean. The proofs do real work: closed-form
  algebraic rewrites + invocation of cycle 158/160 Taylor + Lipschitz
  helpers (substantive cycles' work) + zero-collapse via
  `Asymptotics.isBigO_zero` (substantive Mathlib lemma).
- **Hypothesis strength check**: hypotheses match cycle 156/157/159/161
  exactly. The parametric `(r : ℕ)` does not introduce extra
  constraints over the hand-written instances (`paddedREulerGLM r`'s
  shape is total over `r`, no `NeZero r` / `Nat.succ_pos` pollution).
- **Definition smuggling check**: N/A — no new `def`s land this cycle
  (Phase A's `paddedREulerGLM`, `padCompatStartingMethodR`, etc. are
  already in place from cycle 162).
- **Absent theorem check**: N/A — Phase B doesn't promise any sorry'd
  follow-ups.

## Backup plan

If Phase B.1's i.val = 0 closed-form simp doesn't collapse cleanly
within ~30 minutes of attempts:

1. **Fallback A**: introduce three private unfolding lemmas
   `paddedREulerGLM_U_zero_zero (r : ℕ)`,
   `paddedREulerGLM_B_zero_zero (r : ℕ)`,
   `paddedREulerGLM_V_zero_zero (r : ℕ)` proving the row-0 / col-0
   entries equal 1, plus three more for the `i ≥ 1` zero entries.
   Then `simp` with these in the unfolding set.

2. **Fallback B**: if Fallback A still doesn't collapse, land **only
   the p = 0 parametric witness** (`_hasOrderZero_padCompatStartingR`)
   plus its def:530C wrapper. Defer p = 1 to cycle 164. Cycle's net
   advance is +2 axiom-clean parametric theorems (instead of +4),
   but still subsumes a quarter of the hand-written grid.

3. **Fallback C**: if neither closure works, **revert** the new
   parametric witnesses and instead land **two non-parametric r = 5
   hand-written witnesses** (`padded5DEulerGLM` + `pad5CompatStartingMethod`
   following the cycle 161 r = 4 template). This is a regression
   relative to the strategy but guarantees a +2 axiom-clean cycle. The
   cycle 162 Phase A infrastructure remains intact for cycle 164 to
   retry Phase B with more time.

Document any fallback usage in `task_results/cycle_163.md`.

## Estimated LOC delta

- **Best case** (Phase B.1 + B.2 + B.3 land): +200–350 LOC for B.1+B.2,
  plus +100–200 LOC for B.3 reconciliations. Total ~300–550 LOC.
- **Expected case** (B.1 + B.2 land, B.3 deferred): +200–350 LOC.
- **Fallback A** (B.1 with unfolding helpers, + B.2): +250–400 LOC.
- **Fallback B** (only p=0 closure): +120–200 LOC.
- **Fallback C** (revert + r=5 hand-written): +250–350 LOC.

All within reasonable single-cycle budget.
