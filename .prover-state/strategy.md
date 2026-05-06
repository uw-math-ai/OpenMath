# Cycle 153 Strategy — def:530B Path A Step 3: HasOrderRelativeTo_explicit + p=0 witness

## State recap

* Sorry count: **0** in `OpenMath/Chapter5/Section530.lean` (and 0 in
  `Section550.lean` — the two `sorry` matches there are word-only
  mentions inside docstrings).
* Cycle 152 landed def:530B Path A Step 2 axiom-clean (+213 LOC,
  file 360 → 573 LOC). Operator infrastructure available:
  - `GeneralizedRungeKuttaMethod.explicitStageValue` /
    `.explicitApply`,
  - `StartingMethod.applyExplicit`,
  - `applyExactThenStarting_explicit` (= textbook `ES`),
  - `Section510.GeneralLinearMethod.IsExplicit` /
    `.explicitStageValue`,
  - `applyStartingThenStep_explicit` (= textbook `SM`).
  Sanity lemmas
  `trivialStartingMethod_applyExplicit`,
  `trivialStartingMethod_applyExactThenStarting_explicit`, and
  `explicitEulerGLM_isExplicit` are axiom-clean.
* No pending Aristotle results to incorporate.
* Cycle-148 Aristotle project `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`
  (general-`n` thm:550A, fire-and-forget) was IN_PROGRESS at 18 % at
  the cycle 150 single-poll. ~89 h elapsed. **Single-poll once at
  the start of this cycle, then move on.**

---

## Aristotle housekeeping (do this FIRST, at most once)

1. **Single-poll** project `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`
   via `mcp__aristotle__get_status`. Three branches:

   * **COMPLETE / SUCCESS**: extract the proof. Re-introduce the
     general-`n` statement `doublyCompanionMatrix_det_factorization`
     (removed in cycle 139) into `Section550.lean` with the returned
     proof inlined. Verify axiom-clean via `lean_verify`. If
     axiom-clean, update the §550 row of `plan.md` from `[~]` →
     `[x]` and bump `lean_status.json` → `"status": "formalized"`,
     `"cycle": 153`.
   * **FAILED / CANCELLED / errored**: leave §550 alone; do NOT
     submit any replacement Aristotle job (two prior long-runs —
     cycle 141 project `7062c2a2-…` cancelled at 6 %, cycle 148
     project `2c4630b2-…` — are sufficient evidence the prover
     cannot close this without upstream infrastructure).
   * **IN_PROGRESS** (any percentage): leave it running. Move on.
     Do NOT re-poll later in this cycle.

2. **Do NOT submit a new Aristotle job** for thm:550A general-`n`
   or any n=8 stepping stone this cycle. Cycle 150's task results
   note the seven-`n` data set (n=1..7) is now strong enough that
   further stepping stones provide marginal value; effort should
   pivot to def:530B Path A Step 3 (Priority 1 below).

3. **Do NOT poll any other Aristotle project.** No other jobs are
   pending.

---

## Priority 1 (PRIMARY) — def:530B Path A Step 3

**Target**: define the order predicate `HasOrderRelativeTo_explicit`
and prove the `p = 0` non-vacuity witness for
`explicitEulerGLM × trivialStartingMethod`.

**Estimated**: 50–80 LOC. Single cycle.

### Step 3a — Imports

Add to the head of `OpenMath/Chapter5/Section530.lean` (under the
existing `import OpenMath.Chapter5.Section510` line):

```lean
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
```

(`LipschitzWith` is already in scope transitively via Mathlib's
core; if not, add `import Mathlib.Topology.MetricSpace.Lipschitz`.)
Verify with `lake env lean OpenMath/Chapter5/Section530.lean`
exits 0 before adding the new code.

### Step 3b — Predicate `HasOrderRelativeTo_explicit`

Place at the **end** of the existing
`namespace OpenMath.Chapter5.Section530` block (the second one,
re-opened at file line 539, just before its `end ...` closer at
line 573). Open `Asymptotics` and `Filter` locally:

```lean
section OrderRelativeTo

open Asymptotics Filter

/-- **Definition 530B (Butcher §530, p. 432) — explicit-only variant.**
A general linear method `M` has *order `p`* relative to a non-degenerate
starting method `S` (with both `M` and every `S_i` explicit) at the
initial value problem `(f, x₀, y₀, yex)` if the difference between
the two operators

  * `SM(y₀, h)` (=
    `applyStartingThenStep_explicit M S _hS _hM f y₀ h`)
  * `ES(y₀, h)` (=
    `applyExactThenStarting_explicit S _hS f yex x₀ h`)

is `O(h^{p+1})` componentwise as `h → 0`.

Internal helper for the explicit-only branch of def:530B per
`def_530B_scaffold_strategy.md`. The Path-B implicit variant via
fixed-point machinery remains deferred.

`HasOrderRelativeTo_explicit` does **not** itself impose
non-degeneracy of `S`; downstream consumers should pair it with an
explicit `S.IsNonDegenerate` hypothesis where needed. -/
def HasOrderRelativeTo_explicit
    {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r)
    (S : StartingMethod r)
    (hS : ∀ i, (S.method i).IsExplicit)
    (hM : M.IsExplicit)
    (p : ℕ)
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ i : Fin r,
    (fun h : ℝ =>
        applyStartingThenStep_explicit M S hS hM f y₀ h i
          - applyExactThenStarting_explicit S hS f yex x₀ h i)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (p + 1))
```

### Step 3c — `p = 0` non-vacuity witness

The per-component difference at `(s, r) = (1, 1)` reduces to:

```text
SM(y₀, h)[0]
  = h · (M.B 0 0) · f(Y_0) + (M.V *ᵥ y_input)[0]
  = h · 1 · f(y_input 0) + 1 · (y_input 0)             -- explicitEulerGLM
  = (y₀ + h·f(y₀)) + h · f(y₀ + h·f(y₀))               -- y_input from cycle 152

ES(y₀, h)[0]
  = yex(x₀ + h) + h · f(yex(x₀ + h))                   -- cycle 152 sanity

SM[0] - ES[0]
  = [(y₀ + h·f(y₀)) - yex(x₀ + h)]                     -- "Taylor" piece T1(h)
  + h · [f(y₀ + h·f(y₀)) - f(yex(x₀ + h))]             -- "Lipschitz" piece T2(h)
```

Both pieces are `=O[nhds 0] (fun h => h)` under the natural IVP
hypotheses:

* `T1(h)` is `o(h)` by `HasDerivAt yex (f y₀) x₀` together with
  `yex x₀ = y₀`. Specifically,
  `(fun h => yex (x₀ + h) - y₀ - h·f(y₀)) =o[nhds 0] (fun h => h)`
  unfolds from `HasDerivAt yex (f y₀) x₀`'s
  `HasDerivAtFilter`/`IsLittleO` characterization. Then
  `T1 = -(yex(x₀+h) - y₀ - h·f(y₀))`, so it inherits `o(h)`, and
  `IsLittleO.isBigO` closes it.
* `T2(h)` is `O(h)` by combining: (i) Lipschitz `f` with constant
  `L`, giving `|f(a) - f(b)| ≤ L · |a - b|`; (ii) `|a - b|` is
  bounded near `h = 0` because `a → y₀, b → yex(x₀) = y₀` (use
  `HasDerivAt.continuousAt` on `yex` at `x₀`, and continuity of
  `h ↦ y₀ + h·f(y₀)` at `0`). Hence `|h · (f(a) - f(b))|
  ≤ L · |h| · |a - b|`, with `|a - b|` eventually bounded, so the
  product is `O(h)`.

The skeleton:

```lean
/-- **Non-vacuity (Path A Step 3, p = 0).** Explicit Euler GLM has
order `0` relative to the trivial starting method on any IVP whose
exact solution `yex` satisfies `yex x₀ = y₀` and
`HasDerivAt yex (f y₀) x₀`, with `f` Lipschitz.

Witnesses that `HasOrderRelativeTo_explicit` is genuinely satisfiable
on the most degenerate non-trivial GLM × starting-method shape. -/
theorem explicitEulerGLM_hasOrderZero_trivialStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit explicitEulerGLM trivialStartingMethod
      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
      explicitEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  -- Step 1: collapse SM[0] and ES[0] to closed forms via the cycle
  -- 152 sanity lemmas + an explicit `Section510.GeneralLinearMethod.explicitStageValue`
  -- unfold at `s = 1`.
  -- Step 2: rewrite the difference as `T1(h) + T2(h)` per the
  -- decomposition above.
  -- Step 3: prove `T1 =O h` via `HasDerivAt → IsLittleO → IsBigO`.
  -- Step 4: prove `T2 =O h` via `LipschitzWith.dist_le_mul`,
  -- `Real.dist_eq`, and an eventual `|a - b|`-bound near `h = 0`.
  -- Step 5: combine via `IsBigO.add` and finish with `simpa`.
  sorry  -- replace via the T1 + T2 decomposition
```

The `sorry` placeholder is for the worker to close in this cycle —
the final commit MUST be sorry-free.

### Step 3d — Closing the body

Concrete tactic sketch:

1. **Collapse SM[0] / ES[0] to closed form.** SM[0] requires
   unfolding `applyStartingThenStep_explicit` once, then unfolding
   `Section510.GeneralLinearMethod.explicitStageValue` at the
   `s = 1` base case (the empty `Fin 0` sum collapses via
   `Fin.sum_univ_zero`). The `M.B 0 0`, `M.V 0 0` projections on
   `explicitEulerGLM` evaluate via `simp [explicitEulerGLM,
   Matrix.mulVec, dotProduct, Fin.sum_univ_one]`. ES[0] is already
   closed by `trivialStartingMethod_applyExactThenStarting_explicit`
   (cycle 152). After this step the goal should be a direct
   `=O[nhds 0]` claim about
   `fun h => (y₀ + h·f y₀) + h·f(y₀ + h·f y₀)
              - (yex(x₀+h) + h·f(yex(x₀+h)))`.

2. **Decompose into T1 + T2** via `IsBigO.add` after rewriting the
   difference algebraically. Use `Asymptotics.IsBigO.add`. Concrete
   form to feed `IsBigO.add`: introduce
   `T1 := fun h => y₀ + h·f y₀ - yex(x₀+h)` and
   `T2 := fun h => h * (f(y₀ + h·f y₀) - f(yex(x₀+h)))`, then prove
   the SM[0]-ES[0] expression equals `T1 h + T2 h` pointwise via
   `funext` + `ring`.

3. **T1 is `O(h)`.** Use `HasDerivAt.isLittleO`:
   `hyex_deriv.isLittleO` gives some Mathlib lemma whose conclusion
   is morally `(fun h => yex(x₀+h) - yex x₀ - h·f y₀) =o[nhds 0] id`.
   The exact name to verify — try `HasDerivAt.isLittleO_sub_smul`
   or `HasDerivAt.isLittleO` first via `lean_local_search`. If no
   single-shot wrapper exists, unfold `HasDerivAt → HasFDerivAt →
   HasFDerivAtFilter` and access the `IsLittleO` field directly via
   `hyex_deriv.hasFDerivAt.isLittleO` or
   `hyex_deriv.def`/`HasDerivAt.def`. Then negate (T1 is the
   negative of that little-o) via `IsLittleO.neg_left`, congr-rewrite
   `yex x₀ = y₀` via `hyex_x₀`, and convert to `IsBigO` via
   `IsLittleO.isBigO`. Final shape: `T1 =O[nhds 0] fun h => h`.
   (If Mathlib's `IsLittleO` formulation is `fun h => h` vs `id`,
   bridge via `IsLittleO.congr_right` with `(fun h => h) = id` from
   `funext`.)

4. **T2 is `O(h)`.** Bound:
   - `|f(a h) - f(b h)| ≤ L · |a h - b h|` via
     `LipschitzWith.dist_le_mul` + `Real.dist_eq`, where
     `a h := y₀ + h·f y₀` and `b h := yex(x₀+h)`.
   - `a h - b h → 0` as `h → 0` since both sides → `y₀`. Use
     `hyex_deriv.continuousAt` (HasDerivAt → ContinuousAt) +
     `Continuous.tendsto` for the `a` side. Hence `a - b` is
     `IsLittleO 1` (i.e. → 0) near `0`. Convert to `IsBigO 1` via
     `IsLittleO.isBigO`.
   - `T2 h = h * (f(a h) - f(b h))`. The factor `h` is `O(h)`
     trivially (`Asymptotics.isBigO_refl`). The factor
     `f(a h) - f(b h)` is `O(1)` (bounded near `0`, follows from
     `IsLittleO 1 → IsBigO 1` after the limit argument above plus
     a bound for `h` away from `0` — or simpler: directly use
     `LipschitzWith → Continuous → ContinuousAt 0 → IsBigO 1`).
   - Multiply via `IsBigO.mul`: `O(h) * O(1) = O(h)`. Or simpler
     route — use `IsLittleO` for the second factor (it tends to 0)
     to get `T2 =o[nhds 0] h`, hence `O(h)`.

5. **Combine.** `IsBigO.add` of step 3's `T1 =O[nhds 0] h` and step
   4's `T2 =O[nhds 0] h` gives `(T1 + T2) =O[nhds 0] h`. Note that
   `(p + 1)` in the predicate equals `1` at `p = 0`, so the goal's
   RHS `fun h => h ^ 1` collapses to `fun h => h` via `pow_one`
   (use `simpa [pow_one]` or
   `IsBigO.congr_right (by simp [pow_one])`).

If step 3's HasDerivAt → IsLittleO unfolding turns out to be
finicky (no clean Mathlib wrapper), **fallback A**: use the
simpler `Differentiable + linear approximation` lemma. Or the
"manual" little-o: `hyex_deriv.tendsto_nhdsWithin` gives
`Tendsto (slope yex x₀) (𝓝[≠] x₀) (𝓝 (f y₀))`; reformulate T1 as
the slope minus the limit, multiplied by h.

If step 4's algebra plumbing turns out painful, **fallback B**:
prove T2 is `o(h)` directly (since `f(a h) - f(b h) → 0` and `h →
0`, the product is `o(h)` by `IsLittleO.mul_isBigO` or similar).

### Step 3e — Verification

After landing the proof:

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake build OpenMath.Chapter5.Section530` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → `0`.
* `lean_verify OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero_trivialStarting`
  must return `[propext, Classical.choice, Quot.sound]` only.

---

## Priority 2 (cleanup) — plan.md / lean_status.json bookkeeping

After Priority 1 lands:

1. Update `plan.md` Chapter 5 entry for `def:530B`:
   * Append "Cycle 153: **Path A Step 3 complete** —
     `HasOrderRelativeTo_explicit` predicate + axiom-clean `p = 0`
     non-vacuity witness for explicit Euler GLM × trivialStartingMethod
     (under `LipschitzWith` + `HasDerivAt` IVP hypotheses). Sorry
     count remained 0; LOC delta ~50–80."
   * Status remains `[ ]` → `[~]` (still partial: textbook def:530B
     covers both explicit and implicit methods; only the explicit
     branch has been formalized).
2. Update `lean_status.json` row for `def:530B`:
   * Set `"status": "partial"`, bump `"cycle": 153`, add a brief
     `"notes"` entry pointing at the Path A explicit branch.
3. Update `.prover-state/issues/def_530B_scaffold_strategy.md`'s
   "Cycle plan" section: add a "Cycle 153 update — Path A Step 3
   complete" sub-section mirroring the cycle 152 update format.

---

## What NOT to try (do NOT repeat these failures)

1. **Do NOT** introduce a sorry-first scaffold that closes the
   operators with `sorry` and only writes the predicate (cycle 149
   pattern, scored −2). The cycle 152 explicit-only operator bodies
   are already closed; cycle 153's predicate body has no sorry-able
   intermediates.

2. **Do NOT** attempt the implicit-method (Path B) generalization
   of `HasOrderRelativeTo` via `ContractingWith` /
   `Function.IsFixedPt`. Path B is multi-cycle infrastructure (per
   `def_530B_scaffold_strategy.md`); cycle 153 stays in Path A.

3. **Do NOT** widen the `p = 0` witness to `p = 1` in the primary
   plan. The textbook classifies explicit Euler as order 1 relative
   to the canonical starting method, but proving `p = 1` requires a
   `ContDiff ℝ 2 yex` hypothesis plus a second-order Taylor-remainder
   computation — that's a cycle 154+ stretch goal, NOT cycle 153
   primary scope. (See "Stretch goal" below for an opt-in path.)

4. **Do NOT** raise `maxHeartbeats` above 200000 anywhere. If the
   composition of `T1 + T2` runs slow, decompose into named
   sub-helpers per CLAUDE.md.

5. **Do NOT** edit `scripts/autonomous_loop.py` or any `scripts/*`
   file. Scanner / loop-maintenance is out of scope (per cycle 015
   consultant guidance and `tautology_scanner_false_positives.md`).

6. **Do NOT** introduce `axiom` or `constant` declarations. If
   Mathlib lacks a lemma you'd want, build it inline as a private
   helper.

7. **Do NOT** poll Aristotle more than once for the same project
   in this cycle. The CLAUDE.md "single check after 30 min" rule
   applies; project 2c4630b2 has had >89 h to run, one poll is
   plenty.

8. **Do NOT** submit any new Aristotle job for thm:550A general-`n`
   or n=8 stepping stones. Two prior long-runs (cycle 138 / cycle
   148) failed (one cancelled at 6 % after 24 h; the other still
   IN_PROGRESS at 18 % after 89 h). Manual cofactor-expansion or
   eigenvalue-density infrastructure is multi-cycle work, out of
   cycle 153 scope.

9. **Do NOT** rename `h_<name>` → `h<name>` to silence the
   tautology scanner; the cycle 153 deliverables don't trip it.
   Rename only if the cycle-end evaluator flags a real new false
   positive.

10. **Do NOT** modify `OpenMath/Chapter5/Section510.lean` or any
    file outside `Section530.lean` for this cycle (other than the
    bookkeeping files in Priority 2). The cycle 152 boundary
    (defining `Section510.GeneralLinearMethod.IsExplicit` and
    `.explicitStageValue` inside a re-opened namespace block in
    `Section530.lean`) is the canonical pattern; do NOT relocate
    those defs.

11. **Do NOT** strengthen `HasOrderRelativeTo_explicit`'s
    signature with extra hypotheses (e.g. `S.IsNonDegenerate`,
    `ContDiff yex`, `Continuous f`). Keep the predicate
    definitionally clean — let consumers add hypotheses at the
    call site. (See the predicate's docstring.)

---

## Backup plans

* **B1 (predicate only)**: if the closed-form `T1 + T2`
  decomposition turns out to need more Mathlib plumbing than fits
  in one cycle, land just `HasOrderRelativeTo_explicit` (predicate,
  no sorry) plus a *vacuous* `p = 0` non-vacuity witness using a
  separation trick: specialize at `f := fun _ => 0,
  yex := fun _ => y₀`, where SM[0] = ES[0] = `y₀ + h·0 + h·0 = y₀`
  identically, so the difference is `fun _ => 0`, and
  `(fun _ => (0 : ℝ)) =O[nhds 0] (fun h => h ^ 1)` is trivial via
  `Asymptotics.isBigO_zero`. Document that this is a vacuous
  witness and leave the substantive `HasDerivAt`+`Lipschitz`
  witness for cycle 154. Acceptable but inferior — pursue B1 only
  if the primary plan stalls past 60 minutes of worker time.

* **B2 (no `Asymptotics.Defs` available)**: if the import breaks
  the build (unlikely; `Section515.lean` already uses `Asymptotics`),
  add `import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`
  instead, or fall back to defining `HasOrderRelativeTo_explicit`
  as `Filter.Tendsto (fun h => (diff h) / h^(p+1)) (𝓝 0) (𝓝 0)`
  (equivalent by `Asymptotics.isLittleO_iff_tendsto`). Any reformulation
  must remain **mathematically equivalent** to the textbook
  `O(h^{p+1})` characterization.

* **B3 (Aristotle for the body)**: if both primary and B1 stall,
  submit an Aristotle job for the cycle 153 witness body only (NOT
  the predicate — the predicate is short enough to write manually).
  Provide the closed-form decomposition above as prompt context.
  Single submission, do NOT poll within the cycle; cycle 154 picks
  up the result. **Only fire B3 as a true fallback** — manual
  closure is preferred and the proof is well-scoped.

---

## Stretch goal (only if Priority 1 lands fast)

If Priority 1 + Priority 2 close in under 90 minutes of worker
time, attempt **Step 4: order-`1` witness** using a
`ContDiff ℝ 2 yex` hypothesis + second-order Taylor remainder.
Estimated +50–100 LOC; the witness would refine the cycle 153
result to `p = 1` for explicit Euler × trivialStartingMethod,
matching the textbook classification. The bound on the second-order
Taylor remainder around `x₀` is supplied by Mathlib's
`taylor_within_apply` or equivalent; the residual after the
linear term has `|residual| ≤ M_2 · h^2 / 2` for `M_2` bounding
`|deriv (deriv yex)|` near `x₀`.

If this stretch is attempted, mark it clearly in the commit message
("BONUS: Path A Step 4 p=1 witness"); roll back if it fails to
close cleanly, NEVER let the stretch introduce a sorry that leaks
into the cycle commit.

---

## Definition of done

Cycle 153 is successful (score ≥ +1) iff **all** the following hold
when the worker commits:

* `Section530.lean` has 0 sorries and compiles cleanly.
* `HasOrderRelativeTo_explicit` is defined.
* `explicitEulerGLM_hasOrderZero_trivialStarting` is proven and
  axiom-clean (`[propext, Classical.choice, Quot.sound]` only).
* `plan.md` and `lean_status.json` updated for def:530B status.
* `def_530B_scaffold_strategy.md` updated with a cycle 153 entry.

A score-2 outcome additionally requires the Aristotle housekeeping
to land cleanly (whatever the poll branch was), and the commit
message to clearly summarize Path A Step 3 alongside any §550
update. If Priority 1 lands but Priority 2 bookkeeping is missing,
expect score +1 not +2.
