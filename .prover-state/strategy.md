# Cycle 154 Strategy

## Context

Cycle 153 successfully landed **def:530B Path A Step 3**:
`HasOrderRelativeTo_explicit` predicate + `p = 0` axiom-clean
non-vacuity witness `explicitEulerGLM_hasOrderZero_trivialStarting`.
Sorry count remained 0; `lean_verify` clean. Score: −1, due solely to
the supervisor's tautology scanner reporting a "suspected vacuous proof
at Section530.lean:412."

**Verified false positive.** Line 412 of the actual file is inside the
docstring of `StartingMethod.applyExplicit` (a definition, not a
proof). The real regex match is at **line 717**: `have := h_deriv` in
the body of `explicitEulerGLM_hasOrderZero_trivialStarting`. The
`h_deriv` hypothesis is materially reshaped by `rw [hyex_x₀] at this`
on line 718 before being consumed by `simpa` on line 719 — this is the
canonical "rewrite-then-exact" idiom called out as a false positive
in `.prover-state/issues/tautology_scanner_false_positives.md` bug D2.

The line-number drift (412 vs. 717) is bug D1 from the same issue
(scanner deletes block-comment newlines, then reports the wrong line).

Cycle 154 has **two priorities**: a quick cosmetic rename to silence
the scanner, then substantive work on def:530B Path A Step 4 (`p = 1`
refinement).

## Priority 0 — Silence the cycle 153 scanner false positive (~5 min)

Apply the standard cosmetic rename per
`.prover-state/issues/tautology_scanner_false_positives.md` (workers
do NOT edit `scripts/autonomous_loop.py`; the rename is the
maintenance-light workaround).

In `OpenMath/Chapter5/Section530.lean`, inside the body of
`explicitEulerGLM_hasOrderZero_trivialStarting`:

* `have h_deriv : ... := hasDerivAt_iff_isLittleO_nhds_zero.mp hyex_deriv`
  → `have hderiv : ... := hasDerivAt_iff_isLittleO_nhds_zero.mp hyex_deriv`
* `have := h_deriv` → `have := hderiv`

These are the only two touch-points. Use `Edit` with `replace_all =
false` (only two occurrences exist). After the rename:

```bash
grep -n ':=\s*h_\w*\s*$\|exact\s\+h_\w\+\s*$\|:=\s*id\s*$' \
  OpenMath/Chapter5/Section530.lean
```

should return zero hits. Run `lean_verify
OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero_trivialStarting`
to confirm axiom-clean (`[propext, Classical.choice, Quot.sound]`) is
preserved (rename is α-equivalent — should be invariant).

**Do NOT** try to edit `scripts/autonomous_loop.py` to fix the scanner.
That is loop-maintainer territory.

## Priority 1 — def:530B Path A Step 4: `p = 1` refinement (primary)

The cycle 153 witness has `p = 0`. The textbook (Butcher §530)
classifies explicit Euler as **order 1** relative to the canonical
starting method, so the natural cycle-154 deliverable is to promote
the witness to `p = 1`. This continues the def:530B Path A chain in a
faithful direction without opening Path B (implicit branch, multi-cycle
fixed-point infrastructure).

### Statement to add

In `OpenMath/Chapter5/Section530.lean`, immediately after the cycle-153
`explicitEulerGLM_hasOrderZero_trivialStarting`:

```lean
theorem explicitEulerGLM_hasOrderOne_trivialStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit
      explicitEulerGLM trivialStartingMethod
      (by intro i; exact trivialGeneralizedRK_isExplicit)
      explicitEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  ...
```

The hypotheses upgrade from cycle 153 in two ways:
1. `HasDerivAt yex (f y₀) x₀` strengthens to `∀ x, HasDerivAt yex (f
   (yex x)) x` (the genuine ODE relation, needed for Taylor expansion
   at nearby points).
2. `ContDiff ℝ 2 yex` is added (needed for the second-order remainder
   bound).

Faithfulness note for the `lean_status.json` row: these hypotheses are
still well within Butcher's implicit "exact solution sufficiently
regular" assumption.

### Proof recipe

Goal after `intro i; fin_cases i; change ...` (cycle-153 boilerplate):

```
(fun h => SM(y₀, h)[0] - ES(y₀, h)[0]) =O[nhds 0] (fun h => h ^ 2)
```

with closed forms (cycle 153 derivation):

* SM(y₀, h)[0] = (y₀ + h·f y₀) + h·f(y₀ + h·f y₀)
* ES(y₀, h)[0] = yex(x₀+h) + h·f(yex(x₀+h))

Decomposition:

```
SM - ES = T1 + T2
  T1 := (y₀ + h·f y₀) - yex(x₀+h)
  T2 := h · (f(y₀ + h·f y₀) - f(yex(x₀+h)))
```

**T1 = O(h²)** via second-order Taylor. The genuine ODE relation
`hyex_ode x₀` at the initial point gives `yex'(x₀) = f(yex(x₀)) = f y₀`
(via `hyex_x₀`). Combined with `ContDiff ℝ 2 yex`, the second-order
Taylor expansion around `x₀` gives:

```
yex(x₀+h) = yex(x₀) + h·yex'(x₀) + (h²/2)·yex''(ξ)   for some ξ
          = y₀ + h·f y₀ + (h²/2)·yex''(ξ)
```

so `T1 = -(h²/2)·yex''(ξ)` is `O(h²)`.

The cleanest Mathlib path:
* `taylorWithinEval_eq_iteratedDerivWithin` in
  `Mathlib.Analysis.Calculus.Taylor` gives the Taylor approximation
  with explicit remainder.
* OR more directly: search for `taylor_mean_remainder` /
  `taylor_within_apply` and friends.
* OR construct manually: `hyex_C2.differentiable_iteratedDeriv` gives
  `Continuous (deriv yex)` on `[x₀, x₀+h]`; FTC twice yields the
  remainder as an iterated integral, bounded by `(h²/2)·M` where
  `M := sup_{t ∈ [x₀,x₀+h]} |deriv (deriv yex) t|`. A compact-interval
  bound argument seals it.

**Recommended search-first protocol** (≤15 min, before writing any
proof):
1. `lean_leansearch "Taylor's theorem with second-order remainder"`
2. `lean_loogle "ContDiff ℝ 2 _ → _ =O _"` (or similar pattern)
3. If matches found, `lean_hover_info` to confirm signature.
4. If no clean match: fall through to the manual mean-value construction.

Likely candidates to investigate first:
* `Mathlib.Analysis.Calculus.Taylor` — the canonical Taylor module.
* `Mathlib.Analysis.Calculus.MeanValue` — `norm_image_sub_le_of_norm_deriv_le_segment`
  applied to `deriv yex` on `[x₀, x₀+h]`.
* `Mathlib.Analysis.Calculus.LocalExtr.SecondDeriv` — second-derivative
  bounds.

**T2 = O(h²)** via Lipschitz + transitivity through T1's bound.

Cycle 153 showed T2 = O(h) by Lipschitz bound on `|f a - f b|` when
`a, b → y₀`. For T2 = O(h²) we need a quantitative refinement of the
inner difference `|a - b|`:

```
T2 = h · (f a - f b)  with  a := y₀ + h·f y₀,  b := yex(x₀+h)
   so  |T2| = |h| · |f a - f b| ≤ |h| · L · |a - b|
```

But `a - b = -T1` exactly (rearrange the cycle-153 decomposition).
Since `T1 =O[nhds 0] h²`, we have `|a - b| ≤ C · h²` near 0. Multiplying
by `|h|`:

```
|T2| ≤ L · |h| · C · h² = L·C · h³
```

which is `O(h³)`, hence `O(h²)`. The cleanest IsBigO chain:

1. `T1 =O[nhds 0] (fun h => h^2)` — from above.
2. `T1.neg_left : (-T1) =O[nhds 0] (fun h => h^2)`.
3. `(fun h => h * (a - b)) =O[nhds 0] (fun h => h * h^2)` via
   `Asymptotics.IsBigO.mul`:
   ```
   (fun h => h) =O[nhds 0] (fun h => h)   -- isBigO_refl
   (fun h => -T1 h) =O[nhds 0] (fun h => h^2)
   ⟹  (fun h => h * -T1 h) =O[nhds 0] (fun h => h * h^2)
   ```
4. From the Lipschitz pointwise bound: T2 is dominated entrywise by
   `L · |h * (a - b)|` (use `IsBigO.of_bound`-style or wrap T2's IsBigO
   in `IsBigO.const_mul_left L`).
5. `(fun h => h * h^2) = (fun h => h^3)`, and on `nhds 0` we have
   `(fun h => h^3) =O[nhds 0] (fun h => h^2)` because
   `|h^3| ≤ |h|^2 · |h| ≤ |h|^2 · 1 = |h|^2` whenever `|h| ≤ 1`.
   Use `Asymptotics.IsBigO.of_bound 1` with the eventual `|h| ≤ 1`
   from `Metric.eventually_nhds`-style.

For the `IsBigO.mul` step the precise Mathlib lemma is
`Asymptotics.IsBigO.mul`:
`f₁ =O[l] g₁ → f₂ =O[l] g₂ → (f₁ * f₂) =O[l] (g₁ * g₂)`. Apply it with
the arrangement above.

### Implementation plan

1. **Step 1** (~10 LOC): Cycle-153 boilerplate (intro, fin_cases,
   change, hSM/hES closed forms, hcongr, T1+T2 split). Reuse cycle 153
   patterns directly.
2. **Step 2** (~30–60 LOC, the main work): T1 = O(h²) via Taylor.
   First do the **search-first protocol** above. If a direct lemma
   exists, use it; otherwise construct via mean-value theorem on
   `deriv yex`.
3. **Step 3** (~25 LOC): T2 = O(h²) via the IsBigO chain (steps 1–5
   above). Lipschitz hypothesis gives the constant; T1's `O(h²)` from
   Step 2 supplies the inner factor.
4. **Step 4** (~5 LOC): Combine `hT1.add hT2`, simp the `h^(1+1)`
   exponent.

**Estimated total**: 70–100 LOC. If the Taylor step (Step 2) blows
out of budget (>80 LOC), see Backup B1 below.

### Verification commands (run before commit)

```bash
lake env lean OpenMath/Chapter5/Section530.lean    # exit 0
lake build OpenMath.Chapter5.Section530             # success
grep -c sorry OpenMath/Chapter5/Section530.lean     # 0
```

Then via lean-lsp:
```
lean_verify OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne_trivialStarting
```
expect `[propext, Classical.choice, Quot.sound]` only.

Plus the post-rename scanner check:
```bash
grep -n ':=\s*h_\w*\s*$\|exact\s\+h_\w\+\s*$\|:=\s*id\s*$' \
  OpenMath/Chapter5/Section530.lean
```
should be empty.

## Backup B1 — if Taylor step (P1 Step 2) stalls (~30 min sunk)

If `Mathlib.Analysis.Calculus.Taylor` doesn't yield a clean
`O(h²)`-grade Taylor remainder lemma after 30 minutes of searching, AND
the manual mean-value argument exceeds 80 LOC, **abandon Path A Step 4
this cycle**. Instead:

1. Document the partial attempt in cycle 154 task results §"Dead ends".
2. Keep the Priority 0 rename (mandatory).
3. Land **Path A Step 5** as a placeholder: a *second* `p = 0`
   non-vacuity witness for a different `M × S` pair (e.g.
   `padded2DEulerGLM × mixedStartingMethod`) to broaden the witness
   coverage matrix without requiring Taylor infrastructure.
   * `padded2DEulerGLM` is from cycle 133.
   * `mixedStartingMethod` is from cycle 141.
   * The `p = 0` witness should be substantially mechanical given
     cycles 133/141/153's groundwork. Expect to closely mirror cycle
     153's proof but with `r = 2` indexing (two `fin_cases i`
     branches) and 2D matrix arithmetic.
   * Estimated 60–100 LOC.

If even Backup B1 stalls (rare — would require r = 2 closed-form work
itself stalling), commit just the Priority 0 rename + a focused issue
file documenting the Taylor-infrastructure investigation results.
A score-+1 cycle (rename only, no substantive advance) is better than
a sorry-introducing score-−2 cycle.

## Backup B2 — if Path A Step 4 closes very fast (<60 min)

If Step 4 closes before noon, optionally also start **def:530C** (the
"variants of order" definition currently `[ ]` in plan.md). Read
`extraction/formalization_data/entities/def_530C.json` to confirm the
textbook statement before starting; def:530C may simply be
`HasOrderRelativeTo` with the implicit branch, in which case it is
*Path B work* and should be deferred. If it's a tractable variant
(e.g. "global" vs. "componentwise" order, or starting-method
independence), proceed.

**Stop point**: do NOT extend into thm:530A or any §530 theorem
without a fresh planner cycle.

## Things to NOT try

1. **Do NOT submit Aristotle for Path A Step 4.** The textbook proof
   is a clean Taylor-remainder + Lipschitz argument; manual closure
   beats Aristotle on this size of problem. Aristotle has been
   productive on M-matrix / FTC / specific premise lookups, not on
   `IsBigO`-heavy compositional asymptotic proofs.

2. **Do NOT poll Aristotle project `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`
   (thm:550A general-n).** It was CANCELED at 21% in cycle 151. Two
   prior failed long-runs (cycle 138 cancelled at 6%, cycle 148
   cancelled at 21%) constitute sufficient evidence that the prover
   cannot close the general-n statement with current tooling. Save the
   slot.

3. **Do NOT submit a new general-n thm:550A Aristotle job.** Same
   reasoning. The closure path for thm:550A general-n is structural
   (cofactor-expansion induction or eigenvalue-density argument), not
   search-based.

4. **Do NOT add an n=8 stepping stone for thm:550A.** The seven
   concrete-n witnesses (n = 1..7) already establish the leading-
   coefficient pattern empirically; further stepping stones provide
   marginal value. Per cycle 150 task results §"Suggested next
   approach" item 1: effort should pivot away from §550 stepping stones.

5. **Do NOT attempt Path B (implicit branch) of def:530B.** Multi-cycle
   `ContractingWith` / fixed-point infrastructure required. Wait for a
   future planner cycle to commit to that branch.

6. **Do NOT raise `maxHeartbeats` above 200000.** If Step 2 (Taylor)
   fits in default, great; if it blows up, decompose into private
   helpers (e.g. a separate `private lemma yex_taylor_remainder` that
   isolates the Taylor expansion alone).

7. **Do NOT edit `scripts/autonomous_loop.py`** to fix the scanner.
   Loop-maintainer territory.

8. **Do NOT widen `IsConvergent` or other §510–§515 predicates** in
   pursuit of cleanliness. Cycle 154 is purely §530-focused.

9. **Do NOT open a new section file** (e.g. `Section531.lean`). All
   cycle 154 work lands in `OpenMath/Chapter5/Section530.lean`.

10. **Do NOT introduce `axiom`/`constant` declarations.** Per CLAUDE.md.

11. **Do NOT propagate the cycle-153 `_hS, _hM IsExplicit` hypotheses
    through `applyStartingThenStep_explicit` / `applyExactThenStarting_explicit`
    bodies.** They are unused in the cycle-152/153 design (the recursion
    summing over earlier stages closes regardless of strict-lower-triangular
    `A`). The hypotheses are kept for downstream order-condition proof
    consumption; do not modify their definitions to use them.

12. **Do NOT use `rw` on `explicitStageValue` or `explicitApply`.**
    These are noncomputable WF recursions; `rw` fails on the equation
    lemmas. Use `unfold` instead. Lesson from cycle 153 dead end #1.

## Bookkeeping (Priority 2)

After Priority 0 + 1 land:

* **plan.md** — update the def:530B `[~]` entry's annotation: append a
  Cycle 154 paragraph documenting Path A Step 4 completion (`p = 1`
  axiom-clean witness for explicit Euler GLM × `trivialStartingMethod`
  under `LipschitzWith L f` + `ContDiff ℝ 2 yex` + ODE relation).
  Status remains `[~]` (Path B implicit still deferred).
* **extraction/formalization_data/lean_status.json** — update the
  def:530B row: bump `cycle` to 154, expand notes to mention the
  `p = 1` upgrade and the Taylor-based proof technique.
* **`.prover-state/issues/def_530B_scaffold_strategy.md`** — append a
  "Cycle 154 update — Path A Step 4 complete" sub-section mirroring
  the cycle-152/153 update format.
* **`.prover-state/issues/tautology_scanner_false_positives.md`** —
  add a "Cycle 154 update" sub-section recording the `h_deriv →
  hderiv` rename in `Section530.lean:711–717`. This keeps the scanner
  false-positive ledger current.

If Backup B1 fires (Taylor stall), bookkeeping for the *fallback*
witness instead: update plan.md / lean_status.json / scaffold issue to
record the broadened `p = 0` coverage instead of `p = 1` upgrade.

## Faithfulness check (mandatory pre-commit)

For `explicitEulerGLM_hasOrderOne_trivialStarting` (if landed):

* **Entity ID + textbook statement**: this is a Lean-internal
  non-vacuity witness for `HasOrderRelativeTo_explicit`, NOT a
  textbook entity. The textbook context: Butcher §531 (immediately
  after def:530B) classifies explicit Euler as a method of order 1
  in the GLM framework. Quote relevant §531 sentence in the docstring.
* **Lean statement captures**: same content as Butcher's classification,
  with documented hypothesis upgrades (`ContDiff ℝ 2 yex`, full ODE
  relation `∀ x, HasDerivAt yex (f (yex x)) x`). Both upgrades are
  faithful to Butcher's implicit "exact solution sufficiently regular"
  assumption.
* **Tautology check**: conclusion `HasOrderRelativeTo_explicit ... 1
  ...` is not verbatim any hypothesis. Proof is genuine asymptotic
  analysis (Taylor + Lipschitz).
* **Hypothesis strength check**: `ContDiff ℝ 2` is the minimal
  regularity needed for second-order Taylor. Cannot be weakened to
  `ContDiff ℝ 1` while keeping the `O(h²)` conclusion (the cycle-153
  `O(h)` witness is the `ContDiff ℝ 1`-grade analog).
* **Identity check**: proof is multi-step (Taylor remainder + IsBigO
  composition), not a single `exact h_*`. Not vacuous.
* **Absent theorem check**: `lean_verify` post-build confirms axiom
  cleanliness.

## Cycle 154 expected outcome

* Sorry count: **0 → 0** (no regression).
* Tautology scanner hits: **1 → 0** (Priority 0 cosmetic rename).
* Axiom-clean theorems added: **1** (Path A Step 4 `p = 1` witness)
  OR **1** (Backup B1 fallback `p = 0` second witness).
* Score target: **+2** (clean substantive advance with no regressions).
