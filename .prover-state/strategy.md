# Cycle 152 Strategy — def:530B Path A Step 2: explicit-only operators

## TL;DR

Cycle 151 landed Path A Step 1 (`GeneralizedRungeKuttaMethod.IsExplicit`
+ vacuous/non-vacuous/negative witnesses) axiom-clean in
`OpenMath/Chapter5/Section530.lean`. Sorry count: **0**.
No pending Aristotle results.

**Cycle 152 target**: build the explicit-only operators
`applyStartingThenStep_explicit` and `applyExactThenStarting_explicit`
that the cycle 151 task results mark as the next deliverable
(estimated 80–120 LOC).

Stay strictly within `Section530.lean`. **Do NOT** pivot to thm:550A
general-`n` (deferred per cycles 141/151), cor:550C (depends on
thm:550A), or def:530C (downstream of def:530B).

---

## Priority 0 — Aristotle housekeeping

**None.** Cycle 151 cancelled project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (cycle 148 fire-and-forget
general-`n` thm:550A). No active Aristotle jobs. Do **NOT** submit
new ones this cycle — the operators are pure-recursive function
definitions, well outside Aristotle's strength zone.

---

## Priority 1 — Path A Step 2 operators

The textbook def:530B (Butcher §530, p. 432) compares two compositions
of a starting method `S : StartingMethod r` with a GLM
`M : GeneralLinearMethod s r`:

* `SM(y₀, h)` ≡ apply each `Sᵢ` to scalar `y₀` to produce `r` initial
  approximations, then take one `M`-step.
* `ES(y₀, h)` ≡ advance the exact solution by `h` (yielding scalar
  `yex(x₀ + h)`), then apply each `Sᵢ` to that scalar.

For a generalized Runge–Kutta method `S = (c, A, b₀, b)` the
canonical interpretation is:

* Stage equations: `Y_j = b₀ · y₀ + h · Σ_k A_{jk} · f(Y_k)`.
* Output:        `S(y₀, h) = b₀ · y₀ + h · Σ_j b_j · f(Y_j)`.

When `A` is strict-lower-triangular (`IsExplicit`), the stage equations
are not implicit: each `Y_j` depends only on `Y_0, …, Y_{j-1}` and so
can be evaluated by direct recursion on the stage index `j`. This is
what cycle 152 will encode.

### Step 2a — Stage-value recursion for an explicit GRK method

Add immediately below `implicit2StageGRK_not_isExplicit` (current line
358 of `OpenMath/Chapter5/Section530.lean`):

```lean
/-! ### Stage-value recursion for explicit generalized RK methods
(cycle 152, def:530B Path A Step 2) -/

/-- Given a generalized Runge–Kutta method `M`, the stage value
`Y_j = b₀ · y₀ + h · Σ_{k < j} A_{jk} · f(Y_k)` defined by direct
recursion on `j`. The recursion terminates because each call sums
only over `Fin j.val`, whose elements are strictly less than `j.val`.

The body does **not** use `IsExplicit` — the recursion sums only over
`k < j` regardless of `A`'s shape. The `IsExplicit` hypothesis is
needed downstream when proving this matches the textbook stage
equation `Y_j = b₀·y₀ + h·Σ_k A_{jk}·f(Y_k)` (the `k ≥ j` terms
vanish iff `A` is strict-lower-triangular). -/
noncomputable def GeneralizedRungeKuttaMethod.explicitStageValue
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s)
    (f : ℝ → ℝ) (y₀ h : ℝ) (j : Fin s) : ℝ :=
  M.b₀ * y₀ + h * ∑ k : Fin j.val,
    M.A j ⟨k.val, by omega⟩
      * f (M.explicitStageValue f y₀ h ⟨k.val, by omega⟩)
termination_by j.val
decreasing_by
  simp_wf
  exact k.isLt
```

If Lean's WF elaborator rejects the recursive call inside the
`Finset.sum`, fall back to `Nat.strongRecOn`:

```lean
noncomputable def GeneralizedRungeKuttaMethod.explicitStageValue
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin s → ℝ := fun j =>
  Nat.strongRecOn j.val (motive := fun n => n < s → ℝ)
    (fun n IH hn =>
      M.b₀ * y₀ + h * ∑ k : Fin n,
        M.A ⟨n, hn⟩ ⟨k.val, by omega⟩
          * f (IH k.val k.isLt (by omega)))
    j.isLt
```

Either form is acceptable; pick whichever Lean accepts on the first
`lake env lean` pass. Mark `noncomputable` because `b₀ : ℝ` and `A`
involve real arithmetic.

### Step 2b — Closed-form output of an explicit GRK method

```lean
/-- The scalar output of one application of an explicit generalized
Runge–Kutta method to scalar `y₀` with step `h`:
`S(y₀, h) = b₀ · y₀ + h · Σ_j b_j · f(Y_j)`,
where `Y_j` are computed by `explicitStageValue`. -/
noncomputable def GeneralizedRungeKuttaMethod.explicitApply
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s)
    (f : ℝ → ℝ) (y₀ h : ℝ) : ℝ :=
  M.b₀ * y₀ + h * ∑ j : Fin s, M.b j * f (M.explicitStageValue f y₀ h j)
```

### Step 2c — Lift to a `StartingMethod`

```lean
/-- For each constituent `S_i` of a starting method, compute the
scalar output of `S_i` applied to `y₀` with step `h` via
`explicitApply`. This produces the `Fin r → ℝ` initial-input vector
consumed by the GLM step in `applyStartingThenStep_explicit`. -/
noncomputable def StartingMethod.applyExplicit
    {r : ℕ} (S : StartingMethod r)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin r → ℝ :=
  fun i => (S.method i).explicitApply f y₀ h
```

### Step 2d — `applyExactThenStarting_explicit` (the easy operator)

This side does **not** need `M` at all (it just advances the exact
solution to time `x₀ + h` and feeds that scalar through `S`):

```lean
/-- Textbook `ES(y₀, h)` operator (Butcher §530, def:530B): advance the
exact solution `yex` by `h`, then apply each constituent `S_i` to
that scalar. The result is a `Fin r → ℝ` vector of starting-method
outputs. The `IsExplicit` hypothesis on every `S_i` marks this as
the "explicit-only" variant per the cycle 151 issue file plan; it is
unused in the body (the recursion in `explicitStageValue` works
regardless), but downstream proofs (cycle 153 order witness) consume
the hypothesis to match this definition with the textbook
stage-equation form. -/
noncomputable def applyExactThenStarting_explicit
    {r : ℕ} (S : StartingMethod r)
    (_hS : ∀ i, (S.method i).IsExplicit)
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ h : ℝ) : Fin r → ℝ :=
  S.applyExplicit f (yex (x₀ + h)) h
```

### Step 2e — `applyStartingThenStep_explicit` (the operator that uses M)

The M-step itself involves M's *own* stage equations. To keep
cycle 152 self-contained, add a parallel `GeneralLinearMethod.IsExplicit`
predicate and assume both `S` and `M` are explicit. The cycle 153
witness target (`explicitEulerGLM × trivialStartingMethod`) satisfies
this because `explicitEulerGLM.A = !![0]` is vacuously
strict-lower triangular at `s = 1`.

This requires importing Section510, since `GeneralLinearMethod` lives
there. **Do NOT** do this if it inflates the cycle past the 150 LOC
budget — see "Backup plan" below for the fallback that defers Step
2e to cycle 153.

If proceeding, modify the imports and add to Section530.lean:

```lean
-- At top of Section530.lean (in addition to existing imports), add:
import OpenMath.Chapter5.Section510

-- After `namespace OpenMath.Chapter5.Section530`, add:
open OpenMath.Chapter5.Section510

-- ...then in the new "explicit GLM" sub-section:

/-- A general linear method's stage matrix `A` is strict-lower
triangular, so its internal stages can be evaluated by direct
recursion. This is the GLM analog of
`GeneralizedRungeKuttaMethod.IsExplicit`. -/
def GeneralLinearMethod.IsExplicit
    {s r : ℕ} (M : GeneralLinearMethod s r) : Prop :=
  ∀ i j : Fin s, i.val ≤ j.val → M.A i j = 0

/-- The internal stage value `Y_i` of an explicit GLM applied to an
input `r`-vector `y_input : Fin r → ℝ` with step `h`:
`Y_i = (M.U *ᵥ y_input) i + h · Σ_{k < i} M.A i k · f(Y_k)`. -/
noncomputable def GeneralLinearMethod.explicitStageValue
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (y_input : Fin r → ℝ) (h : ℝ) (i : Fin s) : ℝ :=
  (M.U *ᵥ y_input) i + h * ∑ k : Fin i.val,
    M.A i ⟨k.val, by omega⟩
      * f (M.explicitStageValue f y_input h ⟨k.val, by omega⟩)
termination_by i.val
decreasing_by simp_wf; exact k.isLt

/-- Textbook `SM(y₀, h)` operator (Butcher §530, def:530B): apply each
`S_i` to `y₀` to produce `y_input := S.applyExplicit f y₀ h`, then
take one `M`-step. The output of the `M`-step is
`y_new[ℓ] = h · Σ_i M.B ℓ i · f(Y_i) + (M.V *ᵥ y_input) ℓ`. -/
noncomputable def applyStartingThenStep_explicit
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (S : StartingMethod r)
    (_hS : ∀ i, (S.method i).IsExplicit)
    (_hM : M.IsExplicit)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin r → ℝ :=
  let y_input := S.applyExplicit f y₀ h
  fun ℓ =>
    h * ∑ i : Fin s,
      M.B ℓ i * f (M.explicitStageValue f y_input h i)
    + (M.V *ᵥ y_input) ℓ
```

If the `import OpenMath.Chapter5.Section510` triggers a cyclic
import or a slow build, **abort Step 2e** and document in the cycle
results file that the GLM-side operator was deferred to cycle 153
(when it can be folded in alongside the order predicate). Step 2a-d
already constitute a credible cycle deliverable.

### Step 2f — Non-vacuity sanity computations

To meet the CLAUDE.md "every new structure/def gets a witness" rule
(and to confirm the operators reduce correctly on the cycle 153
target configuration), prove:

```lean
/-- **Non-vacuity sanity**: for the trivial starting method
(r = 1, b₀ = 1, b = 1, A = 0), `applyExplicit` reduces to
`y₀ + h · f(y₀)` (one step of explicit Euler). -/
theorem trivialStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    trivialStartingMethod.applyExplicit f y₀ h
      = fun (_ : Fin 1) => y₀ + h * f y₀ := by
  funext i; fin_cases i
  unfold StartingMethod.applyExplicit
    GeneralizedRungeKuttaMethod.explicitApply
    GeneralizedRungeKuttaMethod.explicitStageValue
  simp [trivialStartingMethod, trivialGeneralizedRK]
```

If the `simp` chain doesn't close it directly, fall back to a
manual reduction:

```lean
  -- The Fin 0 sum in explicitStageValue 0 vanishes:
  --   stageValue 0 = b₀ * y₀ + h * (∑ k : Fin 0, …) = 1 * y₀ + h * 0 = y₀.
  -- The Fin 1 sum in explicitApply collapses to b 0 * f(stageValue 0):
  --   applyExplicit = b₀ * y₀ + h * (b 0 * f y₀) = y₀ + h * f y₀.
  rw [show (∑ k : Fin 0, (0 : ℝ)) = 0 from Finset.sum_empty]
  -- ... finish via `simp` or `ring`.
```

Add a parallel sanity computation for the `ES` side:

```lean
/-- **Non-vacuity sanity** for the `ES` side: with the trivial
starting method (whose single constituent is explicit), advancing
`yex` by `h` then applying `S` produces
`yex(x₀ + h) + h · f(yex(x₀ + h))`. -/
theorem trivialStartingMethod_applyExactThenStarting_explicit
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ h : ℝ) :
    applyExactThenStarting_explicit trivialStartingMethod
        (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
        f yex x₀ h
      = fun (_ : Fin 1) => yex (x₀ + h) + h * f (yex (x₀ + h)) := by
  funext i; fin_cases i
  unfold applyExactThenStarting_explicit
  rw [trivialStartingMethod_applyExplicit]
```

(If proceeding with Step 2e, also add an
`explicitEulerGLM_isExplicit : explicitEulerGLM.IsExplicit` one-liner
plus `applyStartingThenStep_explicit` reducing on
`explicitEulerGLM × trivialStartingMethod`. The body of
`explicitEulerGLM_isExplicit` is `intro i j _; fin_cases i; fin_cases
j; rfl`, since `explicitEulerGLM.A = !![0]` is `0` at `(0, 0)`.)

### Implementation order

1. Steps 2a, 2b, 2c, 2d — minimum viable cycle 152. Land first.
2. Step 2f's first two sanity theorems
   (`trivialStartingMethod_applyExplicit`,
   `trivialStartingMethod_applyExactThenStarting_explicit`).
3. **Verify**:
   * `lake env lean OpenMath/Chapter5/Section530.lean` — clean.
   * `lake build OpenMath.Chapter5.Section530` — clean.
   * `grep -n "sorry" OpenMath/Chapter5/Section530.lean` — empty.
   * `lean_verify` on each new theorem returns
     `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
4. **Then**, only if the above closes cleanly with budget remaining,
   land Step 2e (the `M`-side operator) and its sanity computation.

### LOC budget

Steps 2a–2d + 2f sanity ≈ 60–90 LOC. Step 2e + GLM sanity ≈ 40–60
LOC. Combined target: **≤ 150 LOC** of additions to
`Section530.lean`. If draft exceeds 200 LOC, drop Step 2e to cycle
153.

---

## Priority 2 (stretch, only if Priority 1 closes ≤ 60 minutes)

If Step 2e and its sanity also land, draft a **named `private
lemma`** isolating the `(s = 1, r = 1)` × `trivialStartingMethod`
case for cycle 153's witness, but leave the body as `sorry` is
**FORBIDDEN** — instead, draft the lemma as a *theorem statement
in a comment* referenced by the cycle 152 task results file:

```text
-- Cycle 153 witness target (stated here for planning, NOT introduced
-- as a `sorry`-bodied declaration):
--
--   (applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
--      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
--      explicitEulerGLM_isExplicit f y₀ 0)
--   = (applyExactThenStarting_explicit trivialStartingMethod
--      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
--      f (fun _ => y₀) 0 0)
--
-- (i.e. at h = 0, both sides equal `fun _ => y₀`.)
```

If even drafting the comment takes > 15 min, skip it and let cycle
153 plan it from scratch.

---

## What NOT to do

* **Do NOT** add a `sorry`. Sorry count must remain 0.
  Cycle 149 was rolled back (score −2) precisely because it raised
  sorry count 0 → 3.
* **Do NOT** define `applyStartingThenStep` or
  `applyExactThenStarting` *without* the `_explicit` suffix and
  without the `IsExplicit` hypothesis. The general implicit case is
  Path B (deferred per the issue file
  `def_530B_scaffold_strategy.md`), and attempting it would either
  re-introduce a `sorry` or require fixed-point machinery that
  inflates the cycle past 200 LOC.
* **Do NOT** define `HasOrderRelativeTo` or
  `HasOrderRelativeTo_explicit` predicates this cycle. That is
  cycle 153 (Path A Step 3); the `Asymptotics` machinery can wait.
* **Do NOT** import `Mathlib.Analysis.Asymptotics.Defs` or any
  `HasDerivAt` modules — they are only needed for the order
  predicate.
* **Do NOT** raise `maxHeartbeats` (CLAUDE.md). If a `simp` chain
  in Step 2f exceeds 200 000, decompose: prove
  `(trivialGeneralizedRK.explicitStageValue f y₀ h 0) = y₀` as a
  separate `private lemma` first, then combine.
* **Do NOT** mark new `def`s computable — they involve real
  arithmetic via `b₀ : ℝ` and matrix entries. Cycle 151 caught this
  the hard way; mark `noncomputable` on the *first* try.
* **Do NOT** restate the textbook def:530B order condition this
  cycle. The operators alone are the deliverable; the predicate
  uses them and lands in cycle 153.
* **Do NOT** submit Aristotle jobs. Recursive function definitions
  with `termination_by` are outside Aristotle's strength zone, and
  the job slot should be saved for tractable proof obligations.
* **Do NOT** retry the cycle 149 sorry-first scaffold approach.
  Cycle 150 explicitly rolled back that pattern; the cycle 151 →
  152 cadence is to land *closed* sub-deliverables one step at a
  time, never sorry placeholders.
* **Do NOT** touch `OpenMath/Chapter5/Section520.lean`,
  `Section515.lean`, or any other Chapter 5 file *other than*
  `Section530.lean`. Step 2e's `import OpenMath.Chapter5.Section510`
  is the only allowed cross-file change, and it's an import-only
  modification (no edits to `Section510.lean`).
* **Do NOT** poll the cancelled Aristotle project
  `2c4630b2-…` — it was cancelled in cycle 151.
* **Do NOT** pivot to thm:550A general-`n` proof. Two failed
  long-running Aristotle attempts (cycle 138 and cycle 148, the
  latter cancelled cycle 151 at 21 % after 89 h) plus the manual
  cofactor-expansion infrastructure scope make this multi-cycle
  work. Stay on def:530B Path A.

---

## Backup plan if Step 2a's recursion fails to elaborate

Two tried-and-true fallbacks:

**Fallback B1**: switch from the inline `Finset.sum` recursion to
`Nat.strongRecOn` (template given in Step 2a above). Lean's WF
elaborator sometimes balks at recursive calls inside finset sums but
accepts them inside `Nat.strongRecOn` motive functions.

**Fallback B2**: build the full vector via tail-recursive
extension. Define a helper `buildStages : (n : ℕ) → n ≤ s → (Fin n →
ℝ)` that prepends to a list, then index. More verbose but guaranteed
to terminate without WF acrobatics.

**Fallback B3**: parameterise. If neither B1 nor B2 closes within
30 min, retreat to a *parameterised* `applyExplicit` that takes the
stage vector `Y : Fin s → ℝ` as an additional argument together
with a hypothesis that it satisfies the explicit stage equation.
This is strictly weaker but preserves zero-sorry status:

```lean
noncomputable def GeneralizedRungeKuttaMethod.explicitApplyParam
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s)
    (f : ℝ → ℝ) (y₀ h : ℝ)
    (Y : Fin s → ℝ)
    (_hY : ∀ j, Y j = M.b₀ * y₀ + h * ∑ k : Fin j.val,
                        M.A j ⟨k.val, by omega⟩ * f (Y ⟨k.val, by omega⟩)) :
    ℝ :=
  M.b₀ * y₀ + h * ∑ j : Fin s, M.b j * f (Y j)
```

This sidesteps the WF check entirely. The non-vacuity witness
`trivialStartingMethod_applyExplicit` still works by supplying the
trivial `Y := fun _ => y₀` and discharging the hypothesis directly
on the `s = 1` case.

If even Fallback B3 fails (which would be unprecedented for a
straightforward Finset sum), **STOP and write an issue file** at
`.prover-state/issues/explicitStageValue_termination.md` documenting
the obstruction, then commit only Steps 2c, 2d (lifted forms that
take an abstract per-method `applyOne : ℝ → ℝ → ℝ` argument). Even
that meets the CLAUDE.md "minimum: decompose a sorry or write an
issue" rule.

---

## Verification checklist (before commit)

1. **Compile**: `lake env lean OpenMath/Chapter5/Section530.lean`
   exits clean.
2. **Build**: `lake build OpenMath.Chapter5.Section530` exits clean.
3. **Sorry count**: `grep -n "sorry" OpenMath/Chapter5/Section530.lean`
   returns nothing.
4. **Axiom check**: every new `theorem` axiom-checks via
   `lean_verify` to `[propext, Classical.choice, Quot.sound]` only —
   no `sorryAx`, no extra axioms.
5. **Faithfulness**: each new `def` / `theorem` is documented with a
   docstring referencing Butcher §530 and noting whether the entity
   is internal helper or textbook concept. Internal helpers
   (`explicitStageValue`, `explicitApply`, `applyExplicit`,
   `IsExplicit` for GLMs) are NOT textbook entities — say so
   explicitly in the docstring per the cycle 151 IsExplicit precedent.
6. **Plan/status update**: append a "Cycle 152 update" line to the
   `def:530B` row in `plan.md` mentioning Path A Step 2 progress.
   `extraction/formalization_data/lean_status.json` row for
   `def:530B` stays `partial` (the order predicate from cycle 153
   is still missing).
7. **Cycle results file**: write
   `.prover-state/task_results/cycle_152.md` per the CLAUDE.md
   template (Worked on, Approach, Result, Faithfulness check,
   Dead ends, Discovery, Suggested next approach).
8. **Issue file update**: append a "Cycle 152 update" section to
   `.prover-state/issues/def_530B_scaffold_strategy.md` summarising
   what landed and what (if anything) deferred to cycle 153.

---

## Cycle 153 preview (do NOT start this cycle)

* Define `HasOrderRelativeTo_explicit` predicate using
  `Asymptotics.IsBigO` of `(SM - ES) : ℝ → (Fin r → ℝ)` against
  `h^{p+1}`.
* Prove the trivial-IVP non-vacuity witness for `explicitEulerGLM ×
  trivialStartingMethod` with order `p = 0`.
* Estimated 50–80 LOC.

This is the natural sequel; cycle 152's deliverable is exactly the
infrastructure it consumes.
