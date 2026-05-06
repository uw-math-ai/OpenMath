# Cycle 159 Strategy

## Big picture

Sorry count = 0. The four-corner Path A non-vacuity grid for
`def:530B`/`def:530C` (r ∈ {1, 2} × p ∈ {0, 1}) is saturated as of
cycle 157, and cycle 158 extracted a shared Taylor + Lipschitz helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` consumed by
both p = 1 witnesses. Cycle 158 was a refactor (score = 1).

**Cycle 159's substantive deliverable**: extend Path A coverage to
**r = 3** by lifting cycles 156/157 to a 3-padded explicit Euler GLM,
mirroring the cycle 156 → cycle 157 lift exactly. This:

1. Adds two new **substantive axiom-clean witnesses**
   (`padded3DEulerGLM × pad3CompatStartingMethod` at p = 0 and p = 1),
   plus their `def:530C` wrappers. This is the same pattern cycles
   156/157 used to advance from r = 1 to r = 2; now we go r = 2 → r = 3.
2. **Validates and compounds the cycle 158 refactor**: the new p = 1
   witness's `i = 0` channel becomes a one-line invocation of the
   cycle 158 helper, demonstrating its portability (the i = 1, i = 2
   channels both reuse cycle 156's `Asymptotics.isBigO_zero`
   zero-collapse pattern).
3. **Score expectation = 2** (matches cycle 156/157 substantive
   r-lift cycles).

This is **not** the parameterise-over-Taylor-degree refactor that
cycle 158's task results suggested — that is a refactor (deferred).
This cycle is mathematical advance: two new axiom-clean witnesses +
two def:530C wrappers + supporting infrastructure.

---

## Aristotle plan

**None this cycle.** All deliverables are mechanical extensions of
cycles 156/157/158 with proven proof shapes; manual closure is
strictly faster than waiting on Aristotle.

---

## Concrete deliverables (in order)

All work lives in `OpenMath/Chapter5/Section520.lean` (one new GLM
def) and `OpenMath/Chapter5/Section530.lean` (everything else). Stay
**axiom-clean** throughout (`[propext, Classical.choice, Quot.sound]`
only). Do **not** introduce any sorry.

### Step 1 — `padded3DEulerGLM` (Section520.lean, ~10 LOC)

Add immediately after `padded2DEulerGLM` (Section520.lean line
~1286). The 3-row analog of cycle 133's r = 2 padding:

```lean
/-- 3-padded explicit Euler `(s, r) = (1, 3)`: row 0 carries the
genuine explicit-Euler step (`U[0,0] = 1, B[0,0] = 1`); rows 1 and 2
are passively decoupled zero channels. Lifts `padded2DEulerGLM`
(cycle 133) to r = 3. -/
def padded3DEulerGLM : GeneralLinearMethod 1 3 where
  A := !![0]
  U := !![1, 0, 0]
  B := !![1; 0; 0]
  V := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
```

Place it next to `padded2DEulerGLM` for discoverability. **No new
theorems about `padded3DEulerGLM` are required in Section520** for
this cycle — `IsRKStable`, `IsIRKStable`, A-stability negative
witness, etc. are out of scope. Section530 will use `padded3DEulerGLM`
directly without those Section520 corollaries.

### Step 2 — `pad3CompatMethod` and `pad3CompatStartingMethod` (Section530.lean, ~30 LOC)

Add immediately after `padCompatStartingMethod_constituents_isExplicit`
(Section530.lean line ~367). Mirror of cycle 156's pattern:

```lean
/-- 3-method constituent function for `pad3CompatStartingMethod`:
index 0 active (`trivialGeneralizedRK`, `b₀ = 1`); indices 1 and 2
inactive (`zeroGeneralizedRK`, `b₀ = 0`). -/
def pad3CompatMethod : (i : Fin 3) → GeneralizedRungeKuttaMethod 1
  | 0 => trivialGeneralizedRK
  | 1 => zeroGeneralizedRK
  | 2 => zeroGeneralizedRK

/-- A 3-method starting method (`r = 3`) meshing with
`padded3DEulerGLM`'s zero row-1 and row-2 channels. Non-degenerate at
index 0. -/
def pad3CompatStartingMethod : StartingMethod 3 where
  stages := fun _ => 1
  method := pad3CompatMethod

theorem pad3CompatStartingMethod_isNonDegenerate :
    pad3CompatStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

theorem pad3CompatStartingMethod_constituents_isExplicit :
    ∀ i : Fin 3, (pad3CompatStartingMethod.method i).IsExplicit := by
  intro i
  fin_cases i
  · exact trivialGeneralizedRK_isExplicit
  · intro a b _; fin_cases a; fin_cases b; rfl
  · intro a b _; fin_cases a; fin_cases b; rfl
```

(Confirm the actual `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero`
spelling against cycle 156's analogous theorem at Section530.lean
line 350-355; if your equivalent helper has a different name, use
that one. Same for the `intro a b _; fin_cases a; fin_cases b; rfl`
spelling — match cycle 156's working pattern in
`padCompatStartingMethod_constituents_isExplicit`.)

### Step 3 — `padded3DEulerGLM_isExplicit` (Section530.lean, ~5 LOC)

Add after the `padded2DEulerGLM_isExplicit` theorem (~line 673).
`padded3DEulerGLM`'s `A` is `!![0]` (1×1 zero), so the strict-lower-
triangular condition is vacuous on `Fin 1`:

```lean
theorem padded3DEulerGLM_isExplicit :
    padded3DEulerGLM.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl
```

(Or whatever closure shape `padded2DEulerGLM_isExplicit` uses — match
it.)

### Step 4 — `pad3CompatStartingMethod_applyExplicit` closed form (Section530.lean, ~50 LOC)

Mirror of `padCompatStartingMethod_applyExplicit` (line ~576):
the closed form for the `Fin 3 → ℝ` initial-input vector at each
of the three indices. Index 0 reduces to `y₀ + h·f y₀` (active
trivial channel); indices 1 and 2 reduce to `0` (inactive zero
channels via `zeroGeneralizedRK_explicitApply`).

The proof shape is verbatim from
`padCompatStartingMethod_applyExplicit` (line ~576): expand the
`StartingMethod.applyExplicit` definition, branch by index via
`fin_cases`, then either invoke the cycle 152 trivial-channel
closed form (`trivialStartingMethod_applyExplicit`, or whichever
is the underlying ingredient) for index 0 or
`zeroGeneralizedRK_explicitApply` (cycle 156's private helper at
Section530.lean line ~532) for indices 1 and 2. Read the cycle 156
proof body before writing this Step 4 to confirm the exact tactic
sequence; do not improvise.

The exact statement to match cycle 156's signature:

```lean
theorem pad3CompatStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    pad3CompatStartingMethod.applyExplicit f y₀ h =
      fun i => (if i = 0 then y₀ + h * f y₀ else 0) := by
  funext i
  fin_cases i
  · -- index 0: trivial-channel closed form
    -- replicate cycle 156's i = 0 branch verbatim, swap padCompat → pad3Compat
    ...
  · -- index 1: zero-channel closed form via zeroGeneralizedRK_explicitApply
    ...
  · -- index 2: identical structure to index 1
    ...
```

(If cycle 156's signature uses a different shape — e.g. an `if` with
a 2-branch decidable, or an arithmetic-zero comparison — match
cycle 156 exactly. The strategy here gives intent; the worker
should always defer to the cycle 156 working signature.)

**Close all three branches** — do not commit with sorry.

### Step 5 — `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (Section530.lean, ~70 LOC)

Mirror of cycle 156's `padded2DEulerGLM_hasOrderZero_padCompatStarting`
(line ~1182), extended to three components. Read cycle 156's full
proof body first; this is verbatim porting with three substitutions:

- `padded2DEulerGLM` → `padded3DEulerGLM`
- `padCompatStartingMethod` → `pad3CompatStartingMethod`
- `Fin 2` index range → `Fin 3` index range

The componentwise structure is:

- **i = 0 channel**: SM[0] and ES[0] reduce to the cycle-153 explicit-
  Euler closed form. Cite cycle 153's
  `explicitEulerGLM_hasOrderZero_trivialStarting` via the active
  trivial channel of `pad3CompatStartingMethod`. The proof body at
  this branch is essentially identical to cycle 156's i = 0 branch.
- **i = 1 channel**: SM[1] = ES[1] = 0 (inactive zero channel);
  Diff = 0 pointwise; close by `Asymptotics.isBigO_zero`. Verbatim
  port of cycle 156's i = 1 branch.
- **i = 2 channel**: identical to i = 1.

Statement signature (match cycle 156's hypothesis pack exactly):

```lean
theorem padded3DEulerGLM_hasOrderZero_pad3CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit padded3DEulerGLM pad3CompatStartingMethod
      pad3CompatStartingMethod_constituents_isExplicit
      padded3DEulerGLM_isExplicit
      0 f yex x₀ y₀ := ...
```

### Step 6 — `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` (Section530.lean, ~60 LOC)

Mirror of cycle 157's `padded2DEulerGLM_hasOrderOne_padCompatStarting`,
extended to three components. The **i = 0 channel must be a one-line
invocation** of cycle 158's helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` after the
SM[0]/ES[0] closed-form rewrites and the `h^(1+1) = h^2` collapse.
This is the cycle-158 portability validation.

The componentwise structure:

- **i = 0 channel**: After the standard `change` /
  `hSM` / `hES` / `hcongr` / `hpow` rewrite glue (which you read
  from cycle 157's i = 0 channel), close with **one line**:

  ```lean
  exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
          hf_lip hyex_x₀ hyex_C2 hyex_ode
  ```

  (Possibly inside a `simpa using ...` / `convert ... using N` if
  the `h^2` shape needs trivial massaging. Cycle 157's body for the
  i = 0 channel is the model.)

- **i = 1 channel**: zero-collapse via `Asymptotics.isBigO_zero`,
  exponent `h^(1+1) = h^2`. Verbatim port of cycle 157's i = 1
  branch.

- **i = 2 channel**: identical to i = 1.

Statement signature:

```lean
theorem padded3DEulerGLM_hasOrderOne_pad3CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit padded3DEulerGLM pad3CompatStartingMethod
      pad3CompatStartingMethod_constituents_isExplicit
      padded3DEulerGLM_isExplicit
      1 f yex x₀ y₀ := ...
```

**Critical**: if you find yourself porting more than the rewrite
glue (cycle 157's `change` / `hSM` / `hES` / `hcongr` / `hpow`) for
the i = 0 channel, **stop and re-examine**. The cycle 158 helper
should close the residue immediately. If it doesn't, the issue is
either (a) you reached a different SM[0]/ES[0] closed-form shape
than cycle 154/157 reached (in which case fix the rewrite glue to
match the helper's input shape) or (b) the helper's hypothesis pack
is genuinely insufficient at r = 3 (in which case file an issue
documenting the gap and fall back per the backup plan; do NOT edit
the helper this cycle).

### Step 7 — `def:530C` wrappers (Section530.lean, ~30 LOC)

Mirror of cycle 156's `padded2DEulerGLM_hasOrderZero` (line ~1349)
and cycle 157's `padded2DEulerGLM_hasOrderOne`. Each is a 4-line
existential closure of the underlying `..._pad3CompatStarting`
theorem from Steps 5 and 6:

```lean
theorem padded3DEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit padded3DEulerGLM padded3DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  refine ⟨pad3CompatStartingMethod,
          pad3CompatStartingMethod_constituents_isExplicit,
          pad3CompatStartingMethod_isNonDegenerate, ?_⟩
  exact padded3DEulerGLM_hasOrderZero_pad3CompatStarting
          hf_lip hyex_x₀ hyex_deriv

theorem padded3DEulerGLM_hasOrderOne ... -- analogous
```

(Match cycle 156/157's exact existential-closure shape; the
order/grouping of the existential witness components depends on
how `HasOrder_explicit` is defined in cycle 155.)

---

## Verification (mandatory)

After landing all steps:

1. `lake env lean OpenMath/Chapter5/Section520.lean` exits 0.
2. `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
3. `lake env lean OpenMath/Chapter5.lean` exits 0 (full module check).
4. `grep -c sorry OpenMath/Chapter5/Section530.lean` returns 0.
5. `grep -c sorry OpenMath/Chapter5/Section520.lean` returns 0.
6. Tautology scanner regex
   `':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'` returns 0 hits in
   both files.
7. `lean_verify` is axiom-clean
   (`[propext, Classical.choice, Quot.sound]` only) on:
   - `OpenMath.Chapter5.Section530.pad3CompatStartingMethod_isNonDegenerate`
   - `OpenMath.Chapter5.Section530.pad3CompatStartingMethod_constituents_isExplicit`
   - `OpenMath.Chapter5.Section530.padded3DEulerGLM_isExplicit`
   - `OpenMath.Chapter5.Section530.pad3CompatStartingMethod_applyExplicit`
   - `OpenMath.Chapter5.Section530.padded3DEulerGLM_hasOrderZero_pad3CompatStarting`
   - `OpenMath.Chapter5.Section530.padded3DEulerGLM_hasOrderOne_pad3CompatStarting`
   - `OpenMath.Chapter5.Section530.padded3DEulerGLM_hasOrderZero`
   - `OpenMath.Chapter5.Section530.padded3DEulerGLM_hasOrderOne`
8. **No regression on cycle 153/154/155/156/157/158 theorems**:
   re-verify axiom-clean status for
   `explicitEulerGLM_hasOrderZero_trivialStarting`,
   `explicitEulerGLM_hasOrderOne_trivialStarting`,
   `padded2DEulerGLM_hasOrderZero_padCompatStarting`,
   `padded2DEulerGLM_hasOrderOne_padCompatStarting`,
   `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`,
   `padded2DEulerGLM_hasOrderZero`,
   `padded2DEulerGLM_hasOrderOne`,
   `explicitEulerGLM_hasOrderZero`,
   `explicitEulerGLM_hasOrderOne`.

---

## Faithfulness check

Each of the new declarations is **internal infrastructure**, not a
direct textbook entity:

- `padded3DEulerGLM`, `pad3CompatMethod`, `pad3CompatStartingMethod`,
  `pad3CompatStartingMethod_isNonDegenerate`,
  `pad3CompatStartingMethod_constituents_isExplicit`,
  `pad3CompatStartingMethod_applyExplicit`,
  `padded3DEulerGLM_isExplicit` — supporting non-vacuity
  infrastructure for `def:530B`'s Path A.
- `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` and
  `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` — non-vacuity
  witnesses for `def:530B` (`HasOrderRelativeTo_explicit`,
  cycle 153 predicate).
- `padded3DEulerGLM_hasOrderZero` and
  `padded3DEulerGLM_hasOrderOne` — non-vacuity witnesses for
  `def:530C` (`HasOrder_explicit`, cycle 155 predicate). These ARE
  textbook-aligned (`def:530C`'s textbook statement is the
  existential closure that these wrappers satisfy).

Run the per-deliverable checklist from CLAUDE.md (tautology /
identity / strength / absent-theorem) on each new theorem. No
predicate scaffolding is introduced this cycle (everything reuses
cycle 152/153/155 infrastructure), so the
"definition smuggling" / "structure with Prop fields" rules are
inactive.

---

## What NOT to try

1. **DO NOT introduce any new sorry.** Sorry count must stay 0 after
   the cycle. If you cannot close any step's sorry placeholders,
   stop and revert that step rather than committing with a sorry.
2. **DO NOT generalise the cycle 158 helper**. Parameterising
   `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` over Taylor
   degree is a separate refactor (cycle 158 task results suggested
   it as cycle 159+ candidate, but that conflicts with the
   substantive r-lift this cycle delivers — defer parameterisation
   to cycle 160+).
3. **DO NOT attempt p ≥ 2 witnesses.** Explicit Euler is a 1st-order
   method; its SM−ES diff is genuinely O(h²), NOT O(h³). A p = 2
   witness for explicit Euler is mathematically false. Higher-order
   witnesses require a higher-order GLM (RK2, midpoint, etc.) — that
   is a multi-cycle effort and is out of scope.
4. **DO NOT attempt Path B (implicit branch) for `def:530B`.** It
   needs `ContractingWith` / `Function.IsFixedPt` infrastructure for
   the stage-equation system; multi-cycle. Stay on Path A.
5. **DO NOT modify
   `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`** (cycle
   158). The new p = 1 witness's i = 0 channel must invoke it as-is.
   If you find the helper's signature insufficient, file an issue
   documenting the gap — but do not edit the helper this cycle.
6. **DO NOT submit Aristotle jobs**. Manual closure with the
   cycle 156/157/158 templates is faster.
7. **DO NOT modify `scripts/autonomous_loop.py`**. Per CLAUDE.md and
   the standing `tautology_scanner_false_positives.md` issue.
8. **DO NOT cherry-pick `def:530C` wrappers without the
   `..._pad3CompatStarting` underlying theorems**. The wrappers are
   thin existential closures; landing them in isolation is
   definition smuggling.
9. **DO NOT re-poll any prior Aristotle job**. Per
   `thm_550A_general_n.md`: project `2c4630b2-…` (cycle 148
   general-`n` thm:550A submission) was cancelled in cycle 151. Do
   not resurrect.
10. **DO NOT extend `padded3DEulerGLM` with new Section520
    corollaries** (e.g. its own `IsRKStable`, `IsIRKStable`,
    A-stability negative witness, etc.). Those would saturate
    Section520 coverage at r = 3, not advance `def:530B`/`def:530C`.
    Out of scope.
11. **DO NOT pivot to a new entity (thm:535A, thm:541A, thm:521B,
    thm:550A general-n, etc.)**. All §530+ theorem entities depend
    either on §31x rooted-tree elementary-differential machinery
    (thm:532A, thm:534A, thm:535A, thm:541A) or on
    eigenvalue-density / Schur infrastructure (thm:521B, thm:550A
    general-n) — both are multi-cycle infrastructure efforts and
    are out of scope. Stay on the r-lift this cycle.

---

## Backup plan if scope blows up

If, after Step 5 (~3 hours into the cycle), you have not closed
both `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` and the
i = 1, i = 2 zero-collapse arms, **fall back** to landing only:

- Step 1 (`padded3DEulerGLM`)
- Step 2 (`pad3CompatStartingMethod` + non-degeneracy +
  constituents-explicit)
- Step 3 (`padded3DEulerGLM_isExplicit`)
- Step 4 (`pad3CompatStartingMethod_applyExplicit`)
- Step 5 (`padded3DEulerGLM_hasOrderZero_pad3CompatStarting`)
- Step 7a (`padded3DEulerGLM_hasOrderZero` def:530C wrapper for p=0)

Skip Step 6 and Step 7b (the p = 1 witness and its def:530C wrapper)
to cycle 160. This still delivers a substantive r = 3 advance at
p = 0; the cycle 158 portability test (the one-line helper
invocation) defers to cycle 160 alongside the p = 1 witness.

If even Step 5 stalls past 4 hours of cycle time, revert all changes
in Section530.lean (keep Section520's new `padded3DEulerGLM` def +
the supporting infrastructure of Steps 2/3/4 if those landed
cleanly) and at minimum file an issue file under
`.prover-state/issues/cycle_159_step5_blocker.md` documenting which
sub-arm stalled and the failed proof attempt. **Do not commit with
a new sorry.** A no-Step-5-or-beyond outcome is acceptable per
CLAUDE.md "minimum: decompose a sorry or write an issue" — Steps
1-4 alone are infrastructure that decompose the witness target.

---

## File hygiene

After all closures land:

- Update `extraction/formalization_data/lean_status.json`: bump the
  cycle reference for `def:530B` and `def:530C` to 159; both remain
  `partial` (Path B implicit branch still deferred — see
  `def_530B_scaffold_strategy.md`).
- Update `plan.md`: extend the `def:530B` and `def:530C` rows'
  cycle-159 update note with the r = 3 saturation summary (one or
  two sentences; mirror cycles 156/157's note style).
- Update `.prover-state/issues/def_530B_scaffold_strategy.md` with
  a "## Cycle 159 update — r = 3 non-vacuity witnesses landed"
  section: list the new theorems (the eight enumerated in §
  Verification 7 above, plus `padded3DEulerGLM` itself), confirm
  axiom-cleanliness, and note that the i = 0 channel of the p = 1
  witness validated cycle 158's helper via a one-line invocation
  (compounding LOC savings vs the would-have-been duplicate copy of
  the cycle 154/157 i = 0 body).
- Write `.prover-state/task_results/cycle_159.md` per CLAUDE.md
  template.

---

## Suggested commit message

```
Cycle 159 — def:530B/C Path A r = 3 × p ∈ {0, 1} witnesses (axiom-clean)
```

(Mirrors cycle 157's tag style.)
