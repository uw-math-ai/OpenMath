# Cycle 070 strategy

## TL;DR

**Score=−2 was a phantom.** Cycle 069 closed `thm:405B`
(`convergent_isPreconsistent`) cleanly, wired the `thm:243A` iff
packager, and added two scaffold sorries (`thm:405A`,
`thm:405C`) so the iff packager could compile against the
unfinished reverse direction. The supervisor's "0 → 2 sorrys"
verdict treats the deliberate scaffolds as regressions; they are
not. (Same pattern as cycles 008/014/015/040 — see
`consultant_advice_cycle_040.md` §A. Do not reorganise the work
to game the scanner.)

**This cycle's job: close `thm:405C` (`convergent_isConsistent`)
at `OpenMath/Chapter4/Section405.lean:241`.** That brings the
Section405 sorry count from 2 → 1 and turns the iff packager
into a complete two-direction equivalence modulo only the
remaining `thm:405A` (queued for cycle 071).

`thm:405A` is the *harder* of the two open theorems
(contrapositive on an unbounded sequence + maximum-sequence
construction). `thm:405C` reuses the trivial-IVP machinery from
cycle 069's `thm:405B` proof almost verbatim, so the worker has
the muscle memory.

---

## Priority 0 — incorporate cycle 069's Aristotle results (one shot)

Cycle 069 submitted `Section405.lean` to Aristotle as project
**`4ddc0ab0-9542-49ab-abf1-fa7f5601df37`** at 07:38 UTC and
reported it sitting at 8 % after 47 min. Per CLAUDE.md "check
once at 30 min, then proceed", check the status **once** at the
top of cycle 070 via:

```
mcp__aristotle__get_status project_id=4ddc0ab0-9542-49ab-abf1-fa7f5601df37
```

* If a proof for `convergent_isConsistent` (or
  `convergent_isStable`, or any helper) has been returned: extract
  via `mcp__aristotle__extract_result`, paste into Section405.lean,
  verify with `lake env lean OpenMath/Chapter4/Section405.lean` +
  `#print axioms` (must be `propext, Classical.choice, Quot.sound`
  only). Skip the corresponding manual proof below if Aristotle
  has closed it.
* If still `IN_PROGRESS` and < 50 %: the project is unlikely to
  contribute this cycle. Do **not** poll again. Do **not**
  resubmit.
* If `FAILED` or `COMPLETED` with no usable proofs: log in the
  cycle task results and proceed.

Whatever the outcome, do **not** wait beyond a single status
check. The total wall-clock budget for Aristotle interaction this
cycle is < 5 minutes.

---

## Priority 1 — close `thm:405C` (`convergent_isConsistent`)

### Target

`OpenMath/Chapter4/Section405.lean:241` — replace the current
`sorry` body of
`LinearMultistepMethod.convergent_isConsistent` with a complete
proof.

### Mathematical strategy

`M.IsConsistent` unfolds to `M.IsPreconsistent ∧ M.SatisfiesEq404b`
(Section404.lean:135). The first conjunct is `thm:405B`, already
closed in cycle 069 as `M.convergent_isPreconsistent hConv`. So
the entire content of cycle 070 is the second conjunct,

> `M.SatisfiesEq404b`,
> i.e.  `Σ_{i:Fin k} ((i.val:ℝ) + 1) * M.α i.succ
>      = Σ_{i:Fin (k+1)} M.β i`.

(Verify the exact stated form by re-reading `SatisfiesEq404b`
in Section404.lean before starting; the `(i.val + 1) : ℝ` cast
form is what the cycle 040–062 helper chain uses.)

Use the textbook construction (Butcher §405, p. 344) adapted to
sidestep the "Σ iα ≠ 0" non-degeneracy requirement.  The trivial
IVP is `y'(x) = 1, y(0) = 0`, with `yex t := t`, evaluated at
`x = 1`.  Step size `h = 1/m`.  Use the scaled sequence

```
Y m n := S * (n : ℝ) / (m : ℝ),     where S := Σ_{i:Fin (k+1)} M.β i.
```

#### Algebraic computation of the LMM recurrence at this Y

LHS at index `n`:
```
Σ_{i:Fin (k+1)} M.α i * (S * ((n+k - i.val : ℕ) : ℝ) / (m : ℝ))
  = (S/m) * ((n+k) * Σ M.α i  −  Σ_{i:Fin (k+1)} (i.val : ℝ) * M.α i)
  = (S/m) * (0  −  T)                         [preconsistency: Σ M.α i = 0]
  = -(S/m) * T,
where T := Σ_{i:Fin (k+1)} (i.val : ℝ) * M.α i
        = Σ_{i:Fin k} ((i.val + 1 : ℝ)) * M.α i.succ      [the i=0 term is 0].
```

RHS at index `n`:
```
-(1/m) * Σ_{i:Fin (k+1)} M.β i * 1 = -(S/m).
```

So the LMM recurrence holds **iff** `S * T = S`, i.e.
`S · (T − 1) = 0`.

#### Case analysis on `S`

* **Case `S = 0` (exfalso branch).** The zero sequence
  `Y_zero m n := 0` is an LMM solution of `y' = 1` because the
  recurrence collapses to `0 = -(1/m) * S = 0`. Apply `hConv` to
  this `Y_zero` with the given starts. Convergence yields
  `0 = Y_zero m m → yex(1) = 1`, contradiction. Hence `S ≠ 0`.

* **Case `S ≠ 0` (main branch).** The `Y` above is an LMM
  solution **iff** `T = 1` (since `S · (T − 1) = 0` and `S ≠ 0`).
  But we don't know `T = 1` yet — it's what we're trying to
  prove. So we cannot directly hand `hConv` the sequence `Y`
  without first knowing `T = 1`.

  **Resolution: a sub-case split on `T`.**
  - Sub-case `T = 1`. Then `Y` *is* an LMM solution of `y' = 1`.
    Apply `hConv`: `Y m m = S → yex(1) = 1`, hence `S = 1`.
    Combined with `T = 1`, we get `T = S`, which is the goal.
  - Sub-case `T ≠ 1`. Then the recurrence `S · (T − 1) = 0`
    forces `S = 0`, contradicting the outer case `S ≠ 0`. So
    this sub-case is vacuous; close with `exfalso` + the
    arithmetic contradiction.

So the proof has *three* terminal branches:
- `S = 0` → exfalso via zero-sequence + convergence.
- `S ≠ 0 ∧ T = 1` → main argument via `Y`-sequence + convergence.
- `S ≠ 0 ∧ T ≠ 1` → exfalso via `S · (T − 1) = 0` + arithmetic.

### Numerical sanity check (do this before committing)

Test against `explicitEulerLMM` (`k = 1`, `α 0 = -1`, `α 1 = 1`,
`β 0 = 0`, `β 1 = 1`):

* `T = (0+1) · M.α 1 = 1`.
* `S = M.β 0 + M.β 1 = 0 + 1 = 1`.
* `S ≠ 0`, `T = 1`, `T = S`.  ✓

Test against `implicitEulerLMM` (`α 0 = -1, α 1 = 1, β 0 = 1, β 1 = 0`):

* `T = (0+1) · 1 = 1`, `S = 1 + 0 = 1`.  ✓

Test against a hypothetical inconsistent method (`k = 1`,
`α = (-1, 1)`, `β = (0, 0)`):

* `S = 0` → exfalso branch fires.  ✓

### Concrete Lean skeleton

```lean
theorem LinearMultistepMethod.convergent_isConsistent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hConv : M.IsConvergent) : M.IsConsistent := by
  refine ⟨M.convergent_isPreconsistent hConv, ?_⟩
  -- Goal: M.SatisfiesEq404b
  -- Setup: f ≡ 1, yex t = t, x = 1, S := Σβ, T := Σ_{Fin k} (i+1)·α_succ.
  set S : ℝ := ∑ i : Fin (k + 1), M.β i with hS_def
  set T : ℝ := ∑ i : Fin k, ((i.val : ℝ) + 1) * M.α i.succ with hT_def
  -- 0. Algebraic prep: peel the i=0 term off Σ (i:ℝ)·M.α i.
  have hT_alt : (∑ i : Fin (k + 1), (i.val : ℝ) * M.α i) = T := by
    -- Use Fin.sum_univ_succ; the i=0 term vanishes.
    sorry
  -- 1. Preconsistency:  Σ_{Fin (k+1)} M.α i = 0.
  have hPre : (∑ i : Fin (k + 1), M.α i) = 0 := by
    -- α_zero = -1 plus M.convergent_isPreconsistent hConv (= Σ_{Fin k} α.succ = 1).
    sorry
  -- 2. Trivial IVP setup.
  set f : ℝ → ℝ → ℝ := fun _ _ => 1 with hf_def
  set yex : ℝ → ℝ := fun t => t with hyex_def
  -- starts: any sequence with start h i → 0 as h → 0; pick start h _ := 0.
  set start : ℝ → Fin k → ℝ := fun _ _ => 0 with hstart_def
  -- Discharge the 8 hConv hypotheses (Continuous, LipschitzWith, ContDiff,
  -- HasDerivAt, M_bound = 1, hf_yex_bound, hstart_tendsto, hxx).
  -- See the cycle 069 convergent_isPreconsistent proof (Section405.lean:128–155)
  -- for the boilerplate template; adapt:
  --   • hf_uncurry_const : Function.uncurry f = fun _ => 1
  --   • hf_cont via continuous_const
  --   • hf_lip via LipschitzWith.const
  --   • hyex_x₀ : yex 0 = 0   (rfl)
  --   • hyex_C1 : ContDiff ℝ 1 yex   (use contDiff_id or
  --       (contDiff_id.of_le le_top).restrict_scalars; check name)
  --   • hyex_ode : ∀ x, HasDerivAt yex (f x (yex x)) x
  --       — yex' = 1 = f x (yex x); via hasDerivAt_id'
  --   • M_bound = 1, with `0 ≤ 1` and `∀ t, |1| ≤ 1`.
  --   • hstart_tendsto : Tendsto (fun _ => 0) (𝓝 0) (𝓝 0) is tendsto_const_nhds.
  --   • hxx : (0:ℝ) < 1 by norm_num.
  -- The Y sequence depends on case-split on S; defer setup until after split.
  by_cases hS_zero : S = 0
  · -- Case S = 0: zero sequence + convergence ⇒ 0 = 1.
    exfalso
    set Yzero : ℕ → ℕ → ℝ := fun _ _ => 0 with hYzero_def
    have hYzero_props : ∀ m, 0 < m →
        (∀ i : Fin k, Yzero m i.val = start ((1 - 0)/(m : ℝ)) i) ∧
        M.IsLMMSolution ((1 - 0)/(m : ℝ)) 0 f (Yzero m) := by
      intro m hm
      refine ⟨fun _ => rfl, ?_⟩
      -- Goal: M.IsLMMSolution (1/m) 0 (fun _ _ => 1) (fun _ => 0).
      -- LHS Σα·0 = 0. RHS = -(1/m) · Σβ = -(1/m) · S = 0 (since S = 0).
      intro n
      simp only [Yzero, mul_zero, Finset.sum_const_zero, mul_one, neg_zero]
      -- After simp: 0 = -(1/m) * Σβ.  Need to use hS_zero.
      sorry  -- ~5 lines: rewrite S to 0 via hS_zero
    -- Apply hConv with f, yex, start, Yzero.
    have hconv : Filter.Tendsto (fun m : ℕ => Yzero m m - yex 1)
                   Filter.atTop (nhds 0) := by
      sorry  -- apply hConv … ; ~2 lines
    -- Yzero m m - yex 1 = 0 - 1 = -1, constantly. Cannot tend to 0.
    sorry  -- ~10 lines: tendsto_nhds_unique against tendsto_const_nhds
  · -- Case S ≠ 0.
    -- Sub-case split on T = 1.
    by_cases hT_one : T = 1
    · -- Main branch: Y satisfies recurrence, hConv ⇒ S = 1, hence T = S.
      set Y : ℕ → ℕ → ℝ := fun m n => S * (n : ℝ) / (m : ℝ) with hY_def
      have hY_props : ∀ m, 0 < m →
          (∀ i : Fin k, Y m i.val = start ((1 - 0)/(m : ℝ)) i) ∧
          M.IsLMMSolution ((1 - 0)/(m : ℝ)) 0 f (Y m) := by
        sorry
        -- LMM recurrence reduces (via hPre, hT_alt, hT_one) to S * T = S, i.e. S = S. ✓
        -- Starts: Y m i.val = S · i / m and start (1/m) i = 0; these match only if i = 0!
        -- ⚠️ This is a problem: with start ≡ 0, Y m 0 = 0 = start, but Y m 1 = S / m ≠ 0.
        -- FIX: change `start h i := S * (i.val : ℝ) * h` so that
        --   start (1/m) i = S * i / m = Y m i.val.  Then start h i → 0 as h → 0.
      -- ... (re-do with start h i := S * i.val * h; hstart_tendsto adapts via
      --  `(continuous_const.mul continuous_id).tendsto 0`).
      sorry
    · -- Sub-case T ≠ 1, S ≠ 0: derive contradiction from S · (T − 1) = 0.
      -- The "S · (T − 1) = 0" identity is *not* a free fact; it would follow if Y
      -- were an LMM solution.  We don't have that here.  So this sub-case
      -- requires a different witness: try Y_alt m n := (n : ℝ) / (m : ℝ).
      -- Recompute:  LHS = (1/m) · (Σα·(n+k) − Σ i·α) = (1/m)·(0 − T) = -T/m.
      --             RHS = -S/m.  So Y_alt is LMM solution iff T = S.
      -- Apply hConv: Y_alt m m = 1 → yex(1) = 1.  This is consistent regardless,
      -- so no constraint extracted directly.
      -- HMMMM — try Y_alt2 m n := (S/T) · n / m for T ≠ 0 (need separate sub-case).
      -- This sub-case is genuinely the hardest; see "Fallback" below.
      sorry
```

**The skeleton above exposes a real complication in the
`S ≠ 0 ∧ T ≠ 1` sub-case.** The "S · (T − 1) = 0 ⇒ contradiction"
shortcut from the earlier algebra requires `Y` to *be* an LMM
solution, which we're trying to establish.  The fix is to use a
**second witness sequence** `Y2 m n := (n : ℝ) / (m : ℝ)`
(unscaled), whose LMM-recurrence reads:

* LHS = `(1/m) · (0 − T) = -T/m`.
* RHS = `-S/m`.

So `Y2` is an LMM solution **iff** `T = S`. Apply `hConv`: `Y2 m m
= 1 → yex(1) = 1` — a tautology, no constraint extracted.

So `Y2` doesn't separate the sub-cases. Try a third witness:

`Y3 m n := S * (n : ℝ) / (T * (m : ℝ))` when `T ≠ 0`. The recurrence
becomes `(S/T) · ((1/m)·(0 − T)) = -(S/m)`, i.e. `-S/m = -S/m`. ✓
unconditionally. Then `Y3 m m = S/T → 1` forces `S = T`.

But this only works when `T ≠ 0`. If `T = 0` we need yet another
sub-split.

#### Fallback recommended sub-strategy

Given the case-split tangle, the **cleanest formal route** is to
do the textbook's exact construction and explicitly handle the
degeneracy:

1. **Sub-case `T ≠ 0`**. Define `A := S / T` and `Y m n := A · n / m`.
   The recurrence becomes `A · (-T/m) = -S/m`, i.e.
   `A · T = S`, which holds by `A := S/T`. Apply `hConv`:
   `A → 1`, hence `A = S/T = 1`, so `S = T`. Done.
2. **Sub-case `T = 0`**. From the recurrence with `Y m n := S · n / m`:
   `-(S/m) · 0 = -(S/m)`, i.e. `0 = -(S/m)` for all `m > 0`.
   Hence `S = 0`. Then `T = S = 0`, done.

This avoids the three-way split and reduces to `T = 0` vs `T ≠ 0`.
(The `S = 0` case folds into sub-case 2 transparently.)

**Recommended encoding (final):**

```lean
  by_cases hT_zero : T = 0
  · -- T = 0: with Y m n := S · n / m, the recurrence forces S = 0.
    -- Then S = T = 0, done.
    sorry
  · -- T ≠ 0: with Y m n := (S/T) · n / m, recurrence holds unconditionally.
    -- hConv ⇒ S/T = 1, hence S = T.
    sorry
```

**This is the canonical Lean encoding.** Two sub-cases, each
~80 lines including the `hConv` hypothesis discharge.

### Sub-lemma scaffolding (recommended)

To keep individual proof obligations small, factor out:

* `sum_alpha_zero : (∑ i : Fin (k+1), M.α i) = 0`
  — derive from `M.α_zero = -1` + `M.convergent_isPreconsistent hConv`.
  Likely exists somewhere in Section404; search with
  `Grep "α.*= 0|sum.*α.*zero" OpenMath/Chapter4/Section404.lean`.
* `sum_i_alpha_eq_T : (∑ i : Fin (k+1), (i.val : ℝ) * M.α i)
                    = ∑ i : Fin k, ((i.val : ℝ) + 1) * M.α i.succ`
  — peel the `i = 0` term off via `Fin.sum_univ_succ`.
* `Y_isLMMSolution :  hRecurrence : A * T = S → ∀ m,
   M.IsLMMSolution (1/m) 0 (fun _ _ => 1) (fun n => A * n / m)`
  — encapsulates the algebra; reusable across both sub-cases.

Each of these is ≤ 20 lines.  The main proof then becomes mostly
hypothesis bookkeeping.

### Boilerplate to copy from cycle 069

Lines 124–171 of `Section405.lean` (cycle 069's
`convergent_isPreconsistent`) are the hypothesis-discharge
template for `hConv`. Adapt:

* `f := fun _ _ => 1` (was `fun _ _ => 0`).
* `yex := fun t => t` (was `fun _ => 1`).
* `M_bound := 1` (was `0`); `hf_yex_bound : ∀ t, |1| ≤ 1` via
  `simp [abs_one]`.
* `start := fun h i => (S/T) * (i.val : ℝ) * h` (or `S * i.val * h`
  in the `T = 0` branch); `hstart_tendsto` via
  `(tendsto_const_nhds.mul tendsto_id).comp`.
* `hyex_C1`: `ContDiff ℝ 1 (fun t : ℝ => t)`; first try
  `contDiff_id`. If that produces the wrong instance form, try
  `(contDiff_id : ContDiff ℝ ⊤ _).of_le le_top` or
  `(contDiff_id : ContDiff ℝ _ _)`. Verify the exact lemma name
  with `lean_local_search "contDiff_id"`.
* `hyex_ode`: `∀ x, HasDerivAt (fun t : ℝ => t) (1 : ℝ) x` via
  `hasDerivAt_id'` (or `(hasDerivAt_id x)` plus a coercion/eta).
  Verify with `lean_hover_info` if both names exist.

### Aristotle suitability

`convergent_isConsistent` is one moderately complex theorem with
a case split + algebraic recurrence calculation. Aristotle's
premise selection often misses the `Fin.sum_univ_succ` re-indexing
that drives the `T`-identity. **Recommendation: do not re-submit
`thm:405C` to Aristotle this cycle.** The cycle 069 submission
already includes it; if no proof comes back from that, manual
proof is the cheaper route. If you want to use free compute,
batch-submit the **three sub-lemmas** (`sum_alpha_zero`,
`sum_i_alpha_eq_T`, `Y_isLMMSolution`) to a fresh project — these
are exactly the kind of mechanical algebra Aristotle handles
well.

### Estimated effort

* Sub-lemmas (3): ~60 lines combined.
* `T = 0` branch: ~50 lines (zero-sequence + recurrence + `S = 0`
  extraction + done).
* `T ≠ 0` branch: ~120 lines (`hConv` discharge + limit argument
  + `S/T = 1` extraction + done).
* Total: ~230 LOC, single cycle.

If after 2 hours of focused effort the `T ≠ 0` branch doesn't
land cleanly: file a sub-lemma decomposition issue, sorry-first
the helpers, and target cycle 071 for closure. Do **not** spend
more than one cycle on `thm:405C`.

---

## Priority 2 — only if Priority 1 lands cleanly

Begin scaffolding `thm:405A` (`convergent_isStable`,
Section405.lean:100) for cycle 071. Concretely, write helper
signatures (with `sorry` bodies, not full proofs) for:

* `unboundedSeq_max : (η : ℕ → ℝ) → ℕ → ℝ` — running max of
  `|η_·|`.
* `unboundedSeq_max_records : Unbounded (Set.range (fun n => |η n|)) →
  ∀ N, ∃ n ≥ N, |η n| = unboundedSeq_max η n` — record indices
  form an unbounded subsequence.
* `IsHomogeneousSolution.const_smul :
   M.IsHomogeneousSolution η → ∀ c : ℝ,
   M.IsHomogeneousSolution (fun n => c * η n)` — linearity (the
  recurrence is linear in `η`).

Each of these is independently provable (no convergence required)
and decoupled from `hConv`. They form the toolkit for the
cycle 071 contrapositive proof.

Submit them as a fresh Aristotle batch at cycle's end — but
**only if cycle 070's Priority 1 has landed**. If Priority 1
hasn't landed, defer Priority 2 to keep the cycle's diff focused
and reviewable.

---

## What NOT to do this cycle

* Do **NOT** treat the cycle 069 `score=−2` verdict as a real
  failure. The two scaffold sorries are the deliberate mechanism
  by which `thm:243A`'s iff packager type-checks against the
  staged reverse direction. See `consultant_advice_cycle_040.md`
  §A for the standing prompt-builder phantom diagnosis. Do not
  back-out the scaffolds.
* Do **NOT** revert the cycle 068 strengthening of
  `IsConvergent` (joint Lipschitz, `ContDiff ℝ 1`, `M_bound`).
  See `is_convergent_strengthened.md`. The cycle 069
  `convergent_isPreconsistent` proof relies on the strengthening
  in exactly the same way the cycle 070 `convergent_isConsistent`
  proof will.
* Do **NOT** attempt `thm:405A` (`convergent_isStable`) before
  `thm:405C`. `thm:405A` is harder (contrapositive on an
  unbounded sequence + maximum-sequence + record-indices
  pigeonhole). Closing `thm:405C` first uses the cycle-069-tested
  trivial-IVP machinery.
* Do **NOT** chase the textbook's "Σ iα ≠ 0" hypothesis (Butcher
  derives it from `thm:405A`). The Lean approach above
  side-steps via the case split on `T := Σ_{Fin k} (i+1)·α_succ`,
  mirroring how cycle 069's `thm:405B` proof side-stepped
  Butcher's appeal to `thm:405A`.
* Do **NOT** use the three-way split (`S = 0`, `S ≠ 0 ∧ T = 1`,
  `S ≠ 0 ∧ T ≠ 1`) sketched in the first-pass skeleton. That
  split has a gap in the `S ≠ 0 ∧ T ≠ 1` branch (the `S(T−1)=0`
  identity is not a free fact). Use the **two-way split on `T`
  via `A := S/T`** described in "Fallback recommended sub-strategy"
  above.
* Do **NOT** raise `maxHeartbeats` above 200000. If the
  preconsistency-driven sum manipulation
  `(n+k) · Σ M.α i = 0` triggers a heartbeat blow-up, decompose
  into `sum_alpha_zero` and apply via `rw` rather than letting
  `ring` chew on the entire goal.
* Do **NOT** introduce `axiom`/`constant` to bypass the
  `ContDiff ℝ 1 (fun t => t)` /
  `HasDerivAt (fun t => t) 1 _` obligations. Both are standard
  Mathlib facts (verify exact names with `lean_local_search` /
  `lean_hover_info` before committing to one).
* Do **NOT** modify `scripts/autonomous_loop.py`. The cycle
  scoring vs scaffold-sorry mismatch is a loop-maintainer issue
  tracked in `tautology_scanner_false_positives.md`.
* Do **NOT** poll Aristotle more than once. Single status check
  at top of cycle, then proceed. Do **NOT** resubmit cycle 069's
  project — it is still in flight.
* Do **NOT** cherry-pick easier targets from Chapter 3 (e.g.
  `def:381B`, `def:381D`, `def:381F`) to "rescue" the score.
  The §405 chain is the strategic critical path; Chapter 3 work
  is fine in parallel cycles but should not pre-empt closing the
  `thm:243A` cross-chapter deferral.

---

## Pre-commit faithfulness check (CLAUDE.md mandatory)

For `convergent_isConsistent`:

* **Entity**: `thm:405C`, textbook statement
  > "A convergent linear multistep [method] is consistent."
* **Lean statement**:
  `(hConv : M.IsConvergent) → M.IsConsistent`.
  Captures: **same content**.
* **Proof-side deviation from textbook**: the Lean proof
  side-steps Butcher's appeal to `thm:405A` (used in the
  textbook to derive `Σ iα ≠ 0`). We use a case split on
  `T := Σ (i+1)·α_succ` instead. Document this in the
  docstring + cycle 070 task results §"Faithfulness check".
  The *conclusion* matches Butcher's exactly; the divergence is
  only in the proof.
* **Tautology check**: `IsConsistent` is the conjunction of two
  non-trivial equations on `α, β`; conclusion ≠ any hypothesis.
  ✓
* **Identity check**: proof is non-trivial (case split + LMM
  recurrence + limit argument); not `exact h`. ✓
* **Hypothesis strength check**: the only hypothesis is
  `M.IsConvergent`, matching the textbook exactly. ✓
* **Absent theorem check**: no promised-but-missing helpers.
  All sub-lemmas (if extracted) must be defined and proved
  before commit. ✓

---

## Workflow summary

1. **(5 min)** Check Aristotle status of project
   `4ddc0ab0-9542-49ab-abf1-fa7f5601df37` once.
2. **(10 min)** Read cycle 069's `convergent_isPreconsistent`
   proof (Section405.lean:120–225) to refresh the hypothesis-
   discharge boilerplate.
3. **(15 min)** Verify the sub-sum identity
   `(∑ i : Fin (k+1), (i.val : ℝ) * M.α i)
    = ∑ i : Fin k, ((i.val : ℝ) + 1) * M.α i.succ`
   compiles standalone (use `Fin.sum_univ_succ` and `Fin.val_succ`).
   This is the algebraic heart of the LMM-solution discharge.
   Lock it in as a local `have` or a sub-lemma.
4. **(10 min)** Verify `(∑ i : Fin (k+1), M.α i) = 0` from
   `M.α_zero` + `M.convergent_isPreconsistent hConv`. Lock in
   as `hPre`.
5. **(40 min)** Write the `T = 0` branch. Use the unscaled
   `Y m n := S · n / m`; recurrence forces `S · 0 = S`, hence
   `S = 0`; then `T = S = 0`, done.
6. **(60 min)** Write the `T ≠ 0` branch. Use
   `Y m n := (S/T) · n / m`; recurrence holds unconditionally;
   discharge the 8 `hConv` hypotheses; `Y m m = S/T → 1` gives
   `S/T = 1`, hence `S = T`. Done.
7. **(15 min)** Verify with `lake env lean
   OpenMath/Chapter4/Section405.lean`, `#print axioms`, and
   `lake build`.
8. **(15 min)** Update `lean_status.json` for `thm:405C`
   (status `formalized`, `lean_file`, `lean_symbol`). Update
   `plan.md` row for `thm:405C`. Re-check the cycle 069
   `plan.md` state before bumping the totals.
9. **(15 min)** Write `task_results/cycle_070.md` documenting
   approach, faithfulness deviation (case split on `T`), and
   whether Priority 2 was started.
10. **Commit + push.**

If at hour 4 the `T ≠ 0` branch hasn't landed: file a sorry-first
decomposition issue, leave the case-split branches as `sorry`
placeholders (one per branch), prove at least the three
sub-lemmas (`sum_alpha_zero`, `sum_i_alpha_eq_T`,
`Y_isLMMSolution`), and target cycle 071 for closure. A clean
sorry-first scaffold + 3 sub-lemmas proven counts as cycle
progress under CLAUDE.md.
