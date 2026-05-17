# Cycle 352 strategy

## Context

Cycle 351 shipped **Phase D′.2.2 Route D Step 1** axiom-clean
(+121 LOC, scored 2): `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
plus BDF2 precursor + BDF2 sanity witness. The identity reads

```
∑ᵢ:Fin (k+1) (i.val : ℝ) · M.β i
  = (1/2) · ∑ᵢ:Fin k ((i.val + 1 : ℕ) : ℝ)^2 · M.α i.succ
```

under `M.HasOrderAtLeast 2`. On BDF2 both sides trivially vanish
(`0 = 0`), so the sanity witness is structurally valid but
mathematically uninformative.

**Pivot decision.** §422 has had 16 consecutive cycles
(336–351). The natural next priority is Phase D′.2.2 Step 2 —
prove `0 ≤ ∑ᵢ i²·αᵢ` from `IsStable + IsPreconsistent +
HasOrderAtLeast 2`. The cycle 351 task results acknowledge this
is **multi-cycle**: it requires either a `ρ''(1)` bound bridge
or the §441 Möbius-transform machinery, neither of which is
shipped. Sorry-first scaffolds with no single-cycle close path
get rolled back per cycle 138/149/200 precedent. Defer.

**Cycle 352 target.** Ship the **trapezoidal rule LMM**
(Crank–Nicolson, the canonical order-2 implicit 1-step method)
with structural witnesses, exercising cycle 351's identity at a
**non-trivial non-zero** value (`coef_β = 1/2`, `(1/2)·Σᵢ
(i+1)²·αᵢ = 1/2`). This is:

* a single-cycle clean ship (~70 LOC), axiom-clean target;
* a substantive non-vacuity for the cycle 351 identity that BDF2
  could not provide (BDF2 trivially gives `0 = 0`);
* extends the LMM witness surface (currently `explicitEulerLMM`,
  `implicitEulerLMM`, `bdf2LMM`) with the third canonical
  small-`k` implicit method;
* unblocks future §422 work that needs a non-trivial order-2 case;
* breaks the §422 streak healthily without abandoning §422
  infrastructure consumers.

## Priorities (in order)

### P1 — `trapezoidalLMM` definition + Section404 wire-up

**Where**: `OpenMath/Chapter4/Section404.lean`, immediately after
`implicitEulerLMM_isConsistent` (around line 163, before the
`§403 — Stability` section comment at line 165). Use the
`explicitEulerLMM` / `implicitEulerLMM` template at lines 79–108
and 145–163 verbatim with the trapezoidal coefficients.

**Coefficients**: trapezoidal rule is the implicit 1-step method
`y_n − y_{n-1} = (h/2)·(f(x_n, y_n) + f(x_{n-1}, y_{n-1}))`,
so `k = 1` and (per the §404 convention `α 0 = -1`):

* `α 0 = -1`, `α 1 = 1`
* `β 0 = 1/2`, `β 1 = 1/2`

**Three deliverables** (template: lines 81–84, 87–89, 146–148,
151–153, 156–158, 161–163):

```lean
/-! ### Third witness — trapezoidal rule (Crank–Nicolson) as a 1-step LMM

The trapezoidal rule (also called Crank–Nicolson) is the implicit
1-step method
  `y_n − y_{n-1} = (h/2) · (f(x_n, y_n) + f(x_{n-1}, y_{n-1}))`,
i.e. `α 0 = -1, α 1 = 1, β 0 = 1/2, β 1 = 1/2`. This is the
canonical order-2 implicit 1-step LMM; it provides the first
non-trivial value for `coef_β = ∑ i · βᵢ` among shipped LMMs
(both Euler methods have `coef_β = 0` or `1`; BDF2 has
`coef_β = 0`; trapezoidal has `coef_β = 1/2`). -/

/-- The trapezoidal rule (Crank–Nicolson) as a 1-step linear
multistep method:
`y_n − y_{n-1} = (h/2) · (f(x_n, y_n) + f(x_{n-1}, y_{n-1}))`. -/
def trapezoidalLMM : LinearMultistepMethod 1 where
  α := fun i => if i = 0 then -1 else 1
  β := fun i => if i = 0 then 1/2 else 1/2
  α_zero := by simp

/-- The trapezoidal rule is preconsistent. -/
theorem trapezoidalLMM_isPreconsistent :
    trapezoidalLMM.IsPreconsistent := by
  simp [LinearMultistepMethod.IsPreconsistent, trapezoidalLMM]

/-- The trapezoidal rule satisfies (404b):
`Σ i·αᵢ = 1·1 = 1 = 1/2 + 1/2 = Σ βᵢ`. -/
theorem trapezoidalLMM_satisfiesEq404b :
    trapezoidalLMM.SatisfiesEq404b := by
  simp [LinearMultistepMethod.SatisfiesEq404b, trapezoidalLMM]

/-- The trapezoidal rule is consistent. -/
theorem trapezoidalLMM_isConsistent :
    trapezoidalLMM.IsConsistent :=
  ⟨trapezoidalLMM_isPreconsistent, trapezoidalLMM_satisfiesEq404b⟩
```

If `trapezoidalLMM_satisfiesEq404b`'s `simp` does not close
directly (the `1/2 + 1/2 = 1` arithmetic), add a trailing
`norm_num` or `ring` as fallback. The Euler-method analogs at
lines 146–148, 156–158 close by plain `simp`, but trapezoidal
has a rational coefficient that may need `norm_num` to collapse.

### P2 — `trapezoidalLMM_hasOrderAtLeast_two` + cycle 351 identity witness

**Where**: `OpenMath/Chapter4/Section422.lean`, immediately
after `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha` (line 1326), just
before the `end OpenMath.Chapter4.Section422` (line 1327).

**P2.a — `trapezoidalLMM_hasOrderAtLeast_two`** — port cycle 351's
`bdf2LMM_hasOrderAtLeast_two` recipe (Section422 lines 1284–1307).
The template is `intro j hj; interval_cases j; show ... ; simp;
norm_num` per case, with the Fin sum unfoldings adjusted for
`k = 1` (use `Fin.sum_univ_one` and `Fin.sum_univ_two` instead of
`Fin.sum_univ_two` and `Fin.sum_univ_three`).

```lean
/-- *Phase D′.2.2 trapezoidal precursor (cycle 352):* the
trapezoidal rule satisfies `HasOrderAtLeast 2`. Verified by
checking `C trapezoidalLMM j = 0` for `j ∈ {0, 1, 2}`:
* `C trapezoidalLMM 0 = 1 - 1 = 0` (preconsistency);
* `C trapezoidalLMM 1 = 0` (consistency);
* `C trapezoidalLMM 2 = -(1·1²/2) + (0·(1/2) + 1·(1/2)) =
  -1/2 + 1/2 = 0`. -/
theorem trapezoidalLMM_hasOrderAtLeast_two :
    OpenMath.Chapter4.Section404.trapezoidalLMM.HasOrderAtLeast 2 := by
  intro j hj
  interval_cases j
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section404.trapezoidalLMM 0 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section404.trapezoidalLMM,
      Fin.sum_univ_one, Fin.sum_univ_two]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section404.trapezoidalLMM 1 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section404.trapezoidalLMM,
      Fin.sum_univ_one, Fin.sum_univ_two, Nat.factorial]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section404.trapezoidalLMM 2 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section404.trapezoidalLMM,
      Fin.sum_univ_one, Fin.sum_univ_two, Nat.factorial]
    norm_num
```

Match the cycle 351 qualified-name convention (use full
`OpenMath.Chapter4.Section404.trapezoidalLMM`, parallel to the
existing `OpenMath.Chapter4.Section451.bdf2LMM` references at
lines 1285, 1289–1290, etc.).

**P2.b — `trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha`** —
one-liner instantiation of cycle 351's
`coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two` at
`trapezoidalLMM`. Both sides reduce to `1/2`:

* LHS `coef_β(trapezoidalLMM) = 0·(1/2) + 1·(1/2) = 1/2`;
* RHS `(1/2) · Σᵢ (i+1)²·αᵢ = (1/2) · (1²·1) = 1/2`.

```lean
/-- *Phase D′.2.2 trapezoidal sanity witness (cycle 352):*
end-to-end exercise of `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
on the trapezoidal rule. Unlike BDF2 (where both sides vanish),
this gives the first non-trivial witness of cycle 351's identity:
* LHS `coef_β(trapezoidalLMM) = 0·(1/2) + 1·(1/2) = 1/2`;
* RHS `(1/2) · Σᵢ (i+1)²·αᵢ = (1/2) · 1²·1 = 1/2`. -/
theorem trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha :
    (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.trapezoidalLMM.β i)
      = (1 / 2) *
        ∑ i : Fin 1, (((i.val + 1 : ℕ) : ℝ))^2 *
          OpenMath.Chapter4.Section404.trapezoidalLMM.α i.succ :=
  coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
    OpenMath.Chapter4.Section404.trapezoidalLMM
    trapezoidalLMM_hasOrderAtLeast_two
```

### P3 — (Optional stretch) BDF3 wire-up if time permits

If P1 + P2 land in under 90 minutes, ship **`bdf3LMM`** in
`Section451.lean` near `bdf2LMM` (line 140):

```lean
noncomputable def bdf3LMM : LinearMultistepMethod 3 where
  α := ![-1, 18/11, -9/11, 2/11]
  β := ![6/11, 0, 0, 0]
  α_zero := rfl
```

Plus `bdf3LMM_isPreconsistent` (`Σᵢ αᵢ.succ = 18/11 - 9/11 +
2/11 = 1`). Defer `bdf3LMM_isConsistent` / `HasOrderAtLeast 3`
unless time permits. **Do NOT attempt `bdf3LMM_isStable`** —
BDF3 stability proof requires complex-root analysis of the
characteristic polynomial, which is multi-cycle.

If P1 + P2 take a full cycle, skip P3 entirely.

## Approach details

### Step order

1. **P1**: edit `Section404.lean`. Compile via
   `lake env lean OpenMath/Chapter4/Section404.lean`.
2. **P2**: edit `Section422.lean`. Compile via
   `lake env lean OpenMath/Chapter4/Section422.lean`.
   Section422 is ~1320 LOC; warm rebuild typically <60s.
3. (Optional) **P3**: edit `Section451.lean`.
4. **Verification**: `#print axioms` on the three new public
   theorems (`trapezoidalLMM_isConsistent`,
   `trapezoidalLMM_hasOrderAtLeast_two`,
   `trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha`) — confirm
   `[propext, Classical.choice, Quot.sound]` only.
5. **Aggregator check**: `lake env lean OpenMath/Chapter4.lean`.
6. Update `lean_status.json` (no row change needed — none of
   these are textbook entities; they're auxiliary witnesses
   for existing infrastructure). The `def:422B` row stays at
   `partial`.
7. Update `plan.md` `def:422B` summary line with cycle 352
   one-sentence summary.
8. Write `.prover-state/task_results/cycle_352.md`.

### Fallback recipes if simp doesn't close

* If `simp [trapezoidalLMM]` doesn't unfold the if-then-else
  cleanly: replace with `unfold trapezoidalLMM; simp` or use
  `show` to expose the Fin sum directly, then case-split
  manually.
* If `Fin.sum_univ_one`-style lemmas don't exist under that
  name in current Mathlib: try `Finset.sum_univ_one`,
  `Fin.sum_univ_succ` × N times, or unfold the sum directly
  via `show ∑ i ∈ Finset.univ, _ = _; rfl`. The cycle 351
  `bdf2LMM_hasOrderAtLeast_two` uses `Fin.sum_univ_two` and
  `Fin.sum_univ_three` successfully, so the `Fin.sum_univ_*`
  family is in scope.
* If the `i.succ` notation confuses `simp`: replace with
  explicit `(⟨0, by omega⟩ : Fin 2).succ` or use `Fin.mk_one`.
* If `Nat.factorial` doesn't reduce: add `Nat.factorial_zero,
  Nat.factorial_succ` to the simp set explicitly.

### Faithfulness check (mandatory pre-commit)

For each new `def`/`theorem`:

**`trapezoidalLMM`**:
* Textbook anchor: Butcher §404 / numerous standard references.
  The trapezoidal rule is a textbook-standard implicit method,
  not a specific Butcher entity ID. The definition matches the
  standard:
  `y_n − y_{n-1} = (h/2)·(f(x_n, y_n) + f(x_{n-1}, y_{n-1}))`.
* Per the §404 normalisation convention `α 0 = -1`, this
  rearranges to `α 0·y_n + α 1·y_{n-1} = -h·(β 0·f_n + β 1·f_{n-1})`
  with `α 0 = -1, α 1 = 1, β 0 = β 1 = 1/2`. **Faithful.**
* Non-vacuity: shipped via `trapezoidalLMM_isPreconsistent` and
  `trapezoidalLMM_isConsistent`.

**`trapezoidalLMM_isPreconsistent`** / **`_satisfiesEq404b`** /
**`_isConsistent`**: numerical witnesses of definitional content.
Same shape as the cycle 040-era `explicitEulerLMM_*` and
`implicitEulerLMM_*` witnesses (Section404 lines 87–89, 146–163).
**Faithful.**

**`trapezoidalLMM_hasOrderAtLeast_two`**: matches the standard
classical-order claim that trapezoidal rule has order 2.
Verified case-by-case for `j ∈ {0, 1, 2}`. **Faithful.**

**`trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha`**: one-line
specialisation of cycle 351's
`coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`.
**Faithful** (the only difference vs cycle 351's bdf2 witness
is the underlying method).

## What NOT to attempt

### Multi-cycle / blocked targets (per cycle 351 strategy footer)

* **DO NOT** attempt **Phase D′.2.2 Step 2** (`0 ≤ ∑ᵢ i²·αᵢ`
  under `IsStable + IsPreconsistent + HasOrderAtLeast 2`).
  Requires §441 ρ''(1) infrastructure (Route ρ'') or Möbius-
  transform sign analysis (Route §441) — neither shipped. Cycle
  351 task results explicitly flag this as multi-cycle.
  Scoping doc `eq422a_eta_phase_D_prime_step_2_scoping.md`
  outlines the path; do not implement without finishing the
  scoping decomposition first.

* **DO NOT** attempt **`def:442A`** (principal sheet). Multi-
  cycle Riemann-surface infrastructure not in Mathlib.

* **DO NOT** attempt **`thm:535A`** (GLM analog of underlying
  one-step method). Multi-cycle, parallel to `def:422B` work.

* **DO NOT** attempt **`thm:302A`**. Blocked on the cycle 250
  `alphaWeight` definition-smuggling issue
  (`cycle_250_strategy_alpha_definition_error.md`).

### Specific to cycle 352

* **DO NOT** attempt `trapezoidalLMM_isStable`. Trapezoidal is
  Dahlquist-stable (characteristic polynomial `ρ(z) = z − 1` has
  its only root at `z = 1`, simple, on the boundary), but a
  Lean stability proof requires careful handling of the
  simple-root-on-boundary case. The cycle 346 `bdf2LMM_isStable`
  recipe may not port directly (BDF2 has interior roots, not
  boundary). Save for a later cycle when a downstream consumer
  needs it.

* **DO NOT** ship `bdf3LMM_isStable` (if attempting P3).
  BDF3 stability requires verifying that two complex roots of
  `ρ(z) = z³ - (18/11)z² + (9/11)z - 2/11` lie strictly inside
  the unit disc. Multi-cycle.

* **DO NOT** add new imports to Section404, Section422, or
  Section451. Cycle 351's BDF2 witnesses reference
  `OpenMath.Chapter4.Section451.bdf2LMM` from Section422 with
  no fresh import — the qualified-name resolution pattern is
  already established and works because Section422's existing
  imports transitively bring Section451 into scope. Use the
  parallel form for `Section404.trapezoidalLMM`.

* **DO NOT** continue the §344 small-`s` direct-form ladder.
  Saturated at cycle 335 (six-for-seven audit outcomes; the
  pattern is fully characterised).

* **DO NOT** raise `maxHeartbeats` above 200000.
* **DO NOT** introduce sorries. Cycle 352's deliverable bar is
  "ship axiom-clean or skip the cycle" per cycle 149/150,
  200/201 rollback precedents.
* **DO NOT** introduce `axiom`/`constant` declarations.

### Naming / placement pitfalls

* `trapezoidalLMM` goes in **`Section404.lean`** (next to
  `explicitEulerLMM`/`implicitEulerLMM`), NOT in
  `Section451.lean` (which is reserved for G-stability-flavoured
  methods like BDF). The trapezoidal rule is a fundamental
  implicit 1-step LMM, parallel to the Euler methods.

* The `trapezoidalLMM_hasOrderAtLeast_two` and
  `trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha` theorems go in
  **`Section422.lean`** (they consume `HasOrderAtLeast` from
  Section410 and cycle 351's identity from Section422). Same
  pattern as the bdf2 versions at lines 1284–1326.

* Use the qualified-name pattern
  `OpenMath.Chapter4.Section404.trapezoidalLMM` in Section422.
  Cycle 351 uses `OpenMath.Chapter4.Section451.bdf2LMM` in the
  parallel position; do not strip the qualification even if
  the unqualified form happens to resolve.

## Estimated LOC budget

* P1 (Section404): ~30 LOC (3 theorems × ~5 LOC + 1 def + 1 docstring block).
* P2 (Section422): ~40 LOC (1 ~25-LOC hasOrderAtLeast + 1 ~10-LOC
  identity witness + docstrings).
* P3 stretch (Section451): ~15 LOC if shipped.

Total: **~70 LOC** (P1+P2) or **~85 LOC** (with P3 stretch).

Well under the cycle 351 budget (+121 LOC). Single-cycle target.

## Cycle 353+ outlook (for the next planner)

After cycle 352 lands, the planner has three candidate paths:

1. **Continue trapezoidal expansion**: ship
   `trapezoidalLMM_isStable` (substantive — at-boundary
   stability proof, ~50 LOC). Useful for downstream §451
   G-stability work.

2. **BDF3 wire-up if P3 was skipped**: ship `bdf3LMM` +
   `_isPreconsistent` + `_isConsistent` + `_hasOrderAtLeast_3`
   in 1 cycle (~40 LOC). Provides a third-order witness for
   future `def:422B` Phase E work.

3. **Phase D′.2.2 Step 2 scoping**: write a dedicated multi-
   phase scoping doc analogous to
   `eq422a_eta_phase_D_prime_step_2_scoping.md` for the
   `ρ''(1)` bridge route. Plan 3–4 single-cycle deliverables
   that incrementally build §441 second-derivative
   infrastructure, then bridge to `Σᵢ i²·αᵢ ≥ 0` under stable
   + preconsistent + order ≥ 2.

Recommend (1) or (2) for cycle 353 — both keep the small-cycle
ship cadence going while the multi-cycle Phase D′ Step 2 work
is properly scoped.
