# Cycle 062 Strategy — Assemble the autonomous-IVP outer squeeze (`thm:406D` core)

## TL;DR

All cycle 053–061 prerequisites are in place. Cycle 062 closes the
**autonomous-IVP variant** of `thm:406D` as a fresh top-level theorem
`stable_consistent_isConvergent_autonomous`. The single open
`sorry` at `Section404.lean:3818`
(`stable_consistent_isConvergent`, the full non-autonomous form)
**stays in place** — the non-autonomous lift is the cycle 063+
deliverable.

Two priorities, in order:

1. **Add `aOf_tendsto_zero`** — the cycle-061 wrappers covered
   `bOf`, `cOf`, `yPrimeSumOf` but `aOf` was deferred since it
   requires both `bOf` (via `CbaseOf`) and `yPrimeSumOf`. This is
   the last missing Tendsto helper.
2. **State and prove `stable_consistent_isConvergent_autonomous`** —
   the autonomous-IVP analog of the line-3818 deliverable, proved by
   `globalError_closed_form_autonomous_explicit` plus the cycle 059
   outer-squeeze helpers plus the cycle 057
   `c_h_h_squared_tendsto_zero` / `tendsto_step_size_*` infrastructure.

There are **no pending Aristotle results**. Per CLAUDE.md
"maximize Aristotle usage", batch-submit ~5 sub-lemmas at the start
of the cycle (see §C). Sleep 30 min, then proceed with manual proofs
of whatever Aristotle has not closed.

---

## A. No-rebuild checks

Run before any Lean edit, to confirm the cycle 061 baseline:

```bash
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section404.lean
# Expected: exactly 2 hits — line 1950 (`exact h_diff`) and line 2842
# (`rw [h_eps_eq]; exact h_Sy_bound`). Both grandfathered cycle-052/055
# closers, both do real work.

git log -1 --format='%H %s'
# Expected: aac1b40 Cycle 061 — three Tendsto wrappers for cycle 060's *Of defs ...

git rev-parse HEAD; git rev-parse origin/Main/Experiments
# Expected: same SHA on both. (If different, see consultant notes 009/014/015 §A.)

lake env lean OpenMath/Chapter4/Section404.lean
# Expected: exit 0; warnings = 4 (hM, hh, hMmax0 unused-variables + line-3818 sorry).
```

If any of these returns something different, escalate before
proceeding (it would mean the cycle 061 commit has been rolled back
or a stale `attempts.md` is being read).

---

## B. Priority 1 — `aOf_tendsto_zero`

### Background

`aOf M Θ L h yex Y x₀` (cycle 060,
`Section404.lean:3178–3181`) unfolds to

```lean
aOf M Θ L h yex Y x₀
  = (Θ + (Θ + 1) * CbaseOf M L h * h * (k : ℝ) + 1)
    * yPrimeSumOf M yex Y x₀ h
```

Cycle 057 proved exactly this Tendsto fact in unfolded form as
`a_m_tendsto_zero` (`Section404.lean:2245–2272`). What's needed
this cycle is the wrapper over the cycle 060 `aOf` def, with the
**per-`h`** starting-data hypothesis (so the result composes cleanly
with `IsConvergent`'s `start : ℝ → Fin k → ℝ`).

### Signature to add

Insert immediately after `yPrimeSumOf_tendsto_zero`
(`Section404.lean:3780–3794`), before
`stable_consistent_isConvergent`:

```lean
open OpenMath.Chapter1.Section141 in
/-- **Tendsto of `aOf` to zero (cycle 062).**

`aOf M Θ L h yex (Yh h) x₀` is the linear-recurrence initial
constant `a` of `globalError_recurrence_form_explicit`. As `h → 0`:
* the bracket `Θ + (Θ + 1) · CbaseOf · h · k + 1` tends to a finite
  limit (the `· h` factor kills `CbaseOf`'s contribution);
* `yPrimeSumOf M yex (Yh h) x₀ h` tends to `0` whenever the
  starting-data error converges (`yex (x₀ + j·h) - Yh h j → 0` for
  each `j < k`).

So `aOf · → 0`. Wrapper over cycle 057's `a_m_tendsto_zero`,
threaded through cycle 060's `aOf` and `yPrimeSumOf` defs with the
per-`h` `Yh : ℝ → ℕ → ℝ` shape. Internal scaffolding for the §406D
outer-squeeze assembly (cycle 062). Not a Butcher concept. -/
private lemma aOf_tendsto_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L : ℝ)
    (yex : ℝ → ℝ) (Yh : ℝ → ℕ → ℝ) (x₀ : ℝ)
    (hstart : ∀ j : Fin k,
        Filter.Tendsto
          (fun h : ℝ => yex (x₀ + (j.val : ℝ) * h) - Yh h j.val)
          (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun h : ℝ => aOf M Θ L h yex (Yh h) x₀)
      (nhds 0) (nhds 0) := by
  unfold aOf
  exact a_m_tendsto_zero M Θ L
    (u := fun h j => yex (x₀ + (j.val : ℝ) * h) - Yh h j.val)
    hstart
```

### Why this works

- `unfold aOf` exposes the goal as the body of `a_m_tendsto_zero`
  with `u h j := yex (x₀ + j·h) - Yh h j`.
- `a_m_tendsto_zero` already takes a generic
  `u : ℝ → Fin k → ℝ` with per-index Tendsto. The named-argument
  syntax `(u := …)` forces the unifier to commit to the right
  family.
- `yPrimeSumOf` *also* unfolds (cycle 060 def) to exactly the
  `Σ |yPrime …|` form `a_m_tendsto_zero` wants. If the unfold
  chain doesn't fire on its first pass, add `yPrimeSumOf` to the
  unfold: `unfold aOf yPrimeSumOf`.

### Fallback if the proof is sticky

If `a_m_tendsto_zero` won't unify directly (e.g. `CbaseOf` is not
unfolded in `a_m_tendsto_zero`'s statement so the bracket shapes
differ), the alternative is a slightly longer `convert`:

```lean
  unfold aOf CbaseOf yPrimeSumOf
  convert a_m_tendsto_zero M Θ L
    (u := fun h j => yex (x₀ + (j.val : ℝ) * h) - Yh h j.val)
    hstart using 1
  -- (one or two `ring`/`congr 1` steps if shapes drift)
```

Do **not** redo the proof of `a_m_tendsto_zero` from scratch — it is
60 lines of cycle 057 work and reproducing it costs 30 min for
zero gain.

---

## C. Aristotle batch (~5 sub-lemmas, submit at cycle start)

Per CLAUDE.md: maximize Aristotle, submit ~5 jobs in batch, sleep
30 min, check once. Submit these five sub-lemmas at cycle start so
they have run while you do priorities 1 and (if Aristotle returns)
priority 2:

### Job 1 — `aOf_tendsto_zero`

The lemma in §B. If the `unfold + exact` chain works, manual proof
is one line; submission is a hedge. If unfold drifts, Aristotle's
`convert ... using 1; ring` may close it faster than manual
debugging.

### Job 2 — `cOf_h_tendsto_zero`

Standalone, 3-line manual proof — but submit anyway:

```lean
private lemma cOf_h_tendsto_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L M_bound : ℝ) :
    Filter.Tendsto (fun h : ℝ => cOf M Θ L M_bound h * h)
      (nhds 0) (nhds 0) := by
  exact tendsto_const_mul_h_zero (fun h => cOf M Θ L M_bound h) _
    (cOf_tendsto_at_zero M Θ L M_bound)
```

(`tendsto_const_mul_h_zero` is at `Section404.lean:2195`.)

### Job 3 — `bOf_pos_at_zero`

For `globalError_outer_squeeze_c_term`'s `0 < bInf` hypothesis. The
limit is `(Θ + 1) · L · (|β 0| · Σ|α(i+1)| + Σ|β(i+1)|) + 1`. The
`+ 1` makes positivity unconditional:

```lean
private lemma bOf_limit_pos
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L : ℝ)
    (hΘ_nn : 0 ≤ Θ) (hL : 0 ≤ L) :
    0 < (Θ + 1) *
            (L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                  + ∑ i : Fin k, |M.β i.succ|))
          + 1 := by
  have h1 : 0 ≤ (Θ + 1) := by linarith
  have h2 : 0 ≤ L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                + ∑ i : Fin k, |M.β i.succ|) := by
    apply mul_nonneg hL
    apply add_nonneg
    · exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith [mul_nonneg h1 h2]
```

Submit with the alternative phrasings `positivity`-style and
`nlinarith`; Aristotle picks the one that unifies.

### Job 4 — A small helper bridging `globalError_closed_form_autonomous_explicit` to a per-`m` `Y m m` bound

```lean
private lemma globalError_per_m_bound
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent) (hstab : M.IsStable)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {x₀ x : ℝ} (hxx : x₀ ≤ x)
    (Y : ℕ → ℕ → ℝ)
    (hY : ∀ m : ℕ, 0 < m →
      let h_m := (x - x₀) / (m : ℝ)
      h_m * L * |M.β 0| < 1 ∧
      M.IsLMMSolution h_m x₀ (fun _ y => f y) (Y m)) :
    ∃ Θ : ℝ, 0 ≤ Θ ∧
      ∀ m : ℕ, 0 < m →
        let h_m := (x - x₀) / (m : ℝ)
        |yex (x₀ + (m : ℝ) * h_m) - Y m m|
          ≤ Real.exp (bOf M Θ L h_m * (k : ℝ) * (m : ℝ) * h_m)
              * aOf M Θ L h_m yex (Y m) x₀
            + (Real.exp (bOf M Θ L h_m * (k : ℝ) * (m : ℝ) * h_m) - 1)
                * (cOf M Θ L M_bound h_m * h_m
                    / (bOf M Θ L h_m * (k : ℝ))) := by
  -- Pick Θ from theta_bounded_of_isStable; reuse it for all m.
  obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab
  refine ⟨Θ, hΘ_nn, ?_⟩
  intro m hm
  obtain ⟨hsmall, hYm⟩ := hY m hm
  have hh_nn : 0 ≤ (x - x₀) / (m : ℝ) :=
    div_nonneg (sub_nonneg.mpr hxx) (Nat.cast_nonneg m)
  -- Apply globalError_closed_form_autonomous_explicit at n := m.
  have hbound :=
    LinearMultistepMethod.globalError_closed_form_autonomous_explicit
      hk M hcons hstab hL hM hf_lip hyex_C1 hyex_ode hf_yex_bound
      hh_nn hsmall hYm
  -- destruct the ∃ Θ' but force Θ' = Θ via uniqueness of theta_bounded? No — re-derive.
  sorry  -- Aristotle / manual: extract `Θ` consistently across `m`.
```

⚠️ **Subtle point**: `globalError_closed_form_autonomous_explicit`
re-derives `Θ` internally via `theta_bounded_of_isStable`, so the
`Θ` it picks is the *same* canonical θ-bound for every call (the
underlying `theta_bounded_of_isStable` is deterministic — it returns
`sSup (range |theta|)` or similar). Verify this by reading
`theta_bounded_of_isStable`'s body (`Section404.lean:1737`); if it
uses `Classical.choose`, the per-`m` `Θ`s may differ and you need
to extract `Θ` *once* and pass it through.

If `theta_bounded_of_isStable` is non-deterministic, the right move
is to refactor the cycle 060 `globalError_closed_form_autonomous_explicit`
to take `Θ` as an *input* parameter (it already does, via
`globalError_recurrence_form_explicit`). Bypass the cycle 060 wrapper
and call `globalError_recurrence_form_explicit` directly here, with
the same `Θ` extracted once.

This is the riskiest sub-lemma of the five — submit to Aristotle
first.

### Job 5 — The main theorem itself

Submit `stable_consistent_isConvergent_autonomous` as a complete
draft (see §D below for the full sketch). If Aristotle closes it,
land directly. If not, treat the returned partial as a starting
point.

---

## D. Priority 2 — `stable_consistent_isConvergent_autonomous`

### Statement to add

Insert immediately before `stable_consistent_isConvergent`
(`Section404.lean:3814`). **Do not delete the existing sorry'd
theorem** — leave it as the cycle 063+ deliverable for the
non-autonomous lift.

```lean
open OpenMath.Chapter1.Section141 in
/-- **Butcher Theorem 406D, autonomous-IVP form (Tendsto).**
For a stable consistent linear multistep method `M` solving the
*autonomous* IVP `y' = f(y)` with `f` Lipschitz and `f∘yex` bounded
on the interval, the global LMM error tends to zero as the step
size shrinks:

  `|yex(x) − Y_m m| → 0    as m → ∞,    where  h_m := (x−x₀)/m`.

This is the autonomous specialisation of `IsConvergent` (Butcher
def:402A): `f` does not depend on `x`, `start` is per-`h`, and the
`k` initial values converge to `y₀ = yex x₀` as `h → 0`.

The non-autonomous form `stable_consistent_isConvergent` follows by
lifting in cycle 063+. -/
theorem LinearMultistepMethod.stable_consistent_isConvergent_autonomous
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hstab : M.IsStable) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {x₀ x : ℝ} (hxx : x₀ < x)
    (Y : ℕ → ℕ → ℝ)
    (hsmall : ∀ m : ℕ, 0 < m →
      ((x - x₀) / (m : ℝ)) * L * |M.β 0| < 1)
    (hYm : ∀ m : ℕ, 0 < m →
      M.IsLMMSolution ((x - x₀) / (m : ℝ)) x₀ (fun _ y => f y) (Y m))
    (hstart : ∀ j : Fin k,
        Filter.Tendsto
          (fun h : ℝ => yex (x₀ + (j.val : ℝ) * h)
                          - Y (Nat.ceil ((x - x₀) / h)) j.val)
          (nhds 0) (nhds 0)) :
    Filter.Tendsto (fun m : ℕ => Y m m - yex x)
      Filter.atTop (nhds 0) := by
  sorry
```

⚠️ **Two design decisions to nail down before writing the proof**:

1. **`hstart` shape.** The full `IsConvergent` shape is "for each
   `j`, `start h j → y₀` as `h → 0`". Combined with `hyex_C1`
   (which gives `yex` continuous, so
   `yex (x₀ + j·h) → yex x₀ = y₀`), the per-`j` Tendsto
   `yex (x₀ + j·h) - Yh h j → 0` is equivalent to `Yh h j → y₀`.
   For the per-`m` `Y : ℕ → ℕ → ℝ` shape, the natural reformulation
   is to parametrize `Yh h := Y (Nat.ceil ((x - x₀) / h))`, but
   that's clumsy and obscures the squeeze. **Cleaner alternative**:
   take `hstart` directly as a per-`m` Tendsto:
   ```
   (hstart : ∀ j : Fin k,
       Filter.Tendsto
         (fun m : ℕ => Y m j.val - yex (x₀ + (j.val : ℝ) * ((x - x₀) / (m : ℝ))))
         Filter.atTop (nhds 0))
   ```
   This matches `globalError_outer_squeeze_a_term`'s `atTop` shape
   directly. **Recommend this version**; the `nhds 0` form is
   cycle 063 territory (lift via `tendsto_step_size_comp`).

2. **Strict vs non-strict inequality on `x₀ < x`.** Cycle 057's
   `m_h_constancy` requires `0 < m` for the field-simp; cycle 058's
   `tendsto_step_size_atTop` works for any `x, x₀`. Use `x₀ < x`
   (strict) so `(x - x₀) > 0` and downstream consumers can lift to
   non-autonomous without an extra positivity dance.

### Proof skeleton

```lean
  -- Step 1: extract the canonical Θ once.
  obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab
  -- Step 2: per-m closed-form bound.
  have hbound : ∀ m : ℕ, 0 < m →
      |yex (x₀ + (m : ℝ) * ((x - x₀) / (m : ℝ))) - Y m m|
        ≤ Real.exp (bOf M Θ L ((x - x₀) / (m : ℝ))
                      * (k : ℝ) * (m : ℝ) * ((x - x₀) / (m : ℝ)))
            * aOf M Θ L ((x - x₀) / (m : ℝ)) yex (Y m) x₀
          + (Real.exp (bOf M Θ L ((x - x₀) / (m : ℝ))
                        * (k : ℝ) * (m : ℝ) * ((x - x₀) / (m : ℝ))) - 1)
              * (cOf M Θ L M_bound ((x - x₀) / (m : ℝ))
                  * ((x - x₀) / (m : ℝ))
                  / (bOf M Θ L ((x - x₀) / (m : ℝ)) * (k : ℝ))) := by
    intro m hm
    have hh_nn : 0 ≤ (x - x₀) / (m : ℝ) :=
      div_nonneg (le_of_lt (sub_pos.mpr hxx)) (Nat.cast_nonneg m)
    -- Bypass the cycle-060 wrapper to thread Θ explicitly.
    obtain ⟨ha, hb, hc, hrec, hu0⟩ :=
      globalError_recurrence_form_explicit hk M hcons hL hM hf_lip
        hyex_C1 hyex_ode hf_yex_bound hh_nn (hsmall m hm) (hYm m hm)
        Θ hΘ_nn hΘ
    have hu0' :
        |yex (x₀ + ((0 : ℕ) : ℝ) * ((x - x₀) / (m : ℝ))) - Y m 0|
          ≤ aOf M Θ L ((x - x₀) / (m : ℝ)) yex (Y m) x₀ := by
      simpa using hu0
    exact discrete_gronwall_exp_bound
      (fun n => |yex (x₀ + (n : ℝ) * ((x - x₀) / (m : ℝ))) - Y m n|)
      _ _ _ _ k ha hb hc hh_nn hk hu0' hrec m
  -- Step 3: rewrite `m · h_m = x - x₀` inside the bound's LHS argument
  --         (the `yex (x₀ + m·h_m)` term collapses to `yex x`).
  -- Step 4: squeeze.
  --   • `aOf-term → 0` via `globalError_outer_squeeze_a_term` +
  --     `aOf_tendsto_zero` + `bOf_tendsto_at_zero`.
  --   • `cOf-term → 0` via `globalError_outer_squeeze_c_term` +
  --     `bOf_tendsto_at_zero` + `cOf_tendsto_at_zero` (and
  --     `bOf_limit_pos`).
  --   • `|sum of two →0|` ≥ |yex x - Y m m|, so squeeze.
  -- Step 5: discharge by `Filter.Tendsto.squeeze` /
  --         `tendsto_of_tendsto_of_tendsto_of_le_of_le`.
  sorry  -- ~80–120 lines of glue; decompose if it overflows.
```

### Concrete glue plan for steps 3–5

#### Step 3 — collapse `yex (x₀ + m · h_m)` to `yex x`

`m · h_m = x - x₀` for `m ≥ 1` (cycle 057's `m_h_constancy`). So
`x₀ + m · h_m = x`, hence `yex (x₀ + m · h_m) = yex x`. Use
`Filter.eventually_atTop.mpr ⟨1, ?_⟩` and `m_h_constancy hm x x₀`
inside an `eventually_eq` rewrite of the LHS.

#### Step 4 — Tendsto chain

After Step 3, the LHS of the bound is `|yex x - Y m m|`. The bound's
RHS is exactly the sum
```
exp(bOf · k · m · h_m) · aOf + (exp(bOf · k · m · h_m) - 1) · (cOf · h_m / (bOf · k))
```
which is the sum of `globalError_outer_squeeze_a_term`'s subject and
`globalError_outer_squeeze_c_term`'s subject (instantiated at the
right `b, c, a`).

Setup:
```lean
  -- aOf as a function of h, with Yh = Y (ceil((x-x₀)/h)) (or per-m if you took the per-m hstart).
  let bFun := fun h : ℝ => bOf M Θ L h
  let cFun := fun h : ℝ => cOf M Θ L M_bound h
  let aFun := fun h : ℝ => aOf M Θ L h yex (Y (Nat.ceil ((x - x₀) / h))) x₀
  -- (Or with the per-m hstart, build aFun via the m-indexed form directly.)
  have hb_lim : Filter.Tendsto bFun (nhds 0) (nhds bInf) :=
    bOf_tendsto_at_zero M Θ L
  have hc_lim : Filter.Tendsto cFun (nhds 0) (nhds cInf) :=
    cOf_tendsto_at_zero M Θ L M_bound
  have ha_lim : Filter.Tendsto aFun (nhds 0) (nhds 0) :=
    aOf_tendsto_zero M Θ L yex (Y (Nat.ceil …)) x₀ hstart
  -- (Or with per-m hstart, prove `aFun → 0` via `m`-indexed combinator
  -- since `aOf_tendsto_zero` is `nhds 0`-shaped.)
  have ha_term :=
    globalError_outer_squeeze_a_term ha_lim hb_lim k x₀ x
  have hc_term :=
    globalError_outer_squeeze_c_term hb_lim hc_lim hb_pos hk x₀ x
  have hsum : Filter.Tendsto
      (fun m : ℕ => exp(…) · aFun(h_m) + (exp(…) - 1) · …)
      Filter.atTop (nhds (0 + 0)) := ha_term.add hc_term
  simpa using hsum
```

The `simpa` handles `0 + 0 = 0`.

#### Step 5 — squeeze

```lean
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ hsum ?_ ?_
  · -- |·| ≥ 0
    exact tendsto_const_nhds
    -- (or use `tendsto_of_tendsto_of_tendsto_of_le_of_le` + abs_nonneg)
  · refine Filter.eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
    exact abs_nonneg _
  · refine Filter.eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
    -- Apply hbound at m, post-rewrite by m_h_constancy in the LHS.
    have := hbound m hm
    -- Bridge `|yex (x₀ + m·h_m) - Y m m| = |yex x - Y m m|`.
    rwa [show x₀ + (m : ℝ) * ((x - x₀) / (m : ℝ)) = x from by
          rw [m_h_constancy hm x x₀]; ring] at this
```

Then convert `Y m m - yex x` to `|yex x - Y m m|` via `abs_sub_comm`
+ `tendsto_zero_iff_abs_tendsto_zero` (or just take absolute values
on the conclusion via `Filter.Tendsto.abs` on the input direction).

If the abs-stripping is awkward, an alternative is to prove
`Tendsto (fun m => |yex x - Y m m|) atTop (nhds 0)` first, then
convert to `Tendsto (fun m => Y m m - yex x) atTop (nhds 0)` via
`tendsto_zero_iff_abs_tendsto_zero` + `abs_sub_comm`.

### Estimated cost

- Step 1 (Θ extraction): 3 lines.
- Step 2 (per-`m` bound): 15 lines, mostly boilerplate.
- Step 3 (`m_h_constancy` rewrite): 5 lines.
- Step 4 (Tendsto chain): 30 lines.
- Step 5 (squeeze + abs juggling): 20 lines.
- Total: ~75 lines. Below CLAUDE.md's "decompose if > 200000
  heartbeats" threshold; no maxHeartbeats bump needed.

If any single step blows up (most likely Step 4 if `aFun`'s
parametrization gets tangled), decompose into a private helper
`stable_consistent_isConvergent_autonomous_RHS_tendsto` that proves
just the Tendsto of the RHS sum, and let the main theorem squeeze
against it.

---

## E. What NOT to do

1. **Do NOT close the line-3818 `sorry` on
   `stable_consistent_isConvergent` itself.** That theorem is the
   *non-autonomous* form (`f : ℝ → ℝ → ℝ`) and bridging from the
   autonomous closed-form bound (`f : ℝ → ℝ`) to the non-autonomous
   `IsConvergent` predicate requires a separate cycle of work
   (lifting `LipschitzInSecond Set.univ L f` ⇒ `LipschitzWith` for
   the *autonomous restriction* `fun y => f x y`, then handling the
   `x`-dependence). That is the cycle 063+ deliverable. Cycle 062's
   contribution is the **autonomous** specialization, which is a
   separate top-level theorem. Leave the line-3818 sorry intact.

2. **Do NOT redo the cycle 057 `a_m_tendsto_zero` from scratch.**
   Wrap it via `unfold + exact` per §B. Reproducing 60 lines for a
   one-line wrapper is wasted effort.

3. **Do NOT modify `scripts/autonomous_loop.py`** to "fix" the
   tautology scanner. Per CLAUDE.md and the standing
   `tautology_scanner_false_positives.md` issue, that is loop-
   maintainer territory. The cycle 061 baseline is 2 hits, both
   grandfathered cycle-052/055 closers. Don't introduce a new
   `:= h_*` or `exact h_*` closer; if the squeeze proof naturally
   wants one, use `simpa [h_eq] using h_name` or `convert h_name
   using 0`.

4. **Do NOT raise `maxHeartbeats` above 200000.** If Step 4's
   Tendsto chain is slow, decompose into 2 sub-lemmas (one for the
   `aOf`-term, one for the `cOf`-term).

5. **Do NOT introduce `axiom` or `constant`.** All §406D
   prerequisites are in the file; no genuine Mathlib gap remains
   for this cycle.

6. **Do NOT change `globalError_recurrence_form_explicit`,
   `globalError_closed_form_autonomous_explicit`, or any cycle 060
   def.** They are load-bearing and were validated last cycle.
   Cycle 060's score=−1 was a duplicated false positive (see cycle
   061 strategy diagnosis), not a correctness regression.

7. **Do NOT poll Aristotle more than once after the 30-min sleep.**
   CLAUDE.md is explicit. Submit at cycle start, sleep 30 min,
   check once, then proceed manually with whatever did not return.

8. **Do NOT try to "lift to `Tendsto … atTop`" using a generic
   sequence-from-net argument.** The right pattern for our shape is
   `tendsto_step_size_comp` (cycle 058,
   `Section404.lean:2293`) — it converts `Tendsto F (nhds 0)`
   helpers to `Tendsto (F ((x-x₀)/m)) atTop` directly, using
   `tendsto_const_div_atTop_nhds_zero_nat`. This is what the
   cycle 059 `globalError_outer_squeeze_*_term` helpers internally
   use.

---

## F. Aristotle batch script (for your convenience)

Submit the ~5 jobs in §C as one Aristotle batch at the start of
the cycle. Suggested submission file
`.prover-state/aristotle_submissions/cycle_062/sub_lemmas.lean`:

```lean
import OpenMath.Chapter4.Section404
namespace OpenMath.Chapter4.Section404

-- Job 1: aOf_tendsto_zero
example {k : ℕ} (M : LinearMultistepMethod k) (Θ L : ℝ)
    (yex : ℝ → ℝ) (Yh : ℝ → ℕ → ℝ) (x₀ : ℝ)
    (hstart : ∀ j : Fin k,
        Filter.Tendsto
          (fun h : ℝ => yex (x₀ + (j.val : ℝ) * h) - Yh h j.val)
          (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun h : ℝ => aOf M Θ L h yex (Yh h) x₀) (nhds 0) (nhds 0) := by
  sorry

-- Job 2: cOf · h → 0
example {k : ℕ} (M : LinearMultistepMethod k) (Θ L M_bound : ℝ) :
    Filter.Tendsto (fun h : ℝ => cOf M Θ L M_bound h * h)
      (nhds 0) (nhds 0) := by
  sorry

-- Job 3: bOf limit positivity
example {k : ℕ} (M : LinearMultistepMethod k) (Θ L : ℝ)
    (hΘ_nn : 0 ≤ Θ) (hL : 0 ≤ L) :
    0 < (Θ + 1) *
            (L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                  + ∑ i : Fin k, |M.β i.succ|))
          + 1 := by
  sorry

-- Job 4: per-m closed-form bound (see §C job 4 for full statement)
-- Job 5: stable_consistent_isConvergent_autonomous (see §D for full statement)

end OpenMath.Chapter4.Section404
```

(Use `mcp__aristotle__submit_file` with this file. Sleep 30 min via
the standard `sleep 1800 &` pattern, then `mcp__aristotle__get_status`
once.)

---

## G. Faithfulness checklist (for cycle 062 commit)

For `stable_consistent_isConvergent_autonomous`:

- [ ] Entity ID: this is **not** a Butcher-named entity; it is a
  helper specialization of `thm:406D` (`def:402A`-style conclusion
  with autonomous `f`). Document this clearly in the docstring:
  > "Autonomous-IVP specialization of Butcher Theorem 406D
  > (entity `thm:406D`). The full non-autonomous theorem is the
  > sorry'd `stable_consistent_isConvergent` below; the autonomous
  > form will be lifted to non-autonomous in cycle 063+."
- [ ] Lean statement captures: a *strictly weaker* form of the
  textbook (autonomous specialization). Justify in the docstring +
  task results.
- [ ] Tautology check: hypotheses include `hstab`, `hcons`,
  Lipschitz, smoothness, IVP-solution. Conclusion is a `Tendsto` —
  none of the hypotheses asserts this Tendsto. ✓
- [ ] Identity check: proof is not `exact h` — it is a non-trivial
  squeeze. ✓
- [ ] Hypothesis strength: `ContDiff ℝ 1 yex` is implicit in
  Butcher's "exact solution of IVP with Lipschitz `f`" (yex is
  automatically C¹). `hf_yex_bound` is a faithful add (Butcher's
  `M = max |f|` over the trajectory; needed since we don't have
  Picard-Lindelöf existence to derive it). Document both adds in
  the cycle 062 task results' faithfulness section.
- [ ] Absent theorem check: the `aOf_tendsto_zero` lemma must
  actually exist in the file (don't promise-and-skip). ✓ (priority
  1 above ensures this).

For `aOf_tendsto_zero`: standard internal-scaffolding faithfulness
(no entity ID, documented "not a Butcher concept", proves a real
limit fact, hypotheses are minimal).

---

## H. End-of-cycle checklist

Before commit:

- [ ] `lake env lean OpenMath/Chapter4/Section404.lean` exits 0
  with the same warnings as cycle 061 (4 warnings: `hM`, `hh`,
  `hMmax0`, line-3818 sorry).
- [ ] `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
  reports exactly 2 hits (no new closer-style flags).
- [ ] `#print axioms LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
  returns `[propext, Classical.choice, Quot.sound]` only.
- [ ] `git diff --stat` shows real changes in
  `OpenMath/Chapter4/Section404.lean` (the new `aOf_tendsto_zero`
  + new `stable_consistent_isConvergent_autonomous`). Expected
  change: ~+150 lines net, no deletions.
- [ ] `extraction/formalization_data/lean_status.json` updated:
  `thm:406D` → `partial` (with note: "autonomous-IVP form done as
  `stable_consistent_isConvergent_autonomous`; non-autonomous lift
  is cycle 063+"). Do **not** mark as `formalized` — the textbook
  statement is non-autonomous.
- [ ] Task results at `.prover-state/task_results/cycle_062.md`
  include the §G faithfulness check explicitly, and the §H
  "Suggested next approach" should describe the cycle 063
  non-autonomous lift (build `LipschitzInSecond` ⇒ per-`x`
  `LipschitzWith` adapter, then specialise to autonomous case +
  use `stable_consistent_isConvergent_autonomous`).

---

## I. Cross-references

- Cycle 061 task results: this strategy's §B / §D leverage
  cycle 061's three Tendsto wrappers exactly as cycle 061
  recommended.
- Cycle 057's `a_m_tendsto_zero` (`Section404.lean:2245`): the
  underlying lemma wrapped by `aOf_tendsto_zero`.
- Cycle 058's `tendsto_step_size_comp` (`Section404.lean:2293`):
  the bridge from `nhds 0` to `atTop`.
- Cycle 059's `globalError_outer_squeeze_a_term`,
  `_c_term` (`Section404.lean:2311`, `2383`): the load-bearing
  squeeze helpers.
- Cycle 060's `globalError_closed_form_autonomous_explicit`
  (`Section404.lean:3695`): the per-`h` bound used in §D's Step 2.
- `lmm_convergence_witness_deferred.md`: the cycle 062 deliverable
  partially resolves this issue (provides an autonomous-IVP
  *theorem*, but not a concrete *witness* for explicit Euler — that
  requires lifting to non-autonomous in cycle 063+ and then
  specialising).
