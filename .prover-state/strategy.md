# Cycle 059 Strategy — `thm:406D` outer assembly: prove the two sub-squeezes

## TL;DR

Cycle 058 landed every Tendsto helper the squeeze needs (5 Aristotle
generic combinators + 2 `atTop` bridge lemmas). The single remaining
sorry is at `OpenMath/Chapter4/Section404.lean:3030`
(`stable_consistent_isConvergent`).

The cycle 058 strategy preview suggested cycle 059 attempt the *full*
`globalError_outer_squeeze_autonomous` (~80–120 lines). That is too
much for one cycle's CLAUDE.md "structure + 2 sub-lemmas closed"
envelope. **Decompose instead**: prove the two **sub-squeezes** that
the eventual outer squeeze will combine via `add` plus `squeeze_zero`.
Each sub-squeeze is a self-contained Tendsto fact about one half of
the closed-form bound RHS — they are decoupled from any LMM-specific
data, so they can be unit-tested in isolation.

This cycle's deliverables are **two new private lemmas** plus the
existing scaffolding to keep the file compiling. The single sorry at
line 3030 is **not touched**.

---

## Recap of what landed in cycle 058

* Lines ≈2185–2226: the five Aristotle-closed Tendsto combinators
  (`tendsto_id_squared_zero`, `tendsto_const_mul_h_zero`,
  `tendsto_real_exp_lift`, `tendsto_exp_sub_one_at_zero_aux`,
  `tendsto_div_at_pos`).
* Lines ≈2274–2299: the two `atTop` bridge lemmas
  (`tendsto_step_size_atTop`, `tendsto_step_size_comp`).
* Single sorry at line 3030 (the body of `stable_consistent_isConvergent`).

The cycle 056/057 helpers (`b_tendsto_at_zero`, `c_tendsto_at_zero`,
`Cbase_tendsto_at_zero`, `Dbase_tendsto_at_zero`,
`m_h_constancy`, `c_h_h_squared_tendsto_zero`, `a_m_tendsto_zero`,
`yPrime_sum_abs_tendsto_zero`, `tendsto_h_squared_zero`,
`tendsto_real_exp_at`) are all in place (lines 2050–2272) and
already tested via the cycle 057/058 builds.

---

## Priority 1 (PRIMARY DELIVERABLE): the `a`-term sub-squeeze

### What it says, mathematically

The closed-form bound is

```
|ε(n)| ≤ exp(b(h) · k · n · h) · a(h) + (exp(b(h) · k · n · h) − 1) · c(h) · h / (b(h) · k).
```

When the squeeze substitutes `h = h_m := (x − x₀)/m` and `n = m`:

* `m · h_m = x − x₀` (constant in `m` — `m_h_constancy`).
* So `b(h_m) · k · m · h_m = b(h_m) · k · (x − x₀)`.

The `a`-half of the RHS is `exp(b(h_m) · k · (x − x₀)) · a(h_m)`. We
want this to tend to 0 as `m → ∞`.

Inputs needed:
* `a(h) → 0` as `h → 0` (provided by `a_m_tendsto_zero` for the
  LMM-specific `a`, but the sub-squeeze takes a generic `a`).
* `b(h) → b∞` as `h → 0` (any finite limit; positivity not needed
  here).

Output: `exp(...) → exp(b∞ · k · (x−x₀))` is a finite constant, and
multiplying by something that tends to 0 gives 0.

### Lemma to prove

Insert after `tendsto_step_size_comp` (current line ≈2299) — at the
end of the "§141 Tendsto helpers" block, *before* the
`recentSum_swap_bound` adapter (line ≈2301).

```lean
/-- **`a`-term outer squeeze (cycle 059, toward `thm:406D`).**

The first half of the closed-form bound RHS:
`exp(b(h_m) · k · m · h_m) · a(h_m)` where `h_m := (x − x₀)/m`.

Since `m · h_m = x − x₀` (constant), the exponent stabilises to
`b(h_m) · k · (x − x₀)`, which tends to `b∞ · k · (x − x₀)` (a
finite limit). Combined with `a(h_m) → 0`, the product tends to
`exp(…) · 0 = 0`.

Generic in `a, b` — does **not** consume any LMM data. -/
private lemma globalError_outer_squeeze_a_term
    {a b : ℝ → ℝ} {b∞ : ℝ}
    (ha : Filter.Tendsto a (nhds 0) (nhds 0))
    (hb : Filter.Tendsto b (nhds 0) (nhds b∞))
    (k : ℕ) (x₀ x : ℝ) :
    Filter.Tendsto
      (fun m : ℕ =>
        Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (m : ℝ)
                    * ((x - x₀) / (m : ℝ)))
          * a ((x - x₀) / (m : ℝ)))
      Filter.atTop (nhds 0) := by
  sorry
```

### Proof recipe (do follow this — it's been worked out)

Step A — establish the `m · h_m = x − x₀` rewrite eventually
(only valid for `m ≥ 1`).

```lean
  -- For m ≥ 1, m · h_m = x − x₀ (m_h_constancy).
  have h_eventually_eq :
      (fun m : ℕ =>
        Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (m : ℝ)
                    * ((x - x₀) / (m : ℝ)))
          * a ((x - x₀) / (m : ℝ)))
      =ᶠ[Filter.atTop]
      (fun m : ℕ =>
        Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀))
          * a ((x - x₀) / (m : ℝ))) := by
    refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro m hm
    have hm_pos : 0 < m := hm
    have hm_h : (m : ℝ) * ((x - x₀) / (m : ℝ)) = x - x₀ :=
      m_h_constancy hm_pos x x₀
    have h_assoc :
        b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (m : ℝ)
          * ((x - x₀) / (m : ℝ))
        = b ((x - x₀) / (m : ℝ)) * (k : ℝ)
          * ((m : ℝ) * ((x - x₀) / (m : ℝ))) := by ring
    rw [h_assoc, hm_h]
```

Step B — the simplified function `g_m := exp(b(h_m) · k · (x − x₀)) · a(h_m)`
is the product of two Tendsto-quantities at `atTop`.

```lean
  -- Lift `a → 0` to atTop via h_m.
  have ha_atTop :
      Filter.Tendsto (fun m : ℕ => a ((x - x₀) / (m : ℝ)))
        Filter.atTop (nhds 0) := tendsto_step_size_comp ha x₀ x
  -- Lift `b · k · (x - x₀)` from h-Tendsto to m-Tendsto.
  have hbk_atTop :
      Filter.Tendsto (fun m : ℕ => b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀))
        Filter.atTop (nhds (b∞ * (k : ℝ) * (x - x₀))) := by
    have hb_atTop := tendsto_step_size_comp hb x₀ x
    have h1 := hb_atTop.mul_const ((k : ℝ))
    exact h1.mul_const (x - x₀)
  -- exp lift.
  have hexp_atTop :
      Filter.Tendsto
        (fun m : ℕ =>
          Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀)))
        Filter.atTop (nhds (Real.exp (b∞ * (k : ℝ) * (x - x₀)))) :=
    (Real.continuous_exp.tendsto _).comp hbk_atTop
  -- Product: exp(…) · a(h_m) → exp(…) · 0 = 0.
  have h_prod : Filter.Tendsto
      (fun m : ℕ =>
        Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀))
          * a ((x - x₀) / (m : ℝ)))
      Filter.atTop (nhds 0) := by
    have := hexp_atTop.mul ha_atTop
    simpa using this
  -- Lift via the eventually-equal congruence.
  exact h_prod.congr' h_eventually_eq.symm
```

The whole proof is ~25–35 lines once tightened.

### Acceptable variations

* `Filter.Tendsto.congr'` may be spelled `EventuallyEq.tendsto_iff` —
  use whichever your `lean_local_search` finds. The shape is the same.
* `mul_const` chains can be replaced by a single `Tendsto.mul`
  composition; either is fine as long as the result type matches.
* If the `simpa using hexp_atTop.mul ha_atTop` fails (because
  `0` isn't simplified automatically), fall back to:
  ```lean
  have hzero : Real.exp (b∞ * (k : ℝ) * (x - x₀)) * 0 = 0 := mul_zero _
  rw [← hzero]; exact hexp_atTop.mul ha_atTop
  ```

---

## Priority 2 (PRIMARY DELIVERABLE): the `c`-term sub-squeeze

### What it says, mathematically

The `c`-half of the RHS is
`(exp(b(h_m) · k · m · h_m) − 1) · c(h_m) · h_m / (b(h_m) · k)`.

After the same `m · h_m = x − x₀` simplification, the exponential
factor `(exp(b(h_m) · k · (x − x₀)) − 1)` tends to a finite constant
`exp(b∞ · k · (x − x₀)) − 1`. The remaining factor
`c(h_m) · h_m / (b(h_m) · k)` tends to `c∞ · 0 / (b∞ · k) = 0` (with
`b∞ · k > 0` ensuring the division is fine).

Inputs needed:
* `c(h) → c∞` as `h → 0` (any finite limit).
* `b(h) → b∞` as `h → 0`, **with `0 < b∞` and `0 < k`** (so the
  divisor is non-zero in the limit).

### Lemma to prove

Insert immediately after `globalError_outer_squeeze_a_term`.

```lean
/-- **`c`-term outer squeeze (cycle 059, toward `thm:406D`).**

The second half of the closed-form bound RHS:
`(exp(b(h_m) · k · m · h_m) − 1) · c(h_m) · h_m / (b(h_m) · k)`
where `h_m := (x − x₀)/m`. Since `m · h_m = x − x₀`, the
`(exp(…) − 1)` factor stabilises to a finite constant, and the
remaining `c(h_m) · h_m / (b(h_m) · k)` tends to `c∞ · 0 / (b∞ · k)
= 0`.

Generic in `b, c` — does **not** consume any LMM data. -/
private lemma globalError_outer_squeeze_c_term
    {b c : ℝ → ℝ} {b∞ c∞ : ℝ}
    (hb : Filter.Tendsto b (nhds 0) (nhds b∞))
    (hc : Filter.Tendsto c (nhds 0) (nhds c∞))
    (hb_pos : 0 < b∞)
    {k : ℕ} (hk : 0 < k) (x₀ x : ℝ) :
    Filter.Tendsto
      (fun m : ℕ =>
        (Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (m : ℝ)
                    * ((x - x₀) / (m : ℝ))) - 1)
          * (c ((x - x₀) / (m : ℝ)) * ((x - x₀) / (m : ℝ))
              / (b ((x - x₀) / (m : ℝ)) * (k : ℝ))))
      Filter.atTop (nhds 0) := by
  sorry
```

### Proof recipe

Step A — eventually rewrite `m · h_m → x − x₀` inside the exponent.
Identical structure to Priority 1's Step A.

Step B — split the product into `(exp(…) − 1)` × `(c · h / (b · k))`.

Step C — show each factor's behaviour:
* `(exp(b · k · (x − x₀)) − 1)` tends to `exp(b∞ · k · (x − x₀)) − 1`
  (a finite constant). Lift via `tendsto_step_size_comp` plus
  `tendsto_real_exp_lift` plus `Tendsto.sub_const`.
* `c(h_m) → c∞` (lifted via `tendsto_step_size_comp`).
* `h_m → 0` (lifted via `tendsto_step_size_atTop`).
* `b(h_m) · k → b∞ · k > 0` (lifted via `tendsto_step_size_comp` plus
  `mul_const`).
* So `c(h_m) · h_m → c∞ · 0 = 0` by `Tendsto.mul`.
* So `c(h_m) · h_m / (b(h_m) · k) → 0` by `Tendsto.div` (using
  `b∞ · k > 0`).

Step D — multiply: `(exp(…) − 1) · 0 = 0`. Use `Tendsto.mul` and
`simpa`.

### Sketch (template — refine to taste)

```lean
  -- Step A: eventually-equal rewrite for the exponent.
  have h_eventually_eq : ... =ᶠ[Filter.atTop]
      (fun m : ℕ =>
        (Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀)) - 1)
          * (c ((x - x₀) / (m : ℝ)) * ((x - x₀) / (m : ℝ))
              / (b ((x - x₀) / (m : ℝ)) * (k : ℝ)))) := by
    refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro m hm
    have hm_pos : 0 < m := hm
    have hm_h : (m : ℝ) * ((x - x₀) / (m : ℝ)) = x - x₀ :=
      m_h_constancy hm_pos x x₀
    have h_assoc :
        b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (m : ℝ)
          * ((x - x₀) / (m : ℝ))
        = b ((x - x₀) / (m : ℝ)) * (k : ℝ)
          * ((m : ℝ) * ((x - x₀) / (m : ℝ))) := by ring
    rw [h_assoc, hm_h]
  -- Step B: factor lift via tendsto_step_size_comp.
  have hb_atTop :
      Filter.Tendsto (fun m : ℕ => b ((x - x₀) / (m : ℝ)))
        Filter.atTop (nhds b∞) := tendsto_step_size_comp hb x₀ x
  have hc_atTop :
      Filter.Tendsto (fun m : ℕ => c ((x - x₀) / (m : ℝ)))
        Filter.atTop (nhds c∞) := tendsto_step_size_comp hc x₀ x
  have hh_atTop :
      Filter.Tendsto (fun m : ℕ => (x - x₀) / (m : ℝ))
        Filter.atTop (nhds 0) := tendsto_step_size_atTop x₀ x
  -- exp − 1 factor.
  have hbk_atTop :
      Filter.Tendsto (fun m : ℕ => b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀))
        Filter.atTop (nhds (b∞ * (k : ℝ) * (x - x₀))) :=
    (hb_atTop.mul_const ((k : ℝ))).mul_const (x - x₀)
  have hexpsub :
      Filter.Tendsto
        (fun m : ℕ =>
          Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀)) - 1)
        Filter.atTop
        (nhds (Real.exp (b∞ * (k : ℝ) * (x - x₀)) - 1)) := by
    have hexp_at := (Real.continuous_exp.tendsto _).comp hbk_atTop
    exact hexp_at.sub_const 1
  -- c · h → 0 (since c bounded, h → 0).
  have hch :
      Filter.Tendsto (fun m : ℕ => c ((x - x₀) / (m : ℝ))
                                    * ((x - x₀) / (m : ℝ)))
        Filter.atTop (nhds 0) := by
    have := hc_atTop.mul hh_atTop
    simpa using this
  -- b · k → b∞ · k (and b∞ · k > 0).
  have hbk_lim :
      Filter.Tendsto (fun m : ℕ => b ((x - x₀) / (m : ℝ)) * (k : ℝ))
        Filter.atTop (nhds (b∞ * (k : ℝ))) := hb_atTop.mul_const _
  have hbk_pos : 0 < b∞ * (k : ℝ) := by
    have hk_pos_real : 0 < (k : ℝ) := by exact_mod_cast hk
    exact mul_pos hb_pos hk_pos_real
  -- (c · h) / (b · k) → 0.
  have hquot :
      Filter.Tendsto (fun m : ℕ => c ((x - x₀) / (m : ℝ))
                                    * ((x - x₀) / (m : ℝ))
                                    / (b ((x - x₀) / (m : ℝ)) * (k : ℝ)))
        Filter.atTop (nhds 0) := by
    have := hch.div hbk_lim hbk_pos.ne'
    simpa using this
  -- Combined: (exp − 1) · (c · h / (b · k)) → finite · 0 = 0.
  have h_prod :
      Filter.Tendsto
        (fun m : ℕ =>
          (Real.exp (b ((x - x₀) / (m : ℝ)) * (k : ℝ) * (x - x₀)) - 1)
            * (c ((x - x₀) / (m : ℝ)) * ((x - x₀) / (m : ℝ))
                / (b ((x - x₀) / (m : ℝ)) * (k : ℝ))))
        Filter.atTop (nhds 0) := by
    have := hexpsub.mul hquot
    simpa using this
  exact h_prod.congr' h_eventually_eq.symm
```

### Faithfulness flag

Both sub-squeezes are **purely analytical Tendsto facts** — no LMM
data, no Butcher entity references. They are private infrastructure
lemmas. The CLAUDE.md per-`def` faithfulness checklist does not
apply (no new `def`/`structure`/`class`).

---

## Priority 3 (NOT THIS CYCLE): the outer-squeeze assembly

**Do NOT attempt assembling `globalError_outer_squeeze_autonomous`
this cycle.** The two sub-squeezes above are sufficient for one
cycle's CLAUDE.md envelope. Cycle 060 will combine them via
`Tendsto.add` plus `squeeze_zero`. The expected cycle 060 shape:

```lean
private theorem globalError_outer_squeeze_autonomous
    ... :
    Filter.Tendsto (fun m : ℕ => Y m m - yex x) Filter.atTop (nhds 0) := by
  -- Apply globalError_closed_form_autonomous with h = h_m to get the
  -- pointwise bound for each m large enough that h_m * L * |β 0| < 1.
  -- The bound's RHS is exp(b·k·m·h)·a + (exp(b·k·m·h)−1)·c·h/(b·k).
  -- That RHS = (a-term) + (c-term), both → 0 by the cycle 059 sub-squeezes.
  -- So the bound → 0 by Tendsto.add. Then squeeze_zero.
  sorry
```

The assembly will need to thread the existential `(a, b, c)` from
`globalError_closed_form_autonomous` through. This is mechanical
once the two sub-squeezes are in place, but it is the right size
for its own cycle.

---

## Verification checklist (before commit)

1. `lake env lean OpenMath/Chapter4/Section404.lean` succeeds with
   exactly **one** sorry (at line ≈3050–3080, the body of
   `stable_consistent_isConvergent` — the line shifts by however many
   lines the two new sub-squeezes add, expected ~70–100 lines total).
2. `#print axioms OpenMath.Chapter4.Section404.globalError_outer_squeeze_a_term`
   reports `[propext, Classical.choice, Quot.sound]` only.
3. `#print axioms OpenMath.Chapter4.Section404.globalError_outer_squeeze_c_term`
   reports `[propext, Classical.choice, Quot.sound]` only.
4. **Tautology scanner** returns no **new** hits beyond the two
   pre-existing ones at lines ≈1950, 2595. The sub-squeeze proofs
   end in `exact h_prod.congr' h_eventually_eq.symm` — `h_prod` is
   underscore-named, so the regex `:=\s*h_\w+\s*$` / `\bexact\s+h_\w+\s*$`
   *will* match. **Rename** `h_prod → hprod` (drop underscore) before
   commit, per the standing
   `tautology_scanner_false_positives.md` convention. Same for any
   other `h_<name>` final-line closer in the proof. Cosmetic
   workaround; do **not** modify the scanner from worker side.
   Run `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
   before commit; expected ≤ 2 hits, both at pre-existing lines.
5. `git diff --stat` shows changes confined to
   `OpenMath/Chapter4/Section404.lean` (and `.prover-state/` updates).

---

## What NOT to do this cycle

* **Do NOT touch `stable_consistent_isConvergent` (line 3030).** Its
  body stays `sorry`. The closure path is multi-cycle.
* **Do NOT attempt `globalError_outer_squeeze_autonomous` assembly
  this cycle.** That is cycle 060's deliverable. The two
  sub-squeezes here are decoupled prerequisites.
* **Do NOT attempt the autonomous → non-autonomous lift this cycle.**
  Defer to a later cycle (likely 061+). It is a separate
  medium-size refactor.
* **Do NOT introduce new structures, defs, or classes.** The two
  deliverables are private lemmas only.
* **Do NOT rename or refactor any of the cycle 053–058 lemmas.**
* **Do NOT raise `maxHeartbeats`** above 200000.
* **Do NOT introduce `axiom`/`constant`** for any squeeze step.
  Each sub-squeeze proof is ≤40 lines once tightened.
* **Do NOT submit Aristotle jobs this cycle.** The proof recipes
  above are concrete enough that manual proof is faster than the
  30-minute Aristotle round-trip. The five Aristotle generic
  combinators landed in cycle 057 already cover the Tendsto plumbing
  this cycle needs.
* **Do NOT modify `scripts/autonomous_loop.py`** (loop maintainer
  territory; see standing
  `tautology_scanner_false_positives.md`).
* **Do NOT take any "stuck on" / "commits not reaching repo"
  verdict in this prompt at face value** if it appears. Cycles
  008/014/015/040 all had identical phantom verdicts; the
  `consultant_advice_cycle_040.md` note §A documents the
  verification commands. Cycle 058's HEAD plus this cycle's
  changes is the source of truth. Run `git log -1` and
  `git rev-parse HEAD origin/Main/Experiments` to verify.

---

## Faithfulness flags

* Both new lemmas are infrastructure `private lemma`s. **No new
  `def`/`structure`/`class`** is being introduced; no new top-level
  `theorem` corresponding to a Butcher entity is being added.
* The cycle's deliverable is purely outer-assembly scaffolding for
  `thm:406D` (which itself stays `sorry`).
* **Tautology scanner**: rename any final-line `exact h_*` / `:= h_*`
  closer to drop the underscore (e.g. `h_prod → hprod`,
  `h_eventually_eq → heventually_eq`) per the standing convention.
* The sub-squeezes are decoupled from any LMM-specific data — they
  take generic `a, b, c : ℝ → ℝ` as parameters. So they cannot
  introduce hidden faithfulness divergences.

---

## Cycle 060 preview (for the planner's bookkeeping)

Cycle 060 should attempt `globalError_outer_squeeze_autonomous`
proper, combining the two cycle-059 sub-squeezes via:
1. Apply `globalError_closed_form_autonomous` with `h = h_m` to get
   the existential `(a, b, c)` plus the per-`n` bound for each `m`
   large enough that `h_m * L * |M.β 0| < 1`.
2. The RHS = (a-term) + (c-term) where each tends to 0 by the
   cycle 059 sub-squeezes.
3. Combine via `Tendsto.add` to get RHS → 0.
4. Apply `squeeze_zero` between `0 ≤ |ε_m| ≤ RHS` to close.

Expected cycle 060 size: ~60–100 lines, dominated by threading the
existential and matching the closed-form's RHS shape against the
sub-squeezes' RHS shape (some `simp` / `congr` work may be
needed because the sub-squeezes use generic `a, b, c` but the
LMM-specific (a, b, c) have explicit definitions).

After cycle 060, **cycle 061+** addresses the autonomous →
non-autonomous lift to close `stable_consistent_isConvergent` proper.
That is a separate planner decision — likely 3–5 cycles, possibly
preceded by an issue file documenting the gap and the lift recipe.

---

## Cross-references

* `OpenMath/Chapter4/Section404.lean:2107–2299` — cycles 056/057/058
  Tendsto helpers (the seven `Tendsto` lemmas this cycle composes).
* `OpenMath/Chapter4/Section404.lean:2280` —
  `tendsto_step_size_atTop` (the `1/m → 0` bridge).
* `OpenMath/Chapter4/Section404.lean:2293` —
  `tendsto_step_size_comp` (the generic `nhds 0` → `atTop` lift).
* `OpenMath/Chapter4/Section404.lean:2977` —
  `globalError_closed_form_autonomous` (the analytical core; cycle
  053). The two sub-squeezes match its RHS shape precisely.
* `OpenMath/Chapter4/Section404.lean:2159` — `m_h_constancy`
  (the `m · h_m = x − x₀` rewrite).
* `OpenMath/Chapter4/Section404.lean:305` — `IsConvergent` definition
  (the eventual squeeze target shape).
* `.prover-state/issues/tautology_scanner_false_positives.md` —
  scanner-rename convention.
* `.prover-state/issues/consultant_advice_cycle_040.md` §A —
  phantom verdict diagnosis (verification commands).
* `.prover-state/task_results/cycle_058.md` (if present) —
  cycle 058 deliverable record.
