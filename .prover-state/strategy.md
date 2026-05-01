# Cycle 057 Strategy — More outer-assembly Tendsto helpers + Aristotle batch for the squeeze

**Active target**: `thm:406D` —
`LinearMultistepMethod.stable_consistent_isConvergent`
(`OpenMath/Chapter4/Section404.lean:2878`, body `sorry` at line 2882).

**Phase**: outer-assembly helper construction (continued). Cycle 056
landed seven Tendsto helpers cleanly, ending with the lifts
`b_tendsto_at_zero` (line 2114) and `c_tendsto_at_zero` (line 2138).
Cycle 057 builds the next layer toward the squeeze. **DO NOT close
the main `sorry` at line 2882 this cycle** — there is still missing
infrastructure between the autonomous closed-form bound
`globalError_closed_form_autonomous` (line 2829) and the
non-autonomous `IsConvergent` predicate (line 305), and the squeeze
itself has not been scaffolded yet.

**No Aristotle results pending.** No Priority 0 integration step.

---

## Priority 1 (mandatory) — Two cheap Tendsto helpers

Insert both as `private lemma` immediately after `c_tendsto_at_zero`
(after line 2151 of `OpenMath/Chapter4/Section404.lean`), so the
"§406D outer-assembly Tendsto helpers" cluster grows contiguously.
Match the existing comment header style; add a short `/-- … -/`
docstring on each.

### 1.1 `m_h_constancy` — `(m : ℝ) · ((x − x₀)/m) = x − x₀` for `m > 0`

Pure algebra. Used by the squeeze: when the worker substitutes
`h := (x − x₀)/m` and `n := m` into the closed-form bound, the
quantity `n · h = m · h_m` collapses to the constant `x − x₀`. This
is what makes the exponent `b · k · n · h` bounded as `m → ∞`.

```lean
private lemma m_h_constancy
    {m : ℕ} (hm : 0 < m) (x x₀ : ℝ) :
    ((m : ℝ)) * ((x - x₀) / (m : ℝ)) = x - x₀ := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
```

**If `field_simp` alone leaves a residue**, fall back to
`rw [mul_div_assoc, mul_div_cancel_left₀ _ hm_ne]` or
`mul_comm (m : ℝ) _; rw [div_mul_cancel₀ _ hm_ne]`.

### 1.2 `c_h_h_squared_tendsto_zero` — cycle-056 stretch goal

Combine `c_tendsto_at_zero` (line 2138) with `tendsto_h_squared_zero`
(line 2081) via `Tendsto.mul`. The product goes to `c∞ · 0 = 0`.

```lean
private lemma c_h_h_squared_tendsto_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L M_bound : ℝ) :
    Filter.Tendsto
      (fun h : ℝ =>
        ((Θ + 1) *
          (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
              + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
            * L * M_bound / (1 - h * L * |M.β 0|))) * h ^ 2)
      (nhds 0) (nhds 0) := by
  have hc := c_tendsto_at_zero M Θ L M_bound
  have hh2 := tendsto_h_squared_zero
  have hmul := hc.mul hh2
  simpa using hmul
```

`simpa` reduces the `c∞ · 0` product on the limit side to `0`. If it
does not, replace with an explicit `convert hmul using 1; ring` (or
`mul_zero`).

---

## Priority 2 — `a_m_tendsto_zero`: the `a` constant tends to zero

This is the single most important new helper for the squeeze. The
linear-recurrence form `globalError_recurrence_form` (line 2379)
produces `a = (Θ + (Θ + 1) · Cbase · h · k + 1) · y'sum`. As `h → 0`:

* `Cbase` tends to `Cbase∞` (finite, by `Cbase_tendsto_at_zero`),
* `Cbase · h · k` tends to `0`,
* `y'sum` tends to `0` (this is the *parametric* premise — the
  starting method is required to converge, so each
  `yex(x₀ + j·h) - start h j → 0` as `h → 0`).

Therefore `a → (Θ + 0 + 1) · 0 = 0`.

### Statement (target signature)

```lean
private lemma a_m_tendsto_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L : ℝ)
    {u : ℝ → Fin k → ℝ}
    (hu : ∀ j : Fin k,
      Filter.Tendsto (fun h : ℝ => u h j) (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun h : ℝ =>
        (Θ + (Θ + 1) *
              (L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                    + ∑ i : Fin k, |M.β i.succ|)
                / (1 - h * L * |M.β 0|))
            * h * (k : ℝ) + 1)
        * (∑ i ∈ Finset.range k,
            |OpenMath.Chapter1.Section141.yPrime k
              (fun j : Fin k => M.α j.succ) (u h) i|))
      (nhds 0) (nhds 0) := by
  …
```

(Adjust the `OpenMath.Chapter1.Section141.yPrime` qualifier to match
whatever is already `open`ed at the helper's insertion point — see
`yPrime_sum_abs_tendsto_zero` at line 1886 for the convention.)

### Approach

1. Set `bracket : ℝ → ℝ := fun h => Θ + (Θ + 1) · Cbase_h · h · k + 1`.
2. Show `Tendsto bracket (nhds 0) (nhds (Θ + 1))` by chaining
   `Cbase_tendsto_at_zero` through `.const_mul (Θ + 1)`,
   `.mul tendsto_id`, `.mul_const (k : ℝ)`, `.const_add Θ`,
   `.add_const 1`. The intermediate "× h" multiplication kills the
   `Cbase`-dependent term: `bracket h → Θ + (Θ + 1) · Cbase∞ · 0 · k + 1
   = Θ + 1`.
3. Set `tail : ℝ → ℝ := fun h => Σ_{i ∈ range k} |yPrime k α (u h) i|`.
4. Apply `yPrime_sum_abs_tendsto_zero` (line 1886) to `hu` to get
   `Tendsto tail (nhds 0) (nhds 0)`.
5. Combine via `Tendsto.mul`: `bracket h · tail h → (Θ + 1) · 0 = 0`.

If step 2 is finicky, decompose into smaller `set N := …` blocks and
prove tendsto piece-by-piece using `Cbase_tendsto_at_zero`,
`Filter.tendsto_id`, `tendsto_const_nhds`, and the standard
`.add` / `.mul` / `.const_mul` / `.add_const` combinators. The
template at lines 1992–2008 (proof of `Cbase_tendsto_at_zero`) is the
canonical model.

### What NOT to do

* Do **NOT** open the definition of `globalError_recurrence_form` or
  try to thread the `a` produced by the existential. We are proving
  a parametric Tendsto fact about the **shape** that
  `globalError_recurrence_form` outputs — the squeeze itself, in a
  later cycle, is what threads the existential. Keep this lemma as
  pure analytic combinator content: `a = bracket(h) · tail(h)`.
* Do **NOT** introduce a hypothesis on `Cbase∞ ≠ 0` or
  `M.IsStable`. The Tendsto fact holds at every `M`; the squeeze
  step in a later cycle will provide the stability hypothesis when
  it instantiates `Θ` via `theta_bounded_of_isStable`.

---

## Priority 3 — Aristotle batch of 5 helpers (submit in parallel)

Submit before starting Priority 2 (so Aristotle has compute-time
overlap with the manual proof of P2). One project per submission;
each prompt should include the relevant Mathlib lemma names as
hints based on the cycle 056 discoveries (`Tendsto.const_mul`,
`Tendsto.add_const`, `Tendsto.mul`, `Real.continuous_exp.tendsto`,
`Filter.tendsto_id`).

Place all five into `.prover-state/aristotle_submissions/cycle_057/`
as standalone `.lean` files (one per helper). Use
`.prover-state/aristotle_submissions/cycle_055/` and
`.prover-state/aristotle_submissions/cycle_040/` as templates.
Each file should `import` only what is needed (typically
`Mathlib.Analysis.SpecificLimits.Basic`,
`Mathlib.Analysis.SpecialFunctions.Exp`, and
`Mathlib.Topology.Algebra.Order.Field` are sufficient — do NOT
`import` `OpenMath.Chapter4.Section404` because that drags the whole
project compile time into the submission and may push Aristotle
toward unrelated premises).

After submission, **sleep 30 minutes**, then check status with
`mcp__aristotle__get_status` **once**. CLAUDE.md is explicit on this.
Do not poll repeatedly.

### Submissions (each ≤ ~30 lines, all parametric / generic)

**3.1 `tendsto_id_squared_zero`** (decoupled flavour of P1.2):
generic `(fun h : ℝ => f(h) · h^2) → 0` when `f → c` for some
finite `c`. (The cycle 057 P1.2 hard-codes the `c_h` shape; this
generic version is reusable for `b · h^2`, `Cbase · h^2`, etc.)

**3.2 `tendsto_const_mul_h_zero`**: if `f h → c` then
`(fun h => f h · h) → 0`. Pure `Tendsto.mul tendsto_id`.

**3.3 `tendsto_real_exp_lift`**: if `Tendsto g (nhds 0) (nhds c)`,
then `Tendsto (Real.exp ∘ g) (nhds 0) (nhds (Real.exp c))`. One
line via `(tendsto_real_exp_at c).comp hg` (or
`Real.continuous_exp.continuousAt.tendsto.comp`).

**3.4 `tendsto_const_sub_one_div`**: `(fun h => (Real.exp (k h) - 1) /
k h) → 1` when `k h → c` with `c ≠ 0`. NOT NEEDED YET — replace with:
`tendsto_exp_sub_one_at_zero_aux`: if `Tendsto p (nhds 0) (nhds 0)`
then `Tendsto (fun h => (Real.exp (p h) - 1)) (nhds 0) (nhds 0)`.
This is the simpler shape we need for the squeeze.

**3.5 `tendsto_div_at_pos`**: if `Tendsto f (nhds 0) (nhds 0)` and
`Tendsto g (nhds 0) (nhds c)` with `c > 0`, then
`Tendsto (fun h => f h / g h) (nhds 0) (nhds 0)`. Standard
`Tendsto.div_const`-flavoured fact via `Tendsto.div`. Used to bound
`c · h / (b · k)` in the squeeze.

These five have a high Aristotle-success-rate profile (small
goals, canonical Mathlib premises, no domain-specific data).

---

## Out of scope (cycle 057 ceiling)

* The `globalError_outer_squeeze` lemma itself (the cycle 056
  task-results "step 5"). This needs P1.1, P1.2, P2 *and* the
  Aristotle batch results, plus a non-trivial weaving step. Defer
  to cycle 058+.
* Closing line 2882 (`stable_consistent_isConvergent`). Same reason.
* Rewriting `globalError_closed_form_autonomous` to a non-autonomous
  form. The autonomous → non-autonomous lift is a separate (large)
  refactor; a dedicated cycle plus an issue file is the right
  resolution. Do **not** start it inline this cycle.
* Touching `globalError_recurrence_form` (line 2379), the
  closed-form bound (line 2829), or any of the `discrete_gronwall_*`
  / `theta_*` infrastructure. All are stable and consumed downstream;
  edits risk regressions.

---

## Pre-commit checklist (CLAUDE.md §"Pre-Commit Faithfulness Checklist")

The cycle 057 deliverables are *infrastructure* `private lemma`s in
`OpenMath/Chapter4/Section404.lean`, not Butcher-named entities.
Faithfulness obligations are minimal:

* No new `def`s, `class`es, or `structure`s — skip those sections.
* For each new `private lemma`:
  * Tautology check: confirm the conclusion is not verbatim a
    hypothesis. (P1.1 and P1.2 are pure analytic combinator facts;
    P2 chains two existing Tendsto lemmas through `.mul`. None
    should fire the tautology scanner.)
  * Run `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
    after the edits — expect zero hits.
  * Hypothesis-strength check: P2 takes `hu : ∀ j, Tendsto … 0`,
    which is the minimal premise that makes `yPrime_sum_abs_tendsto_zero`
    apply. No `M.IsStable` or `M.IsConsistent` should creep in.

After build:

```bash
lake env lean OpenMath/Chapter4/Section404.lean
lake build OpenMath.Chapter4.Section404
```

(Both should pass with no new sorry's introduced; the line-2882
`stable_consistent_isConvergent` `sorry` is the only one expected.)

Then commit with message
`Cycle 057 — outer-assembly Tendsto helpers (m_h_constancy, c_h_h², a_m → 0)`
(adjust based on what actually landed; if Aristotle returned closed
proofs and you also integrated those, mention them).

---

## What NOT to try this cycle (re-state for the worker)

Failed-approach summary distilled from `attempts.md` and the recent
consultant notes:

1. **DO NOT close `stable_consistent_isConvergent` (line 2882)
   directly.** The squeeze infrastructure is incomplete; closing
   prematurely will either fail or require a giant monolithic proof
   that exceeds `maxHeartbeats`. Build helpers, then weave.
2. **DO NOT raise `maxHeartbeats` above 200000.** CLAUDE.md is
   explicit; decompose instead.
3. **DO NOT rename / rework the cycle-056 helpers.** They compile
   cleanly and downstream code (cycle 057 P2, cycle 058 squeeze)
   relies on their exact names.
4. **DO NOT modify `scripts/autonomous_loop.py`.** The
   prompt-builder phantoms and the tautology-scanner false positives
   are loop-maintainer territory; see
   `.prover-state/issues/tautology_scanner_false_positives.md` for
   the canonical recommendation. (No tautology hits expected from
   the cycle 057 deliverables.)
5. **DO NOT introduce `axiom` / `constant`** anywhere.
6. **DO NOT replace the `Tendsto.div` proof of
   `tendsto_const_div_one_sub_mul`** (line 2060) with the original
   Aristotle `le_trans` chain — that closure was diagnosed as
   type-incorrect for a `Filter.Tendsto` goal in cycle 056 and
   replaced manually. Leave it as-is.
7. **DO NOT submit P2 (`a_m_tendsto_zero`) to Aristotle.** The
   helper threads through a domain-specific shape (the LMM `α` /
   `yPrime` chain) that Aristotle is unlikely to discover from a
   stub file. Manual proof following the cycle 056 long-form
   template is the right move. Aristotle gets the small generic
   helpers (Priority 3 batch).
8. **DO NOT poll Aristotle more than once.** Submit, sleep 30 min
   (use the time on Priority 1 + Priority 2 manual proofs), check
   status once at the end of the cycle.

---

## Cycle-057 success criteria

* Two new `private lemma`s land in `OpenMath/Chapter4/Section404.lean`
  (P1.1 `m_h_constancy`, P1.2 `c_h_h_squared_tendsto_zero`) plus
  P2 `a_m_tendsto_zero`. Total: **3 new helpers**.
* `lake env lean OpenMath/Chapter4/Section404.lean` is clean
  (warnings allowed; no errors; one expected `sorry` at line ~2882).
* `lake build OpenMath.Chapter4.Section404` succeeds.
* Aristotle batch of 5 generic helpers submitted; status checked
  once after 30 minutes.
* Tautology scanner returns zero hits across `OpenMath/`.
* `task_results/cycle_057.md` records: which Aristotle helpers
  returned closed proofs (deferred to cycle 058 for integration), the
  three manual deliverables, and the planned cycle-058 next step
  (the actual `globalError_outer_squeeze`).

If P2 stalls (>45 min on the manual proof, or `simpa` / `convert`
fails to close the `(Θ + 1) · 0 = 0` reduction), fall back: land
P1.1 + P1.2 + the Aristotle submission only, file an issue at
`.prover-state/issues/a_m_tendsto_zero_decomposition.md` describing
the specific obstacle, and end the cycle. A 2-helper cycle with a
clean issue file beats a stuck cycle.
