# Cycle 044 Strategy — Open `thm:406C` (Global error bound for LMMs)

## Status (no work pending from prior cycle)

* `OpenMath/` is **sorry-free** as of cycle 043 (`37857ac`).
* `lem:406B` (`localTruncationError_bound`) is fully formalized.
* `lean_status.json` shows `lem:406B` as `formalized`.
* No Aristotle results pending. No open infrastructure issues that
  block §406 work (the existing
  `picard_lindelof_bound_strengthening.md`,
  `lmm_convergence_witness_deferred.md`,
  `lem_406B_textbook_check.md`, etc. are all about *previous*
  entities — they do not gate `thm:406C`).
* The cycle 040 consultant note (still in
  `.prover-state/issues/consultant_advice_cycle_040.md`) and the
  cycle 043 worker's "Suggested next approach" both name `thm:406C`
  as the natural next target. Follow that.

## Verification first (do not trust the prompt's "stuck" framing — verify HEAD)

Same phantom pattern as cycles 008, 014, 015, 040 keeps appearing.
Before doing anything, run these and confirm:

```bash
git log -1 --format='%H %s'
# Expected: 37857ac Cycle 043 — close lem:406B (LMM local truncation error bound)

git rev-parse HEAD
git rev-parse origin/Main/Experiments
# Expected: equal

rg -nP '^\s*sorry\b|:=\s*sorry\b' OpenMath/
# Expected: no matches

lake env lean OpenMath/Chapter4/Section404.lean
# Expected: only the two pre-existing unused-variable warnings (hM at 527, hh at 586). No errors.
```

If any of these returns something different, escalate. Otherwise
proceed to the §"Target" section below.

---

## Target — `thm:406C` "Global error bound for linear multistep methods"

**Entity file:** `extraction/formalization_data/entities/thm_406C.json`
(read this first; `statement_latex` and `proof_latex` are the source
of truth).

**Textbook statement (Butcher §406, p. 347, eq. (406c)):** Let
`n` denote the global error vector `n_n = y(x_n) − y_n`, where
`y` is the exact solution and `Y_n` is the LMM iterate. Then for
`h_0` sufficiently small that `h_0 · L · |β_0| < 1` and `h < h_0`,
there exist constants `C` and `D` such that

```
| n_n − ∑_{i=1}^k α_i · n_{n−i} | ≤ C · h · max_{i=1}^k |n_{n−i}| + D · h^2.    (406c)
```

**Textbook proof outline (Butcher §406, p. 347):**

> The value of `n − ∑ α_i n_{−i} − h ∑ β_i (f(y(x_{n−i})) − f(y_{n−i}))`
> is the difference of two terms, of which the first can be bounded
> by a constant times `h²` (by Theorem 406B = our `lem:406B`), and
> the second is zero. Therefore
>
> ```
> n − ∑ α_i n_{−i} = T_1 + T_2 + T_3                                 (406d)
> ```
>
> where
>
> * `T_1 = h β_0 (f(y(x_n)) − f(y_n))`, bounded by `h L |β_0| · |n_n|` (eq. 406e).
> * `T_2 = h ∑_{i=1}^k β_i (f(y(x_{n−i})) − f(y_{n−i}))`, bounded by `h L ∑_{i=1}^k |β_i| · max |n_{n−i}|` (eq. 406f).
> * `T_3 = L(y, x_n, h)`, the local truncation error at step `n`, bounded by `D · h²` via `lem:406B`.
>
> Triangle inequality on (406d) yields (406c).

Note Butcher *also* uses (406d) "twice" to derive a bound on
`‖n_n‖` itself, but **that further derivation is outside the
theorem statement**. Do not formalize the second use unless cycle
045+ needs it for `thm:406D`. Cycle 044 stops at (406c).

---

## Approach — sorry-first + Aristotle batch

Per the autonomous workflow rules in `CLAUDE.md`:

1. **Sorry-first scaffold (priority 1).** Open the §406 block of
   `OpenMath/Chapter4/Section404.lean` (extend the existing file —
   it is at 994 lines but the §406 section is the natural home; do
   **not** create a new `Section406.lean` yet) and write the full
   structure with `sorry` at every step. Verify it compiles via
   `lake env lean OpenMath/Chapter4/Section404.lean` before any
   proof attempts.

2. **Identify five sub-lemmas (priority 2).** The decomposition
   below mirrors cycles 040–043's pattern for `lem:406B`. Aim for
   the *exact* hypothesis shapes given here so you can re-use the
   `lem:406B` and `def:406A` machinery directly.

3. **Aristotle batch (priority 3, MANDATORY per CLAUDE.md).**
   Submit sub-lemmas A, B, C, plus the main theorem to Aristotle
   in a single batch (4 jobs — sub-lemma D is a one-liner, no need
   to submit). Use `mcp__aristotle__submit_directory` with a
   freshly-prepared
   `.prover-state/aristotle_submissions/cycle_044/sub_lemmas.lean`
   following the cycle-040 template. **Sleep 30 min, then check
   once.** Do NOT poll repeatedly.

4. **Manual closure (priority 4).** While Aristotle is running,
   prove sub-lemma A manually (the algebraic identity is the
   cleanest target, see §"Sub-lemma A" below). After Aristotle
   returns, incorporate any clean proofs for B/C/main; manually
   close anything Aristotle missed. **Cycle 044's deliverable
   ceiling: structure + 2 sub-lemmas closed.** Anything more is a
   stretch.

---

## Decomposition — five sub-lemmas

Throughout, fix the IVP setup we already have for `lem:406B`:

* `f : ℝ → ℝ` with `LipschitzWith L.toNNReal f` and `0 ≤ L`.
* `yex : ℝ → ℝ` with `ContDiff ℝ 1 yex` and `∀ t, deriv yex t = f (yex t)`.
* `|f (yex t)| ≤ M_bound` for all `t` (with `0 ≤ M_bound`).
* `M : LinearMultistepMethod k` with `M.IsConsistent`.
* `Y : ℕ → ℝ` is an LMM solution: `M.IsLMMSolution h x₀ f Y`.
* `h > 0` is the step size; `x₀` is the grid origin.
* The grid is `x_n := x₀ + n·h`.

Define a local notation/abbreviation for the **global error**:
```lean
def globalError (yex : ℝ → ℝ) (Y : ℕ → ℝ) (x₀ h : ℝ) (n : ℕ) : ℝ :=
  yex (x₀ + (n : ℝ) * h) - Y n
```
(Or use it inline with `let n_err := …`. Both are fine; keep it
local — do **not** make it a method on `LinearMultistepMethod`.)

### Sub-lemma A — `globalError_decomposition` (algebraic identity, 406d)

**The cleanest target this cycle.** No analysis, just unfolding
`IsLMMSolution` + `localTruncationError`.

```lean
lemma globalError_decomposition {k : ℕ} (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {yex : ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hY : M.IsLMMSolution h x₀ f Y)
    (n : ℕ) (hn : k ≤ n) :
    globalError yex Y x₀ h n
      - ∑ i : Fin k, M.α i.succ * globalError yex Y x₀ h (n - (i.val + 1))
      = h * M.β 0 * (f (yex (x₀ + (n : ℝ) * h)) - f (Y n))
        + h * (∑ i : Fin k, M.β i.succ
                * (f (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h))
                   - f (Y (n - (i.val + 1)))))
        + M.localTruncationError yex (x₀ + (n : ℝ) * h) h := by
  sorry
```

**Proof strategy.** This is a *purely algebraic* identity — no
inequalities, no analysis. Steps:

1. Unfold `globalError`, `localTruncationError`, and `IsLMMSolution`.
2. The LMM recurrence `∑ M.α i · Y(n+k−i.val) = h · ∑ M.β i · f(...)`
   (with `M.α 0 = -1`) splits the LHS into the contribution from
   `Y_n − ∑α_i Y_{n-i}` (which equals `h ∑ β_i f(x_{n-i}, Y_{n-i})`)
   and similar for `yex` (which differs from the RHS by exactly
   the LTE).
3. Subtract and combine. The `α 0 = -1` normalisation handles the
   sign on the leading `Y_n` term.

**Index alignment caveat.** `IsLMMSolution` indexes solutions at
`n + k - i.val` (for `n : ℕ`); the present statement indexes at
`n - (i.val + 1)`. Re-index by setting `n := m + k` for some
`m : ℕ`, applying `hY m`, then converting back. The `hn : k ≤ n`
hypothesis ensures the `ℕ`-subtraction `n - (i.val + 1)` doesn't
truncate. This re-indexing is the main bookkeeping cost; allow
~40 lines.

**Faithfulness check (cycle 044 pre-commit):** the identity above
matches Butcher's (406d) when read coefficient-by-coefficient.
Verify on explicit Euler (`k = 1`, `α_0 = -1, α_1 = 1, β_0 = 0,
β_1 = 1`) as a sanity test before believing the formulation.

### Sub-lemma B — `T1_bound`

```lean
lemma T1_bound {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {β₀ : ℝ} (h : ℝ) (hh : 0 ≤ h) (a b : ℝ) :
    |h * β₀ * (f a - f b)| ≤ h * L * |β₀| * |a - b| := by
  sorry
```

**Proof strategy.** `LipschitzWith.dist_le_mul`, convert `dist` to
`|·|` via `Real.dist_eq`, then `abs_mul` and `mul_le_mul_of_nonneg_left`.

This is essentially the proof of `deriv_diff_bound` (sub-lemma D
of `lem:406B`, cycle 041) with the function-argument as
`a = yex(x_n), b = Y_n`. **Should be ~10–15 lines.**

### Sub-lemma C — `T2_bound`

```lean
lemma T2_bound {k : ℕ} (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    (h : ℝ) (hh : 0 ≤ h)
    (a : Fin k → ℝ) (b : Fin k → ℝ) (Mmax : ℝ)
    (hMmax : ∀ i : Fin k, |a i - b i| ≤ Mmax) (hMmax0 : 0 ≤ Mmax) :
    |h * ∑ i : Fin k, M.β i.succ * (f (a i) - f (b i))|
      ≤ h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax := by
  sorry
```

**Proof strategy.** Follow `localTruncationError_β_sum_bound`
(cycle 043, lines ~923–952) verbatim — it is the same shape
(triangle inequality on a sum of `β_{i+1}`-weighted differences,
each bounded by Lipschitz × `|a_i − b_i|`, then ≤ Lipschitz × `Mmax`).

The hypothesis interface is generic so the theorem doesn't have
to commit to "max of global errors" yet — we'll fix that at the
main-theorem assembly step.

### Sub-lemma D — `T3_bound` (one-liner, no Aristotle needed)

```lean
lemma T3_bound {k : ℕ} (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |M.localTruncationError y x h|
      ≤ ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * L * M_bound * h^2 :=
  M.localTruncationError_bound hcons hL hM hf_lip
    hy_C1 hy_ode hf_y_bound x h hh
```

**This sub-lemma is a one-liner — direct application of
`lem:406B`.** Skip Aristotle for this one. It exists only to give
a clean name for the LTE bound at the assembly step. (You may
inline it directly into the main theorem if preferred — it is not
"new content".)

### Main theorem — `globalError_recurrence_bound` (`thm:406C`)

```lean
theorem LinearMultistepMethod.globalError_recurrence_bound
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hY : M.IsLMMSolution h x₀ f Y)
    (n : ℕ) (hn : k ≤ n)
    (Mmax : ℝ) (hMmax0 : 0 ≤ Mmax)
    (hMmax : ∀ i : Fin k,
              |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1))| ≤ Mmax) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ h * L * |M.β 0| * |yex (x₀ + (n : ℝ) * h) - Y n|
        + h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
          * L * M_bound * h^2 := by
  sorry
```

**Note the LHS has `|n_n|` floating around** (the first term on
the RHS is `h L |β_0| · |n_n|`). This is the "T_1 + T_2 + T_3"
inequality directly, **before** the Butcher (1 − hL|β_0|)-trick
that absorbs T_1 into the LHS. Stopping here keeps cycle 044
focused on the algebraic decomposition + per-term bounds; the
absorption / inversion step is for cycle 045+ when `thm:406D`
needs it.

**Faithfulness flag.** The textbook statement (406c) reads
`Ch · max + Dh²` — i.e. with the T_1 already absorbed via the
`(1 − hL|β_0|)` factor. Our cycle-044 statement keeps T_1 explicit
so that the proof is just triangle inequality on (406d). Document
this carefully in the docstring: this is **faithful** (the
identity (406d) is exactly Butcher's (406d); only the cosmetic
"final inequality" is deferred). The full (406c) form will follow
from this lemma + a one-step inversion in cycle 045 once we have
a "small h" hypothesis (`h * L * |β_0| < 1`). Mark `thm:406C` as
`partial` in `lean_status.json` until the inversion step lands.

If you want to commit the full (406c) form *this cycle*, add
the inversion as a final corollary `globalError_recurrence_bound_final`
after the main lemma. Aristotle is unlikely to handle it (it
requires `1/(1 − hL|β_0|)` algebra), so attempt only if cycle
budget permits.

**Proof strategy for the main lemma** (after sub-lemmas A, B, C, D
land):

1. Apply sub-lemma A to rewrite LHS as `|T_1 + T_2 + T_3|`.
2. Triangle inequality (`abs_add_le` × 2) to split into
   `|T_1| + |T_2| + |T_3|`.
3. Bound each via sub-lemmas B, C, D.
4. Assemble via `add_le_add` + `add_le_add` + final `ring` /
   `linarith`.

Estimated ~30 lines. Should not need `maxHeartbeats` adjustment.

---

## What NOT to do — explicit prohibitions

* **Do NOT treat the prompt's "stuck on" framing as a real
  problem.** Per cycles 008/014/015/040 phantom pattern. Verify
  `git log -1` and `rg sorry OpenMath/` first; if both clean,
  proceed.
* **Do NOT increase `maxHeartbeats` above 200000.** Per CLAUDE.md.
  If `ring` is slow on the main theorem, decompose further.
* **Do NOT introduce `axiom`, `constant`, or `noncomputable def`
  for any of the sub-lemma gaps.** All of them are tractable from
  existing Mathlib + cycle-040–043 infrastructure.
* **Do NOT generalise `Y` to vector-valued (`ℕ → ℝ^N`).** Stay
  scalar, as cycle 040–043 strategies dictated. The proof above
  all works in the scalar case.
* **Do NOT poll Aristotle more than once.** CLAUDE.md is explicit.
  Submit once at the start of the cycle, sleep 30 min, check once.
  Do not extend the wait beyond ~1 h regardless.
* **Do NOT edit `scripts/autonomous_loop.py`** (loop-maintainer
  territory; per cycle-014 / cycle-015 standing rule).
* **Do NOT rewrite the cycle-043 `lem:406B` machinery.** It is
  axiom-clean and load-bearing for sub-lemma D.
* **Do NOT attempt `thm:406D` or `thm:243A` this cycle.** Both
  are downstream of `thm:406C`'s *full* form; defer to cycle 045+.
* **Do NOT formalize the `(1 − hL|β_0|)`-inversion / Butcher's
  "use (406d) twice" maneuver this cycle** unless sub-lemmas A–D
  and the main lemma all land cleanly with > 30 min cycle budget
  remaining. The deliverable ceiling is structure + 2 sub-lemmas.
* **Do NOT define `globalError` as a structure-instance method
  on `LinearMultistepMethod`.** Keep it as a plain local function
  (or just inline the expression). The textbook treats it as a
  shorthand notation, not a categorical operation.
* **Do NOT skip the §"Faithfulness check" in the
  `task_results/cycle_044.md` file.** It is mandatory per
  CLAUDE.md, and the divergence between cycle-044's statement
  (T_1 explicit on RHS) and Butcher's (406c) (T_1 absorbed) needs
  explicit justification.
* **Do NOT use `abs_add` (no underscore-le suffix).** Per cycle
  043 discovery the current Mathlib name is `abs_add_le`.
* **Do NOT submit sub-lemma D to Aristotle.** It is a one-line
  application of `lem:406B`. Aristotle compute is finite — save
  it for sub-lemmas A, B, C, main.

---

## Pre-commit checklist (per CLAUDE.md)

Before committing, verify:

- [ ] `lake env lean OpenMath/Chapter4/Section404.lean` succeeds
      with at most the two pre-existing unused-variable warnings
      (`hM` at L527, `hh` at L586). No new warnings/errors.
- [ ] `lake build OpenMath.Chapter4.Section404` succeeds.
- [ ] `#print axioms ...` for every new `theorem` / `lemma`
      reports `[propext, Classical.choice, Quot.sound]` only — no
      `sorryAx` (except in declarations explicitly left as `sorry`
      for future cycles, in which case clearly comment them and
      list them in `cycle_044.md` §Result).
- [ ] If any `sorry` remains in committed code, document each in
      `task_results/cycle_044.md` with the planned cycle-045
      target.
- [ ] `extraction/formalization_data/lean_status.json` updated:
      `thm:406C` → `partial` (if some sub-lemmas remain `sorry`)
      or `formalized` (if everything closed). Include the
      `lean_file` and `lean_symbol` entries.
- [ ] `task_results/cycle_044.md` written with the full
      Worked-on / Approach / Result / Faithfulness check / Dead
      ends / Discovery / Suggested-next sections (cycles 040–043
      have good templates).
- [ ] **Faithfulness check** explicitly addresses:
      (a) the algebraic identity (406d) matches Butcher's
          decomposition,
      (b) the divergence from textbook (406c) (T_1 explicit
          vs. absorbed) is documented and justified.
- [ ] If anything blocks, write an issue file to
      `.prover-state/issues/thm_406C_*.md` describing **WHY** (not
      "it's hard"), and reference it from cycle_044.md.

---

## Aristotle batch — exact submission shape

Create `.prover-state/aristotle_submissions/cycle_044/sub_lemmas.lean`
with:

```lean
import Mathlib
import OpenMath.Chapter4.Section404

-- Submit only A, B, C, and the main theorem (4 jobs, well under
-- the ~5/cycle budget). Sub-lemma D is a one-liner — skip it.

-- (Sub-lemma A statement — full Lean signature as above)
-- ...
-- sorry

-- (Sub-lemma B statement — Lipschitz + h-scaling)
-- ...
-- sorry

-- (Sub-lemma C statement — sum-of-Lipschitz bound)
-- ...
-- sorry

-- (Main theorem statement)
-- ...
-- sorry
```

After submission, record the project ID in `cycle_044.md` and
proceed to manual sub-lemma A. Sleep 30 min, then check once.
Incorporate any returned proofs that are axiom-clean; reject
proofs that introduce new axioms or rely on unstated hypotheses
(per cycle 043's discovery: Aristotle added `Continuous f` to
sub-lemma B for `lem:406B`, which we avoided by using `ContDiff
ℝ 1 yex`. Watch for similar over-strengthening here).

---

## Reference — relevant prior work

| Source | What's there |
|---|---|
| `OpenMath/Chapter4/Section404.lean:390–394` | `localTruncationError` definition (def:406A) |
| `OpenMath/Chapter4/Section404.lean:790–870` | `localTruncationError_decomposition` (sub-lemma E of cycle 040–042) — the algebraic shape for sub-lemma A |
| `OpenMath/Chapter4/Section404.lean:880–952` | α-sum and β-sum helpers (cycle 043) — templates for T_2 bound |
| `OpenMath/Chapter4/Section404.lean:954–992` | `localTruncationError_bound` = `lem:406B` — sub-lemma D's one-liner |
| `OpenMath/Chapter4/Section404.lean:260–266` | `IsLMMSolution` definition — needed for sub-lemma A |
| `OpenMath/Chapter4/Section404.lean:526–574` | `exact_solution_norm_bound` (cycle 041) — proof template for analytic sub-lemmas |
| `extraction/formalization_data/entities/thm_406C.json` | textbook source of truth |
| `.prover-state/issues/lem_406B_textbook_check.md` | cycle 040 verification of the β_i decomposition (relevant for faithfulness check) |
| `.prover-state/task_results/cycle_043.md` | cycle 043 template |

---

## Mathlib lemmas to expect

| Goal | Lemma |
|---|---|
| Triangle inequality | `abs_add_le` (NB: not `abs_add` — that name is gone in current Mathlib, per cycle 043 discovery) |
| `\|Σ\| ≤ Σ \|·\|` | `Finset.abs_sum_le_sum_abs` |
| Monotone sum | `Finset.sum_le_sum` |
| `\|a · b\| = \|a\| · \|b\|` | `abs_mul` |
| Lipschitz application (real-valued) | `LipschitzWith.dist_le_mul`, then bridge `dist a b = |a − b|` via `Real.dist_eq` |
| `mul_le_mul_of_nonneg_left` / `_right` | std |
| Distribute coefficient over sum | `Finset.sum_mul`, `Finset.mul_sum` |
| Casting `((i.val + 1 : ℕ) : ℝ)` arithmetic | follow MEMORY pattern `feedback_satisfieseq404b_cast.md` if needed |

All are in pinned Mathlib v4.28.0. Verify each name with
`lean_local_search` before committing.

---

## Cycle 044 deliverable contract (deliberately bounded)

**Minimum acceptable** (satisfies CLAUDE.md "no zero-change cycles"
rule):

* Sorry-first scaffold for `thm:406C` (sub-lemmas A–D + main
  theorem, all `sorry` except D).
* Sub-lemma A (`globalError_decomposition`) closed manually.
* Sub-lemma D closed (it is a one-liner; ~5 min).
* Aristotle batch submitted, project ID recorded.
* `lean_status.json` updated with `thm:406C` = `partial`.
* `cycle_044.md` written with the full template.

**Stretch (if Aristotle returns clean proofs ≤ 1 h after submission):**

* Sub-lemmas B and C closed (incorporated from Aristotle, or
  derived from `localTruncationError_β_sum_bound` template).
* Main theorem assembled.
* `lean_status.json` updated to `formalized`.

**Beyond stretch (do NOT attempt unless above are done with > 30
min budget):**

* `globalError_recurrence_bound_final` corollary in the (406c)
  form (after the `(1 − hL|β_0|)`-inversion step).
* `thm:406D` opening scaffold.

---

## End-of-cycle action items (mandatory)

1. Append cycle-044 row to `.prover-state/history.jsonl`.
2. Update `.prover-state/heartbeat.json`.
3. Commit to `Main/Experiments` branch.
4. Push to `origin`.
5. Re-verify `git rev-parse HEAD == git rev-parse
   origin/Main/Experiments` after push.
