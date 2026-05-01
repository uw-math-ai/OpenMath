# Cycle 055 Strategy — recover sorry count + add Tendsto helpers for `thm:406D`

## Status snapshot

- **Sorry count: 2** (line 2640 cycle-054 stub; line 2664 non-autonomous scaffold).
- **Cycle 054 was scored -2** purely because sorry count went 1 → 2
  (the autonomous Tendsto stub `stable_consistent_isConvergent_autonomous`
  was added with body `sorry`).
- The cycle-054 slack-removal refactor on `globalError_recurrence_form`
  IS on disk and IS correct — keep it.
- The cycle-053 closed-form theorem `globalError_closed_form_autonomous`
  IS on disk and IS axiom-clean — keep it.
- Aristotle: no pending results.

## Cycle 055 goal — non-negotiable

**Sorry count must end at 1**, recovering from cycle 054's regression.
The cycle ALSO must add genuine forward progress (helper lemmas) toward
the eventual closure of the autonomous Tendsto theorem in cycle 056+.

A cycle that only deletes the stub and adds nothing else is acceptable
but minimal; aim for stub-deletion **plus** at least one fully closed
Tendsto/continuity helper.

---

## Required steps (in order)

### Step 1 — Remove the cycle-054 sorry stub (REQUIRED)

In `OpenMath/Chapter4/Section404.lean`, delete lines 2579–2640 (the
entire docstring + theorem `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`).

The stub has no callers (verify with
`grep -rn 'stable_consistent_isConvergent_autonomous' OpenMath/`)
and exists purely as a future target. Removing it restores
sorry count to 1 (just the line-2664 non-autonomous scaffold).

The non-autonomous scaffold `stable_consistent_isConvergent` at
line 2660 STAYS untouched (it is the long-term cycle 056+ target).

### Step 2 — Add helper lemma `yPrime_sum_abs_tendsto_zero` (REQUIRED — at least this one)

This is the largest standalone piece of the eventual squeeze proof
and unblocks the "a_m → 0" sub-goal of cycle 056+. It is a pure
Tendsto lemma about the `yPrime` transformation defined in
`OpenMath/Chapter1/Section141.lean:86`.

**Mathematical content.** `yPrime k α u : ℕ → R` is a triangular
recurrence: `yPrime _ _ u m = u m - Σ_{i<m} θ_{m-i} · yPrime _ _ u i`
for `m < k`, and `0` otherwise. Hence each `yPrime k α u i` for
`i < k` is a *finite linear combination* of `u 0, …, u i`. So if
the family `(u_h : Fin k → R)` parametrized by `h` satisfies
`u_h j → 0` as `h → 0` for each `j : Fin k`, then
`yPrime k α u_h i → 0` as `h → 0` for each `i < k`, and therefore
`Σ_{i ∈ range k} |yPrime k α u_h i| → 0`.

**Suggested signature** (worker should adjust as needed):

```lean
private lemma yPrime_sum_abs_tendsto_zero
    {k : ℕ} (α : Fin k → ℝ)
    {u : ℝ → Fin k → ℝ}
    (hu : ∀ j : Fin k,
      Filter.Tendsto (fun h : ℝ => u h j) (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun h : ℝ =>
        ∑ i ∈ Finset.range k, |yPrime k α (u h) i|)
      (nhds 0) (nhds 0)
```

**Proof plan.**

1. Show by *strong induction on `m < k`* that
   `Tendsto (fun h => yPrime k α (u h) m) (nhds 0) (nhds 0)`.
   Base case `m = 0`: `yPrime _ _ u 0 = u 0 - 0 = u 0` (use
   `yPrime_of_lt` at `m = 0`; the inner sum is over `Fin 0 = ∅`).
   Apply `hu 0` (with `0 : Fin k`).
   Inductive step: `yPrime k α (u h) m = u h ⟨m, _⟩ - Σ_{i:Fin m} θ_{m-i.val} · yPrime k α (u h) i.val`.
   Each summand: `θ_{m-i.val}` is a constant (independent of `h`),
   `yPrime k α (u h) i.val → 0` by IH, so each `θ * yPrime → 0` by
   `Filter.Tendsto.const_mul`. Finite sum tends to 0 by
   `tendsto_finset_sum`. Subtract from `u h ⟨m, _⟩ → 0`.
2. Lift to `|·|` via `Filter.Tendsto.abs`.
3. Lift to the sum via `tendsto_finset_sum` (sum of finitely many
   things each → 0 tends to 0).

**Mathlib citations** (verify exact names with `lean_local_search`):

- `Filter.Tendsto.const_mul` — `c · f h → c · L` if `f h → L`.
- `Filter.Tendsto.sub` — `f - g → L - M`.
- `Filter.Tendsto.abs` — `|f h| → |L|`.
- `tendsto_finset_sum` — `Σ_{i ∈ s} f i h → Σ_{i ∈ s} L i` if each `f i h → L i`.
  Already used at `Section404.lean:1869`.
- `yPrime_of_lt` — equation lemma at `OpenMath/Chapter1/Section141.lean:124`.

**Use `Nat.strong_induction_on m hk` or `Fin.induction`** for the
intra-`Fin k` strong induction. The simpler shape is `∀ m, m < k →
Tendsto …`, then `induction m using Nat.strong_induction_on`.

### Step 3 (STRETCH) — Add second helper if Step 2 lands cleanly

If Step 2 lands and there is residual cycle time, add ONE of:

**Option A — `Cbase_continuousAt_zero`**: continuity-style helper
showing the rational function
```
fun h => L * (|β 0| · Σᵢ |α(i+1)| + Σᵢ |β(i+1)|) / (1 - h · L · |β 0|)
```
is continuous at `h = 0` (denominator → 1). This is the form of
`Cbase` from `globalError_recurrence_form` line 2125. State as a
top-level helper that takes `M : LinearMultistepMethod k`, `L`, and
returns a Tendsto fact; do NOT refactor `globalError_recurrence_form`
itself this cycle.

**Option B — `tendsto_const_of_tendsto_zero`**: a generic Tendsto
combinator showing that if `f h → 0` and `g h → c` (with `c` finite),
then `f h * g h → 0`. (Mathlib has `Filter.Tendsto.zero_mul_isBoundedUnder`
and `Filter.Tendsto.mul_const`; one or both already suffices, so this
"helper" might just be a one-line `simpa` on a Mathlib name. If so,
skip and pick option A or C.)

**Option C — `bounded_div_oneSub_nonneg`**: a uniform bound
`|f h / (1 - h · c)| ≤ 2 · |f h|` whenever `0 ≤ h · c ≤ 1/2`. Useful
as a coarse upper bound for the `Cbase`/`Dbase` shape.

**Recommend Option A** (most directly useful for cycle 056). If it
proves too slow, fall back to skipping Step 3.

### Step 4 — Aristotle batch (MANDATORY)

Submit the helpers from Steps 2 + 3 to Aristotle in a single batch.
Per CLAUDE.md: ~5 jobs, sleep 30 min, check ONCE.

Suggested batch (5 sub-goals, even if some overlap with Step 2's
plan):

1. `yPrime_sum_abs_tendsto_zero` (full statement from Step 2).
2. The strong-induction helper alone:
   `∀ m < k, Tendsto (fun h => yPrime k α (u h) m) (nhds 0) (nhds 0)`.
3. The Step 3 helper (whichever option chosen).
4. A small Tendsto.abs lift if the worker spells it out as a sub-lemma.
5. **Optional fifth slot**: a *re-attempt* of any cycle-053/054
   sub-lemma that previously needed manual proof — Aristotle has
   improved over time and may now close them quickly.

**Do NOT poll Aristotle more than once.** One 30-min sleep, one
status check.

### Step 5 — Verify, commit, document

- `lake env lean OpenMath/Chapter4/Section404.lean` — clean compile.
  Allow pre-existing warnings; no NEW warnings.
- `lake build OpenMath.Chapter4.Section404` — clean build (needed so
  `#print axioms` can see new theorems via import).
- `grep -c '^\s*sorry\s*$' OpenMath/Chapter4/Section404.lean` →
  expect **1**. (NOT 2, NOT 0.)
- `#print axioms` for each new helper → expect
  `[propext, Classical.choice, Quot.sound]` only.
- Commit message: `Cycle 055 — yPrime_sum_abs tendsto + autonomous stub removal (thm:406D)`.

Write `.prover-state/task_results/cycle_055.md` per CLAUDE.md.

---

## Why this plan and not "just close the autonomous theorem"

Closing `stable_consistent_isConvergent_autonomous` requires *all*
of:
- a refactor of `globalError_recurrence_form` to expose explicit
  `a, b, c` (currently they are existential witnesses inside the ∃),
  OR a heavy `Classical.choice` extraction;
- `y'sum → 0` (= Step 2 above);
- `Cbase` bounded (= Step 3 option A above);
- `Dbase` bounded (similar);
- `b · k = ((Θ+1)·Cbase + 1) · k` bounded above and below;
- `c_m · h_m / (b_m · k) → 0`;
- the `m · h_m = x - x₀` constancy argument;
- `eventually` filter management to engage `hsmall` and `0 < m`;
- `squeeze_zero` final assembly.

That is **at least 4–6 lemmas plus a 50-line outer assembly**.
Cycles 045–054 averaged ~1 lemma per cycle on this proof. Trying
to land all of it in cycle 055 risks a fifth consecutive partial-
or-reverted cycle. Step-by-step infrastructure with **zero net
sorry change per cycle** is the proven path; that is what cycles
045–052 did successfully.

Cycle 056+ takes Step 2's helper (and ideally Step 3's) and adds
the remaining bounded/exponential helpers. Cycle 057 or 058 then
does the outer squeeze assembly and re-introduces (with a real
proof body) the autonomous Tendsto theorem.

---

## What NOT to do this cycle

- **DO NOT** attempt to close `stable_consistent_isConvergent_autonomous`
  in full. Multi-cycle work; see "Why this plan" above. Just *delete*
  the stub.
- **DO NOT** modify `stable_consistent_isConvergent` (line 2660,
  the non-autonomous scaffold). It is the long-term target for
  cycle 056+ after the autonomous form is closed.
- **DO NOT** modify `globalError_recurrence_form`,
  `globalError_closed_form_autonomous`, or any cycle 045–053
  helper. They compile, are axiom-clean, and have downstream
  callers. The cycle-054 slack removal landed correctly — leave it.
- **DO NOT** introduce ANY new `sorry`. The cycle is judged on
  sorry count; net change must be **−1** (going 2 → 1) or in the
  worst case **0** (going 2 → 2 with helpers added). A cycle that
  ends at sorry count 2 with no helpers is unacceptable.
- **DO NOT** use `exact h_<name>` patterns (scanner false-positive
  trigger per `tautology_scanner_false_positives.md`). Use
  `exact this`, `exact hyz`, drop underscores, etc.
- **DO NOT** raise `maxHeartbeats` above 200000.
- **DO NOT** introduce `axiom` or `constant`.
- **DO NOT** refactor `Cbase` / `Dbase` into top-level
  `noncomputable def`s this cycle. That refactor is for cycle 056+
  when the squeeze proof actually needs them as accessible terms.
  The Step-3-option-A helper just states a Tendsto fact about the
  *expression*, not about a name.
- **DO NOT** poll Aristotle more than once. One 30-min sleep, one
  status check.
- **DO NOT** spend time chasing the cycle-053 "vacuous proof" or
  cycle-054 "REVERTED" verdict. The "REVERTED" was a sorry-count
  regression that this cycle's Step 1 fixes; the "vacuous proof"
  is a known scanner false positive.
- **DO NOT** edit `scripts/autonomous_loop.py` from the worker.
- **DO NOT** edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/` (they are regenerated;
  see `extraction/EXTENSIBILITY.md`).

---

## Faithfulness flags for this cycle

For each new lemma introduced:

* **`yPrime_sum_abs_tendsto_zero`** (Step 2):
  * Not in textbook directly — internal helper for the §406D proof.
  * Statement: "the sum of absolute values of `yPrime k α u_h i` over
    `i < k` tends to 0 as h → 0, given each `u_h j → 0`".
  * **Tautology check:** the conclusion is a `Tendsto` fact that
    differs from each `hu j` (which is a per-component Tendsto fact).
    The lemma genuinely combines `k` separate per-component facts
    into a single combined-sum fact via the triangular `yPrime`
    recursion. Not vacuous. ✓
  * **Identity check:** body should NOT be a single `exact hu` or
    `exact h_<anything>`. It should perform the strong induction +
    finite-sum lift. ✓
  * **Hypothesis strength:** `hu j → 0` is the weakest possible
    hypothesis on `u h`. ✓

* **Step 3 helper** (if added):
  * Document its specific statement and its justification in the
    cycle 055 task results.

---

## Cross-references

- `OpenMath/Chapter1/Section141.lean:86` — `yPrime` definition.
- `OpenMath/Chapter1/Section141.lean:124` — `yPrime_of_lt` equation.
- `OpenMath/Chapter4/Section404.lean:1810` —
  `starting_error_each_tendsto_zero` (the per-component Tendsto fact
  that the eventual outer assembly will feed into Step 2's `hu`).
- `OpenMath/Chapter4/Section404.lean:1851` —
  `starting_error_sum_tendsto_zero` (the `Σ |u_h j| → 0` fact, *not*
  what Step 2 proves — Step 2 is about `Σ |yPrime k α (u h) i| → 0`,
  which is finer).
- `OpenMath/Chapter4/Section404.lean:2098` —
  `globalError_recurrence_form`, the consumer of Step 3-option-A's
  Cbase/Dbase shape.
- `OpenMath/Chapter4/Section404.lean:2098` line 2148 — the
  `y'sum` term whose `→ 0` behaviour Step 2 captures.

---

## Brief: what Aristotle should see

If Aristotle struggles, the worker can reword the prompt to emphasize:

* "yPrime is a finite triangular recurrence: yPrime k α u 0 = u 0
  and for `0 < m < k`, yPrime k α u m = u m - Σ_{i<m} θ_{m-i} ·
  yPrime k α u i".
* "Each yPrime k α (u h) m for m < k is therefore a finite linear
  combination of `u h 0, …, u h m` with coefficients independent of h."
* "Each linear factor `u h j` tends to 0 as h → 0 by hypothesis."
* "Use Filter.Tendsto.const_mul and Filter.Tendsto.sub repeatedly."
