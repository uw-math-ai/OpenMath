# Cycle 112 Strategy

## State entering cycle 112

* Branch tip: `e089b28 Cycle 111 — close aux_515D_stage_eventually_bounded via sum-norm self-bound`.
* `OpenMath/` sorry count: **1** — the *single* remaining sorry is at
  `OpenMath/Chapter5/Section515.lean:1504`, the body of
  `aux_515D_output_tendsto`. Closing it closes the §515D capstone end-to-end.
* No pending Aristotle results.
* Capstone `GeneralLinearMethod.stable_consistent_isConvergent` and
  `aux_515D_stage_tendsto` already compile cleanly modulo this last sorry.

## Goal

**Open a controlled sorry-first scaffold for `aux_515D_output_tendsto`
covering the discrete-Grönwall-plus-squeeze argument, hand-prove the
*squeeze* sub-lemma (the easiest of the three), submit the harder two
to Aristotle, and document the propagated faithfulness divergences on
the capstone signature.**

Net sorry-count target: **1 → 3** (one closed `aux_515D_output_tendsto`
body + 2 still-open sub-lemma sorries that Aristotle is working on).
This mirrors cycle 108's 0→3 scaffold but **avoids the cycle-108
regression** by closing one sub-lemma manually in the same cycle and
having Aristotle in flight on the rest. Score expectation: +1 for a
clean scaffold + 1 closure + clean axioms.

If you find yourself cornered by hypothesis-strengthening pain
(see Priority 2 / "Faithfulness alarms" below) and end up with sorry
count > 3, **stop and revert to a *minimal* scaffold** (Backup plan
in §F): just decompose `aux_515D_output_tendsto` into 2 helpers (one
recurrence, one squeeze) without trying to close anything. Net 1 → 3
is the floor either way.

---

## Priority 0 — Aristotle batch (sorry-first, do FIRST)

Submit BEFORE writing any Lean. Aristotle is free compute that runs
in parallel with your hand-work; per CLAUDE.md, "MAXIMIZE Aristotle
USAGE — submit ~5 jobs per cycle in batch."

### What to submit

Compose `.prover-state/aristotle_submissions/cycle_112/` with three
self-contained `.lean` files, one per sub-lemma below (named
`sub_A_recurrence.lean`, `sub_B_gronwall.lean`,
`sub_C_squeeze.lean`). Each file should contain:

* All required imports (mirror what the cycle 111 file
  `aux_515D_stage_eventually_bounded` already imports).
* The sub-lemma's statement *exactly* as in §A below (worker may
  finalize names, but stay close to the proposed signatures).
* The relevant lemma names visible to Aristotle:
  - `GeneralLinearMethod.localStepError_bound`
    (`OpenMath/Chapter5/Section515.lean:1183`).
  - `OpenMath.Chapter4.Section404.discrete_gronwall_exp_bound`
    (`OpenMath/Chapter4/Section404.lean:1663`).
  - `Filter.Tendsto.add`, `tendsto_pi_nhds`, `Real.exp_pos`,
    `squeeze_zero` (standard Mathlib).

### How to submit

`mcp__aristotle__submit_directory` for the whole cycle_112 dir
(one project), OR three separate `submit_file` calls (three projects)
if Aristotle prefers per-file isolation. Note project IDs in the
submission directory's `README.md`. **Continue immediately to
Priority 1.** Per CLAUDE.md, poll **once** ~30 min later (or at end
of cycle, whichever is later); do not re-poll.

Past Aristotle performance on discrete-Grönwall-style arguments has
been mixed (cycles 094/096/103 weak; cycle 050 success). Set
expectations accordingly — Aristotle is the backup, not the primary
plan.

---

## Priority 1 — Hand-write the scaffold + close sub-lemma C

Estimated 90–120 min of focused work. Concrete steps; follow in order.

### Step 1 — Audit the missing hypotheses

`localStepError_bound` (`Section515.lean:1183`) requires hypotheses
not present in `aux_515D_output_tendsto`'s current signature:

| Required by `localStepError_bound`     | In `aux_515D_output_tendsto`? |
|----------------------------------------|-------------------------------|
| `0 ≤ M_bound`, `∀ t, |yex t| ≤ M_bound`| **NO** — must be added or derived |
| `∀ t, |deriv yex t| ≤ L * M_bound`     | **NO** |
| `ContDiff ℝ 1 yex`                     | **NO** — derivable from `_hyex_ode` |
| `‖h₀ L • |A|‖ < 1` (Frobenius)         | **NO** — must be added on capstone |
| `M.B *ᵥ 𝟙 + M.V *ᵥ v = u + v` (`hCons`) | YES (`_hCons_eq`) |
| `M.V *ᵥ u = u`                          | YES (`_hVu`) |
| `M.U *ᵥ u = 𝟙`                          | YES (`_hUu`) |

The first three (`M_bound`, `ContDiff`) can in principle be
*derived* from `_hyex_ode` + Lipschitz + compactness on `[x₀, x]`,
but doing so turns the scaffold into a multi-cycle proof. **Choose
the faithfulness-divergence path**: surface them as hypotheses on
the helper signature (analogous to cycle 098's stage-limit clause
and cycle 107's Frobenius hypothesis on `localStepError_bound`).
Document each as a faithfulness divergence in the docstring with a
pointer to a new issue file `aux_515D_output_tendsto_hypotheses.md`.

The Frobenius hypothesis `‖((x - x₀) * L) • M.A.map (|·|)‖ < 1`
must propagate up to `stable_consistent_isConvergent`'s signature,
exactly as cycle 107 propagated the analogous hypothesis on
`lem:515B`. This is acceptable per cycle 098/107 precedent.

### Step 2 — Strengthen the helper signature

Modify `aux_515D_output_tendsto` (currently
`Section515.lean:1481-1504`) to add the following hypotheses
(use prefixed underscores `_hM`, `_hyex_M`, etc. on any you don't
end up consuming yet, per CLAUDE.md hygiene):

```lean
private theorem aux_515D_output_tendsto {s r : ℕ}
    (hs : 0 < s)                                            -- new (cycle 109 style)
    (M : GeneralLinearMethod s r)
    (hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    (hyex_C1 : ContDiff ℝ 1 yex)                            -- new
    {M_bound : ℝ} (hM_nn : 0 ≤ M_bound)                     -- new
    (hyex_M : ∀ t, |yex t| ≤ M_bound)                       -- new
    (hyex'_LM : ∀ t, |deriv yex t| ≤ (L : ℝ) * M_bound)     -- new
    {u v : Fin r → ℝ}
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {φ : ℝ → Fin r → ℝ}
    (hφ : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                          (nhds 0) (nhds (u i * y₀)))
    {x : ℝ} (hxx : x₀ < x)
    (h_norm : ‖((x - x₀) * (L : ℝ)) •
                  M.A.map (fun a => |a|)‖ < 1)              -- new
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))) :
    Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
        (nhds (fun i => u i * yex x))
```

The exact `Matrix.frobeniusNorm` spelling: read cycle 107's
`localStepError_bound` Frobenius hypothesis at `Section515.lean:1221`
and reuse the same idiom — the prevailing convention is the default
`‖·‖` instance on `Matrix _ _ ℝ`.

Propagate `hyex_C1`, `hM_nn`, `hyex_M`, `hyex'_LM`, `h_norm` up to
`aux_515D_stage_tendsto` (line ~1469) and the capstone
`stable_consistent_isConvergent` (line ~1952) signatures. The
capstone takes them as additional hypotheses BEFORE its `intro f L
hf_lip x₀ y₀ yex` chain — i.e. the capstone now proves a *strengthened*
`IsConvergent`-like statement, packaged in the form
`(strengthening hypotheses) → IsConvergent` if at all possible, OR
proves a strengthened statement and we update the entity tracking
accordingly. **Default**: just add the new hypotheses to the capstone
and accept that the capstone's conclusion `M.IsConvergent` will be
provable only under the new premises (which is faithfulness-divergent
but documented). See §C "Faithfulness alarms" below.

### Step 3 — Define the per-step error δ

Inside `aux_515D_output_tendsto`, introduce the discretization-dependent
per-step error:

```lean
let h_n : ℕ → ℝ := fun n => (x - x₀) / (n : ℝ)
let δ : ℕ → ℕ → ℝ :=
  fun n m =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin r => |Y n m i - (u i * yex (x₀ + m * h_n n)
                                    + v i * h_n n * deriv yex (x₀ + m * h_n n))|)
```

(`Finset.univ_nonempty` requires `[Nonempty (Fin r)]`; if that's not
available, supply `r > 0` separately or default to a max via
`Finset.sup_le`. If `r = 0` the conclusion is trivially `True` because
all functions to `Fin 0` are equal; add a `match r with | 0 => …
| r' + 1 => …` outer split if needed.)

### Step 4 — Sorry-first scaffold

Open three sub-lemmas, all `private`, in `Section515.lean` immediately
above `aux_515D_output_tendsto`:

#### Sub-lemma A — Per-step recurrence (delegates to `localStepError_bound`)

```lean
/-- **Sub-lemma A for `aux_515D_output_tendsto`** — applying
`localStepError_bound` at each iteration step, the per-step error
`δ_n m` satisfies a discrete-Grönwall-shaped recurrence:
`δ_n (m+1) ≤ ‖V‖_∞ · δ_n m + α · h_n · δ_n m + β · h_n²` for explicit
constants `α, β` depending only on `M, L, M_bound`. -/
private theorem aux_515D_per_step_recurrence {s r : ℕ}
    (hs : 0 < s) (M : GeneralLinearMethod s r)
    (hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ : ℝ} {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    {M_bound : ℝ} (hM_nn : 0 ≤ M_bound)
    (hyex_M : ∀ t, |yex t| ≤ M_bound)
    (hyex'_LM : ∀ t, |deriv yex t| ≤ (L : ℝ) * M_bound)
    {u v : Fin r → ℝ}
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {x : ℝ} (hxx : x₀ < x)
    (h_norm : ‖((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|)‖ < 1)
    (Y : ℕ → ℕ → Fin r → ℝ) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
      ∀ n : ℕ, 0 < n → ∀ m : ℕ, m < n →
        let h_n : ℝ := (x - x₀) / (n : ℝ)
        let δ : ℕ → ℝ := fun k =>
          Finset.univ.sup' (sorry : (Finset.univ : Finset (Fin r)).Nonempty)
            (fun i : Fin r =>
              |Y n k i - (u i * yex (x₀ + k * h_n)
                          + v i * h_n * deriv yex (x₀ + k * h_n))|)
        δ (m + 1) ≤ (some_norm_V) * δ m + α * h_n * δ m + β * h_n^2 := by
  sorry
```

(Bracket the `Finset.univ.sup'` shape carefully — for `r = 0` this
needs special-casing; for `r ≥ 1` use the standard nonempty witness
`Finset.univ_nonempty` requiring `[Nonempty (Fin r)]`. Worker may
adjust the δ-spec to use `Σᵢ |…|` instead of `sup |…|` if that
matches `localStepError_bound`'s output more cleanly.)

#### Sub-lemma B — Closed-form Grönwall bound

```lean
/-- **Sub-lemma B for `aux_515D_output_tendsto`** — applying
`OpenMath.Chapter4.Section404.discrete_gronwall_exp_bound` to the
per-step recurrence, the diagonal error `δ_n n` is bounded by
`exp((α + ‖V‖) · (x - x₀)) · δ_n 0 + (β / (α + ‖V‖)) · h_n`. -/
private theorem aux_515D_gronwall_bound
    {α β : ℝ} (hα_nn : 0 ≤ α) (hβ_pos : 0 < β) :
    ∀ (h₀ : ℝ) (k : ℕ) (hh : 0 ≤ h₀) (hk : 0 < k)
      (δ : ℕ → ℝ) (a : ℝ),
      0 ≤ a → δ 0 ≤ a →
      (∀ m, 1 ≤ m → δ m ≤ a + α * h₀ * (k : ℝ) *
                              (∑ i ∈ Finset.Ico 1 m, δ i)
                            + β * h₀^2 * (m : ℝ)) →
      ∀ n, δ n ≤ Real.exp (α * (k : ℝ) * (n : ℝ) * h₀) * a
                  + (Real.exp (α * (k : ℝ) * (n : ℝ) * h₀) - 1)
                      * (β * h₀ / (α * (k : ℝ))) := by
  intro h₀ k hh hk δ a ha hδ0 hrec n
  exact OpenMath.Chapter4.Section404.discrete_gronwall_exp_bound
          δ a α β h₀ k ha hβ_pos.le.lt_of_ne
              (by simp [hα_nn]; sorry) hh hk hδ0 hrec n
```

(The signature is a thin re-statement of `discrete_gronwall_exp_bound`
specialized to the §515 setting. If it closes immediately by `exact
discrete_gronwall_exp_bound …`, this sub-lemma can be inlined
directly. Aristotle should crush this one.)

**Important**: re-shape sub-lemma A's recurrence to the
`u n ≤ a + b·h·k·(∑ i ∈ Ico 1 n, u i) + c·h²·n` shape that
`discrete_gronwall_exp_bound` consumes (see Section404.lean:1667).
The `‖V‖_∞ · δ m` term needs to be absorbed into the sum-form via
the iteration `‖V‖_∞ · δ m ≤ ‖V‖ · max_{i<m+1} δ i`, but the cleaner
move is to bundle `‖V‖_∞` into `α` (it only matters that `α` is a
bound on the linear-in-δ coefficient).

#### Sub-lemma C — Squeeze (close manually)

```lean
/-- **Sub-lemma C for `aux_515D_output_tendsto`** — given the
closed-form Grönwall bound and `δ_n 0 → 0` (from the starting
procedure), the diagonal error `δ_n n → 0` as `n → ∞`. -/
private theorem aux_515D_squeeze
    {α β : ℝ} (hα_nn : 0 ≤ α) (hβ_pos : 0 < β)
    (Δx : ℝ) (hΔx_pos : 0 < Δx)
    (δ : ℕ → ℝ) (δ0_seq : ℕ → ℝ)
    (hδ_nn : ∀ n, 0 ≤ δ n)
    (hδ0_nn : ∀ n, 0 ≤ δ0_seq n)
    (hδ0_tendsto : Filter.Tendsto δ0_seq Filter.atTop (nhds 0))
    (h_bound : ∀ n : ℕ, 0 < n →
      δ n ≤ Real.exp (α * Δx) * δ0_seq n
            + (Real.exp (α * Δx) - 1) * (β * (Δx / (n : ℝ)) / α)) :
    Filter.Tendsto δ Filter.atTop (nhds 0) := by
  sorry
```

This is the **squeeze** step. Hand-prove it. The argument:

1. The first term `Real.exp (α * Δx) * δ0_seq n → 0` because
   `δ0_seq → 0` (Tendsto.const_mul).
2. The second term `(Real.exp (α * Δx) - 1) * (β · Δx / n / α) → 0`
   because `1/n → 0` (`tendsto_one_div_atTop_nhds_zero_nat` plus
   `Tendsto.const_mul`).
3. Sum of the two bounds → 0; squeeze with `δ n ≥ 0` and the upper
   bound to conclude `δ n → 0`.

Use `squeeze_zero` (Mathlib name: `tendsto_of_tendsto_of_tendsto_of_le_of_le`
or `Filter.Tendsto.squeeze` — verify with `lean_local_search`).
Estimated 30–60 lines.

**This is the sub-lemma you commit to closing this cycle.** It's
the most independent (no `localStepError_bound` machinery needed,
just standard Tendsto plumbing) and the most certain to land.

### Step 5 — Compose into `aux_515D_output_tendsto`

Compose A + B + C inside `aux_515D_output_tendsto`'s body:

1. Extract `α, β` from sub-lemma A.
2. Show the recurrence on `δ_n m` for fixed `n` matches the shape
   sub-lemma B consumes.
3. Apply sub-lemma B at `m = n` to get the closed-form bound.
4. The `δ_n 0` term is bounded by the starting-procedure error
   `|φ(h_n) − u·y₀|`, which → 0 by `hφ`. Show `δ0_seq n → 0`.
5. Apply sub-lemma C to conclude `δ_n n → 0`.
6. Convert `δ_n n → 0` (sup-norm of components) to the pointwise
   `Y n n i → u i · yex x` claim — for each `i`, the i-th component
   bound is ≤ `δ_n n` and `v i · h_n · deriv yex (x₀ + n h_n) → 0`
   (since `h_n → 0`), so `Y n n i - u i · yex x → 0`. Use
   `tendsto_pi_nhds` to lift to function-level convergence.

If steps 1–6 don't all fit cleanly, **the body itself can stay
`sorry`**. The cycle deliverable is:
* Helper signature strengthened (Step 2).
* Three sub-lemmas defined as sorries (Steps 4 A/B/C).
* Sub-lemma C closed manually.
* Capstone signature updated to take the new hypotheses.
* `lake env lean OpenMath/Chapter5/Section515.lean` exits clean
  modulo the `sorry`s.

---

## Priority 2 — Faithfulness divergence documentation

Create `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
documenting the strengthened hypotheses on the capstone signature.
Cover:

* Each of the 5 new hypotheses (`hyex_C1`, `hM_nn`, `hyex_M`,
  `hyex'_LM`, `h_norm`).
* Why each is needed (delegate to `localStepError_bound`'s
  signature).
* Whether each is *derivable* from the original `IsConvergent`
  hypotheses on a compact interval (most are; deriving them is
  multi-cycle work and we defer).
* Cross-link to `is_convergent_strengthened.md` (LMM precedent),
  `glm_isconvergent_strengthened.md` (cycle 098), and cycle 107's
  `lem:515B` Frobenius strengthening.

Update `extraction/formalization_data/lean_status.json` for
`thm:515D`'s `notes` field with a brief mention of the
faithfulness divergences.

---

## Priority 3 — Pre-commit faithfulness checklist

Per CLAUDE.md "Pre-Commit Faithfulness Checklist":

1. **Tautology check**: none of the 3 new sub-lemma statements
   restate a hypothesis as a conclusion. Verify by reading each.
2. **Identity check**: sub-lemma B may close as `exact
   discrete_gronwall_exp_bound …`; that is *not* a vacuous
   theorem (it is genuine specialization with shape adaptation).
   Sub-lemma C is non-trivial (real Tendsto plumbing).
3. **Hypothesis strength check**: the 5 new hypotheses on
   `aux_515D_output_tendsto` are strictly necessary per Step 1's
   audit. The Frobenius `h_norm` is the only one Butcher does not
   write down explicitly; the rest are tacit in the textbook.
4. **Absent theorem check**: each promised sub-lemma must actually
   be stated in the file. After the cycle, run
   `Grep -P 'aux_515D_(per_step|gronwall|squeeze)'` to confirm.

---

## What NOT to do

* **Do NOT** open more than 3 sub-lemma sorries. The cycle 108
  regression (0→3 sorries with no closures) cost score=−2 and was
  reverted. Net 1→3 with one closure (sub-lemma C) is the floor.
* **Do NOT** try to derive `M_bound`, `ContDiff ℝ 1 yex` from the
  weak `_hyex_ode` hypothesis on a compact interval this cycle. The
  reduction is real (compact + continuous = bounded), but it adds
  ~150 LOC of compactness machinery and risks a multi-cycle slip.
  Surface them as hypotheses; document the divergence; move on.
* **Do NOT** try to inline-prove `localStepError_bound`'s
  consequences without invoking it as a black-box. The lemma takes
  20+ hypotheses; assembling them inside `aux_515D_per_step_recurrence`
  is the *point* of decomposing into sub-lemma A.
* **Do NOT** raise `maxHeartbeats` above 200000. If sub-lemma A's
  application of `localStepError_bound` is slow, decompose A
  further into helpers — but only inside cycle 113, not this cycle.
* **Do NOT** modify `OpenMath/Chapter5/MMatrix.lean` or any other
  file outside `OpenMath/Chapter5/Section515.lean` and the new
  issue file. The cycle scope is the §515 capstone; cross-file
  refactors break the "small decomposed wins" cadence.
* **Do NOT** introduce `axiom` or `constant` declarations to skip
  the missing hypotheses. CLAUDE.md is explicit on this. If a
  proof seems to need an axiom, file a blocker issue instead.
* **Do NOT** poll Aristotle more than once. Submit at the start;
  check once near the end (or after ~30 min); if results are not
  ready by then, defer to cycle 113.
* **Do NOT** edit `OpenMath/Chapter4/Section404.lean` to "specialize"
  `discrete_gronwall_exp_bound` — its signature already matches the
  §515 use case (cycles 050/064 confirmed). Just call it from
  sub-lemma B.
* **Do NOT** try Approach 3 from
  `aux_515D_stage_eventually_bounded_deferred.md` (Aristotle on
  M-matrix arguments). M-matrix is not the path here; we use
  `discrete_gronwall_exp_bound` directly for the Grönwall step.
* **Do NOT** revisit the closed cycle 111 `aux_515D_stage_eventually_bounded`
  proof. It is axiom-clean and the sum-norm argument is settled.

---

## Backup plan (if Priority 1 stalls past 90 min)

If sub-lemma C's squeeze takes longer than 60 min, OR if the helper
signature update in Step 2 cascades into compile failures elsewhere,
**de-scope to a *minimal* scaffold**:

1. Keep Step 2's signature update but **only on the helper**
   `aux_515D_output_tendsto`, not on the capstone. The capstone can
   then take *all* the new hypotheses as `(hyex_C1 hM_nn ...)`
   universally quantified `intro`s **inside** the body of the
   capstone, rather than on the capstone's signature, by deriving
   them from the IsConvergent hypotheses. *Wait — `IsConvergent`
   doesn't supply them.* So actually: keep the signature change
   and **revert the capstone to its current sorry-modulo-helper
   shape** by also marking `stable_consistent_isConvergent`'s body
   as `sorry`. Net 1 → 4 sorries (1 helper + 3 sub-lemmas). Bad,
   but recoverable next cycle.
2. Alternatively: open just **2 sub-lemmas** (A and B+C combined)
   instead of 3. This is messier mathematically but reduces sorry
   count to 1 → 3 without trying to close anything.
3. Worst case: leave `aux_515D_output_tendsto` untouched and write
   an issue file `.prover-state/issues/aux_515D_output_tendsto_blocker.md`
   explaining the hypothesis-strengthening obstruction, then file a
   plan for cycle 113. CLAUDE.md "minimum: decompose a sorry or
   write an issue" — option (3) satisfies the minimum.

---

## Definition of done

* `OpenMath/Chapter5/Section515.lean` compiles with at most 3 sorry
  occurrences (the unclosed sub-lemmas), at most 4 if backup plan
  step 1 is invoked.
* `aux_515D_squeeze` (sub-lemma C) is closed with axioms
  `[propext, Classical.choice, Quot.sound]` only (verify via
  `lean_verify`).
* `aux_515D_output_tendsto`'s body either composes A + B + C (no
  new sorries inside) or remains a single sorry referencing the
  three sub-lemmas in a comment.
* `stable_consistent_isConvergent` capstone takes the new
  faithfulness-divergent hypotheses; the capstone body remains the
  cycle 111 shape with no new sorries inside.
* `aux_515D_output_tendsto_hypotheses.md` issue file exists in
  `.prover-state/issues/` documenting the divergence.
* `lean_status.json` `thm:515D` row's `notes` field updated.
* Aristotle batch submitted with project IDs noted.
* Pre-commit faithfulness checklist passed.
* `lake env lean OpenMath/Chapter5/Section515.lean` exits with at
  most 3 (or 4 if backup) sorry warnings, no errors.
* `git diff --stat` shows changes only to:
  - `OpenMath/Chapter5/Section515.lean`
  - `extraction/formalization_data/lean_status.json`
  - `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` (new)
  - `.prover-state/aristotle_submissions/cycle_112/` (new)
  - `.prover-state/task_results/cycle_112.md` (new)
  - `.prover-state/strategy.md` (this file's predecessor — auto-rotated)
  - `.prover-state/heartbeat.json` and `history.jsonl` (auto)

---

## Scoring rubric (worker self-check before commit)

* +2: 3-sub-lemma scaffold opened, sub-lemma C closed clean,
  capstone signature updated faithfully, axioms clean, issue
  file written, Aristotle in flight.
* +1: 3-sub-lemma scaffold opened, capstone signature updated,
  axioms clean, but sub-lemma C blocked / partially proved
  (sorries retained but body fully written).
* 0: minimal scaffold (backup plan step 2) opened, no closures.
* −1: scaffold opened with > 4 sorries, or compile failures
  introduced outside Section515.lean.
* −2: scaffold opened with closures undocumented, or
  faithfulness divergences not surfaced in an issue file.

Aim for +2; settle for +1; treat 0 as a graceful retreat.
