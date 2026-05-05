# Cycle 114 — Strategy

## TL;DR

Compose the body of `aux_515D_output_tendsto`
(`OpenMath/Chapter5/Section515.lean:1648–1671`, the lone sorry in
`OpenMath/`) by chaining the three sub-lemmas A, B, C (all closed
cycles 112/113) plus `GeneralLinearMethod.localStepError_bound`
(lem:515B, `Section515.lean:1183`). Strengthen the helper's
signature with 5 hypotheses already required by
`localStepError_bound`. Propagate the strengthening to the
capstone `stable_consistent_isConvergent` (line 2119) and to the
GLM `IsConvergent` predicate in `OpenMath/Chapter5/Section512.lean`
(faithfulness divergence, mirroring LMM cycle 068's
`is_convergent_strengthened.md`). Goal: sorry count `1 → 0`.

## Aristotle status

**No pending results.** Cycle 113's two Aristotle batches
(sub-lemmas A and B) returned COMPLETE last cycle and have been
incorporated. **Do not submit any new Aristotle batches in
cycle 114** — the body composition is structural plumbing, not the
kind of premise-search task Aristotle excels at, and the per-step
sub-pieces are already cited Lean lemmas. Skip Priority 0.

## Priority 1 — Strengthen `IsConvergent` predicate (Section512.lean)

Edit `OpenMath/Chapter5/Section512.lean::GeneralLinearMethod.IsConvergent`
(currently lines 150–171). Add the **5 strengthening hypotheses**
after the existing `hyex_x₀ + hyex_ode` clauses, BEFORE the
`∃ u : Fin r → ℝ` part. Concretely, insert:

```lean
∀ M_bound : ℝ, 0 ≤ M_bound →
  ContDiff ℝ 1 yex →
  (∀ t, |yex t| ≤ M_bound) →
  (∀ t, |deriv yex t| ≤ (L : ℝ) * M_bound) →
  ...
∀ x : ℝ, x₀ < x →
  ‖((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|)‖ < 1 →
  ...
```

The `h_norm` hypothesis is `x`-dependent so it must sit AFTER the
`∀ x : ℝ, x₀ < x →` quantifier (where `x` is bound). The other
4 hypotheses are global on `f`/`yex`. `M` is already in scope at
the outer `∀ M : GeneralLinearMethod` level — fine.

Reference shape: `Section515.lean:1186–1221` (the `localStepError_bound`
signature). Copy hypothesis names verbatim (`hM_nn`, `hyex_C1`,
`hyex_M`, `hyex'_LM`, `h_norm`) for legibility.

**Faithfulness divergence**: this strengthens Butcher's textbook
`def:512A`. The divergence MUST be documented by extending
`.prover-state/issues/glm_isconvergent_strengthened.md` with a
new "Cycle 114 strengthening" section listing the 5 new
hypotheses, each with a per-hypothesis derivability note copied
verbatim from `aux_515D_output_tendsto_hypotheses.md` §"Faithfulness
analysis". The precedent is LMM cycle 068's
`is_convergent_strengthened.md`.

## Priority 2 — Propagate strengthening to §513 and §514

`thm:513A` (`OpenMath/Chapter5/Section513.lean`) and `thm:514A`
(`OpenMath/Chapter5/Section514.lean`) consume `IsConvergent` as a
hypothesis. Their proofs `intro` all the IsConvergent quantifiers.
After Priority 1, these proofs need to additionally bind the new
hypotheses (typically as anonymous underscores since the §513/§514
proofs do not USE the strengthening — they only use the conclusion).

Concretely, locate every `intro f L hf_lip x₀ y₀ yex hyex_x₀ hyex_ode`
in `Section513.lean` and `Section514.lean` and extend to
`intro f L hf_lip x₀ y₀ yex hyex_x₀ hyex_ode M_bound hM_nn hyex_C1 hyex_M hyex'_LM`,
then for the `x`-dependent `h_norm` extend the inner `intro x hxx`
to `intro x hxx h_norm`. Adjust `Tendsto`/`refine`/`obtain`
signatures accordingly.

If §513 / §514 use a different intro pattern (e.g. `obtain` on the
`∃ u`), trace through and add the new hypotheses at the right
binding depth. Verify by `lake env lean OpenMath/Chapter5/Section513.lean`
and likewise §514. Both should compile clean (no proof body
changes — the new hypotheses simply become unused bindings).

If §513 / §514 *construct* a fake `IsConvergent` to derive a
contradiction (e.g. cycle 093's `convergent_isStable` builds an
arbitrary IVP), the proofs WILL need to supply the 5 hypotheses
to their constructed `IsConvergent` instance — supply them with
the trivial-IVP values (`f := fun _ => 0`, so `M_bound := 0`,
`yex := fun _ => y₀`, `ContDiff ℝ 1 yex` is `contDiff_const`,
etc.). Audit both files carefully before claiming the cascade is
trivial.

## Priority 3 — Strengthen `aux_515D_output_tendsto` signature

Edit `Section515.lean:1648–1670` to add the 5 hypotheses:

```lean
private theorem aux_515D_output_tendsto {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    -- NEW (cycle 114):
    {M_bound : ℝ} (hM_nn : 0 ≤ M_bound)
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_M : ∀ t, |yex t| ≤ M_bound)
    (hyex'_LM : ∀ t, |deriv yex t| ≤ (L : ℝ) * M_bound)
    -- (existing) consistency packaging:
    {u v : Fin r → ℝ}
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {φ : ℝ → Fin r → ℝ}
    (hφ : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                          (nhds 0) (nhds (u i * y₀)))
    {x : ℝ} (hxx : x₀ < x)
    -- NEW (cycle 114): Frobenius norm contraction at chosen step.
    (h_norm : ‖((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|)‖ < 1)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i = ...)) :
    Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
        (nhds (fun i => u i * yex x))
```

Drop the leading underscores on the existing hypotheses since they
will be USED in the cycle 114 body (per cycle 113's "Discovery" note
about scaffolds leaving the underscores in place).

## Priority 4 — Compose the body of `aux_515D_output_tendsto`

This is the load-bearing work. The composition must:

### Step 1 — Define the per-step error sequence

Use the **sum norm** `δ : ℕ → ℕ → ℝ` defined by
```lean
let h_n : ℕ → ℝ := fun n => (x - x₀) / (n : ℝ)
let xnm : ℕ → ℕ → ℝ := fun n m => x₀ + (m : ℝ) * h_n n
let δ : ℕ → ℕ → ℝ := fun n m => ∑ i, |Y n m i - (u i * yex (xnm n m)
                                  + v i * h_n n * deriv yex (xnm n m))|
```

(Sum-norm is preferred over max-norm because:
* The `Finset.sum_le_sum` plumbing matches sub-lemma A's recurrence
  shape directly without `Finset.sup'` boilerplate.
* Cycle 111's `aux_515D_stage_eventually_bounded` already uses the
  sum-norm convention, so callers downstream will not face a basis
  mismatch.
* `δ_max` in `localStepError_bound` is a *bound* on each `|δ k|`,
  not an exact maximum, so sum-norm bounds are a valid upper
  bound on `δ_max` and the sub-lemma B Grönwall input shape works
  cleanly.)

### Step 2 — Per-step recurrence via `localStepError_bound`

For each `n ≥ 1`, applying `localStepError_bound` at micro-step
`m → m + 1` with:
* `h := h_n n`, `h₀ := x - x₀` (so `h ≤ h₀` is `h_n ≤ x - x₀`,
  which holds for `n ≥ 1` since `h_n n = (x-x₀)/n ≤ (x-x₀)`).
* `M_bound, L` from the strengthened hypotheses.
* `c := M.glmAbscissae v` (existing helper).
* `ell_U`, `phi_A` constructed by Banach-perturbation —
  USE `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
  (cycle 106 helper, `OpenMath/Chapter5/MMatrix.lean`) to invert
  `(I − h₀ L |A|)` and define `ell_U := (I − h₀ L |A|)⁻¹ · 𝟙_U`,
  `phi_A := (I − h₀ L |A|)⁻¹ · 𝟙_A`. The `_hellU_eq` and
  `_hphiA_eq` side conditions become *defining equations* of
  these constructions.
* `α := L · max_i (∑_j |B_{ij}| ell_U_j)`, `β := L² · M_bound · ...`
  (per `_hα_def`, `_hβ_def`).
* `δ_max := δ n m` (the previous-step error).

This yields `K i` such that
`|K i| ≤ α · h_n · δ n m + β · h_n^2`. From this, the per-step
recurrence:

```
δ n (m+1) = ∑_i |Y n (m+1) i - exact_i(x_{n,m+1})|
         ≤ ∑_i (|∑_j V_{ij} · (Y n m j - exact_j(x_{n,m}))| + |K_i|)
         ≤ ‖V‖_{1→1} · δ n m + s · (α · h_n · δ n m + β · h_n^2)
       = (V_norm + s · α · h_n) · δ n m + s · β · h_n^2
```

where `V_norm := ‖V‖_{1→1} = max_j ∑_i |V_{ij}|`. This matches
sub-lemma A's recurrence shape with
`V_norm_A := V_norm`, `α_A := s · α`, `β_A := s · β`.

(The `‖V‖_{1→1}` exists by stability — `M.IsStable` gives
power-boundedness of `V`, so a finite operator norm bound exists;
extract it via `M.stabilityBound` if defined, or use
`Matrix.opNorm_le_iff` from Mathlib.)

### Step 3 — Apply sub-lemma A

Invoke `aux_515D_per_step_recurrence` (line 1497) with the
recurrence from Step 2 to get
```
δ n n ≤ (V_norm + s·α·h_n)^n · δ n 0
       + s·β·h_n^2 · ∑_{k<n} (V_norm + s·α·h_n)^k.
```

### Step 4 — Translate to Grönwall sum-form for sub-lemma B

Sub-lemma B (`aux_515D_gronwall_bound`, line 1555) consumes a
sum-form recurrence
```
u m ≤ a + α' · h · (∑_{i ∈ Ico 1 m} u i) + β' · h^2 · m.
```

PREFERRED: skip Step 3's closed form and apply sub-lemma B
*directly* to the per-step recurrence (fewer rewrites). Concretely,
summing the per-step recurrence:

```
δ n m ≤ a + α' · h_n · (∑_{i ∈ Ico 1 m} δ n i) + β' · h_n^2 · m
```
where `a := V_norm^n · δ n 0` (or just `δ n 0` if `V_norm = 1`,
which is the textbook stability case),
`α' := s · α`, `β' := s · β`. Then sub-lemma B gives:

```
δ n n ≤ exp(α' · n · h_n) · a + (exp(α' · n · h_n) - 1) · (β' · h_n / α').
```

Note `α' · n · h_n = α' · (x - x₀)` is a constant (independent of
n). So the exp-factor `exp(α' · (x - x₀))` is a uniform constant.

### Step 5 — Apply sub-lemma C (squeeze)

`aux_515D_squeeze` (line 1585) consumes the bound from Step 4 with
`Δx := x - x₀`, `δ0_seq n := δ n 0`. Verify:
* `δ n 0 → 0`: this is the `hφ` hypothesis applied to the
  starting procedure. Concretely, `Y n 0 = φ (h_n n)` and
  `φ (h_n n) i → u_i · y₀ = u_i · yex(x₀)` as `n → ∞`, so
  `δ n 0 → 0` by continuity of subtraction + sum.
* `α' > 0`: `α' = s · α = s · L · max_i (∑_j |B_{ij}| ell_U_j)`.
  When `L = 0`, `α' = 0` and sub-lemma C's `0 < α` hypothesis fails
  — handle the `L = 0` degenerate case separately (it's a trivial
  ODE; `δ n m = 0` at all levels via `f` constant).

Conclude `δ n n → 0`.

### Step 6 — Lift to function-level convergence

`δ n n → 0` (sum-norm) implies `Y n n i - exact_i(x) → 0` for
each `i` since each summand is `≤ δ n n`. The exact target is
`u_i · yex(x) + v_i · h_n · deriv yex(x)`, but the second term
`v_i · h_n · deriv yex(x) → 0` since `h_n → 0` (use
`tendsto_one_div_atTop_nhds_zero_nat` lifted to ℝ via
`Tendsto.comp`). So `Y n n i → u_i · yex(x)` for each `i`,
and the function-level limit `Y n n → fun i => u_i · yex(x)`
follows by `tendsto_pi_nhds`.

## Priority 5 — Update capstone `stable_consistent_isConvergent`

After Priority 1, the capstone (`Section515.lean:2119`) destructures
`IsConvergent`'s quantifiers. Add the new intros to bind the 5
strengthening hypotheses. Then forward them to
`aux_515D_output_tendsto` and `aux_515D_stage_tendsto` calls.

`aux_515D_stage_tendsto` (line 1989) DOES NOT need to be
strengthened — it consumes the OUTPUT-side `h_output` as a
hypothesis but does NOT call `localStepError_bound` directly
(per cycle 110/111 closure). Confirm by reading its signature; if
it does need strengthening, mirror Priority 3.

The capstone signature itself remains unchanged; only the proof
body (the `intro` line and the `aux_515D_output_tendsto` call) changes.

## Priority 6 — Verify and document

1. `lake env lean OpenMath/Chapter5/Section515.lean` — should exit
   with **0 sorries, 0 errors**.
2. `lake env lean OpenMath/Chapter5/Section513.lean` — clean.
3. `lake env lean OpenMath/Chapter5/Section514.lean` — clean.
4. `lake env lean OpenMath/Chapter5/Section512.lean` — clean.
5. `lake build OpenMath.Chapter5.Section515` to refresh `.olean`
   cache — clean.
6. `#print axioms GeneralLinearMethod.stable_consistent_isConvergent`
   should show only `[propext, Classical.choice, Quot.sound]`.
7. Update `extraction/formalization_data/lean_status.json`:
   `thm:515D` row → `closed`, with citation to
   `OpenMath/Chapter5/Section515.lean:2119` and
   `glm_isconvergent_strengthened.md`.
8. Update `plan.md`: change `[~] thm:515D` to `[x] thm:515D` with
   axiom-clean note, mirroring the `lem:515A`/`lem:515B` rows.
9. Append a "Cycle 114 closure" section to
   `aux_515D_output_tendsto_hypotheses.md` documenting the
   strengthening landed.

## What NOT to try (failed approaches from history)

* **Do NOT submit the body composition to Aristotle.** The cycle
  113 sub-lemmas (A, B) closed via Aristotle because they were
  abstract scalar inequalities. The composition is GLM-specific
  plumbing with inline `localStepError_bound` invocations across
  multiple iteration depths — Aristotle has historically struggled
  on similar §515 plumbing (cycles 094, 096, 103). Hand-write the
  composition.
* **Do NOT inline the `localStepError_bound` proof.** It is the
  cycle-104 lem:515B closure; treat it as a black-box helper.
  Do NOT re-derive its conclusion from `localStageError_bound_a`
  and `localStageError_bound_b` directly — that re-derivation is
  exactly what cycle 104 packaged into `localStepError_bound`.
* **Do NOT use max-norm for `δ`.** Per Step 1 above, sum-norm
  matches sub-lemma A and cycle 111's existing convention. The
  cycle 113 task results' "either/or" flexibility is resolved
  here: pick sum-norm.
* **Do NOT raise `maxHeartbeats`.** If a single tactic block is
  too slow, decompose into more `have` clauses; this is the
  CLAUDE.md rule.
* **Do NOT introduce `axiom`/`constant`** for any of the 5
  strengthening hypotheses. They go into `IsConvergent`'s
  signature as proper hypotheses (faithfulness divergence,
  documented).
* **Do NOT skip Priority 2 (the §513/§514 cascade).** Even if
  it appears the proofs don't need to change, the new
  hypotheses MUST be threaded through `intro` so the proofs
  type-check after Priority 1.
* **Do NOT modify `localStepError_bound`'s signature.** Its
  current form is what the helper consumes; cycle 107 has
  already strengthened it with the Frobenius `_h_norm`
  hypothesis. The cycle 114 work is downstream of that
  strengthening — propagate it through, don't re-touch it.
* **Do NOT touch `aux_515D_stage_tendsto` or
  `aux_515D_stage_eventually_bounded`** unless Priority 5
  reveals a propagation gap. Per cycle 110/111 closures, both
  consume the OUTPUT-side limit symbolically and should be
  unaffected.
* **Do NOT use `Finset.sum_le_sum_nbij'`** for any sum-reindexing
  step — it does not exist in Mathlib (cycle 050 dead end).
  Use `← Finset.sum_image hinj` + `Finset.sum_le_sum_of_subset_of_nonneg`
  instead.
* **Do NOT use `add_le_add_left hA c`** to produce `a + c ≤ b + c`
  — it produces `c + a ≤ c + b`. Use `linarith [hA]` or `gcongr`
  for monotone-addition with a left constant.

## Fallback if scope blows out

Cycle 114 has high scope. If after ~3 hours the body composition
is not landing cleanly, FALL BACK to a smaller deliverable:

**Fallback option 1 (signature strengthening only)**: do
Priorities 1, 2, 3, 5 (the cascade), leave Priority 4's body
composition as `sorry` for cycle 115. Sorry count: 1 → 1 (same
location, but signature now matches `localStepError_bound`'s
shape, removing the cycle-115 friction). Score: probably +1.

**Fallback option 2 (defer cascade, deliver only Step 2 of
Priority 4)**: do NOT touch `IsConvergent` or §513/§514. Keep the
helper signature unchanged, but ADD a private wrapper
`aux_515D_output_tendsto_strengthened` taking the 5 extra
hypotheses, prove that wrapper using the composition above, and
file an issue documenting the cycle-115 cascade obligation. Sorry
count: 1 → 1 (the original `aux_515D_output_tendsto` body still
sorry, but a strengthened parallel exists). NOT recommended — it
adds dead code unless cycle 115 lands the cascade.

**Recommended**: try the full cycle 114 plan; fall back to
option 1 if needed. Do NOT attempt option 2.

## Scoring rubric

* +2: full closure (sorry count 1 → 0), `thm:515D` row of
  `lean_status.json` flips to `closed`, axioms clean.
* +1: signature strengthening lands (Priorities 1, 2, 3, 5) but
  Priority 4 body composition deferred to cycle 115.
* 0: no progress on the §515 capstone, but a substantive
  helper-side advance (e.g. δ definition + per-step recurrence
  scaffolded with sub-`sorry`s).
* −1 or worse: REGRESSION (sorry count goes up, or §513/§514
  break, or `lake build` fails).

## Worker checklist

Before committing:

- [ ] Sorry count delta verified by
      grep/rg over `OpenMath/` for `sorry` (excluding comments).
- [ ] `lake env lean OpenMath/Chapter5/Section515.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter5/Section513.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter5/Section514.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter5/Section512.lean` exits 0.
- [ ] `#print axioms GeneralLinearMethod.stable_consistent_isConvergent`
      shows only `[propext, Classical.choice, Quot.sound]`.
- [ ] `glm_isconvergent_strengthened.md` extended with cycle 114
      strengthening note.
- [ ] `aux_515D_output_tendsto_hypotheses.md` extended with cycle
      114 closure note.
- [ ] `lean_status.json` thm:515D row updated.
- [ ] `plan.md` thm:515D row flipped to `[x]`.
- [ ] `cycle_114.md` task results written, including:
      - faithfulness check for the IsConvergent strengthening
      - dead ends (any tactic blocks that needed >2 attempts)
      - Priority 4 composition outline (whichever steps landed)

## References

* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` —
  precise hypothesis list and per-hypothesis derivability analysis.
* `.prover-state/issues/glm_isconvergent_strengthened.md` —
  cycle 098 precedent for `IsConvergent` strengthening.
* `.prover-state/issues/is_convergent_strengthened.md` — cycle 068
  LMM analog (the canonical pattern for this kind of cascade).
* `OpenMath/Chapter5/Section515.lean:1183` —
  `GeneralLinearMethod.localStepError_bound` (lem:515B), the
  black-box helper.
* `OpenMath/Chapter5/Section515.lean:1497` — sub-lemma A.
* `OpenMath/Chapter5/Section515.lean:1555` — sub-lemma B.
* `OpenMath/Chapter5/Section515.lean:1585` — sub-lemma C.
* `OpenMath/Chapter5/MMatrix.lean::Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
  — the M-matrix inversion needed for `ell_U`/`phi_A` construction
  in Step 2.
* `OpenMath/Chapter4/Section404.lean:1663` —
  `discrete_gronwall_exp_bound` (the parent of sub-lemma B; for
  reference if Step 4's translation hits friction).
