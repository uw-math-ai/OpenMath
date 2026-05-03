# Cycle 108 Strategy — Open `thm:515D` (Stability + Consistency ⇒ Convergence) sorry-first

## Status snapshot

* **Sorry count**: 0 in `OpenMath/`. Cycle 107 closed the last
  outstanding `sorry` (`aux_515B_eta_contraction`). `lem:515B` is now
  fully formalized with clean axioms.
* **Progress**: 65/175 entities. The natural Chapter-5 next step is
  `thm:515D` (the §515 capstone — stability + consistency ⇒ convergence
  for general linear methods).
* **Aristotle**: project `4688b630-…` is still parked at >50h, ~6%
  (cycle-103 η-contraction batch — now obsolete; lem:515B is closed).

## Primary target — `thm:515D` (sorry-first scaffold)

Per `extraction/formalization_data/entities/thm_515D.json`:

> **Theorem 515D.** A stable and consistent general linear method is
> convergent. (Butcher 2008 p. 417)

The textbook proof (the brief paragraph at the end of lem:515B's proof,
p. 414) reads:

> "To complete the argument that stability and consistency imply
> convergence, we estimate the global error in the computation of `y(x)`
> by carrying out `n` steps from an initial value `y(x_0)` using a
> stepsize equal to `h = (x − x_0)/n`."

Concretely, this means: iterate the per-step bound from `lem:515B`
across `n` steps, apply discrete-Grönwall to absorb the linear-in-error
term into an exponential, then take `h → 0` (i.e. `n → ∞`).

The Chapter-4 LMM analog
`LinearMultistepMethod.stable_consistent_isConvergent` (cycle 068,
`OpenMath/Chapter4/Section404.lean:5455`) is a directly-relevant
template. Both Chapter 4 and Chapter 5 use the same recipe:
per-step error bound → discrete-Grönwall → squeeze to zero as `h → 0`.

### Goal for cycle 108

**One file edit, ≤ 2 sub-lemma sorries** (matches the cycle-103
"sorry-first opening" ceiling, NOT the cycle-103 reverted shape):

1. The main theorem `GeneralLinearMethod.stable_consistent_isConvergent`
   stated and `sorry`'d (the body factors through the sub-lemmas).
2. **At most two** named private sub-lemmas introduced as `sorry`'s.
3. **No new top-level definitions** unless absolutely required for the
   statement of `thm:515D` itself; the IsConvergent / IsStable /
   IsConsistent / IsGLMSolution definitions all already exist.

### Where the work lands

Append at the **end of `OpenMath/Chapter5/Section515.lean`** (after the
existing `localStepError_bound` at line 1183). Do NOT create a new file
`Section515D.lean` — `thm:515D` is the §515 capstone and naturally
belongs in the same file as its lem:515B prerequisite.

### Concrete shape of the main theorem

The signature must match the existing `IsConvergent` predicate
(`Section512.lean:150`, after the cycle-098 stage-limit strengthening).
That predicate takes:

* a Lipschitz autonomous RHS `f : ℝ → ℝ` with `LipschitzWith L f`;
* an initial-value condition `yex x₀ = y₀` plus
  `∀ x, HasDerivAt yex (f (yex x)) x`;
* a starting procedure `φ : ℝ → Fin r → ℝ` with
  `∀ i, Tendsto (fun h => φ h i) (nhds 0) (nhds (u i * y₀))`;
* a target time `x > x₀`;
* the GLM iteration `Y : ℕ → ℕ → Fin r → ℝ` and stage sequence
  `Y_int : ℕ → Fin s → ℝ` with the per-step properties (start
  condition + `IsGLMSolution` + stage equation);
* and concludes `Y n n → (fun i => u i * yex x)` AND
  `Y_int n → (fun _ => yex x)`.

The output preconsistency vector `u` should come from `IsConsistent`
via `IsConsistent.isPreconsistent`. The proof skeleton should look
like:

```lean
/-- **Theorem 515D** (Butcher 2008, p. 417) — A stable and consistent
general linear method is convergent. -/
theorem GeneralLinearMethod.stable_consistent_isConvergent
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hStab : M.IsStable) (hCons : M.IsConsistent) :
    M.IsConvergent := by
  -- Unfold IsConvergent and intro all named hypotheses
  intro f L hf_lip x₀ y₀ yex hyex_x₀ hyex_ode
  -- Extract the preconsistency / consistency witnesses
  obtain ⟨u, v, ⟨hVu, hUu⟩, hCons_eq⟩ := hCons
  refine ⟨u, ?_, ?_⟩
  · -- u ≠ 0  — derive from U·u = 𝟙 (since 𝟙 ≠ 0)
    -- Inline trivial: assume u = 0, then U·0 = 0 ≠ 𝟙. Done.
    intro hu0
    have h1 : (M.U *ᵥ u : Fin s → ℝ) = 0 := by rw [hu0]; simp
    rw [hUu] at h1
    -- 𝟙 = 0 in Fin s → ℝ, but 𝟙 0 = 1 ≠ 0 (if s > 0); for s = 0
    -- vacuous so still fine.
    sorry  -- worker may inline this fully; if it fits in 1-2 lines
            -- keep it inline (no extra sub-lemma slot needed)
  · intro φ hφ x hxx Y Y_int hY_props
    refine ⟨?_, ?_⟩
    · -- Output convergence: Y n n → u · yex x
      exact aux_515D_output_tendsto M hStab hCons hf_lip hyex_x₀ hyex_ode
              hφ hxx hY_props u v hVu hUu hCons_eq  -- ARGS to be filled
    · -- Stage convergence: Y_int n → yex x
      exact aux_515D_stage_tendsto M hStab hCons hf_lip hyex_x₀ hyex_ode
              hφ hxx hY_props u hUu  -- ARGS to be filled
```

The two `sorry`'s under sub-lemmas are the cycle's deferred work; the
`u ≠ 0` clause should fit inline (no sub-lemma slot needed). If the
inline `u ≠ 0` proof exceeds 5 lines, defer it as a third trivial
helper `aux_515D_u_ne_zero`, but keep it inside the ≤ 2 sub-lemma
budget if at all possible.

### Approach (specific, do these in order)

**Step A — Read the data.** Re-read
`extraction/formalization_data/entities/thm_515D.json` and the §515
"Stability and consistency imply convergence" section from
`extraction/raw_text/ch05.txt` to nail down the textbook hypotheses.
The extraction's `proof_text` is empty, so the textbook proof is just
the brief gloss at the end of lem:515B's proof.

**Step B — Read the LMM template.** Skim
`OpenMath/Chapter4/Section404.lean:5455-5800` (the `LinearMultistepMethod.
stable_consistent_isConvergent` proof) to see the canonical scaffold:
it intro's the IsConvergent fields, extracts a Θ-bound from stability
via `theta_bounded_of_isStable`, applies `discrete_gronwall_exp_bound`
to a recurrence built from per-step error bounds, then closes with
explicit-`h` squeeze helpers (`globalError_outer_squeeze_*`). The same
recipe should work for GLMs, with `localStepError_bound` (the closed
cycle-107 lemma) playing the per-step role.

**Step C — Write the scaffold.** At the end of
`OpenMath/Chapter5/Section515.lean`:

1. Add the two private sub-lemma signatures with `sorry` proofs.
2. Add the main theorem, factoring the two `sorry`'s through the
   sub-lemmas (so the main theorem's body has zero direct `sorry`).
3. Verify `lake env lean OpenMath/Chapter5/Section515.lean` compiles
   without errors.
4. Run `lake build OpenMath.Chapter5.Section515` to refresh the
   `.olean` cache (cycle-072 lesson: `lake env lean` does NOT update
   the cache, leading to false-positive `sorryAx` reports otherwise).
5. Verify `#print axioms aux_515D_output_tendsto` and the analog for
   `aux_515D_stage_tendsto` show `[propext, Classical.choice,
   Quot.sound, sorryAx]` (the `sorryAx` is expected — it's the
   deferred sub-lemma proofs). The main theorem
   `stable_consistent_isConvergent` should also show `sorryAx`
   transitively.

**Step D — Submit Aristotle batch on the two sub-lemmas.**

Once the scaffold compiles, batch-submit both sub-lemma `sorry`'s to
Aristotle. Use `mcp__aristotle__submit_directory` with both stub files
in `.prover-state/aristotle_submissions/cycle_108/`:

* `aux_515D_output_tendsto.lean` — opens `OpenMath.Chapter5.Section515`,
  re-states the helper as `theorem ... := sorry`, includes only the
  imports strictly needed (`Mathlib`, `OpenMath.Chapter5.Section515`).
* `aux_515D_stage_tendsto.lean` — same pattern.

Keep the submission files lean (no extraneous imports). Aristotle has
historically struggled with iteration / squeeze arguments; do NOT block
on the response. Per CLAUDE.md, sleep 30 min then check ONCE.

**Step E — Cancel the dead Aristotle project.** Optional but
recommended (planner suggested it in cycle 107):

Call `mcp__aristotle__cancel_project` with id
`4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`. This was the cycle-103
η-contraction batch; lem:515B is now closed manually, so the project's
output is irrelevant. Cancelling frees an Aristotle slot for cycle 108's
new submissions.

**Step F — Update plan.md and lean_status.json.**

* `plan.md`: change `[ ] thm:515D` (under Chapter 5) to `[~] thm:515D`
  with a brief status note (`scaffold + 2 sub-lemma sorries opened
  cycle 108 in OpenMath/Chapter5/Section515.lean`). Update the progress
  count in the header (65 → still 65; partial doesn't count toward
  formalized).
* `extraction/formalization_data/lean_status.json`: bump `thm:515D`
  status from `unformalized` to `partial` and point its `lean_file`
  to `OpenMath/Chapter5/Section515.lean` plus `lean_symbol` to
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`.

**Step G — Pre-commit faithfulness check.**

This cycle introduces ONE new theorem signature plus ≤ 2 private
sub-lemma signatures. Run the CLAUDE.md faithfulness checklist:

* The main theorem's hypothesis list (`IsStable` + `IsConsistent`) and
  conclusion (`IsConvergent`) match the textbook statement verbatim
  ("A stable and consistent general linear method is convergent").
* No new `def`/`structure` is being introduced — `IsConvergent`,
  `IsStable`, `IsConsistent` all exist already.
* The two sub-lemmas are *internal helpers*, not Butcher entities;
  document this in their docstrings (label as "Sub-lemma for thm:515D").
* The `sorry`'s are real (not promised-but-absent) — they live in the
  proof bodies of the two sub-lemmas, NOT inside the main theorem.
* Tautology check: the main theorem's body should NOT be `exact hCons`
  or any single-hypothesis closer. The body should `obtain ⟨u, v, …⟩
  := hCons; refine ⟨u, _, _⟩; …` and dispatch to the helpers.

**Step H — Write the cycle-108 task results.**

Per CLAUDE.md template, write `.prover-state/task_results/cycle_108.md`
documenting: the scaffold landed, the two sorries are intentional,
where they live, what each is supposed to do, and what the cycle-109
worker should attack first (recommendation: stage-tendsto first, since
it's the easier of the two and unlocks downstream §515 cleanup).

**Step I — Commit and push.**

```text
Cycle 108 — open thm:515D scaffold (2 sub-lemma sorries, +2 sorries)
```

Verify `git status` shows the commit landed and pushed before
finishing. Cycle-008/035/071 had repeated commit-not-reaching-repo
failures; check `git rev-parse HEAD == git rev-parse origin/Main/Experiments`
explicitly in the task-results file.

## Sub-lemma signature templates (use these as starting points)

These are SUGGESTIONS — the worker should adjust the signatures to
match the actual `IsConvergent` shape. The key constraint: *they must
close the two `sorry`'s in the main theorem with concrete arguments*.

```lean
/-- Sub-lemma for `thm:515D`: under stability + consistency,
the GLM iteration's output sequence converges to `u · yex(x)`.

Proof outline (deferred to cycles 110+): iterate `localStepError_bound`
across n steps, get a discrete-Grönwall recurrence in
`max_i |Y n m i - exact_value|`, apply `discrete_gronwall_exp_bound`
(or its GLM analog) to absorb the linear-in-error term, then squeeze
as `h = (x - x₀)/n → 0`. -/
private theorem aux_515D_output_tendsto {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (hStab : M.IsStable) (hCons : M.IsConsistent)
    -- ... mirror IsConvergent's intro'd hypotheses ...
    (u v : Fin r → ℝ)
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    -- ... φ, x, Y, Y_int, hY_props ...
    :
    Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
        (nhds (fun i => u i * yex x)) := by
  sorry  -- main work: per-step bound iteration + discrete Grönwall + squeeze

/-- Sub-lemma for `thm:515D`: stage convergence follows from output
convergence via the stage equation `Y_int n i = h·(A·f(Y_int))_i +
(U·Y n n)_i`.

Proof outline (deferred to cycle 109): in the stage equation
`Y_int n i = h_n·∑_j A_ij f(Y_int n j) + ∑_j U_ij Y n n j`, take
n → ∞: the first summand vanishes (h_n → 0 and f bounded along
trajectory), the second tends to `(U·u·yex(x))_i = (𝟙·yex(x))_i =
yex(x)` since `U·u = 𝟙` and `Y n n → u·yex(x)`. -/
private theorem aux_515D_stage_tendsto {s r : ℕ}
    (M : GeneralLinearMethod s r)
    -- ... mirror IsConvergent's intro'd hypotheses ...
    (u : Fin r → ℝ) (hUu : M.U *ᵥ u = (fun _ => 1))
    -- ... φ, x, Y, Y_int, hY_props ...
    (h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
                    (nhds (fun i => u i * yex x))) :
    Filter.Tendsto Y_int Filter.atTop (nhds (fun _ => yex x)) := by
  sorry  -- stage equation + h → 0 limit + apply U·u = 𝟙
```

## What NOT to do (explicit failed-approach blocklist)

* **Do NOT** try to prove either sub-lemma in cycle 108. The cycle-100
  / cycle-074 / cycle-079 precedent for sorry-first openings is
  scaffold + ≤ 2 sub-lemma sorries; close them in cycles 109+.
* **Do NOT** introduce new top-level `def`'s or `structure`'s. The
  `IsConvergent`, `IsStable`, `IsConsistent`, `IsGLMSolution` predicates
  all already exist; the main theorem just composes them.
* **Do NOT** add a `_h_norm` Frobenius hypothesis to `thm:515D`'s
  signature. The textbook's "h₀ small enough" condition is captured in
  `lem:515B`'s `_h_norm` parameter; for `thm:515D` we should choose
  `h₀` (during the proof, in cycles 110+) such that the Frobenius
  condition holds. This is the analog of cycle-068's choice in the
  LMM proof. Surfacing `_h_norm` at `thm:515D`'s top-level signature
  would diverge from the textbook statement "*A* stable and consistent
  GLM is convergent" (no extra precondition).
* **Do NOT** treat the cycle-103-style "sorry-count went up" verdict
  as a regression. This is the EXPECTED shape of a sorry-first opening
  cycle. Cycle 103 was reverted (score −2) only because it failed to
  produce a coherent scaffold; cycle 108 should be evaluated against
  the *cycle-100 / cycle-074 / cycle-079 standard* of "scaffold + ≤ 2
  sub-lemma sorries + clean compile + sorries triaged in commit
  message". State this explicitly in the task-results file.
* **Do NOT** poll Aristotle more than once after the 30-min sleep.
  CLAUDE.md is explicit on this.
* **Do NOT** edit `scripts/autonomous_loop.py` or any loop infrastructure.
  Worker scope only.
* **Do NOT** raise `maxHeartbeats` above 200000. If `lake env lean
  Section515.lean` slows to a crawl after the new theorem lands,
  decompose further (e.g. add a third internal helper) — but try to
  stay within the ≤ 2-sub-lemma budget if possible.
* **Do NOT** create a new file `Section515D.lean`. `thm:515D` belongs
  in `Section515.lean` next to `lem:515B`.
* **Do NOT** cherry-pick easier targets like `def:520B`, `def:530A`,
  etc. `thm:515D` is the §515 capstone and unblocks `lem:515C` (the
  remaining `[ ]` entry under §515) plus the §521/§523 stability work.
* **Do NOT** introduce `axiom` or `constant`. If a Mathlib gap appears
  during scaffolding, file an issue — but at the scaffold stage no real
  proof obligations are being discharged, so this should not arise.
* **Do NOT** rename `h_*` → `h*` cosmetic workarounds (cycle-014/015
  pattern) on the new code unless the tautology scanner trips. The
  `private theorem aux_515D_*` proofs end in `sorry` so the scanner
  will not match them anyway.
* **Do NOT** attempt to also start `lem:515C` ("Accumulated error
  estimate for multistep methods", §515) in this cycle. Even though
  it lives in §515, it is a separate theorem with its own proof
  structure; defer to cycle 113+ once `thm:515D` is fully closed.

## Aristotle status (reference for cycle 109's polling)

* **Project `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`** (cycle 103
  η-contraction batch) — DEAD. **Cancel this cycle.** Already
  obsolete: cycle 107 closed `aux_515B_eta_contraction` manually via
  the M-matrix comparison principle.
* **New cycle-108 project (sub-lemma scaffold submissions)** — submit
  late in cycle 108 per Step D. Check ONCE during cycle 109 after a
  30-min sleep window.

## Backup plan (if Step C scaffold proves harder than expected)

If the main theorem's signature won't unify (e.g., the `Y_int`
existential is fiddly to thread through, or the `obtain ⟨u, v, …⟩
:= hCons` destructuring fails), fall back to:

* Land ONLY the main theorem with one consolidated `sorry` (no
  sub-lemmas), file an issue documenting the shape obstruction, and
  defer the sub-lemma decomposition to cycle 109.
* This is still positive cycle work (+1 sorry triaged into a structured
  scaffold + issue), avoiding the cycle-103 revert pattern.

If even the main theorem `sorry` fails to compile (e.g., the
`IsConvergent` predicate's signature has a subtlety we missed),
escalate by:

* Filing an issue describing the unification failure.
* Pivoting to a smaller deliverable: write a non-vacuity stub for
  `lem:515C` instead, or open `def:520B` (one of the `[ ]` Chapter-5
  entries that's purely a definition).

But the unification should be straightforward — `IsConvergent` is a
purely existential predicate with no dependently-typed surprises, and
the LMM analog at `OpenMath/Chapter4/Section404.lean:5455` is a
working blueprint.

## Why this target now

* `lem:515B` (the *only* prerequisite of `thm:515D` per the textbook
  proof) is closed (cycle 107).
* `IsConvergent` (def:512A, cycle 091/098) and `IsStable`/`IsConsistent`
  (def:510B/C, cycle 090) are all formalized.
* `discrete_gronwall_exp_bound` (Chapter 4, line 1663) is a reusable
  scalar Grönwall lemma that should drop in for the sub-lemma 1 closure
  in a future cycle (it's stated for general scalar sequences, not
  LMM-specific).
* No outstanding deferred-issue blocker exists for `thm:515D` —
  `.prover-state/issues/glm_isconvergent_strengthened.md` (cycle-098
  strengthening) is RESOLVED, and
  `.prover-state/issues/u_prime_equals_u_bridge.md` (cycle-099) is
  RESOLVED.

After cycle 108 lands the scaffold, the natural arc is:
* **Cycle 109**: close `aux_515D_stage_tendsto` (the easier of the two
  — pure linear-algebra limit using `U·u = 𝟙` and continuity of
  `Matrix.mulVec`).
* **Cycles 110–112**: close `aux_515D_output_tendsto` (the harder one
  — per-step iteration via `localStepError_bound` + discrete Grönwall
  + h → 0 squeeze; budget 3 cycles given the LMM analog took 4 cycles
  064–068).
* **Cycle 113+**: tackle `lem:515C` (accumulated error for multistep,
  the last `[ ]` entry under §515).
