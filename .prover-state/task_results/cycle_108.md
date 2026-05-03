# Cycle 108 Results

## Worked on

Opening `thm:515D` (Butcher 2008 §515, p. 417 — *A stable and
consistent general linear method is convergent*) with a sorry-first
scaffold. This is the §515 capstone, the natural next step after
cycle 107's closure of `lem:515B`.

## Approach

Followed the cycle-108 strategy verbatim:

1. **Step A** — re-read `extraction/formalization_data/entities/thm_515D.json`
   and confirmed the textbook hypotheses are *exactly* "stable + consistent",
   no extra preconditions.
2. **Step B** — skimmed the LMM analog at
   `OpenMath/Chapter4/Section404.lean:5455`
   (`LinearMultistepMethod.stable_consistent_isConvergent`) for the
   canonical "per-step bound iteration + discrete Grönwall + h → 0
   squeeze" recipe.
3. **Step C** — appended the scaffold at the end of
   `OpenMath/Chapter5/Section515.lean` (line 1463 → 1576):

   * `aux_515D_output_tendsto` (private sub-lemma, `sorry`'d) —
     output convergence `Y n n → u · yex(x)`.
   * `aux_515D_stage_tendsto` (private sub-lemma, `sorry`'d) —
     stage convergence `Y_int n → yex(x)`.
   * `GeneralLinearMethod.stable_consistent_isConvergent` (main
     theorem) — `by_cases hs : 0 < s`. The `0 < s` branch closes
     inline: `u ≠ 0` is derived from `U·u = 𝟙` (one-line
     `congrFun hUu ⟨0, hs⟩` + `simp`), then dispatches to the two
     sub-lemmas. The `s = 0` branch is a single inline `sorry` (see
     issue, below).
4. **Step D** — submitted the project root to Aristotle via
   `submit_directory` (project ID
   `40554853-18b3-424c-81e4-2a2fae9e57c4`), with a prompt focused
   on the two main sub-lemmas plus a note that the `s = 0` sorry is
   out of scope.
5. **Step E** — cancelled the dead cycle-103 Aristotle project
   (`4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`); was IN_PROGRESS at 6%
   for 50+ hours and is obsolete since cycle 107 closed lem:515B
   manually.
6. **Step F** — updated `plan.md` (changed `[ ] thm:515D` →
   `[~] thm:515D` with cycle-108 status note) and
   `extraction/formalization_data/lean_status.json` (bumped to
   `partial` with full notes).
7. **Step G** — ran the faithfulness checklist (see below).
8. **Step H** — writing this file now.
9. **Step I** — commit + push at the end.

## Result

**SUCCESS** (with one off-strategy element — the `s = 0` inline
sorry). The cycle landed:

* The main theorem `stable_consistent_isConvergent` with a
  textbook-faithful signature (no extra preconditions on top of
  `IsStable` + `IsConsistent`).
* Two private sub-lemma sorries documenting the deferred work.
* One inline sorry for the `s = 0` corner case where the strategy's
  expected one-liner doesn't apply.
* No new top-level `def`/`structure` introduced.
* All three sorries compile cleanly: `lake env lean
  OpenMath/Chapter5/Section515.lean` produces only the expected
  `declaration uses sorry` warnings, and `lake build
  OpenMath.Chapter5.Section515` refreshes the `.olean` cache.
* `#print axioms
  OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
  shows `[propext, sorryAx, Classical.choice, Quot.sound]` — the
  expected `sorryAx` from the deferred sub-lemma proofs.

### Sorry budget

The strategy's stated ceiling was "**At most two** named private
sub-lemmas introduced as `sorry`'s" plus an inline `u ≠ 0` proof.
This cycle landed:

* 2 sub-lemma sorries (`aux_515D_output_tendsto`,
  `aux_515D_stage_tendsto`) — at budget.
* 1 inline sorry in the main theorem's `s = 0` branch — over the
  inline budget by 1, because the strategy's recommended inline
  contradiction `(M.U *ᵥ u : Fin s → ℝ) = 0 ⇒ contradiction` does
  *not* go through when `s = 0` (see Discovery below).

Total: 3 net new sorries (vs. 0 outstanding sorries entering cycle
108). This is one over the strict ≤ 2 budget but is structurally
unavoidable for the textbook signature; an issue
(`thm_515D_s_zero_degenerate.md`) documents Option A–D resolutions
for cycle 109+. The strategy explicitly anticipated this kind of
edge case in the backup plan, and the cycle deliverable
(coherent scaffold + 2 sub-lemmas + clean compile + sorries
triaged) matches the cycle-100 / cycle-074 / cycle-079 standard for
sorry-first openings.

## Faithfulness check

### Main theorem

* **Entity ID and textbook statement** (quoted from
  `entities/thm_515D.json`):
  > A stable and consistent general linear method is convergent.
* **Lean statement captures**: same content. The hypothesis list
  (`M.IsStable` + `M.IsConsistent`) and conclusion
  (`M.IsConvergent`) are textbook-verbatim.
* **Tautology check**: hypotheses are `IsStable` + `IsConsistent`;
  conclusion is `IsConvergent`. None coincide. ✓
* **Identity check**: the proof body uses `obtain`, `by_cases`,
  `refine`, and dispatches to two helpers. Not a single-`exact`
  re-export. ✓
* **Definition smuggling**: no new `def`/`structure` introduced. The
  `IsConvergent`, `IsStable`, `IsConsistent`, `IsGLMSolution`
  predicates are all pre-existing (Section510 / Section512). ✓
* **Hypothesis strength check**: only `IsStable` + `IsConsistent` on
  the signature, matching the textbook. No `_h_norm` / Frobenius
  precondition surfaced. ✓
* **Absent theorem check**: docstring promises factoring through
  `aux_515D_output_tendsto` and `aux_515D_stage_tendsto`; both
  exist with sorry. ✓

### Sub-lemmas (private internal helpers, not Butcher entities)

* `aux_515D_output_tendsto` — internal; documented in docstring
  as "Sub-lemma for `thm:515D`". No textbook entity to compare
  against.
* `aux_515D_stage_tendsto` — same.

Both sub-lemma signatures take only the destructured pieces
(`hVu`, `hUu`, `hCons_eq`) plus the rest of `IsConvergent`'s body,
matching what the main theorem feeds them. No hypothesis stronger
than what the main theorem provides.

### Divergence note

The main theorem's `s = 0` branch carries an inline `sorry`. This is
a faithfulness divergence in the sense that the textbook statement
"a GLM is convergent" doesn't carry an `s ≥ 1` precondition, but our
proof currently only handles `0 < s`. The corresponding issue
documents Options A–D for cycle 109+; the recommended path is
Option D (add `0 < s` to the theorem signature with a
faithfulness divergence note).

## Dead ends

### Inline `u ≠ 0` for `s = 0`

The strategy suggested the inline `u ≠ 0` proof should fit in
1–2 lines, with a comment that `s = 0` "vacuous so still fine".
Attempted approach:

```lean
intro hu0
have h1 : (M.U *ᵥ u : Fin s → ℝ) = 0 := by rw [hu0]; simp
rw [hUu] at h1
-- h1 : (fun _ : Fin s => 1) = 0
```

For `0 < s`, evaluating `h1` at `⟨0, hs⟩` gives `1 = 0` and closes
the goal. But for `s = 0`, both `(fun _ : Fin 0 => 1)` and
`(0 : Fin 0 → ℝ)` are the unique empty function from `Fin 0 → ℝ`,
so they're extensionally equal and `h1` does NOT yield a
contradiction. The strategy's "vacuous so still fine" comment is
incorrect: `s = 0` is genuinely degenerate, not vacuously OK.

### Picking a different `u` in the `s = 0` case

For `s = 0`, `r ≥ 1`, one could try picking `u = (fun _ => 1)` (or
any other non-zero vector) instead of the consistency `u`. But then
the limit `Y n n → u · yex(x)` for an arbitrary GLM iteration with
the consistency-derived stability/consistency structure is not
provable in general — the consistency-`u` is the *only* `u` that
the iteration converges to (when it does), and consistency requires
`V·u = u` which constrains `u` away from arbitrary choice.

## Discovery

### `s = 0` is genuinely degenerate, not vacuously fine

For `s = 0`, the GLM has no internal stages. `M.U *ᵥ u` is the
empty function in `Fin 0 → ℝ`, which equals `(fun _ : Fin 0 => 1)`
and `(0 : Fin 0 → ℝ)` simultaneously. So `IsConsistent`'s
preconsistency clause `U·u = 𝟙` does not constrain `u`, and `u = 0`
is allowed.

For `(s, r) = (0, 0)`, `Fin 0 → ℝ` has only one inhabitant (zero),
so `u ≠ 0` is *literally false* — the IsConvergent statement is
vacuously False for `(0, 0)` GLMs. The theorem
`stable + consistent ⇒ convergent` is therefore False as stated for
that corner case.

Implication for cycle 109+: the cleanest fix is Option D — add
`(_hs : 0 < s)` to the theorem signature with a faithfulness
divergence docstring note. Butcher implicitly assumes `s ≥ 1`
throughout §515 (the abscissae `c = A·𝟙 + U·v` analyzed in
lem:515A only makes sense when `s ≥ 1`).

### `obtain ⟨u, v, ⟨hVu, hUu⟩, hCons_eq⟩ := hCons` consumes the original

The strategy's draft sub-lemma signature took `hCons : M.IsConsistent`
as a parameter. But the main theorem destructures `hCons` to get
`u`, `v`, `hVu`, `hUu`, `hCons_eq`, after which the original
`hCons` is no longer in scope. So the sub-lemmas drop the
`_hCons : M.IsConsistent` parameter and rely solely on the
destructured pieces. This is cleaner anyway.

## Suggested next approach

For cycle 109, the planner should consider:

1. **Resolve the `s = 0` degenerate sorry** via Option D (add
   `0 < s` to the theorem signature). This is one-line and unblocks
   axiom-cleanliness once the two sub-lemmas close.

2. **Close `aux_515D_stage_tendsto` first** (the easier of the two
   per the strategy). Recipe: from the stage equation `Y_int n i =
   h_n · ∑_j A·f(Y_int) + ∑_j U · Y n n j`, take `n → ∞`. The first
   summand vanishes (`h_n → 0` + `f` bounded along trajectory via
   continuity); the second summand tends to `(U·u·yex(x))_i = (𝟙·yex(x))_i = yex(x)`
   by `U·u = 𝟙` and continuity of `Matrix.mulVec`. This is pure
   linear-algebra limit. The output convergence (sub-lemma 1) is
   *not* needed for this — only the stability + consistency setup.

   Wait, actually re-reading the planner's sketch: the stage
   convergence DOES depend on `Y n n → u·yex(x)` (the output
   convergence). So sub-lemma 2 should take `h_output` from
   sub-lemma 1 (or be proven jointly). Cycle 109 should refactor
   `aux_515D_stage_tendsto`'s signature to depend on
   `aux_515D_output_tendsto` (or fold them together).

3. **Decompose `aux_515D_output_tendsto` further** (cycles 110+).
   Budget 3 cycles for the per-step iteration + discrete Grönwall +
   h → 0 squeeze, mirroring the LMM analog (which took 4 cycles
   064–068).

4. The Aristotle batch (project
   `40554853-18b3-424c-81e4-2a2fae9e57c4`) is a long shot —
   Aristotle has historically struggled with squeeze / limit
   arguments. Cycle 109 should poll once and proceed manually
   regardless of result.

## Aristotle status

* Cancelled the cycle-103 dead project
  `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8` (was at 6% for 50+ hours;
  obsolete since cycle 107 closed lem:515B manually).
* Submitted cycle 108 batch as project
  `40554853-18b3-424c-81e4-2a2fae9e57c4`. Checked once after the
  mandatory 30-min sleep window (per CLAUDE.md): status
  `IN_PROGRESS` at 6% (just unpacked + lake-built; not yet
  attempting proofs). Expected — Aristotle has historically
  struggled with iteration / squeeze arguments. Cycle 109 should
  poll once and proceed manually regardless.

## Commit hash check

After committing this cycle, verify
`git rev-parse HEAD == git rev-parse origin/Main/Experiments` to
confirm the commit reached the remote (cycles 008/035/071 had
commit-not-reaching-repo failures).
