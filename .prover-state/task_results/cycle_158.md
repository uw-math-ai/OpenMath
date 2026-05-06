# Cycle 158 Results

## Worked on

Refactor of duplicated Taylor + Lipschitz machinery shared between cycle
154's `explicitEulerGLM_hasOrderOne_trivialStarting` and cycle 157's
i=0 channel of `padded2DEulerGLM_hasOrderOne_padCompatStarting`,
extracting it into a single private helper inside
`OpenMath/Chapter5/Section530.lean`. No new textbook entities opened;
no Aristotle traffic this cycle (the planner explicitly directed
"Aristotle plan: None this cycle").

## Approach

1. Located the four cycle 153/154/156/157 witnesses and confirmed (per
   the planner's read) that the cycle 154 and cycle 157 i=0 closures
   share the same Taylor + Lipschitz machinery while the p=0 cases
   (cycle 153 + cycle 156 i=0) use a different (one-degree
   `HasDerivAt` + Lipschitz) shape — leaving the p=0 cases alone.

2. Inserted a `private theorem` immediately before
   `explicitEulerGLM_hasOrderOne_trivialStarting`:
   ```
   private theorem
   taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
       {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
       {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
       (hyex_x₀ : yex x₀ = y₀)
       (hyex_C2 : ContDiff ℝ 2 yex)
       (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
       (fun h : ℝ =>
           ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
             - (yex (x₀ + h) + h * f (yex (x₀ + h))))
         =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2)
   ```
   Body: split into T1 + T2 form via `funext h; ring`, then port the
   T1 (Taylor at degree 2) and T2 (Lipschitz on `f`, Cauchy bound,
   `|h| ≤ 1` near 0) sub-blocks verbatim from cycle 154, finishing
   with `hT1.add hT2`.

3. Refactored cycle 154's witness body: kept the `change`,
   `hSM`, `hES`, then replaced the ~135-LOC `hcongr / hpow / hT1 /
   hT2 / exact` block with a 3-step closure — `hcongr` (no `ring`,
   just `funext h; rw [hSM, hES]`), `hpow` (h^(1+1) → h^2), and a
   one-liner `exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
   hf_lip hyex_x₀ hyex_C2 hyex_ode`.

4. Refactored cycle 157's i=0 channel identically. The i=1 channel
   (zero-collapse via `Asymptotics.isBigO_zero`) was left untouched
   per the strategy's "do NOT change the i=1 channel" instruction.

5. Verified each step with `lake env lean
   OpenMath/Chapter5/Section530.lean` after the helper was added,
   then again after each refactor — all clean exits.

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake env lean OpenMath/Chapter5.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0 (unchanged).
* Tautology-scanner regex
  `':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'` → 0 hits.
* `lean_verify` returns `[propext, Classical.choice, Quot.sound]`
  (axiom-clean) for all four primary affected theorems:
  * `OpenMath.Chapter5.Section530.taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
    (new helper)
  * `OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne_trivialStarting`
    (refactored; cycle 154)
  * `OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne_padCompatStarting`
    (refactored; cycle 157)
  * `OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne`
    (def:530C wrapper transitively citing cycle 157; verified clean)
* No collateral damage: `lean_verify` axiom-clean on the cycle
  153/155/156 theorems
  (`explicitEulerGLM_hasOrderZero_trivialStarting`,
  `padded2DEulerGLM_hasOrderZero_padCompatStarting`,
  `explicitEulerGLM_hasOrderZero`,
  `padded2DEulerGLM_hasOrderZero`,
  `explicitEulerGLM_hasOrderOne`).
* File LOC: `OpenMath/Chapter5/Section530.lean` 1600 → 1524
  (**−76 LOC**). Smaller net reduction than the planner's −200 LOC
  target because the helper retains the full T1 + T2 Taylor +
  Lipschitz body (cf. the original cycle 154 closure, which was
  inline) and each call site still needs the `change` + `hSM` +
  `hES` + `hcongr` + `hpow` glue, but the duplication
  *between the two witnesses* is now eliminated.

## Faithfulness check

For the new private helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`:

* Not a textbook entity — internal infrastructure helper (per CLAUDE.md
  "If Mathlib is missing something, build it yourself as a helper
  lemma").
* **Tautology check**: ✓ — the conclusion is an asymptotic statement
  `=O[nhds 0] (fun h => h ^ 2)`; no hypothesis has this form.
* **Identity check**: ✓ — proof body is the Taylor + Lipschitz
  machinery (T1 via 2nd-order Taylor remainder; T2 via Lipschitz on
  `f`, `IsBigOWith`, and `|h| ≤ 1` near 0), not `exact h_*`.
* **Hypothesis strength check**: hypotheses match cycle 154's
  exactly — `LipschitzWith L f`, `yex x₀ = y₀`, `ContDiff ℝ 2 yex`,
  `∀ x, HasDerivAt yex (f (yex x)) x`. No extra hypotheses; no
  weakened-but-still-needed shortcuts.
* **Absent theorem check**: no comment in the new helper promises
  content elsewhere; the body is self-contained.

For the refactored cycle 154 witness
`explicitEulerGLM_hasOrderOne_trivialStarting`:
- Entity ID and textbook statement (no direct entity — this is the
  Path A non-vacuity Step 4 witness for `def:530B`):
  > Witnesses `HasOrderRelativeTo_explicit explicitEulerGLM
  > trivialStartingMethod _ _ 1 f yex x₀ y₀` under `LipschitzWith L f`,
  > `yex x₀ = y₀`, `ContDiff ℝ 2 yex`, and `∀ x, HasDerivAt yex (f
  > (yex x)) x` — exactly the cycle 154 statement.
- Lean statement captures: same content. Statement signature
  unchanged from cycle 154; only the proof body now invokes the
  helper after the SM[0]/ES[0] closed-form rewrites.
- Tautology / identity / strength / absent checks: ✓ on all four,
  identical to cycle 154's status.

For the refactored cycle 157 witness
`padded2DEulerGLM_hasOrderOne_padCompatStarting`:
- Entity ID and textbook statement (no direct entity — this is the
  r=2 × p=1 corner of the Path A non-vacuity grid for `def:530B`):
  > Witnesses `HasOrderRelativeTo_explicit padded2DEulerGLM
  > padCompatStartingMethod _ _ 1 f yex x₀ y₀` under
  > `LipschitzWith L f`, `yex x₀ = y₀`, `ContDiff ℝ 2 yex`, and
  > `∀ x, HasDerivAt yex (f (yex x)) x` — exactly the cycle 157
  > statement.
- Lean statement captures: same content. Statement signature
  unchanged from cycle 157; only the i=0 channel's proof body now
  invokes the helper. The i=1 channel (zero-collapse) is verbatim
  from cycle 157.
- Tautology / identity / strength / absent checks: ✓ on all four,
  identical to cycle 157's status.

## Dead ends

None. The strategy was conservative ("Priority 1 backup" /
"Priority 1 deeper backup" tiers were defined for the case the
helper signature stalled) but the first signature shape compiled
cleanly on the first try, so neither backup was needed.

## Discovery

* The cleanest helper conclusion shape is the **direct subtraction
  form** (`((y₀ + h·f y₀) + h·f(y₀ + h·f y₀)) − (yex(x₀+h) +
  h·f(yex(x₀+h)))`) rather than the `T1 + T2` rearranged form. This
  matters because both call sites reach the direct form *purely
  algebraically* via `funext h; rw [hSM, hES]` (no `ring` needed),
  and the helper's body opens with a `funext h; ring` to bring it
  into the T1 + T2 form internally. Splitting the responsibility
  this way keeps the call-site `hcongr` step minimal.

* Re-verifying the cycle 153/155/156 + def:530C wrapper theorems
  axiom-clean after the refactor was zero-cost (cached `.olean`s
  pick up no axiom changes), but worth doing routinely after any
  shared-helper refactor — the def:530C wrappers transitively cite
  the cycle 154/157 witnesses, so a regression in either would
  cascade.

* The actual LOC reduction (−76) was smaller than the planner's
  target (−200). This is because the cycle 154 closure body was
  ~135 LOC, the cycle 157 i=0 closure body was ~95 LOC, and the
  helper itself is ~140 LOC. The arithmetic gain is from
  eliminating the duplication: `135 + 95 − 140 = 90` LOC of
  bookkeeping savings minus the new `change` / `hcongr` / `hpow`
  glue (~12 LOC × 2 sites ≈ 24 LOC) ⇒ net ~66 LOC, roughly
  matching the observed −76. The next refactor (cycle 159+) that
  reuses this helper at a third site would push the net deeper
  negative without adding anything to the helper.

## Suggested next approach

For the planner to consider next cycle:

1. **Path A r = 3 or higher-`s` witness.** A third call site for
   the new helper would compound the LOC win and demonstrate the
   refactor's portability. Concretely: a `(s, r) = (1, 3)`
   3-padded explicit-Euler GLM with three padCompat-style channels
   would let the i=0 channel be a one-line helper invocation while
   the i=1, i=2 channels reuse cycle 156's zero-collapse pattern.
   This is mechanical infrastructure work, not new mathematics.

2. **Generalising the helper over the Taylor degree.** The
   strategy explicitly defers this ("Do NOT extend the helper to
   cover cycles 153/156 (p=0 cases). Parameterizing the helper
   over the Taylor degree is a separate refactor; defer to cycle
   159+ if cycle 158 lands cleanly"). Now that 158 has landed
   cleanly, this is an obvious cycle-159 candidate. The
   parameterised form would absorb cycles 153/156 i=0 + 154/157
   i=0 (four sites total) into a single helper indexed by
   `Nat.succ p` Taylor degree.

3. **`thm:532A`** remains blocked on the §31x rooted-tree
   elementary-differential infrastructure (per the cycle 157 task
   results). A multi-cycle plan that opens §31x deliberately would
   unblock the substantive §530+ work; absent that, `thm:532A`
   remains too costly for a single-cycle attempt.

4. **`thm:550A` general-`n`** remains blocked per
   `thm_550A_general_n.md` (two failed Aristotle long-runs at
   24 h and 89 h cancellation; manual cofactor expansion or
   eigenvalue-density infrastructure is the only path forward —
   multi-cycle work).

5. **A minor hygiene pass on `Section530.lean`**: with the file at
   1524 LOC after the refactor, there may be additional opportunities
   to extract shared algebraic-closed-form helpers (e.g. the SM[0] /
   ES[0] explicit-Euler shape that's now duplicated between cycle
   154 and cycle 157 call sites). This would be a +1 cycle, not a
   +2 cycle, but it's available if the planner wants a low-risk
   pivot.
