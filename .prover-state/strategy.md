# Cycle 048 strategy — `thm:406D` Σ θψ contraction sub-lemma

**Last cycle**: cycle 047 landed at `85771f1` (verified: `HEAD =
origin/Main/Experiments`). Three deliverables shipped:

1. `theta_isHomogeneousSolution` — connector from `Section141.theta`
   to `Section404.IsHomogeneousSolution`.
2. `theta_bounded_of_isStable` — extracts `Θ ≥ 0` with
   `∀ n, |θ n| ≤ Θ` from `M.IsStable`.
3. `LinearMultistepMethod.stable_consistent_isConvergent` — `thm:406D`
   scaffold with `sorry` body (locked-in signature).

**Sorry count: 1** (the `thm:406D` scaffold at
`OpenMath/Chapter4/Section404.lean:1771`). DO NOT touch this sorry
this cycle. The auto-scorer punishes net sorry increases — keep net
sorry count flat (1 → 1) by adding new helper lemmas with closed
proofs only.

## Phantom verdict (ignore)

The "Recent cycle history" line says cycle 047 score=-2 / "REVERTED:
sorry count increased 0→1". This is **not a real revert**. `git log`
confirms `85771f1` is on the branch tip and `task_results/cycle_047.md`
lists exactly the deliverables enumerated above. The "REVERTED" tag is
the auto-scorer's verdict on a *deliberate* sorry-first scaffold cycle
(see CLAUDE.md "sorry-first ABSOLUTE RULE"). Treat as the same
phantom pattern documented in
`.prover-state/issues/consultant_advice_cycle_009.md` §A,
`consultant_advice_cycle_014.md` §A, `consultant_advice_cycle_015.md`
§B, `consultant_advice_cycle_040.md` §A. The cycle 047 worker did the
right thing; the score is wrong.

## Aristotle status

No pending results. No project in flight. You may optionally
submit one batch this cycle (5 lemmas max) as a parallel safety
net; not required. The primary lemma below is short enough that
manual proof is the safer path.

## What to work on this cycle

**Primary deliverable**: prove `sum_theta_psi_contraction` —
the abstract Σ θψ contraction inequality used in the textbook
"406h closed form" derivation. This is the first of the three
follow-up sub-lemmas listed in `task_results/cycle_047.md`
"Suggested next approach".

### Target signature (final, faithful to Butcher's argument)

Add this private lemma in `OpenMath/Chapter4/Section404.lean`
**immediately before** `LinearMultistepMethod.stable_consistent_isConvergent`
(approximately line 1745, between the `theta_bounded_of_isStable`
lemma and the scaffold theorem):

```lean
/-- **Butcher §406D contraction lemma (helper for `thm:406D`).**
Bounds `|Σ θ_{·} ψ_·|` by `Θ · (C·h·Σ Sε + D·h²·#range)` whenever
each `|ψ i|` is dominated pointwise by `C·h·Sε i + D·h²` and
`|θ i| ≤ Θ`.

The user supplies the per-index "max-of-recent-errors" upper bound
`Sε i` themselves (typically `max_{j<k} |ε(i - j - 1)|`, but we keep
this abstract to avoid bringing `Finset.sup'` into the lemma).

This is the Σ → Σ contraction Butcher invokes in the (406h) recurrence
derivation: the sum over `i ∈ Ico k n` of bounded `|ψ i|` collapses to
a "weighted total error" plus a "linear-in-n h² term".

The `idx` parameter abstracts the index passed to `θ` (typical caller
will use `idx := fun i => n - 1 - i`, matching Butcher's `θ_{n-1-i}`).
This avoids fighting `Nat`-subtraction inside the inequality and makes
the lemma reusable. -/
private lemma sum_theta_psi_contraction
    {Θ C D h : ℝ} (hΘ : 0 ≤ Θ) (hh : 0 ≤ h)
    (θ : ℕ → ℝ) (hθ : ∀ i, |θ i| ≤ Θ)
    (ψ : ℕ → ℝ) (Sε : ℕ → ℝ)
    (k n : ℕ) (hkn : k ≤ n)
    (idx : ℕ → ℕ)
    (hψ : ∀ i, k ≤ i → i < n → |ψ i| ≤ C * h * Sε i + D * h^2) :
    |∑ i ∈ Finset.Ico k n, θ (idx i) * ψ i|
      ≤ Θ * C * h * (∑ i ∈ Finset.Ico k n, Sε i)
        + Θ * D * h^2 * ((n - k : ℕ) : ℝ) := by
  sorry
```

### Proof outline (~25 lines, no axioms)

```lean
  -- Step 1: |Σ| ≤ Σ |·|.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Step 2: pointwise: |θ * ψ| = |θ| * |ψ| ≤ Θ * (C h Sε + D h²).
  have hbound : ∀ i ∈ Finset.Ico k n,
      |θ (idx i) * ψ i| ≤ Θ * (C * h * Sε i + D * h^2) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [abs_mul]
    have h_psi := hψ i hi.1 hi.2
    have h_psi_nn : 0 ≤ |ψ i| := abs_nonneg _
    calc |θ (idx i)| * |ψ i|
        ≤ Θ * |ψ i| :=
          mul_le_mul_of_nonneg_right (hθ (idx i)) h_psi_nn
      _ ≤ Θ * (C * h * Sε i + D * h^2) :=
          mul_le_mul_of_nonneg_left h_psi hΘ
  -- Step 3: sum the bound.
  refine (Finset.sum_le_sum hbound).trans ?_
  -- Step 4: distribute Θ over the (Chx + Dh²) split.
  have hpoint : ∀ i, Θ * (C * h * Sε i + D * h^2) =
                       Θ * C * h * Sε i + Θ * D * h^2 := by intro; ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Ico, smul_eq_mul]
  ring
```

If `simp_rw [hpoint]` fights with `Finset.sum_congr` quirks, fall back
to `refine le_of_eq ?_; rw [Finset.sum_congr rfl (fun i _ => hpoint i)];
…`. The end-goal is the two-summand RHS exactly as in the signature.

### Mathlib lemmas (verify each with `lean_local_search` or `lean_loogle`)

| Goal | Lemma |
|---|---|
| `\|Σ\| ≤ Σ \|·\|` | `Finset.abs_sum_le_sum_abs` |
| `\|a · b\| = \|a\| · \|b\|` | `abs_mul` |
| Mono `*` (right factor `≥ 0`) | `mul_le_mul_of_nonneg_right` |
| Mono `*` (left factor `≥ 0`) | `mul_le_mul_of_nonneg_left` |
| `Σ (f + g) = Σ f + Σ g` | `Finset.sum_add_distrib` |
| `Σ c · f = c · Σ f` | `Finset.mul_sum` (note direction; may need `← Finset.mul_sum`) |
| `Σ (constant) = card • c` | `Finset.sum_const` |
| `(Ico k n).card = n - k` | `Nat.card_Ico` |
| `n • r = (n : ℝ) * r` | `nsmul_eq_mul` (or `smul_eq_mul`) |

All of these were used in cycles 044/045/046 — they are
known-good in this codebase. If `Finset.sum_add_distrib` is the wrong
spelling, try `Finset.sum_add` or `Finset.sum_add_sum` (loogle the
type pattern).

### Verification

1. `lake env lean OpenMath/Chapter4/Section404.lean` → clean (one
   sorry warning on the `thm:406D` scaffold only — same as before).
2. Axiom check on the new lemma:
   ```lean
   #print axioms OpenMath.Chapter4.Section404.sum_theta_psi_contraction
   ```
   Expected: `[propext, Classical.choice, Quot.sound]`. Add the
   `#print` line, run, then **delete it** before committing.
3. **Sorry count check**:
   `rg '\bsorry\b' OpenMath/ -c` (or `grep -rn '\bsorry\b' OpenMath/ | wc -l`)
   should show exactly **1** sorry (the existing scaffold). If it
   shows `2`, you've left an open sub-proof — fix before committing.
4. Optional: `lake build` to confirm full-project compile (cached;
   should be fast).

### Stretch goal (only if primary lands cleanly with > 30 min remaining)

Prove a small companion: **`abs_max_le_sum_in_Fin_k`** — the "factor `k`"
trick that bounds a max over `Fin k` by the sum of the same terms.

```lean
private lemma abs_max_le_sum_in_Fin_k
    {k : ℕ} (hk : 0 < k) (g : Fin k → ℝ) (hg : ∀ j, 0 ≤ g j) :
    Finset.univ.sup' Finset.univ_nonempty g ≤ ∑ j : Fin k, g j := by
  apply Finset.sup'_le
  intro j _
  exact Finset.single_le_sum (f := g) (fun i _ => hg i) (Finset.mem_univ j)
```

This isn't strictly needed yet, but cycle 049/050 will want to
specialise `sum_theta_psi_contraction` to a "Sε i := max_j |ε(i - j - 1)|"
form, and this lemma is the bridge to cycle 045's per-step bound
(which uses a uniform `Mmax`). If the primary lemma eats the cycle,
defer this to the next cycle.

## What NOT to do

- **DO NOT** touch `LinearMultistepMethod.stable_consistent_isConvergent`'s
  `sorry`. The full close requires φ(h) → 0 (cycle 049) and the
  outer assembly (cycle 050). Keep the scaffold's `sorry` in place.
- **DO NOT** introduce `Finset.sup'` (max over a finset) into the
  primary lemma's signature. The abstract `Sε : ℕ → ℝ` parameter is
  the cleanest formulation; consumers can specialise. Adding `sup'`
  brings a Mathlib-API tax that isn't needed yet.
- **DO NOT** weaken the `0 < k` constraint of `theta_isHomogeneousSolution`
  or `theta_bounded_of_isStable`. Those constraints are
  mathematically necessary (Butcher's `θ_0 = 1` contradicts the
  homogeneous recurrence at `k = 0`). Documented in
  `task_results/cycle_047.md` faithfulness check.
- **DO NOT** try to prove the LMM-specific contraction (involving
  `M.α`, `M.β`, `Mmax`, the LTE) in this cycle — that's the cycle 050
  outer-assembly job. The cycle 048 deliverable is the *abstract*
  inequality, parameterised over `θ`, `ψ`, `Sε`, `idx`.
- **DO NOT** raise `maxHeartbeats`. The proof is small enough that
  `ring`/`linarith` should close the algebra without trouble.
- **DO NOT** add an `axiom` or `constant`.
- **DO NOT** revert cycle 047's changes. The phantom "REVERTED"
  verdict (§"Phantom verdict" above) is wrong; the work landed.
- **DO NOT** submit the same lemma to Aristotle and prove it
  manually in parallel. Pick manual — the proof is short, doesn't
  need premise selection, and reproducibility from a known shape is
  worth more than a parallel safety net here.
- **DO NOT** edit `scripts/autonomous_loop.py` (loop maintainer
  territory; see `tautology_scanner_false_positives.md`).

## Past failed approaches to avoid (from `attempts.md`)

None directly relevant to this cycle's target. The closed-form bound
`discrete_gronwall_exp_bound` (cycle 046) and the per-step bound
`globalError_recurrence_bound_textbook` (cycle 045) are both
already in place — the contraction is a fresh, isolated piece of the
proof that doesn't touch their plumbing.

The phantom-verdict pattern from cycles 008/014/015/040/047 is the
main thing to be aware of: "Recent cycle history" auto-scoring lines
that contradict `git log` should be treated as
attempts.md/prompt-builder noise, not real reverts. See §"Phantom
verdict" above.

## Cycle 048 commit ritual

1. Edit `OpenMath/Chapter4/Section404.lean` — insert
   `sum_theta_psi_contraction` immediately before
   `LinearMultistepMethod.stable_consistent_isConvergent` (around
   line 1745).
2. (Optional stretch) insert `abs_max_le_sum_in_Fin_k` immediately
   before that.
3. `lake env lean OpenMath/Chapter4/Section404.lean` — confirm clean
   compile (only the existing scaffold sorry warning).
4. Axiom check the new lemma(s) via in-place `#print axioms`. **Delete
   the `#print` line(s) after** the axioms confirm clean.
5. **Verify net sorry count is unchanged at 1** before committing.
6. Update `extraction/formalization_data/lean_status.json` only if a
   Butcher entity changes status — `sum_theta_psi_contraction` is
   infrastructure, not a Butcher entity, so **no `lean_status.json`
   change this cycle** unless you happen to bump `thm:406D` (don't —
   it's still partial).
7. Write `.prover-state/task_results/cycle_048.md` per the format in
   CLAUDE.md. Include the faithfulness check (this is *infrastructure*,
   no Butcher entity, document the abstraction choices).
8. Commit with message
   `Cycle 048 — sum_theta_psi_contraction (helper for thm:406D)`
   and push to `origin/Main/Experiments`. Verify push landed via
   `git log -1 origin/Main/Experiments` matching `git rev-parse HEAD`.

## Estimated cost

~30–60 minutes of worker time for the primary lemma (signature is
small, proof is mechanical). Add ~15 minutes for the stretch goal.
This is a **low-risk cycle** — the scaffold is locked, the algebra
is elementary, and Mathlib has direct support for every step.

## Looking ahead (for the cycle 049 planner)

After `sum_theta_psi_contraction` lands, cycle 049 should target the
**φ(h) → 0** helper. From `IsConvergent`'s starting-method
hypothesis (`∀ i, Tendsto (fun h => start h i) (nhds 0) (nhds y₀)`),
plus continuity of `yex` at `x₀`, conclude
`Tendsto (fun h => max_{i < k} |yex(x₀ + i·h) - start h i|) (nhds 0)
 (nhds 0)`. Pure `Filter.Tendsto` analysis; no LMM-specific content.
Then `abs_max_le_sum_in_Fin_k` (this cycle's stretch) gives the
"sum form" of φ(h) → 0 for use in the outer assembly.

Cycle 050 then does the outer assembly, dispatching the scaffold's
`sorry` by chaining: cycle 045 (per-step ψ bound) → cycle 048
(Σ θψ contraction) → cycle 046 (discrete Grönwall) → cycle 049
(φ(h) → 0) + `Real.exp_nonneg` to drive the limit.
