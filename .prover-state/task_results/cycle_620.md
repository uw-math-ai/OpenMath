# Cycle 620 Results

## Worked on

Butcher §510 / §512 LMM stability lift, Phase B
(`.prover-state/issues/butcher_section512_lmm_stability_lift.md`):
the structural h·f-slot vanishing of `V`-iterates of the LMM-as-GLM
embedding, in `OpenMath/LMMAsGLM.lean`.

## Approach

Followed the strategy recipe verbatim:

1. Added the headline theorem `LMM.toGLM_V_iter_natAdd_eq_zero` next
   to the cycle 619 simp lemmas, sorry-first, and verified the file
   compiled.
2. Closed the proof by induction on `n` with `k` and the hypothesis
   `s ≤ n + (k:ℕ)` quantified inside (so the IH is universal in `k`):
   * **Base `n = 0`:** the hypothesis gives `s ≤ (k:ℕ)`, contradicting
     `k.isLt`. Discharged with `omega`.
   * **Step `n+1`:** unfolded one iterate with
     `Function.iterate_succ_apply'`, beta-reduced via an explicit
     `show`, then case-split on `(k:ℕ) + 1 = s`.
     * `(k:ℕ) + 1 = s` (last past-h·f row): rewrote every `V` entry
       with `toGLM_V_natAdd_last_apply` (cycle 619), then closed with
       `zero_mul, Finset.sum_const_zero`.
     * `(k:ℕ) + 1 ≠ s` (shift past-h·f row): rewrote each `V` entry
       with `toGLM_V_natAdd_shift_apply` (cycle 619), built the unique
       column `l₀ = Fin.cast _ (Fin.natAdd s ⟨(k:ℕ)+1, hkSucc⟩)` whose
       value is `s + (k:ℕ) + 1`, used `Finset.sum_eq_single l₀` to
       collapse the sum, then applied the IH at `⟨(k:ℕ)+1, hkSucc⟩`
       with `s ≤ n + ((k:ℕ)+1)` (from the outer hypothesis by
       `omega`).

The iterate shape is `(fun v => fun k' => ∑ l, m.V k' l * v l)^[n] q`
which matches `GeneralLinearMethod.IsStable`
(`OpenMath/GeneralLinearMethod.lean:152`), so downstream Phase D will
apply directly.

## Result

SUCCESS. `LMM.toGLM_V_iter_natAdd_eq_zero` lands in
`OpenMath/LMMAsGLM.lean` (191 lines added near line 188). No new
`sorry` in the file or anywhere in `OpenMath/`.

Verified:

* `lake env lean OpenMath/LMMAsGLM.lean` — exit 0, no warnings.
* No other tracked Lean file imports `OpenMath.LMMAsGLM`, so the
  downstream surface is undisturbed.

`plan.md` updated with the one-line cycle 620 note in the §512 row of
Chapter 5.

## Dead ends

None. The strategy recipe was tight and the row-level simp lemmas
from cycle 619 dropped each branch into a clean elementary closure
(`zero_mul / Finset.sum_const_zero` for the last row;
`Finset.sum_eq_single` + IH for the shift row).

The only minor friction was Lean not auto-collapsing
`(Fin.cast _.symm (Fin.natAdd s ⟨(k:ℕ)+1, _⟩) : ℕ)` to
`s + (k:ℕ) + 1`; it happily reduces to `s + ((k:ℕ) + 1)` and `omega`
finishes via the auxiliary `hl₀_val`.

## Discovery

The `Function.iterate_succ_apply'` unfolding leaves the outer lambda
not beta-reduced under `simp_rw`'s row rewrites, so an explicit
`show` of the beta-reduced sum form was the cleanest way to expose
the row position `Fin.cast _ (Fin.natAdd s k)` to the cycle 619
`@[simp]` lemmas. (Trying to drive the proof entirely through
`simp only` with the iterate primed up was clumsier.)

## Suggested next approach

Phase B headline closed. The strategy-listed Phase B optional
follow-ups (`toGLM_V_iter_natAdd_eq_zero_of_le` and the in-range
shift formula) were not attempted this cycle: the headline used the
full single-cycle budget once Aristotle policy ruled out external
help and the outer hypothesis quantification took a moment to set
up. Cycle 621 should:

1. (cheap) Add `toGLM_V_iter_natAdd_eq_zero_of_le` as a one-line
   corollary specialised to `n ≥ s`. This is the exact form Phase D
   will consume, so it pays for itself.
2. Open Phase C — the row-bound on the first `s` iterates
   (combinatorial bookkeeping over the y-shift block). This is the
   piece needed before Phase D's spectral bridge.

Phase C is independent of any complex / spectral input; the only
requirement is a uniform bound `|((step^[n] q) k)| ≤ C^n · M_max`
for `n ≤ s`, where `M_max = ‖m.α‖_∞ + ‖m.β‖_∞ + 1`. Either landing
that bound or scaffolding a single-row inductive helper would be a
clean cycle 621 deliverable.

## Aristotle

Per cycle policy, no Aristotle submission was attempted; the proof
was tight enough to close manually using the cycle 619 simp lemmas.
