# Cycle 618 Results

## Worked on

Butcher §512 — Definition of convergence for general linear methods. The
cycle target was three-tiered: (1) the §512 definition, (2) the RK-side
sanity check `ButcherTableau.toGLM_isConvergent`, and (3) the substantive
LMM-side stability lift `LMM.toGLM_isStable` (with `toGLM_isConvergent`
as a one-liner on top).

## Approach

1. Added `GeneralLinearMethod.IsConvergent : Prop` in
   `OpenMath/GeneralLinearMethod.lean` (line 154) as
   `m.IsConsistent ∧ m.IsStable`, mirroring the LMM-side two-conjunct
   `IsConvergent` shape from
   `OpenMath/DahlquistEquivalence.lean:493`.

2. Added `ButcherTableau.toGLM_isConvergent` in `OpenMath/RKAsGLM.lean`
   (line 153) as a two-line `⟨_, _⟩` composition of the existing
   `toGLM_isConsistent` and `toGLM_isStable` sanity checks.

3. For the LMM-side stability lift, evaluated the four-phase decomposition
   in the strategy:
   * Phase 1 — combinatorial bound on first `s` iterates.
   * Phase 2 — h·f slots zero after `n ≥ s` iterates.
   * Phase 3 — y-slot bound from zero-stability through
     `stableRecurrence_of_zeroStable` /
     `uniformly_bounded_tupleSucc_iterates`.
   * Phase 4 — combine.

## Result

* SUCCESS — §512 GLM convergence definition landed in
  `OpenMath/GeneralLinearMethod.lean`.
* SUCCESS — RK-side sanity check `ButcherTableau.toGLM_isConvergent`
  landed in `OpenMath/RKAsGLM.lean`.
* DEFERRED — LMM-side `toGLM_isStable` lift not landed this cycle. The
  strategy explicitly marks this as the "acceptable cycle 618 minimum"
  closure when the LMM lift is blocked. A focused issue file
  `.prover-state/issues/butcher_section512_lmm_stability_lift.md`
  records the concrete multi-cycle plan needed.

## Dead ends

None substantively explored. The LMM-side lift was not attempted this
cycle because the four-phase scaffolding (~200–300 lines of new proofs
plus structural V-row simp lemmas to unblock Phase 2) is well beyond a
single-cycle budget when the V-row normal forms have to be developed
from scratch. Inserting a sorry-bearing scaffold into `LMMAsGLM.lean`
(which is a tracked file with downstream consumers) would have violated
the project rule against live `sorry`s outside the active proof target.

## Discovery

* The §512 definition + RK convergence sanity check together total ~10
  lines and unblock §513 / §514 / §515 statements: any future GLM
  convergence theorem can now be stated against
  `m.IsConvergent` directly.
* The LMM-side stability lift naturally splits into four phases that
  share no proof state and can be developed independently: structural
  V-row simp lemmas (mirroring the existing `toGLM_U_castAdd` /
  `toGLM_U_natAdd` pattern) are the right next-cycle target because
  every phase consumes them.
* `GeneralLinearMethod.IsStable` is over `ℝ` while
  `uniformly_bounded_tupleSucc_iterates` is over `ℂ`. Phase 3 needs
  an `(· : ℝ → ℂ)` coercion for the input vector and
  `Complex.norm_real` to bring the bound back. This is a known gotcha
  that should be documented inline once the lift lands.

## Suggested next approach

Split the LMM-side stability lift into ≥3 cycles:

1. **Cycle 619 (recommended)**: Land structural V-row simp lemmas in
   `OpenMath/LMMAsGLM.lean`:
   * `toGLM_V_castAdd_shift_apply` for past-y shift rows.
   * `toGLM_V_castAdd_last_apply` for the LMM update row.
   * `toGLM_V_natAdd_shift_apply` for h·f shift rows.
   * `toGLM_V_natAdd_last_apply` for the zero last-h·f row.
   These mirror the existing `toGLM_U_castAdd` (line 87) and
   `toGLM_U_natAdd` (line 92) and unblock Phases 1–3.

2. **Cycle 620**: Phase 2 — `toGLM_V_iter_eq_zero_on_hf_slots`. Bottom-up
   induction on `n` and `k`, no spectral input needed. This is the
   cleanest of the four phases.

3. **Cycle 621**: Phase 1 (combinatorial first-`s`-iterates bound) +
   Phase 3 (y-slot bound from zero-stability). These can share helper
   lemmas; the ℝ → ℂ coercion belongs here.

4. **Cycle 622**: Phase 4 (combine) + close `toGLM_isStable` and
   `toGLM_isConvergent` as one-liners. After this, Backlog #1
   (§513 / §514 GLM Dahlquist) opens cleanly.

The §521 stability-order predicate scaffold (cycle 616, reverted) stays
gated behind §512–§515 closing per the strategy.
