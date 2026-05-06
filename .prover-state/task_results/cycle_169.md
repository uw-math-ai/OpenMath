# Cycle 169 Results

## Worked on

* **`thm:454A`** — `LinearMultistepMethod.gStable_isAStable`
  (Butcher Theorem 454A: a G-stable LMM is A-stable, §454, p. 387).
* **BDF2 corollary** — `bdf2LMM_isAStable` (BDF2 is A-stable),
  by composing cycle 165's `bdf2LMM_isGStable` with Theorem 454A.

Both targets landed in a single commit, axiom-clean. Stretch goal
(start a new entity such as `def:422B` or `def:442A`) was skipped to
preserve cleanliness; the planner queue can pick that up next cycle.

## Approach

Followed the strategy's named-decomposition playbook (cycle 168's
pattern). Seven private helpers in
`OpenMath/Chapter4/Section454.lean`'s `Section404` namespace block
(immediately after the existing `Section454` block):

| Helper | Role |
|---|---|
| `gMatrix_quadForm_re_nonneg` | Step 4: `LHS.re ≥ 0` via PSD lift |
| `G_quadForm_W₁_re_pos` | Step 5: `(W₁* G W₁).re > 0` via PD lift + `vanW₁ w 0 = 1` |
| `one_sub_normSq_re_pos` | Step 6: `0 < 1 - ‖w‖²` |
| `alpha_div_beta_re_pos_of_star_alpha_beta_re_pos` | Step 8: `Re(α/β) > 0` ← `Re(star α · β) > 0` |
| `star_beta_alpha_re_eq_star_alpha_beta_re` | Glue: cross-term symmetry |
| `mul_re_of_real_complex` | Glue: `((1 - r) · z).re = (1 - r).re · z.re` |
| `star_alpha_beta_re_pos` | Step 7: analytic core; composes Steps 4–6 + identity |

The main theorem `LinearMultistepMethod.gStable_isAStable` is then a
3-line composition of Step 7 + Step 8.

The BDF2 corollary `bdf2LMM_isAStable` is a one-liner discharging
`hk : 0 < 2` with `by norm_num` and applying cycle 165's
`bdf2LMM_isGStable`.

## Result

**SUCCESS** — both theorems closed axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Sorry count remains 0
across `Section454.lean` and `Section454Aux.lean`. No
`maxHeartbeats` bumps.

## Faithfulness check

### `LinearMultistepMethod.gStable_isAStable`

* **Entity ID**: `thm:454A`. Statement quoted from
  `extraction/formalization_data/entities/thm_454A.json`:
  > A G-stable linear multistep method is A-stable.

* **Lean signature**:
  ```
  theorem LinearMultistepMethod.gStable_isAStable {k : ℕ}
      (M : LinearMultistepMethod k) (hk : 0 < k) (hG : M.IsGStable) :
      M.IsAStable
  ```

* **Lean statement captures**: weaker (with documented divergence)
  — adds `(hk : 0 < k)` precondition. The textbook proof and BDF2
  worked example implicitly assume `k ≥ 1`; LMMs with `k = 0` are
  degenerate (Butcher §404 introduces LMMs with `k ≥ 1` throughout).
  Mirrors cycle 109's `0 < s` precondition on `thm:515D` (analogous
  GLM degeneracy guard).

* **`IsAStable` is the boundary-locus form** (already documented in
  the existing file-level docstring, cycle 166) — not a new
  divergence.

* **Tautology / identity / definition-smuggling checks**: the
  hypothesis `hG : M.IsGStable` is unfolded via `obtain ⟨G, _, hPD,
  hPSD⟩` and all three of `G`, `hPD`, `hPSD` are used (as the matrix
  witness, in Step 5, and in Step 4 respectively). The `hk` is used
  in Step 5. The conclusion `0 < (α/β).re` is genuine — derived via
  Steps 4–8, not re-exported from any hypothesis.

### `bdf2LMM_isAStable`

* No new mathematical content; corollary of two existing theorems.
* `IsAStable` is non-vacuous in the positive direction (BDF2 is
  A-stable) complementing cycle 166's negative witness
  `explicitEulerLMM_not_isAStable`. The predicate is now confirmed
  refutable (explicit Euler) and satisfiable (BDF2).

## Dead ends

Three minor pitfalls hit during initial drafting; all fixed within
the cycle (none required strategy revision):

1. **`Complex.star_def` rewrite no-op.** After `Complex.mul_re`, the
   goal already shows `starRingEnd ℂ` not `star`, so `rw
   [Complex.star_def]` errored with "Did not find an occurrence of
   the pattern `star`". Fixed by `show ((starRingEnd ℂ) z * w).re =
   …` to expose the `Complex.conj_re` / `Complex.conj_im` form
   directly.

2. **`div_add_div_same` deprecated and reversed.** The replacement
   is `add_div` with the opposite direction; switched the rewrite
   to `← add_div`.

3. **Symmetric rewrite over-matching.** The lemma
   `star_beta_alpha_re_eq_star_alpha_beta_re` has the form
   `(star β * α).re = (star α * β).re`; naive `rw` matches BOTH
   cross-term occurrences in the identity (with metavariables
   instantiated in opposite directions) and rewrites them
   inconsistently. Fix: instantiate the lemma at the specific
   `Polynomial.aeval w (αPoly M)` / `Polynomial.aeval w (βPoly M)`
   arguments first via `have hsymm := …`, then `rw [hsymm]` matches
   only the second term.

## Discovery

* The `vanW₁ w ⟨0, hk⟩ = 1` non-vanishing witness is best discharged
  by `show w ^ (0 : ℕ) = 1` followed by `pow_zero w`, which avoids
  any need to unfold `vanW₁` via `simp`/`rfl` games.

* `Complex.normSq_pos` (`0 < normSq z ↔ z ≠ 0`) is the cleanest
  bridge from `β ≠ 0` to `0 < Complex.normSq β` for the
  `div_pos`-style finisher in Step 8.

* For arithmetic over real-coerced complex factors (Step 7's
  `(1 - ‖w‖²) · z`), `Complex.mul_re` plus `Complex.sub_im /
  Complex.one_im / Complex.ofReal_im` collapsing the imaginary part
  to 0 is more reliable than `push_cast` / `simp` here.

* Cycle 168's pre-shipped `algebraic_identity_454A` and the two
  Aux helpers carried the entire weight of the analytic content.
  This cycle's seven helpers are all glue (`.re` extraction +
  symmetry + sign rearrangement); each ≤ ~15 LOC. **The
  named-decomposition playbook scaled cleanly here.**

## Suggested next approach

Chapter 4's §454 cluster is now complete (`def:451A`, `thm:454A`,
`bdf2LMM_isGStable`, `bdf2LMM_isAStable` all closed; the negative
witness `explicitEulerLMM_not_isAStable` was already in cycle 166).

Recommended next targets, in priority order:

1. **`def:442A`** (principal sheet, §441) — listed in the strategy
   as a stretch backup. Pure structural definition; non-vacuity
   should fit in <100 LOC.

2. **`def:422B`** (underlying one-step method, §422) — the other
   strategy backup. Also structural, similarly small.

3. **`thm:243A`** (Ch.2→Ch.4 deferral) — long-deferred per
   `FORMALIZATION_DATA_GUIDE.md`. Worth a fresh look now that §451
   / §454 infrastructure exists.

4. **A-stability ↔ boundary-locus equivalence** — currently
   `IsAStable` is the boundary-locus form *only*. Closing the
   equivalence with the standard "stability region contains the
   closed left half-plane" form would strengthen the cycle 166
   divergence note. This requires §351 / boundary-locus
   infrastructure that is not yet in the codebase; would be a
   multi-cycle effort.

Status update: 70 → 71/175 entities formalised (`thm:454A`
closed). `bdf2LMM_isAStable` is a non-counted helper corollary in
the same file.
