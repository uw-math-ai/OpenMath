# Cycle 070 Results

## Worked on
`thm:405C` — `LinearMultistepMethod.convergent_isConsistent`
(Section405.lean:241→256). Closed the second of the three reverse-direction
sorries that scaffold `thm:243A`'s iff packager.

## Approach
Followed the planner's "two-way split on `T := Σ_{Fin k} ((i.val:ℝ) + 1) * M.α i.succ`"
strategy.

**Step 1 — Aristotle status check (single-shot, per CLAUDE.md "1 check at 30 min").**
Project `4ddc0ab0-9542-49ab-abf1-fa7f5601df37` from cycle 069 was at
`IN_PROGRESS, 10%` after ~1h45m. Per planner instructions ("if < 50% don't poll
again"), abandoned for this cycle and proceeded with manual proof.

**Step 2 — Algebraic helpers (factored as local `have`s, not separate lemmas).**

- `hPre := M.convergent_isPreconsistent hConv` — preconsistency from cycle 069.
- `hsum_α : (∑ i : Fin (k+1), M.α i) = 0` — peel `α 0 = -1` off
  preconsistency `1 = ∑ Fin k, α.succ`.
- `hsum_iα : (∑ i : Fin (k+1), (i.val:ℝ) * M.α i) = T` — peel the `i = 0`
  term (which vanishes since `i.val = 0`) via `Fin.sum_univ_succ`, then
  `Finset.sum_congr` + `push_cast; ring` on the residual.
- `hLHS_collapse : ∀ A m n, 0 < m → Σ M.α i · (A · ((n+k - i.val : ℕ):ℝ) / m) =
   -A·T/m` — the algebraic heart. Cast `((n+k - i.val : ℕ):ℝ)` to
  `(n+k:ℝ) - (i.val:ℝ)` via `Nat.cast_sub` (using `i.val ≤ k ≤ n+k`),
  then expand and apply `hsum_α` (kills the `(n+k)` coefficient) and
  `hsum_iα` (extracts `T`).

**Step 3 — Case split on `T = 0` vs `T ≠ 0`.**

*Case `T = 0` (vacuous via contradiction):* Use the trivial IVP
`y' = 0, y(0) = 0` (`f ≡ 0`, `yex ≡ 0`, `M_bound = 0`) with
`Y m n := (n:ℝ) / (m:ℝ)` and `start h i := (i.val:ℝ) * h`.
The LMM-recurrence at this `Y` collapses to `-T/m = 0`, which holds by
`hT_zero`. So `Y` is an LMM solution. By `hConv`,
`Y m m - yex 1 → 0`. But `Y m m = m/m = 1` for `m > 0`, so
`Y m m - 0 = 1`, which converges to `1 ≠ 0`. Contradiction via
`tendsto_nhds_unique`.

*Case `T ≠ 0` (main argument):* Set `A := S / T` (where `S := ∑ M.β i`),
so `A · T = S` (via `field_simp`). Use the trivial IVP `y' = 1, y(0) = 0`
(`f ≡ 1`, `yex t = t`, `M_bound = 1`) with `Y m n := A · n / m` and
`start h i := A · i · h`. The LMM-recurrence at this `Y` collapses to
`-A·T/m = -(1/m) · S`, which holds by `hA_T`. By `hConv`,
`Y m m - yex 1 → 0`. But `Y m m - yex 1 = A·m/m - 1 = A - 1` for
`m > 0`, so `A - 1 = 0`, i.e., `A = 1`. Then `S = A·T = T`, hence
`T = S`. ✓

**Cast handling.** The repeated pattern was bridging
`((n + k - i.val : ℕ) : ℝ)` to `(n+k:ℝ) - (i.val:ℝ)` via
`Nat.cast_sub hile` followed by `push_cast; ring`. Once factored into
the `hLHS_collapse` helper, both branches reused it.

**Hypothesis discharge for `IsConvergent`.** Eight obligations per branch
(joint Lipschitz, `ContDiff ℝ 1 yex`, etc.). Reused the cycle-069 boilerplate
from `convergent_isPreconsistent` (Section405.lean:124-171), adapting:

- `T = 0` branch: same as cycle 069 (`f ≡ 0`, `yex` constant), but
  `yex := 0` instead of `1`, `start := fun h i => i.val · h` instead of
  constant 1, `Y := fun m n => n/m` instead of `homogeneousFromOnes`.
- `T ≠ 0` branch: `f := fun _ _ => 1`, `yex := id` (use `contDiff_id`,
  `hasDerivAt_id`), `M_bound := 1`, `start := fun h i => A · i · h`,
  `Y := fun m n => A · n / m`.

## Result
**SUCCESS.** `OpenMath/Chapter4/Section405.lean` compiles with only
the two pre-existing cosmetic warnings (lines 50, 60 — unused
variables in `homogeneousFromOnes`'s decreasing_by) and the cycle-071
scaffold sorry at line 97 (`thm:405A` `convergent_isStable`).
`#print axioms LinearMultistepMethod.convergent_isConsistent` shows
only `propext, Classical.choice, Quot.sound`. `lake build` completes
with all 8030 jobs.

The `thm:243A` iff packager
(`isConvergent_iff_isStable_and_isConsistent`) now type-checks against
a fully-proven `convergent_isConsistent`; only `convergent_isStable`
remains as the last reverse-direction sorry.

Sorry count in Section405.lean: **2 → 1**.

## Faithfulness check
For the new theorem `convergent_isConsistent` (entity `thm:405C`):

- **Entity ID**: `thm:405C`. Textbook statement (from
  `extraction/formalization_data/entities/thm_405C.json`):
  > "A convergent linear multistep method is consistent."
- **Lean statement**: `(hConv : M.IsConvergent) → M.IsConsistent`.
  Captures: **same content**.
- **Tautology check**: `IsConsistent` is the conjunction of two
  non-trivial equations (`IsPreconsistent` and `SatisfiesEq404b`) on
  `M.α, M.β`; conclusion ≠ any hypothesis. ✓
- **Identity check**: proof is non-trivial (case split on `T`,
  algebraic LMM-recurrence collapse, two `hConv` applications +
  limit arguments + `tendsto_nhds_unique`); not `exact h`. ✓
- **Hypothesis strength check**: only `M.IsConvergent`, matching the
  textbook exactly. ✓ (The strengthening of `IsConvergent` itself
  was deliberate per cycle 068's
  `is_convergent_strengthened.md`; not introduced this cycle.)
- **Definition smuggling check**: no new definitions.
- **Absent theorem check**: no promised-but-missing helpers; all
  `have`s are inline with full proofs.
- **Proof-side deviation from textbook**: the Lean proof side-steps
  Butcher's appeal to `thm:405A` (used in the textbook to derive
  `T ≠ 0` from stability). Instead, we case-split on `T`. In
  `T = 0` we apply `hConv` to the homogeneous solution `n/m` and
  derive `1 → 0` contradiction; this is a Lean-friendly substitute
  for Butcher's "method would not be stable" appeal. The conclusion
  matches Butcher's exactly; only the proof tactic differs.
  Documented in the theorem's docstring (Section405.lean:227-254).

## Dead ends
- First-pass `push_cast [Nat.cast_sub hile]` in the cast helper left
  an unsolved `↑n + ↑k - ↑↑i = ↑n + ↑k - ↑↑i` goal. Fixed by switching
  to `rw [Nat.cast_sub hile]; push_cast; ring`.
- First-pass `field_simp [hT_zero]` for `A * T = S` (where
  `A := S / T`) failed. Fixed by `rw [hA_def]; field_simp`.
- First-pass `rw [hA_T]` to substitute `A * T = S` in `-A * T / m`
  failed because `-A * T` parses as `(-A) * T`, not `-(A*T)`.
  Fixed by `rw [show -A * T = -(A * T) from by ring, hA_T]`.
- First-pass `(Filter.tendsto_congr' h).mpr hconst` had the eventual
  equality direction backwards (`hm.symm` instead of `hm`); the
  congruence wants `f₁ =ᶠ f₂` where `f₁` is the unknown limit
  source — fixed by `exact hm` (no symm).

## Discovery
- The `T = 0 ↔ T ≠ 0` split is structurally cleaner than the
  three-way split sketched in the planner's first-pass
  ("`S = 0 ∧ T ≠ 1` etc.") and avoids the `S(T-1) = 0` red herring
  that doesn't follow from the LMM equation alone. The planner's
  "Fallback recommended sub-strategy" (set `A := S/T` in the
  `T ≠ 0` branch) is exactly what worked.
- For `T = 0`, the `Y m n := n/m` witness is even cleaner than the
  planner's suggested `Y m n := S · n / m` because it doesn't
  require `S = 0` to be an LMM solution — it's an LMM solution iff
  `T = 0`, period. The contradiction `1 → 0` is also cleaner than
  the planner's `0 → 1` (no need to know `S` at all).
- `hLHS_collapse` is a strong reusable algebraic kernel — any
  future LMM-stability/consistency argument that needs to evaluate
  the LMM-recurrence on a linear sequence `A · n / m` can quote it
  directly. Worth promoting to a top-level Section405 lemma in a
  future cycle if `thm:405A` reuses it.

## Suggested next approach
1. **Cycle 071**: close `thm:405A` (`convergent_isStable`,
   Section405.lean:97). This is the harder of the remaining two; per
   the planner's note in the Section405 docstring (lines 86-94),
   Butcher's argument uses an unbounded homogeneous solution `η`,
   running max `ζ_n := max_{i≤n} |η_i|`, and convergence applied to
   `η_i / ζ_n` to derive `|η_n / ζ_n| → 0` against `|η_n / ζ_n| = 1`
   on a record-index subsequence. Lean strategy: `IsHomogeneousSolution`
   linearity (closed under scalar multiply and add); decompose
   `IsStable` via classical contradiction; build the running-max
   sequence + record-index pigeonhole.
2. The Priority 2 helper signatures suggested by the planner
   (`unboundedSeq_max`, `unboundedSeq_max_records`,
   `IsHomogeneousSolution.const_smul`) are useful scaffolding for
   cycle 071. Submit those to a fresh Aristotle batch at the top of
   cycle 071 — Aristotle's premise selection should handle the
   linearity lemma and the sup-recursion mechanically.
3. After `thm:405A` lands, the `thm:243A` iff packager will be
   fully proven (zero sorries in Section405.lean) and the
   cross-chapter Ch.2→Ch.4 deferral is closed.
4. **Promote `hLHS_collapse` to a top-level lemma** if cycle 071 also
   needs it (likely — `thm:405A`'s contrapositive will instantiate
   `hConv` on a linear `Y m n := η_n / ζ_m` and need the same
   algebraic collapse).
