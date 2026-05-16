# Cycle 312 Results

## Worked on

`butcherGaussLegendreRK_satisfiesE` — Phase 3.3 of the §342 ↔ §321
`RKTableau` lift, closing the `E(n, n)` fourth prong of `cor:342D`'s
B/C/D/E quadrature characterisation for the canonical Gauss–Legendre
tableau (collocation `A`-matrix `butcherShiftedLegendre_collocationA n`,
Lagrange weights `butcherShiftedLegendre_quadratureWeights n`, shifted
Legendre zeros `butcherShiftedLegendre_zeros n`).

## Approach

Per the cycle 312 strategy §D: the proof is a *purely algebraic*
two-step composition of cycle 309's `B(2n)` and cycle 310's `C(n)` —
not an IBP repeat of cycle 311's `D(n)` recipe.

Concrete steps in the headline proof:

1. **Pre-flight signature verification (strategy §C).** Used
   `Read` on `OpenMath/Chapter3/Section321.lean` to confirm:
   - `SatisfiesE p q := ∀ k, 1 ≤ k → k ≤ p, ∀ l, 1 ≤ l → l ≤ q,
     (∑ i j, b_i · c_i^(k-1) · A_ij · c_j^(l-1)) = 1 / (l · (k + l))`
     (no `0 < p ∨ 0 < q` precondition; denominator is `l · (k+l)`).
   - `butcherGaussLegendreRK_satisfiesB n hn` takes `(hn : 0 < n)`;
     `butcherGaussLegendreRK_satisfiesC n` does not.
   - Cycle 308's coincidence theorem name is
     `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`.

   Signatures match the §D recipe exactly; no fallback needed.

2. **Inner-sum reduction via C(n).** Built `hCi := fun i =>
   butcherGaussLegendreRK_satisfiesC n i l hl1 hl` giving
   `∑ j, A_ij · c_j^(l-1) = c_i^l / l` per row `i`. The result type
   unfolds to the explicit field-named form (`(.A)`/`(.c)` reduce by
   definitional equality), so the `:= fun i => ...` ascription works
   without a `show` rewrite.

3. **Outer-sum rewrite.** Inside `h_outer`, used `rw [Finset.mul_sum]`
   to factor `(1/l)` out of the RHS, then `Finset.sum_congr rfl`
   to descend to the per-`i` equation. Inside each `i`-row: an
   internal `show ... = ... by rw [Finset.mul_sum]; sum_congr; ring`
   factors the `i`-only term `b_i · c_i^(k-1)` out of the inner
   `j`-sum, then `rw [hCi i]` substitutes the C(n) value. The
   power identity `(k-1) + l = (k+l) - 1` (for `1 ≤ k`, discharged
   by `omega`) is applied via `show ... by rw [hexp]`, then
   `pow_add` separates `c_i^((k-1)+l) = c_i^(k-1) · c_i^l`. Final
   `field_simp` (with `hl_ne : (l : ℝ) ≠ 0` in scope) closes the
   per-`i` equation. No trailing `ring` needed — `field_simp`
   already closes (verified by removing the `ring` and recompiling
   after Lean flagged "No goals to be solved").

4. **Outer B(2n) substitution.** Used
   `butcherGaussLegendreRK_satisfiesB n hn (k+l) hkl_lo hkl_hi`
   directly (definitional unfolding of `.b`/`.c` makes the result
   ascribe to the unfolded field-named form), with
   `hkl_lo : 1 ≤ k + l` (from `omega` on `h1`) and
   `hkl_hi : k + l ≤ 2 * n` (from `omega` on `hk` + `hl`). `hn`
   is derived inside the proof from `lt_of_lt_of_le hl1 hl`.

5. **Arithmetic closure.** `push_cast` lifts the natural-number
   cast `((k + l : ℕ) : ℝ) = (k : ℝ) + (l : ℝ)`, then `field_simp`
   closes the final identity `(1/l) · (1/(k+l)) = 1/(l · (k+l))`.

Plus two non-vacuity witnesses: `(butcherGaussLegendreRK 2).SatisfiesE 2 2`
(direct application) and `gaussLegendre1Stage.SatisfiesE 1 1`
(round-trip through `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`).

## Result

**SUCCESS.**

- `lake env lean OpenMath/Chapter3/Section342.lean` exits 0 in ~36s.
- `lake env lean OpenMath/Chapter3.lean` exits 0.
- `grep -c sorry OpenMath/Chapter3/Section342.lean` = 0.
- `lean_verify` on
  `OpenMath.Chapter3.Section342.butcherGaussLegendreRK_satisfiesE`
  returns axiom set
  `[propext, sorryAx, Classical.choice, Quot.sound]` — same profile
  as cycles 308–311 (the `sorryAx` is the pre-existing cycle-301
  upstream leak from `_rootsInIoo_card_ge`, not a regression).
- Headline + two non-vacuity examples + doc comments add ~125 LOC
  to `Section342.lean`.
- No new sorries, no `axiom`/`constant`, no `maxHeartbeats` bump.
- `lean_status.json` row for `cor:342D` updated with cycle 312
  symbol and partial-evidence note (overall status remains
  `unformalized` because the iff headline is multi-cycle).
- `plan.md` cor:342D row updated with partial-evidence note;
  cumulative cycle history appended to lem:342B's row.

## Faithfulness check

For the single new theorem this cycle:

- **`butcherGaussLegendreRK_satisfiesE` — Entity ID**:
  `cor:342D` partial (fourth/E(n,n) prong only).
  Textbook statement (`extraction/formalization_data/entities/cor_342D.json`):

  > A Runge–Kutta method has order 2s if and only if its
  > coefficients are chosen as follows:
  >   (i) Choose c₁, c₂, …, cₛ as the zeros of Pₛ*.
  >  (ii) Choose b₁, b₂, …, bₛ to satisfy the B(s) condition.
  > (iii) Choose aᵢⱼ, i, j = 1, 2, …, s, to satisfy the C(s) condition.

  The full iff statement quantifies `order 2s` over arbitrary RK
  methods and requires `thm:342C` + `thm:314A` (independence of
  elementary differentials) — multi-cycle infrastructure not in
  scope. The cycle 312 theorem ships *evidence* that the canonical
  Gauss–Legendre tableau (cycle 309's `butcherGaussLegendreRK n`)
  satisfies the `E(n, n)` simplifying assumption implied by the
  iff's RHS, completing the B/C/D/E package shipped across cycles
  309/310/311/312. The theorem docstring explicitly flags this
  as partial evidence.

- **Lean statement captures**: same content — the predicate
  `(butcherGaussLegendreRK n).SatisfiesE n n` is the §321
  `E(n, n)` predicate verbatim (audited in cycle 306, no
  divergence introduced this cycle). The RHS denominator is
  `(l : ℝ) * ((k : ℝ) + (l : ℝ))` matching Butcher's
  `1 / (l (k + l))`.

- **No `0 < n` precondition** on the signature (matches cycle
  310's `_satisfiesC` and cycle 311's `_satisfiesD`); positivity
  derived inside from `1 ≤ l ≤ n` via `lt_of_lt_of_le hl1 hl`.

- **Tautology check**: PASS. The conclusion
  `1 / (l · (k + l))` does not appear among the hypotheses
  (which are `1 ≤ k`, `k ≤ n`, `1 ≤ l`, `l ≤ n`). The result is a
  genuine arithmetic consequence of B(2n) at `k+l` and C(n) at `l`.

- **Identity check**: PASS. The proof is structural (multiple
  `rw`/`Finset.sum_congr`/`show` steps), not a single `exact`/
  `:= h_*`/`:= id`. The theorem does genuine mathematical work
  (composes B(2n) + C(n) into E(n,n) via algebraic manipulation).

- **Definition smuggling**: not applicable — no new `def`,
  `class`, or `structure` introduced this cycle.

- **Hypothesis strength**: the proof uses exactly the predicate's
  built-in `1 ≤ k`, `k ≤ n`, `1 ≤ l`, `l ≤ n` (plus the derived
  `hn : 0 < n`). No extra hypotheses beyond the §321/Butcher §342
  textbook derivation. Matches the strategy's `§H` requirement.

## Dead ends

One minor false start: the initial draft included a trailing
`ring` after the `field_simp` inside the per-`i` rewrite of
`h_outer`. Lean flagged "No goals to be solved" at that line —
`field_simp` already closes the goal (the LHS/RHS coincide after
denominator-clearing). Removed the dangling `ring` and recompiled
clean.

No other dead ends. The strategy §D recipe was followed verbatim;
the proof closed in one pass after the spurious `ring` removal.

## Discovery

- **C(n) composition pattern.** Cycle 310's `_satisfiesC` is
  pleasantly *composable*: `butcherGaussLegendreRK_satisfiesC n i l
  hl1 hl` returns a row-`i` equation `∑ⱼ A_ij · c_j^(l-1) = c_i^l/l`
  whose type unfolds (by definitional equality on the `.A`/`.c`
  projections) directly to the explicit field-named form. This
  means downstream consumers don't need a `show` block to bridge
  the abstract `M.A`/`M.c` form into the unfolded form — the
  `:= fun i => ...` ascription Just Works. Worth remembering for
  future §321 ↔ §342 bridges.

- **`field_simp` closes simple field identities outright.** In
  the per-`i` rewrite where the goal is
  `b · c^(k-1) · (c^l / l) = (1/l) · (b · (c^(k-1) · c^l))`, a
  single `field_simp` closes — no trailing `ring` needed. Useful
  rule: when the only operations are division by a known-nonzero
  scalar and reassociation, `field_simp` alone suffices.

- **No-IBP shortcut.** Cycle 311's task results conjectured E(n,n)
  as a "plausible 2-cycle target". The actual proof is a
  ~70-line algebraic composition — comparable to cycles 309/310,
  much smaller than cycle 311's ~140-line IBP proof. The textbook
  `E(s, s) ⇔ B(2s) ∧ C(s)` direction (Butcher §342 p. 240's
  "Conversely, ...") is *constructively* one-direction-mechanical
  once B(2n) and C(n) are in hand. This is a discovery worth
  carrying forward: structural-composition prongs are often
  shorter than analytic-machinery prongs.

## Suggested next approach

The §342 ↔ §321 bridge is now *complete on the B/C/D/E side*:
the canonical Gauss–Legendre tableau satisfies all four §321
simplifying assumptions at general `n`. The natural next steps,
in priority order:

1. **`thm:342C` scoping cycle** (Butcher §342 p. 240 main
   theorem: `RK has order 2s ⇔ B(2s) ∧ C(s) ∧ D(s)`). The
   forward direction requires `thm:314A` (independence of
   elementary differentials), which is itself multi-cycle
   prerequisite infrastructure. Cycle 313 could do *scoping*:
   read `thm:342C.json` + `thm:314A.json`, identify the
   elementary-weight infrastructure needed (Chapter 3.1
   `T_R` rooted-tree theory, BCK structure, B-series), and
   write a multi-cycle plan. Don't try to ship `thm:314A`
   itself in one cycle.

2. **`thm:342C` reverse direction (B(2s) ∧ C(s) ∧ D(s) ⇒
   order 2s)** is the harder direction and also requires
   `thm:314A`. Defer along with the forward direction.

3. **`thm:342C` partial scaffold** at fixed small `s` (e.g.
   `s = 1`, `s = 2`): the iff at concrete `s` might be
   provable directly without `thm:314A`'s full machinery,
   since elementary differentials at small order are
   enumerable. Could be a useful intermediate target if
   `thm:314A` scoping reveals a long blocker chain.

4. **Pivot to a §35x stability target** (e.g. `lem:351A`
   "Criteria for A-stability", `thm:356C` "AN stability
   necessary conditions") if §342 is genuinely capped until
   §31x infrastructure lands. The §35x stability theory is
   self-contained relative to the chapter-3 elementary-tree
   theory and could ship several axiom-clean theorems in
   isolation.

5. **Polishing pass on cycles 309–312's docstrings** — minor:
   add cross-references between the four `_satisfies{B,C,D,E}`
   theorems, document the §321 ↔ §342 bridge as a "complete
   package" in a leading module docstring. Worth doing but not
   urgent. Could pair with #1 if cycle 313 is a scoping cycle.

The cleanest cycle 313 plan: **option 1** (`thm:342C` scoping)
or, if scoping reveals a 5+ cycle blocker chain, **option 4**
(§35x pivot). Avoid option 3 (small-`s` `thm:342C`) unless
scoping reveals it's a quick win.
