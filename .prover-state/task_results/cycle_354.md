# Cycle 354 Results

## Worked on
Per the planner's §B–§C strategy:
* **P1 — `trapezoidalLMM_isStable`** in `Section404.lean` (shipped).
  Trapezoidal-rule (Crank–Nicolson) Dahlquist-stability witness:
  `k = 1`, `α 1 = 1`, homogeneous recurrence collapses to
  `y (m+1) = y m`, constant-sequence bound. Direct port of
  `explicitEulerLMM_isStable`/`implicitEulerLMM_isStable`.
* **P2 — `bdf3LMM_isStable`** in `Section451.lean` (shipped).
  BDF3 Dahlquist-stability via auxiliary-sequence + Lyapunov route.
  One private helper (`bdf3_aux_const`) plus the public theorem.

Two new public theorems + one private helper. No sorries opened. Both
files build clean.

## Approach

### P1 (trapezoidal): direct port
Inserted `trapezoidalLMM_isStable` in `Section404.lean` immediately
after `implicitEulerLMM_isStable` (line 274). Verbatim port of the
explicit/implicit Euler stability pattern — same recurrence shape
(`y (m+1) = y m`), same proof skeleton (induction on `n`, then
constant-bound `|y 0|`). 15 LOC.

### P2 (BDF3): auxiliary-sequence + Lyapunov

Math (paper-verified before writing Lean):

1. BDF3's homogeneous recurrence is
   `Y(n+3) = (18/11)·Y(n+2) − (9/11)·Y(n+1) + (2/11)·Y n`.
   The characteristic polynomial factors as
   `11z³ − 18z² + 9z − 2 = (z − 1)(11z² − 7z + 2)`, with roots
   `z = 1` and `(7 ± i√39)/22` (magnitude `√(2/11) ≈ 0.426`).
2. **Auxiliary sequence is constant**:
   `Z(n) := Y(n+2) − (7/11)·Y(n+1) + (2/11)·Y n` satisfies
   `Z(n+1) = Z(n)` by direct substitution of the recurrence. Hence
   `Z(n) = C₀ := Y 2 − (7/11)·Y 1 + (2/11)·Y 0` for all `n`.
3. **Constant particular solution**: `A := (11/6)·C₀` satisfies
   `(6/11)·A = C₀`, so `Y(n+2) = (7/11)·Y(n+1) − (2/11)·Y n + C₀`
   has unique constant solution `A`. The deviation
   `W(n) := Y(n) − A` then satisfies the homogeneous 2-term
   recurrence `W(n+2) = (7/11)·W(n+1) − (2/11)·W n`.
4. **Lyapunov form** `Q(n) := 2·W(n)² + 11·W(n+1)²` is non-increasing:
   `Q(n+1) − Q(n) = 11·W(n+2)² − 2·W(n)² − 9·W(n+1)²
                  = (−2/11)·(25·W(n+1)² + 14·W(n)·W(n+1) + 9·W(n)²)`
   where the inner quadratic form has discriminant
   `14² − 4·25·9 = 196 − 900 = −704 < 0` and is therefore non-negative
   (concretely, `25·(25a² + 14ab + 9b²) = (25a + 7b)² + 176·b²`).
5. **Boundedness**: `2·W(n)² ≤ Q(n) ≤ Q(0)`, so `W(n)²` is bounded
   by `(Y 0 − A)² + (11/2)·(Y 1 − A)²`. Then
   `|Y(n)| = |A + W(n)| ≤ |A| + |W(n)|
          ≤ |A| + √((Y 0 − A)² + (11/2)·(Y 1 − A)²)`.

**Lyapunov coefficient choice `(α, β) = (2, 11)`**: paper-derived from
the general criterion that the form
`(4β − 121α)·b² − 28β·a·b + (121α − 72β)·a² ≤ 0` be negative
semi-definite. The boundaries `α ≥ 4β/121` and `α ≤ 72β/121` give a
non-empty rational region; `(2, 11)` lies cleanly inside (verified via
`B² − AC = 14² − (−198)(−550)/121² = …` working out to `−704 < 0`
discriminant of the residual form `25a² + 14ab + 9b²`).

### Lean implementation

Two declarations added to `Section451.lean` after `bdf2LMM_isConsistent`:

* `private theorem bdf3_aux_const` — induction-on-`n` proof that the
  auxiliary sequence is constant. Uses
  `simp [bdf3LMM, Fin.sum_univ_three]` to unfold the homogeneous
  recurrence (matching the BDF2 idiom at cycle 346's
  `bdf2_solution_decomp`), then `linarith [hrec, ih]` to close.
* `theorem bdf3LMM_isStable` — main public theorem. Uses `set A`
  to abbreviate the constant, derives the 2-term recurrence for
  `Y − A` via `linarith`, then `nlinarith` with the Lyapunov SOS
  hint `sq_nonneg (25·(Y(n+1) − A) + 7·(Y n − A))` for the per-step
  monotonicity inequality. Outer induction combines per-step
  monotonicity into a uniform Q-bound; final bound uses
  `Real.sqrt_sq_eq_abs` + `abs_add_le`.

## Result
SUCCESS — both theorems shipped axiom-clean. Both files build clean.

Build evidence:
* `lake build OpenMath.Chapter4.Section404` → Built (560s)
* `lake build OpenMath.Chapter4.Section451` → Built (247s)

Axiom check (both public theorems clean):
```
'OpenMath.Chapter4.Section404.trapezoidalLMM_isStable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section451.bdf3LMM_isStable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```
(`bdf3_aux_const` is `private` and not exposed externally — `#print
axioms` from outside the namespace returns "Unknown constant", which
is the expected behaviour for a private declaration.)

## Faithfulness check

**(1) `trapezoidalLMM_isStable`** — entity `def:403A`'s predicate
`LinearMultistepMethod.IsStable`. No separate textbook theorem; the
stability of the trapezoidal rule (Crank–Nicolson) is folklore (any
LMM with `k = 1` and `α 1 = 1` is trivially zero-stable; the
characteristic polynomial `z − 1 = 0` has the simple root `z = 1` on
the unit circle).
* Lean statement: `trapezoidalLMM.IsStable` ≡ `∀ y, IsHomogeneousSolution y → ∃ C, ∀ n, |y n| ≤ C`. **Same content** as the predicate.
* Tautology check: PASS — the proof does real work (induction on the
  recurrence to show `y` is constant, then `|y 0|` bound).
* Identity check: PASS (no `exact h` re-export).
* Hypothesis-strength check: PASS (no extra hypotheses).

**(2) `bdf3_aux_const`** — private auxiliary lemma. Not a textbook
entity; the auxiliary-sequence trick is part of the proof of stability.
* Lean statement: `Y(n+2) − (7/11)·Y(n+1) + (2/11)·Y n = Y 2 − (7/11)·Y 1 + (2/11)·Y 0` for all `n`, given `bdf3LMM.IsHomogeneousSolution Y`.
* Mathematical content: paper-verified above (§2 of approach).
* Tautology / Identity / Hypothesis-strength: all PASS.

**(3) `bdf3LMM_isStable`** — entity `def:403A`'s predicate at BDF3.
BDF3 stability is standard (Butcher §403/§441 establish BDF3 satisfies
the root condition: roots of `11z³ − 18z² + 9z − 2 = 0` are `1` (simple
on unit circle) and a conjugate pair of magnitude `√(2/11) < 1`).
* Lean statement: `bdf3LMM.IsStable` ≡ the predicate; the proof
  exhibits a uniform bound for every homogeneous-recurrence solution.
* Tautology / Identity / Hypothesis-strength: all PASS — the proof is
  a Lyapunov decomposition, not a hypothesis re-export.

## Dead ends

* **Index normalisation gotcha**: the induction-step `succ n` goals
  initially had `Y (n + 1 + 1)` and `Y (n + 1 + 2)`, while the
  `simp [bdf3LMM, Fin.sum_univ_three]`-derived recurrence and the
  manually stated `hWrec` hypothesis used `Y (n + 2)` and `Y (n + 3)`.
  `linarith` happened to unify the two forms in `bdf3_aux_const`, but
  `nlinarith` in the Lyapunov step **did not** — fix was to insert
  `show … = …` clauses normalising the goal to `Y (n + 2)`/`Y (n + 3)`
  notation before invoking the tactic. This is the standard
  `Nat.add_assoc` defeq-vs-syntactic gap.
* **Over-eager `rw [hY_decomp]`**: `rw [hY_decomp]` (where
  `hY_decomp : Y n = A + (Y n - A)`) recursively rewrote `Y n`
  inside the `Y n - A` subterm on the calc's RHS, producing the
  un-normal-form `|A + (A + (Y n - A) - A)|`. Replaced with
  `congr 1; ring` which reduces `|x| = |y|` to `x = y` then closes
  by ring.
* **Lyapunov coefficient `(α, β) = (2, 11)`**: paper-verified cleanly
  on first attempt (discriminant `−704 < 0`), no dead-end exploration.

## Discovery

* **The `(α, β) = (2, 11)` Lyapunov pair for BDF3 stability is
  rational-clean**: the residual quadratic form `25·a² + 14·a·b + 9·b²`
  decomposes as `((25a + 7b)² + 176·b²)/25`, which `nlinarith` can
  prove via the SOS hint `sq_nonneg (25·a + 7·b)` plus `sq_nonneg b`.
  This avoids needing complex-number machinery or trigonometric
  closed-form solutions for the conjugate-pair root structure.
* **Auxiliary-sequence + Lyapunov is the canonical route for higher-k
  LMM stability with complex roots in the closed unit disc**, as
  opposed to BDF2's real-roots closed-form decomposition route
  (cycle 346's `bdf2_solution_decomp`). For BDF3 specifically, the
  characteristic polynomial's factor `11z² − 7z + 2` (the part
  contributing complex roots) directly gives the auxiliary-sequence
  coefficients `(7/11, −2/11)`.
* **The general Lyapunov criterion for 2-term recurrences**: for
  `W(n+2) = p·W(n+1) + q·W n`, the form `α·W(n)² + β·W(n+1)²` is
  non-increasing iff `(α − q²β)·b² + 2pqβ·a·b + (β·p² + α − β)·a² ≤ 0`
  is negative semi-definite, giving paper-checkable constraints
  `α ≥ q²β / (1 − p² + something)` etc. (Specific to `p = 7/11`,
  `q = −2/11`: `β = 11, α = 2` works.) This template will likely apply
  to BDF4 / Adams stability proofs in future cycles.

## Suggested next approach

With both `trapezoidalLMM_isStable` and `bdf3LMM_isStable` shipped,
all four §404 LMM witnesses (explicit Euler, implicit Euler,
trapezoidal, BDF2, BDF3) now have stability + consistency. Plausible
cycle 355 directions:

1. **Phase D′.2.2 Step 2** (the original Phase D′ target): prove
   `0 ≤ Σᵢ (i+1)²·α(i.succ)` under stable + preconsistent +
   order ≥ 2. The cycle 351 algebraic identity reduces this to a
   polynomial-derivative positivity claim. With more LMM witnesses
   available (BDF3 in particular), the motivation for an unconditional
   Phase D′ corollary is stronger. **Substantive but multi-cycle**.
2. **`trapezoidalLMM_sum_β_pos`** (Section422.lean, ~5 LOC) —
   compose `trapezoidalLMM_isStable` + `trapezoidalLMM_isConsistent`
   through cycle 349's `sum_β_pos_of_stable_consistent`. Guaranteed
   one-cycle close; exercises today's stability ship at a downstream
   consumer.
3. **`bdf3LMM_isGStable`** (Section451.lean, ~50–80 LOC) — port
   cycle 346's G-stability route to BDF3 with a textbook G-matrix.
   Requires looking up the BDF3 G-witness (not currently in
   codebase); medium risk.
4. **`bdf3LMM_sum_β_pos`** (Section422.lean) — analogous to (2)
   but at BDF3. Closes another consumer of today's stability ship.

Recommended: **(2) trapezoidalLMM_sum_β_pos** as a guaranteed
one-cycle ship that exercises today's stability work, OR **(1)
Phase D′.2.2 Step 2** as the principled multi-cycle next target.
