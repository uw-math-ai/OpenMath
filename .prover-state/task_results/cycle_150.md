# Cycle 150 Results

## Worked on

Two priorities, both completed per the cycle 150 strategy:

1. **Priority 1 (CRITICAL recovery)**: Rolled back cycle 149's
   def:530B sorry-first scaffold from
   `OpenMath/Chapter5/Section530.lean` per the cycle 138 → cycle 139
   precedent. Removed: the `applyStartingThenStep` and
   `applyExactThenStarting` operator defs (sorry'd), the
   `HasOrderRelativeTo` predicate, the
   `explicitEulerGLM_hasOrderZero_trivialStarting` non-vacuity
   witness (sorry'd), three new imports, and the
   `OrderRelativeToStartingMethod` section block.
2. **Priority 2 (substantive)**: Added the n = 7 stepping stone
   `doublyCompanionMatrix_det_factorization_n_seven` for thm:550A
   to `OpenMath/Chapter5/Section550.lean`, axiom-clean.

Aristotle single-poll on project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (cycle 148 fire-and-forget
general-n attempt) returned IN_PROGRESS at 18 % — left running per
strategy.

## Approach

### Priority 1 (rollback)

Removed cycle 149's four declarations from `Section530.lean` plus
the entire `OrderRelativeToStartingMethod` section block and
docstring. Removed the three new imports
(`Mathlib.Analysis.Asymptotics.Defs`,
`Mathlib.Analysis.Calculus.Deriv.Basic`,
`OpenMath.Chapter5.Section510`) since the rollback removed all
their consumers. Verified post-rollback that the cycle 139/141
infrastructure (`GeneralizedRungeKuttaMethod`, `StartingMethod`,
`IsDegenerate` / `IsNonDegenerate`, all four witnesses
`trivialStartingMethod`, `zeroStartingMethod`, `mixedStartingMethod`,
`zero2StartingMethod`) remained intact and compiles clean.

Bookkeeping: reverted def:530B in `lean_status.json` to
`unformalized` (clearing `lean_file` / `lean_symbol`) and in
`plan.md` from `[~]` back to `[ ]`. Created issue file
`.prover-state/issues/def_530B_scaffold_strategy.md` documenting
the rollback rationale, the structural insight that sorry-first
scaffolding does not work for def:530B (operator bodies are
indivisible multivariate fixed-point computations), and Path A
(explicit-only, ~2-3 cycles) and Path B (general implicit via
`ContractingWith` / `Function.IsFixedPt`, ~3-5 cycles) for future
closure cycles.

### Priority 2 (n = 7 stepping stone)

Applied the cycle 148 four-layer Laplace template scaled by one
nesting level:
* Reduce `doublyCompanionMatrix α β` at n = 7 to an explicit
  7×7 `!![…]` form via
  `ext i j; fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]`.
* Reduce `1 - z • X` to a second 7×7 `!![…]` form via
  `fin_cases` + `first | (simp; ring) | simp`.
* Expand the 7×7 determinant via four-layer nested Laplace
  expansion: outer `Matrix.det_succ_row_zero` gives seven 6×6
  cofactor terms; each 6×6 → six 5×5 via `(n := 5)`; each 5×5 →
  five 4×4 via `(n := 4)`; each 4×4 → four 3×3 via `(n := 3)`;
  close every 3×3 minor by `Matrix.det_fin_three`.
* Close the `IsBigO` via `Asymptotics.IsBigO.of_bound` with
  constant `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖`, where
  the residue factors as
  `z⁸ · (a + z·b + z²·c + z³·d + z⁴·e + z⁵·f + z⁶·g)` with the
  seven convolution coefficients
  (each a negated sum of α·β products following the cycle 148
  pattern).

**Heartbeat overflow** required a structural split. The naive
one-shot `simp [...; alphaPoly; betaPoly]; ring` (cycle 148
template) blew past 200 000 heartbeats (timeout at `whnf` during
simp normalization of the ~5 040-monomial raw expansion plus the
alphaPoly·betaPoly polynomial product). Per cycle 150 strategy
("If the n=7 Laplace expansion times out, factor the determinant
expansion into a separate `private theorem` rather than crank the
heartbeat ceiling"), I introduced the helper:

```
private lemma matrix7_oneMinusZSmul_det (α β : Fin 7 → ℂ) (z : ℂ) :
    (!![1 + z * α 0, ..., 1 + z * β 0] : Matrix (Fin 7) (Fin 7) ℂ).det
      = 1 + (α 0 + β 0) * z + ... + (... + α 6 + β 6) * z^7 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_seven, ..., Matrix.det_fin_three, ...]
  ring
```

The main theorem `rw [hmat, matrix7_oneMinusZSmul_det]` and then
`simp [alphaPoly, betaPoly, Fin.sum_univ_seven]; ring` finishes the
residue identity. Both halves fit within default 200 000 heartbeats;
total `lake env lean` build time ~8 min.

## Result

**SUCCESS** for both priorities.

* **Priority 1**: Section530.lean compiles clean,
  `grep -c '\bsorry\b' OpenMath/Chapter5/Section530.lean` = 0,
  no remaining cycle 149 declarations. Sorry count restored to 0.
* **Priority 2**: Section550.lean compiles clean,
  `lake build OpenMath.Chapter5.Section550` succeeds in ~8 min,
  `_n_seven` axiom-clean (verified via `#print axioms`).
* **Aristotle poll**: project
  `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` returned `IN_PROGRESS`
  at 18 % (cycle 148 submission, ~24 h after cycle 149's last
  poll).

Sorry count: 3 → 0 (recovers cycle 149's −2 regression). Score
expectation: +2 (sorry restored to 0 + axiom-clean substantive
deliverable).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `private lemma matrix7_oneMinusZSmul_det`

* **Not a textbook entity** — internal helper for the n = 7
  stepping stone. Computes the explicit 7 × 7 determinant of the
  `1 - z • doublyCompanion` matrix at n = 7 as a degree-7
  polynomial in `z`. No textbook claim is being formalized; it's
  a load-bearing lemma in the n = 7 proof.
* **Tautology check**: conclusion is a polynomial identity,
  matrix-determinant equation, NOT verbatim any hypothesis.
* **Identity check**: proof body is `rw [Matrix.det_succ_row_zero];
  simp [...]; ring` — performs real computation (four-layer
  Laplace expansion + ring canonicalization).
* **Hypothesis strength check**: hypotheses are minimal
  (`α β : Fin 7 → ℂ`, `z : ℂ`); no ambient assumptions.

### `theorem doublyCompanionMatrix_det_factorization_n_seven`

* Entity ID: `thm:550A` — Theorem 550A (Butcher §550, p. 457),
  "Doubly companion matrices".
* Textbook statement (quoted from
  `extraction/formalization_data/entities/thm_550A.json`):
  > Let `\alpha`, `\beta` be column vectors in `\mathbb{C}^n` and
  > define a polynomial `\alpha(z)` by `\alpha(z) = 1 + \alpha_1 z
  > + \alpha_2 z^2 + ... + \alpha_n z^n`. Define `\beta(z)` in
  > terms of `\beta` similarly. The doubly companion matrix `X`
  > defined by `\alpha`, `\beta` has the property that
  > `\det(I - z X) = \alpha(z) \beta(z) + O(z^{n+1})`.
* **Lean statement** (n = 7 specialization) captures: **stronger**
  in scope-restriction direction (n = 7 only), but the *content* of
  the asymptotic identity is verbatim — `(1 - z • doublyCompanionMatrix
  α β).det - alphaPoly α z * betaPoly β z =O[nhds 0] z^8`. The seven
  concrete-`n` stepping stones (n = 1..7) are jointly weaker than the
  general-n statement but each is axiom-clean and witnesses the
  pattern. The general-n statement remains absent (deferred per
  `.prover-state/issues/thm_550A_general_n.md` to multi-cycle
  closure infrastructure).
* **Tautology check**: conclusion `=O[nhds 0] (· ^ 8)` does not
  appear as a hypothesis (no hypotheses other than the closed
  `α β : Fin 7 → ℂ`).
* **Identity check**: proof is multi-step real work — explicit
  matrix reduction, four-layer Laplace expansion, polynomial
  factorization, Big-O bound via `IsBigO.of_bound` — not a one-line
  hypothesis re-export.
* **Hypothesis strength check**: minimal — no extra constraints on
  `α, β` beyond `Fin 7 → ℂ`. Matches the textbook scope at n = 7.
* **Definition smuggling check**: not applicable (no new `def`
  introduced, only a private helper lemma + the public theorem).
* **Absent theorem check**: no comments promise theorems that
  don't exist in the file.

### Rollback content (Section530.lean)

No new definitions or theorems introduced; pure deletion of
cycle 149's content. Documented in
`.prover-state/issues/def_530B_scaffold_strategy.md`.

## Dead ends

### Naive cycle-148 template at n = 7 (200 000 heartbeat overflow)

First attempt copied the cycle 148 n = 6 template verbatim with
one extra Laplace layer (`Matrix.det_succ_row_zero (n := 5)`,
`Fin.sum_univ_seven`). The integrated `simp [Fin.sum_univ_seven,
..., alphaPoly, betaPoly, ...]; ring` blew past 200 000 heartbeats
(timeout at `whnf` during simp normalization). The error surfaced
twice — once during simp itself, once as a tactic-execution
heartbeat overflow — confirming the bottleneck is the combined
~5 040-monomial matrix expansion + alphaPoly · betaPoly polynomial
product fed to `ring`.

The fix per cycle 150 strategy was to factor the determinant
expansion into a `private lemma` (`matrix7_oneMinusZSmul_det`) so
the expansion `simp` runs in isolation from the alphaPoly/betaPoly
identity. Both halves fit within default heartbeats. Did NOT raise
`maxHeartbeats` per CLAUDE.md absolute rule.

## Discovery

* **Heartbeat-budget scaling: cycle 148 n = 6 used `simp [...,
  alphaPoly, betaPoly, ...]; ring` in one shot; cycle 150 n = 7
  cannot.** The combinatorial blowup factor across the four-layer
  Laplace is `7! / 6! = 7×` the cycle 148 work, plus the
  alphaPoly · betaPoly product is one more degree. Empirically the
  default 200 000 heartbeat ceiling holds at n = 6 but not n = 7.
* **The fix is mechanical**: factor the matrix-expansion `simp`
  into a `private lemma` proving `det(...) = explicit polynomial`,
  then the main theorem only needs to prove the polynomial-identity
  residue (a much smaller `ring` call). This recipe should
  generalize to n = 8 and beyond if needed, by repeating the
  factoring pattern.
* **Approximate rule of thumb for future stepping stones**: the
  cycle 148 one-shot template will likely work up through n = 6 in
  a single `simp + ring`; from n = 7 onward, the determinant
  expansion must be factored. Worth documenting in the planner's
  recipe library.
* **Build time at n = 7**: ~8 minutes with the split. Likely ~12-15
  minutes at n = 8 if the same pattern holds (extending one more
  Laplace layer).

## Suggested next approach

* **For thm:550A**: cycle 151+ poll Aristotle project
  `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (currently IN_PROGRESS
  18 %); if still running >24 h, planner decides on cancellation.
  Otherwise, continue stepping-stone series at n = 8 only if
  marginal value remains; the seven-`n` data set is already strong
  evidence for the leading-coefficient pattern.
* **For def:530B**: planner picks Path A vs Path B for the next
  attempt. Recommendation: Path A (explicit-only) is safer first —
  it's more bounded scope (~2-3 cycles), captures the most common
  textbook examples (explicit Euler, Heun, classical RK4), and
  defers the implicit infrastructure to a later cycle. Path B
  (general implicit) requires multi-cycle Lipschitz/Banach
  fixed-point machinery that would make the order-relative
  theorems heavier to use downstream.
* **Avoid sorry-first scaffolds for definitions whose bodies are
  atomic computations** (fixed-point equations, integrals,
  spectral data). The sorry-first workflow is suited to
  decompositional proofs, not atomic definitional content.
* **Cycle 150's n = 7 closure pattern** (factor heavy `simp` into
  a private lemma) should be added to the planner's recipe library
  for future high-`n` stepping-stone work.
