# Cycle 104 Results

## Worked on

- `aux_515B_lipschitz_bridge` (line 906, was sorry → closed manually).
- `GeneralLinearMethod.localStepError_bound` (line 999, was sorry →
  closed via composition of three sub-lemmas).
- `aux_515B_eta_contraction` (line 931, sorry → triaged: deferred
  with structured issue file).
- Aristotle status check (Priority 0, ONE poll only).
- `lean_status.json`, `plan.md` updates.

## Approach

**Priority 0 — Aristotle check.** One status poll on
`4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`: `IN_PROGRESS` at 2%.
Per CLAUDE.md, no further polling this cycle.

**Priority 1 — `aux_515B_lipschitz_bridge`.** Manual closure
(~50 LOC) following the structural pattern of `aux_T4_bound`
(cycle 101, same file): peel out the leading `h` via `abs_mul`,
push `|·|` inside the sum via `Finset.abs_sum_le_sum_abs`, apply
the Lipschitz bridge `LipschitzWith.dist_le_mul` summand-wise,
and reorganize.

**Priority 2 — `localStepError_bound` composition.** Decomposed the
bound into three pieces, each closed by an existing or new helper:
1. `Yhat_j := yex(xn1 + h c_j)` (exact ODE values at abscissae)
   and `y_prev_k := u_k yex(xn1) + v_k h yex'(xn1)` introduced as
   `let` definitions.
2. The exact-side residual `R_i` is bounded by
   `localStageError_bound_b` (515A).
3. The per-stage residual on `Yhat` is bounded by
   `localStageError_bound_a` (515A) for each `j`.
4. `K_i = h Σ B·(f(Y) − f(Yhat)) − R_i` (algebraic key
   identity, by `ring`).
5. The Lipschitz piece is bounded by `aux_515B_lipschitz_bridge`.
6. The η contraction estimate
   `|η_j − Σ U·δ| ≤ h L Σ|A|·|η| + h²L²M(½c_j² + Σ|A·c|)` is
   derived from (4) and the per-stage residual (3).
7. `aux_515B_eta_contraction` is applied as a black box (its
   proof remains `sorry`) to get
   `|η_j| ≤ ell_U_j δ_max + h²L²M phi_A_j`.
8. Final triangle inequality plus `_hα_def`, `_hβ_def`, and
   `h ≤ h₀` collapse the bound to `α h δ_max + β h²`.

Total proof size: ~190 LOC (compositional).

**Priority 3 — `aux_515B_eta_contraction`.** Default decision (b-i
in the cycle 104 strategy): defer with a structured issue file
documenting the M-matrix infrastructure gap. See
`.prover-state/issues/lem_515B_eta_contraction_deferred.md`.

## Result

**SUCCESS** — Sorry count delta: 3 → 1.

* `aux_515B_lipschitz_bridge` — closed (sorry removed).
* `localStepError_bound` — closed (sorry removed).
* `aux_515B_eta_contraction` — remains `sorry`, deferred with
  issue file.

Build: `lake build OpenMath.Chapter5.Section515` succeeds with
exactly one `sorry` warning (line 973, `aux_515B_eta_contraction`).

Axiom check (after `lake build`):
* `localStepError_bound` axioms: `[propext, sorryAx,
  Classical.choice, Quot.sound]`. The `sorryAx` is from the
  transitive use of `aux_515B_eta_contraction` (which is `sorry`).
  Will become clean once cycle N+1+ closes the M-matrix
  infrastructure and the η contraction.

## Faithfulness check

### `aux_515B_lipschitz_bridge` (private helper, no entity)

A pure helper lemma; not an entity in `formalization_data/`. The
statement encodes the textbook Lipschitz-bridge step
`|f(Ŷ_j) − f(Y_j)| ≤ L |Ŷ_j − Y_j|` summed against `Σ B_{ij}`.
- Tautology check: conclusion ≠ any hypothesis.
- Hypothesis check: requires `0 ≤ L`, `LipschitzWith L.toNNReal f`,
  `0 ≤ h`. All necessary; none extraneous.

### `GeneralLinearMethod.localStepError_bound` (lem:515B)

Entity `lem:515B`, textbook statement (from
`extraction/formalization_data/entities/lem_515B.json`):
> Under the conditions of Lemma 515A, the exact and computed
> solutions in a step are related by `ỹ_i^[n] − y_i^[n] =
> Σ_j V_{ij}(ỹ_j^[n−1] − y_j^[n−1]) + K_i^[n]`, with
> `‖K^[n]‖ ≤ h α max|ỹ^[n−1] − y^[n−1]| + β h²`, and `α`, `β`
> determined by linear systems involving `(I − h₀ L|A|)^{−1}`.

Lean statement captures: **same content, with documented
encoding choices** (proxy parameters; documented in the
docstring at lines 967–1001 of Section515.lean).

**Encoding deviations** (no new ones from cycle 104; the four
listed in cycle 103 still apply):
1. `α`, `β`, `δ_max` are parametric upper bounds (proxy
   parameters with side conditions), not the textbook's `Finset.sup`
   maxima. Strictly weaker — any valid choice works. The user can
   instantiate them with the textbook's `Finset.sup` formulas to
   recover the original bound.
2. `ell_U`, `phi_A` are parametric vectors with linear-system
   side conditions, not constructed via `(I − h₀ L|A|)^{−1}`.
   Will be discharged once M-matrix infrastructure is in place.
3. `‖K^[n]‖_∞` is encoded as `∀ i, |K i| ≤ ...`, equivalent.
4. `α ≥ L Σ_j |B_{ij}| ell_U_j` (per-row), not the textbook's
   `α = L max_i |ℓ_i|` (which appears to assume `Σ_j |B_{ij}| ≤ 1`,
   not stated in the textbook). This was already documented in
   the cycle 103 docstring.

**No new faithfulness deviations introduced this cycle.** The
K-witness `K i := LHS − Σ V·δ` makes the identity clause a
`ring` identity, and the bound clause is the textbook chain
`R + h Σ B·(f(Y)−f(Ŷ)) → R + h L Σ|B|·|η| → α h δ_max + β h²`.

## Dead ends

None this cycle — the manual proof of
`aux_515B_lipschitz_bridge` worked first try (after copying the
shape of `aux_T4_bound`), and the composition for
`localStepError_bound` worked on the second attempt (initial
attempt failed because the K-witness `(fun i => ...) i` did not
beta-reduce automatically inside `|·|`, requiring a `show`
tactic to expose the explicit form before the algebraic
rearrangement; also `Finset.sum_add_distrib` did not match
`Σ b·(x + y)` directly, requiring a manual distributive `ring`
step first).

## Discovery

* **`let`-bound functions in proof contexts unfold definitionally**
  for absolute-value rewrites: with `let η := fun j => Y j − Yhat j`,
  the term `|η k|` is *definitionally* equal to `|Y k − Yhat k|`,
  so calls to `aux_515B_lipschitz_bridge` (which produce
  `Σ |·| * |Y_hat j − Y j|`) match the η form without a `congr` or
  `simp` step. Avoid `congr 1` here — the goal collapses to `rfl`
  immediately, and `congr` will then complain "no goals".

* **Beta-reduction of refine-introduced lambdas**: when using
  `refine ⟨fun i => ..., ?_, ?_⟩` for `∃ K, ... ∧ ...`, the goal
  for the second clause is `|(fun i => ...) i| ≤ ...`, which
  contains an unreduced beta-redex. `rw` will not see through it.
  Use a `show` tactic with the explicit beta-reduced form to
  expose it first.

* **`Finset.sum_add_distrib` requires the summand to literally
  be `f x + g x`**: it does NOT distribute through
  `Σ x, c x * (f x + g x)`. For the latter, manually distribute
  with `Finset.sum_congr ... ring` first to convert to
  `Σ x, (c x * f x + c x * g x)`, then apply `sum_add_distrib`.

## Suggested next approach

**Cycle 105 priorities** (in decreasing order of value):

1. **Check Aristotle status** for project
   `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`. If it returned a proof
   for `aux_515B_eta_contraction` (likely too hard for Aristotle,
   but worth checking), incorporate it. This would close the last
   §515 sorry and complete `lem:515B` with clean axioms.

2. **Begin M-matrix infrastructure** (`OpenMath/Chapter5/MMatrix.lean`
   or extend `Section515.lean`). Target: define `IsMMatrix M : Prop`
   and prove `(I − cM)^{−1} ≥ 0` for `M ≥ 0`, `c ≥ 0`,
   `c·ρ(M) < 1`. This is the long-term unblock for
   `aux_515B_eta_contraction` (estimated 2–3 cycles total). Mathlib
   pointers: search for `Matrix.IsM`, `Matrix.inv`, Neumann series
   lemmas. See `.prover-state/issues/lem_515B_eta_contraction_deferred.md`
   for the full proof outline.

3. **Begin `lem:515C` scaffold** (Accumulated error estimate for
   multistep methods, depends on `lem:515B`). The dependency on
   `localStepError_bound` is now satisfied (modulo the
   `sorryAx` from η contraction, which is acceptable since
   `lem:515C`'s proof structure should be analogous to `cesaro_*`
   §514). Sorry-first scaffold + Aristotle batch.

Recommendation: **option 2** is most valuable. M-matrix
infrastructure unblocks not only `aux_515B_eta_contraction` but
likely also future `lem:515C` analysis and any Chapter 5 GLM
stability work. Once landed, the η contraction closes in a few
lines.

Option 3 is also viable as a parallel track if option 2 stalls.
