# Cycle 319 Results

## Worked on

Phase C.1 of `thm:344A`: small-`s` explicit-root theorems for the
Radau I, Radau II, and Lobatto polynomial families defined in
cycle 317. Six new theorems in
`OpenMath/Chapter3/Section344.lean`, appended after the cycle 318
orthogonality block (file 469 → 585 LOC, +116 LOC).

Deliverables:
* `butcherRadauI_one_root` — root `x = 0` of `2X`.
* `butcherRadauI_two_roots` — roots `x ∈ {0, 2/3}` of `6X² − 4X`,
  with distinctness `0 ≠ 2/3`.
* `butcherRadauII_one_root` — root `x = 1` of `2X − 2`.
* `butcherRadauII_two_roots` — roots `x ∈ {1/3, 1}` of
  `6X² − 8X + 2`, with distinctness `1/3 ≠ 1`.
* `butcherLobatto_two_roots` — roots `x ∈ {0, 1}` of `6X² − 6X`,
  with distinctness `0 ≠ 1`.
* `butcherLobatto_three_roots` (P3 stretch — shipped) — roots
  `x ∈ {0, 1/2, 1}` of `20X³ − 30X² + 10X`, with three pairwise
  distinctness clauses.

## Approach

Followed the planner's strategy verbatim:
1. Read cycle 317's small-`s` polynomial closed forms at
   `Section344.lean:179–263` to confirm the rewrite targets
   (`butcherRadauI_one`, `butcherRadauI_two`, etc.).
2. Appended the six theorems after the cycle 318
   `butcherLobatto_orthogonal_to_lower_degree` non-vacuity
   examples (line 467).
3. Each proof: `rw [closed_form]` → `simp` (or
   `simp only [Polynomial.eval_*] + norm_num` for rational
   non-zero arguments) → `norm_num` for distinctness clauses.
4. Verified compilation incrementally with `lake env lean
   OpenMath/Chapter3/Section344.lean`.
5. Verified each theorem axiom-clean via `lean_verify`.
6. Verified aggregator `OpenMath/Chapter3.lean` builds clean.
7. Updated `plan.md` line 102 (`thm:344A` row) to reflect Phase
   C.1 ship.

## Result

SUCCESS — all six theorems shipped axiom-clean
(`[propext, Classical.choice, Quot.sound]` only); no sorries
introduced; sorry count 0 → 0.

Observed deviations from planner's draft proofs (minor):
* The planner-suggested `simp [Polynomial.eval_sub, ...]` for
  endpoint cases worked even more concisely as bare `simp`
  (since `simp` already includes the polynomial-eval lemmas).
  Used bare `simp` for the four endpoint cases (`eval = 0`).
* Two cases (`butcherRadauII 2` at `x = 1`, `butcherLobatto 3`
  at `x = 1`) initially failed with bare `simp` because the
  arithmetic `6 - 8 + 2 = 0` and `20 - 30 + 10 = 0` were left
  unsolved. Switched to `simp only [Polynomial.eval_*] +
  norm_num` (matching the planner's R5 mitigation pattern). Both
  closed cleanly.

LOC: 116 added (close to the planner's ~110 P1 + ~35 P3-stretch
budget envelope; under the 200 LOC abort threshold).

Build times: `Section344.lean` recompiles in ~4.6s on warm cache;
`Chapter3.lean` aggregator recompiles in ~4.5s. No heartbeat
issues anywhere.

## Faithfulness check

For each new theorem (no new `def`/`structure`/`class` introduced):

### `butcherRadauI_one_root`
* Entity: substantiates `thm:344A` clause I (Radau I, `c_1 = 0`)
  at `s = 1`. Textbook (Butcher §344 p. 244, quoted from
  `extraction/formalization_data/entities/thm_344A.json`):
  > For the Radau I formula, c1 = 0.
* Lean statement captures: same content (at `s = 1`, the
  Radau I polynomial vanishes at `0`).
* Tautology check: conclusion `eval 0 = 0` not present in
  hypotheses (no hypotheses).
* Identity check: proof is `rw [butcherRadauI_one]; simp`, doing
  real evaluation work (rewriting `2X` and evaluating at `0`).
* Hypothesis strength: no hypotheses; universal numerical fact.

### `butcherRadauI_two_roots`
* Entity: substantiates `thm:344A` clause I at `s = 2`.
  Textbook (verbatim above).
* Lean statement captures: same content (Radau I at `s = 2` has
  `0` and `2/3` as roots; the two roots are distinct, anchoring
  the strict ordering `c_1 < c_2` from the textbook).
* Tautology, identity, strength checks: pass (analogous).

### `butcherRadauII_one_root`
* Entity: substantiates `thm:344A` clause II (Radau II,
  `c_s = 1`) at `s = 1`. Textbook:
  > For the Radau II formula, cs = 1.
* Lean statement captures: same content.
* Tautology, identity, strength checks: pass.

### `butcherRadauII_two_roots`
* Entity: substantiates `thm:344A` clause II at `s = 2`.
* Lean statement captures: same content (`1/3` and `1` are roots;
  distinctness anchors strict ordering).
* Tautology, identity, strength checks: pass.

### `butcherLobatto_two_roots`
* Entity: substantiates `thm:344A` clause III (Lobatto,
  `c_1 = 0`, `c_s = 1`) at `s = 2`. Textbook:
  > For the Lobatto formula, c1 = 0, cs = 1.
* Lean statement captures: same content (at `s = 2`, both
  endpoints are roots; distinctness `0 ≠ 1`).
* Tautology, identity, strength checks: pass.

### `butcherLobatto_three_roots`
* Entity: substantiates `thm:344A` clause III at `s = 3`.
* Lean statement captures: same content (`0`, `1/2`, `1` are
  roots; pairwise distinctness establishes three abscissae).
* Tautology, identity, strength checks: pass.

### Definition smuggling
None — no new `def`/`structure`/`class`. All six theorems
operate on the cycle 317 polynomial definitions and cycle 317
closed-form lemmas, both already in the file.

### Hypothesis strength
None of the six theorems take hypotheses; the small-`s` roots
are universal numerical facts. Distinctness clauses are
independent numerical facts (no `linarith` chain needed; closed
by `norm_num`).

## Dead ends

* **`simp` over-reduction at non-zero rational arguments**:
  For `(butcherRadauII 2).eval (1 : ℝ)` and `(butcherLobatto 3
  ).eval (1 : ℝ)`, bare `simp` after `rw [closed_form]` left the
  arithmetic residual `6 - 8 + 2 = 0` / `20 - 30 + 10 = 0`
  unsolved. Switched to `simp only [Polynomial.eval_*] +
  norm_num` per the planner's R5 mitigation. Worked first try.

  This is a one-line cost; would not warrant decomposing the
  proof or writing a helper lemma.

* No other dead ends — the entire cycle was mechanical `rw +
  simp + norm_num`.

## Discovery

* **`simp` vs `simp only` decision rule for `Polynomial.eval`
  arithmetic**: when the residual after `simp [Polynomial.eval_*]`
  is `0 = 0` (endpoint roots), bare `simp` works because the
  default simp set includes both the eval lemmas and basic
  arithmetic. When the residual is a non-trivial arithmetic
  identity (`6 * (2/3)^2 - 4 * (2/3) = 0`,
  `6 - 8 + 2 = 0`), bare `simp` either over-reduces or stalls;
  `simp only [Polynomial.eval_*] + norm_num` is the safe pattern.
  Cycle 294's `butcherShiftedLegendre_one_root` uses the same
  decision rule.

* **Distinctness clauses**: `(0 : ℝ) ≠ 2/3`, `(0 : ℝ) ≠ 1`,
  `(0 : ℝ) ≠ 1/2`, `(1/2 : ℝ) ≠ 1` all close by single
  `norm_num` invocations. No `linarith` needed; `norm_num`
  handles literal-rational inequalities directly.

* **Conjunctive theorem packaging**: bundling all roots + all
  pairwise distinctness clauses into one named theorem
  (`butcherLobatto_three_roots` has six conjuncts: 3 roots + 3
  distinctness pairs) is idiomatic and allows downstream callers
  to destructure with a single `obtain ⟨h₀, h_half, h₁, _, _, _⟩`
  pattern. This matches cycle 294's pattern for the §342
  `butcherShiftedLegendre_two_roots`.

* **Existence of cycle 318 `example` blocks**: the file already
  carried four anonymous `example` non-vacuity witnesses
  (Section344.lean:270–280) that fired the cycle 317 closed
  forms at endpoint roots. Cycle 319's `_one_root` named
  theorems supersede those for downstream citation; the
  anonymous examples remain as additional sanity checks (kept,
  not removed).

## Suggested next approach

Per the planner's cycle 320 entry-point hint, three options:

(a) **Small-`s` Lagrange weights** for the cycle 319 abscissae —
    `butcherRadauI_quadratureWeights_{one,two}`,
    `butcherRadauII_quadratureWeights_{one,two}`,
    `butcherLobatto_quadratureWeights_{two,three}`, mirroring
    cycle 303's `butcherShiftedLegendre_quadratureWeights`
    construction restricted to the small-`s` abscissae from
    this cycle. Stepping stone to Phase D RKTableau construction
    (Radau IA/IIA, Lobatto IIIA/IIIB/IIIC). ~30 LOC per weight
    set. **Recommended** — clean follow-up that unblocks
    small-`s` Phase B.2 and provides RKTableau-side non-vacuity
    witnesses.

(b) **General-`s` Phase C** — attempt the §344 analog of cycle
    301's `butcherShiftedLegendre_n_distinct_real_zeros`. Higher
    risk: endpoint-zero factoring (`x` for Radau I,
    `(x − 1)` for Radau II, `x(x − 1)` for Lobatto) requires
    careful bookkeeping on the residual quotient before the
    sign-change argument applies. Multi-cycle.

(c) **Pivot to fresh entity** — e.g., `thm:302C` (Rooted Tree
    Enumeration Formulas) or one of the open §380 entities.

Recommend **(a)** for cycle 320: clean follow-up with low risk
and direct downstream relevance to the eventual `RKTableau`
construction.

A note on Phase B.2 (polynomial-exactness for Radau I): per the
cycle 318 task results, Phase B.2 needs Lagrange-interpolation
infrastructure at the (yet-unconstructed) Radau abscissae. Cycle
319's small-`s` root theorems are the abscissae-side prerequisite
for the small-`s` slice of Phase B.2 (`R.natDegree < s` Lagrange
collapse for `s ∈ {1, 2, 3}`). If cycle 320 ships option (a),
cycles 321+ can attempt the small-`s` slice of Phase B.2 as a
stepping stone to general-`s` Phase B.2.
