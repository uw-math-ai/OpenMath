# Cycle 314 Results

## Worked on

`thm:342C` clause **(342o)** `B(2s) ∧ D(s) ⇒ E(s, s)` (Butcher §342,
3rd ed., p. 238). Partner of cycle 313's clause (342m): same
conclusion `E(s, s)`, same `B(2s)` half of the hypothesis, but
routed through the adjoint condition `D(s)` rather than the
collocation condition `C(s)`. Shipped as a generic algebraic
bridge in the §321 B/C/D/E abstract predicate API.

Deliverable:
`OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesD`
in `OpenMath/Chapter3/Section321.lean` (inserted immediately after
the cycle 313 `satisfiesE_of_satisfiesB_satisfiesC` block), plus a
non-vacuity `example` exercising it through `gaussLegendre1Stage`
(`B(2) ∧ D(1) ⇒ E(1, 1)`).

## Approach

Followed the strategy file's tactic recipe verbatim (mirror of
cycle 313's (342m) proof with a sum-swap prefix and the
`(1 − c_j^k)` split):

1. **Sum-swap** `∑ᵢ ∑ⱼ → ∑ⱼ ∑ᵢ` via `Finset.sum_comm` — the key
   structural change from (342m), needed so that `D(s)` (which
   fixes column `j` and sums over rows `i`) can be applied per
   column.
2. **Factor** `c_j ^ (l - 1)` out of the inner `i`-sum (per column
   `j`) via a `show … = …` rewrite + `Finset.mul_sum` + `ring`.
3. **Apply `D(s)`** at exponent `k` per column `j` to reduce
   `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ / k) (1 − cⱼ^k)`.
4. **Distribute `(1/k)` and split** `c_j^(l-1) · (b_j/k) · (1 − c_j^k)
   = (1/k) · (b_j · c_j^(l-1) − b_j · c_j^((k+l)-1))` using the
   exponent identity `(l - 1) + k = (k + l) - 1` (omega, since
   `1 ≤ l`) and `pow_add`. The inner equality was discharged by
   `field_simp` (which used `hk_ne` in scope); the trailing `ring`
   suggested by the strategy was redundant ("No goals" — field_simp
   closed it).
5. **`Finset.sum_sub_distrib`** to unpack the `∑ j (X_j - Y_j)` into
   `∑ X_j - ∑ Y_j`.
6. **Apply `B(2s)`** at exponents `l` (legal: `1 ≤ l ≤ s ≤ 2s`) and
   `k + l` (legal: `1 ≤ k + l ≤ 2s` by `omega` from `1 ≤ k ≤ s` and
   `1 ≤ l ≤ s`).
7. **Arithmetic closure** `(1/k)(1/l − 1/(k+l)) = 1/(l(k+l))` via
   `push_cast` (to normalize `((k + l : ℕ) : ℝ)` to `(k : ℝ) + (l : ℝ)`),
   followed by `field_simp` (using `hk_ne`, `hl_ne`, and an
   explicit `hkl_real_ne : (k : ℝ) + (l : ℝ) ≠ 0` derived via
   `positivity`), then `ring`.

Non-vacuity example mirrors cycle 313's pattern: build `B(2)` and
`D(1)` witnesses for `gaussLegendre1Stage` (using `interval_cases` +
`simp [gaussLegendre1Stage] + norm_num` — the `D(1)` body matches
the existing hand-built `gaussLegendre1Stage.SatisfiesD 1`
witness exactly), then feed them to the new bridge.

## Result

**SUCCESS** — axiom-clean ship.

Verification:

* `lake env lean OpenMath/Chapter3/Section321.lean` → exit 0
  (only required edit: drop the trailing `ring` after the inner
  `field_simp` in the per-`j` rewrite — field_simp closed the goal
  by itself).
* `lake build OpenMath.Chapter3.Section321` → success (3.5s).
* `lake build OpenMath.Chapter3` → success (5.9s; only warnings are
  pre-existing linter notes in `Section342.lean` lines 1414, 1418,
  3672 — unrelated to this cycle).
* `grep -c sorry OpenMath/Chapter3/Section321.lean` → 0.
* `#print axioms
  OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesD`
  → `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no
  custom axioms.
* `#print axioms
  OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesC`
  (cycle 313 regression check) → still
  `[propext, Classical.choice, Quot.sound]`. No regression.

Net file delta: ~115 LOC added (~85 LOC theorem + docstring,
~20 LOC non-vacuity example, ~10 LOC blank/comment lines).

## Faithfulness check

New theorem: `satisfiesE_of_satisfiesB_satisfiesD`.

* **Entity ID**: `thm:342C` (clause (342o)).
* **Textbook statement** (quoted from
  `extraction/formalization_data/entities/thm_342C.json`
  `statement_latex`):
  > `B(2s) \land D(s) \Rightarrow E(s, s)`     (342o)
* **Lean statement captures**: *same content* — flat implication
  `M.SatisfiesB (2 * s) → M.SatisfiesD s → M.SatisfiesE s s`, with
  hypothesis pack expressed as named hypotheses `hB`/`hD` and
  conclusion `M.SatisfiesE s s` (the §321 `E(η, ζ)` predicate at
  `η = ζ = s`).
* **Tautology check**: ✓ Conclusion `M.SatisfiesE s s` does NOT
  appear among hypotheses (`M.SatisfiesB (2 * s)`,
  `M.SatisfiesD s` — distinct §321 predicates).
* **Identity check**: ✓ Proof is structural, multi-step
  `have`/`rw`/`show` composition (~85 LOC); NOT a one-line
  `exact h_*` re-export.
* **Definition smuggling check**: ✓ No new `def`/`class`/`structure`.
  The §321 B/D/E predicates were audited cycle 306 and match
  Butcher §321 verbatim (B p. 171, D p. 173, E p. 174 eq. (321c)).
* **Hypothesis strength check**: ✓ Hypotheses match Butcher's
  (342o) exactly. `SatisfiesB (2 * s)` is needed at exponent `k + l`
  with `k + l ≤ 2s` (full strength used). `SatisfiesD s` is needed
  at exponent `k` with `1 ≤ k ≤ s` (full strength used). Neither
  can be weakened.
* **No extra hypotheses**: ✓ No `0 < s` precondition. At `s = 0`
  the bound `1 ≤ k ≤ 0` forces `hkl_lo`/`hkl_hi` to derive `False`
  via `omega` early, so the quantifier in `M.SatisfiesE 0 0` is
  vacuously satisfied (matches cycle 313's (342m) signature).

The non-vacuity `example` is unnamed and has no faithfulness
obligation; its body is a direct application of the new theorem
plus hand-built `B(2)` and `D(1)` witnesses (which match the
existing hand-built `gaussLegendre1Stage.SatisfiesD 1` and
`gaussLegendre1Stage.SatisfiesB 2` examples at lines 317–321 and
328–332 of `Section321.lean`).

## Dead ends

* **Inner `ring` after `field_simp` was redundant.** The strategy's
  recipe ended the per-`j` rewrite with `field_simp; ring`, but
  on first compile this produced "No goals to be solved" at the
  `ring]` closing bracket. Removing the trailing `ring` was the
  only edit needed beyond the verbatim recipe — `field_simp`
  using `hk_ne` in scope already discharges the polynomial
  identity. This was a minor 30-second fix.

No other dead ends; the proof tracked the strategy verbatim.

## Discovery

* **`field_simp` is sometimes too eager.** When the strategy's
  recipe ends with `field_simp; ring`, expect `field_simp` to
  occasionally close the goal alone — leaving `ring` to throw
  "No goals". This is exactly the pattern seen in cycle 313's
  (342m) inner rewrite, where the recipe also ended with just
  `field_simp` (no trailing `ring`). Worth noting for future
  algebraic-composition cycles: if `field_simp` is the last
  visible step in the cycle 313 (342m) recipe, expect the same
  in (342o)-style proofs.

* **The (342m)/(342o) symmetry is genuinely tight.** The two
  proofs share ~70% of their body structure verbatim: same
  `have hX_pos`/`hX_ne` boilerplate, same `have h_outer :
  (∑ᵢ ∑ⱼ …) = (1 / k) · (… - …)` outer-rewrite shape, same
  `B(2s)` application at the combined exponent, same
  `push_cast + field_simp + ring` closure. The only structural
  asymmetries are (a) the `Finset.sum_comm` prefix in (342o)
  (forcing the column-first viewpoint that `D(s)` natively
  expresses), and (b) the `Finset.sum_sub_distrib` step in
  (342o) needed to unpack the `(1 − c_j^k)` split. This
  symmetry suggests that future Vandermonde-converse clauses
  (342n)/(342p) — which invert (342m)/(342o) respectively —
  should also share substantial body structure, motivating a
  unified treatment if/when they ship.

* **`positivity` cleanly discharges `(k : ℝ) + (l : ℝ) ≠ 0`** when
  `hk_pos` and `hl_pos` are in scope. Useful for the final
  `field_simp` close in algebraic-composition proofs that
  introduce summed casts. Faster than spelling out
  `linarith [hk_pos, hl_pos]` or `add_pos hk_pos hl_pos |> ne_of_gt`.

## Suggested next approach

Three candidates for cycle 315, in approximate order of strategic
value:

1. **`thm:342C` Vandermonde-converse pair (342n) + (342p)**
   `B(2s) ∧ E(s, s) ⇒ C(s)` and `B(2s) ∧ E(s, s) ⇒ D(s)`. These
   are the structural converses of (342m) and (342o) shipped this
   cycle. Per Butcher's proof (p. 238, "because the matrix
   multiplier is non-singular"), the proof recipe is: build the
   weighted Vandermonde matrix
   `V_{kj} := b_j · c_j^{k-1}`, show it's non-singular (via
   `Polynomial.vandermonde_invertible` or hand-built — requires
   distinct `c_j`, which is a side hypothesis), and use that
   non-singularity to invert the (342m)/(342o) implications.
   Estimated ~150 LOC each; can ship as a paired cycle since the
   proof skeletons are symmetric. Note that "distinct `c_j`" is
   NOT a §321 predicate hypothesis — it's a side condition that
   the Gauss–Legendre tableau satisfies automatically (by cycle
   302's `_zeros_strictMono`) but a general `RKTableau` might
   not. This may require a new abstract hypothesis or a side
   condition on the tableau.

2. **`thm:344A` Radau/Lobatto methods** (§344, p. 244). The
   natural next user of the §321 B/C/D/E API, now strengthened
   with both algebraic clauses (342m) and (342o). Builds the
   Radau IA/IIA and Lobatto IIIA/IIIB/IIIC families as concrete
   `RKTableau`s and proves their B/C/D order via the abstract
   bridges. Likely multi-cycle (each family is ~200-300 LOC), but
   the first family (Radau IA) is a single-cycle target.

3. **`cor:359B` / `lem:359A` consumers of `thm:342C`**. These are
   the immediate downstream dependents listed in the formalization
   data. May be tractable single-cycle targets if they only need
   the (342m)/(342o) algebraic clauses already shipped.

The planner should probably pick (1) — the Vandermonde-converse
pair — because it strengthens the abstract toolkit *before* the
Radau/Lobatto pivot, and because the paired structure means
shipping them together amortizes the matrix-inversion
infrastructure cost across two clauses. (2) is the second-best
target if (1) is judged too expensive for one cycle.

Do NOT pursue (342j)/(342k)/(342l) — they involve `G(2s)` and
remain blocked on the unformalized `thm:314A` elementary-
differential / B-series order condition infrastructure, which is
multi-cycle prerequisite work.
