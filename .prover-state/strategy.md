# Cycle 314 Strategy — `thm:342C` clause (342o): `B(2s) ∧ D(s) ⇒ E(s, s)`

## A. Target

Ship the **second** algebraic clause of `thm:342C` (Butcher §342, p. 238):

> `B(2s) ∧ D(s) ⇒ E(s, s)`     (342o)

This is the partner of cycle 313's clause (342m) — same conclusion
`E(s, s)`, same `B(2s)` half of the hypothesis, but with `D(s)`
replacing `C(s)`. Like (342m), this clause is purely algebraic in the
abstract `RKTableau` B/C/D/E predicates of §321 and requires zero new
infrastructure.

**Deliverable**: a new theorem
`OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesD`
inserted into `OpenMath/Chapter3/Section321.lean` immediately after
the cycle 313 `satisfiesE_of_satisfiesB_satisfiesC` block (line 207),
plus one non-vacuity `example` exercising it through
`gaussLegendre1Stage`.

## B. Why this is the right target

Per cycle 313's task results §"Suggested next approach":

> **Clause (342o) `B(2s) ∧ D(s) ⇒ E(s, s)`** — the partner algebraic
> clause sketched in cycle 313 strategy §D. Sum-swap LHS via
> `Finset.sum_comm`, apply `D(s)` per column `j` at exponent `k`,
> collapse via `B(2s)` at exponents `l` and `k + l`, arithmetic
> close `(1/k)(1/l - 1/(k+l)) = 1/(l(k+l))`. Estimated ~90 LOC.
> No new infrastructure needed; pure algebraic composition like
> (342m). High-confidence single-cycle target.

The Vandermonde-converse clauses (342n)/(342p) are deferred — they
need a non-singular-matrix argument (~150 LOC each) and should ship
as a pair in a separate cycle. The G(2s)-involving clauses
(342j)/(342k)/(342l) remain blocked on unformalised `thm:314A`
elementary-differential infrastructure (multi-cycle).

## C. Proof recipe (concrete tactic script)

The proof is a mirror of cycle 313's (342m) proof at
`OpenMath/Chapter3/Section321.lean:207-254`, with the following
substitutions:

1. **Sum-swap first** (the key structural change): apply
   `Finset.sum_comm` to swap `∑_i ∑_j` to `∑_j ∑_i`. This puts the
   `D(s)` shape `∑_i b_i · c_i^(k-1) · A_{ij} = (b_j/k)(1 - c_j^k)`
   in the inner sum.
2. **Per column** apply `D(s)` at exponent `k` (legal: `1 ≤ k ≤ s`).
3. **Distribute** `(1/k)` and split the resulting `b_j · c_j^(l-1) ·
   (1 - c_j^k) = b_j · c_j^(l-1) - b_j · c_j^((k+l)-1)`.
4. **Apply `B(2s)` twice** — at exponents `l` (legal: `1 ≤ l ≤ s ≤
   2s`) and `k+l` (legal: `1 ≤ k+l ≤ 2s`).
5. **Arithmetic close**: `(1/k) · (1/l - 1/(k+l)) = 1/(l·(k+l))`
   via `field_simp` + `ring`.

### Concrete skeleton (use this verbatim; the body slots in directly)

```lean
/-! ### Butcher §342 Theorem 342C, clause (342o) — `B(2s) ∧ D(s) ⇒ E(s, s)`

Clause (342o) of the seven-way `thm:342C` equivalence:

>     `B(2s) ∧ D(s) ⇒ E(s, s)`            (342o)

This is the partner of (342m) shipped cycle 313: same conclusion
`E(s, s)`, but routed through `D(s)` (the adjoint condition) rather
than `C(s)` (the collocation condition). Like (342m), the proof is
purely algebraic in the §321 B/C/D/E predicates.

Proof recipe:

1. Sum-swap `∑ᵢ ∑ⱼ` → `∑ⱼ ∑ᵢ` via `Finset.sum_comm`.
2. Factor `c_j ^ (l - 1)` out of the inner `i`-sum (per column `j`).
3. Apply `D(s)` at exponent `k` per column `j` to reduce
   `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ / k)(1 - cⱼ^k)`.
4. Distribute `(1/k)` and use `1 - cⱼ^k` to split into two sums:
   `bⱼ cⱼ^{l-1} - bⱼ cⱼ^{(k+l)-1}`.
5. Apply `B(2s)` at exponents `l` and `k+l` to reduce both sums.
6. Close via `(1/k)(1/l - 1/(k+l)) = 1/(l(k+l))` with `field_simp + ring`.

No `0 < s` hypothesis required. -/
theorem satisfiesE_of_satisfiesB_satisfiesD {s : ℕ}
    (M : RKTableau s) (hB : M.SatisfiesB (2 * s))
    (hD : M.SatisfiesD s) :
    M.SatisfiesE s s := by
  intro k h1 hk l hl1 hl
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast h1
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  -- Step 1: D(s) at exponent k, per column j.
  have hDj : ∀ j : Fin s,
      (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j)
        = (M.b j / (k : ℝ)) * (1 - M.c j ^ k) :=
    fun j => hD j k h1 hk
  -- Step 2: sum-swap, factor c_j^(l-1) out per column, apply D(s),
  -- expand the (1 - c_j^k) split, and re-express both sums in B(2s)
  -- shape.
  have h_outer :
      (∑ i : Fin s, ∑ j : Fin s,
        M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
      = (1 / (k : ℝ)) *
        ((∑ j : Fin s, M.b j * M.c j ^ (l - 1))
          - ∑ j : Fin s, M.b j * M.c j ^ ((k + l) - 1)) := by
    rw [Finset.sum_comm]
    -- Goal: ∑_j ∑_i (b_i · c_i^(k-1) · A_ij · c_j^(l-1)) = ...
    rw [show (∑ j : Fin s, ∑ i : Fin s,
              M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
            = ∑ j : Fin s, M.c j ^ (l - 1) *
              (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j) by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    -- Apply D(s) per column j.
    rw [show (∑ j : Fin s, M.c j ^ (l - 1) *
              (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j))
            = ∑ j : Fin s, M.c j ^ (l - 1) *
              ((M.b j / (k : ℝ)) * (1 - M.c j ^ k)) by
        apply Finset.sum_congr rfl
        intro j _
        rw [hDj j]]
    -- Split each summand: c_j^(l-1) · (b_j/k) · (1 - c_j^k)
    --                   = (1/k) · (b_j · c_j^(l-1) - b_j · c_j^((k+l)-1))
    rw [show (∑ j : Fin s, M.c j ^ (l - 1) *
              ((M.b j / (k : ℝ)) * (1 - M.c j ^ k)))
            = (1 / (k : ℝ)) * ∑ j : Fin s,
              (M.b j * M.c j ^ (l - 1)
                - M.b j * M.c j ^ ((k + l) - 1)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hexp : (l - 1) + k = (k + l) - 1 := by omega
        rw [show M.c j ^ ((k + l) - 1)
              = M.c j ^ ((l - 1) + k) by rw [hexp]]
        rw [pow_add]
        field_simp
        ring]
    rw [Finset.sum_sub_distrib]
  rw [h_outer]
  -- Step 3: B(2s) at exponents l and k + l.
  have hl_hi : l ≤ 2 * s := by omega
  have hkl_lo : 1 ≤ k + l := by omega
  have hkl_hi : k + l ≤ 2 * s := by omega
  have hB_l : (∑ j : Fin s, M.b j * M.c j ^ (l - 1))
                = 1 / ((l : ℕ) : ℝ) :=
    hB l hl1 hl_hi
  have hB_kl :
      (∑ j : Fin s, M.b j * M.c j ^ ((k + l) - 1))
        = 1 / ((k + l : ℕ) : ℝ) :=
    hB (k + l) hkl_lo hkl_hi
  rw [hB_l, hB_kl]
  -- Step 4: arithmetic closure.
  -- (1/k) · (1/l - 1/(k+l)) = 1/(l · (k+l)).
  push_cast
  field_simp
  ring
```

### Likely tactic snags & fallbacks

* **`Finset.sum_sub_distrib` direction.** Mathlib provides
  `Finset.sum_sub_distrib : ∑ x ∈ s, (f x - g x) = (∑ x ∈ s, f x) -
  (∑ x ∈ s, g x)`. We need the **forward** direction to convert the
  `∑_j (X_j - Y_j)` shape into `∑ X_j - ∑ Y_j`. Use `rw
  [Finset.sum_sub_distrib]` (no arrow). If the name has drifted in
  the pinned Mathlib version, try `lean_local_search "sum_sub"` —
  alternatives include `Finset.sum_sub_distrib`, `Finset.sum_sub`,
  or expanding via `simp only [← Finset.sum_sub_distrib]`.
  **Five existing files** in the repo already use this lemma
  (Sections 319, 381, 441, 454Aux, 515); grep them for the exact
  spelling if any uncertainty arises.

* **`hexp : (l - 1) + k = (k + l) - 1`.** Closed by `omega` because
  `1 ≤ l` (from `hl1`) ensures the Nat subtraction is well-behaved.
  Same pattern as cycle 313 (which used `(k - 1) + l = (k + l) - 1`).

* **`field_simp` + `ring` final close.** If `field_simp` leaves a
  goal that `ring` cannot close because of the `(l : ℝ)` and
  `((k + l : ℕ) : ℝ)` casts not aligning, run `push_cast` *before*
  `field_simp` (as written above) so all natural-number arguments
  push outward to `ℝ` numerals first.

* **Inner `ring` after `pow_add`.** After
  `rw [show M.c j ^ ((k + l) - 1) = M.c j ^ ((l - 1) + k) by ...,
      pow_add]`, the summand is
  `M.c j ^ (l - 1) · ((M.b j / k) · (1 - M.c j ^ k))
   = (1/k) · (M.b j · M.c j ^ (l - 1)
              - M.b j · (M.c j ^ (l - 1) · M.c j ^ k))`.
  `field_simp` followed by `ring` should discharge this, since
  `k ≠ 0` (we have `hk_ne` in scope). If `field_simp; ring` stalls,
  try the more aggressive `field_simp [hk_ne]; ring` or split into
  two rewrites.

## D. Non-vacuity witness

Add one `example` after the cycle 313 `gaussLegendre1Stage`
non-vacuity block (currently lines 341–358 of `Section321.lean`):

```lean
/-- *Non-vacuity for the abstract (342o) clause via `gaussLegendre1Stage`.*
The implicit-midpoint tableau satisfies `B(2)` and `D(1)` (existing
witnesses above), so the abstract bridge
`RKTableau.satisfiesE_of_satisfiesB_satisfiesD` yields `E(1, 1)`. -/
example : gaussLegendre1Stage.SatisfiesE 1 1 :=
  gaussLegendre1Stage.satisfiesE_of_satisfiesB_satisfiesD
    (hB := by
      intro k h1 hk
      interval_cases k
      · simp [gaussLegendre1Stage]
      · simp [gaussLegendre1Stage])
    (hD := by
      intro j k h1 hk
      interval_cases k
      simp [gaussLegendre1Stage]
      norm_num)
```

The `D(1)` proof body matches the existing `gaussLegendre1Stage.SatisfiesD
1` witness at line 328-332 verbatim.

## E. Verification protocol (mandatory, in order)

After editing `OpenMath/Chapter3/Section321.lean`:

1. **Compile**: `lake env lean OpenMath/Chapter3/Section321.lean`
   (exit 0).
2. **Refresh oleans** (cycle 313 discovery — `lake env lean` does
   NOT update `.olean` files):
   `lake build OpenMath.Chapter3.Section321`.
3. **Aggregator**: `lake build OpenMath.Chapter3` (exit 0; this also
   catches any downstream regressions in `Section342.lean`).
4. **Sorry count**: `grep -c sorry OpenMath/Chapter3/Section321.lean`
   → 0.
5. **Axiom check on the new theorem**:
   ```text
   #print axioms OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesD
   ```
   Expected: `[propext, Classical.choice, Quot.sound]`. NO
   `sorryAx`, NO custom axioms.
6. **Regression check**: cycle 313's
   `satisfiesE_of_satisfiesB_satisfiesC` and cycle 312's
   `butcherGaussLegendreRK_satisfiesE` should remain axiom-clean.

If step 5 leaks `sorryAx` from upstream, that is a **pre-existing**
status of cycles 301+'s `_rootsInIoo_card_ge` (see `plan.md`'s
`lem:342B` row); the cycle 313 theorem was also affected and is
documented. Do NOT attempt to fix this leak — it's outside cycle
314 scope.

## F. Pre-commit faithfulness checklist (mandatory per CLAUDE.md)

Cycle 314 introduces ONE new theorem (`satisfiesE_of_satisfiesB_satisfiesD`)
and ONE unnamed `example`. The example has no faithfulness
obligation. For the theorem:

* **Entity ID**: `thm:342C` (clause (342o)).
* **Quote from textbook** (from
  `extraction/formalization_data/entities/thm_342C.json`'s
  `statement_latex`):
  > `B(2s) \land D(s) \Rightarrow E(s, s)`     (342o)
* **Lean statement captures**: *same content* — flat implication
  with hypothesis pack (B(2s) ∧ D(s)) expressed as named hypotheses
  `hB`/`hD`, conclusion `E(s, s)`.
* **Tautology check**: ✓ Conclusion `M.SatisfiesE s s` does NOT
  appear among hypotheses (which are `M.SatisfiesB (2*s)` and
  `M.SatisfiesD s`).
* **Identity check**: ✓ Proof is structural, multi-step `have`/`rw`
  composition; NOT a one-line `:= h_*`.
* **Definition smuggling check**: ✓ No new `def`/`class`/`structure`.
  The §321 B/D/E predicates were audited cycle 306.
* **Hypothesis strength check**: ✓ Hypotheses match Butcher's
  (342o) exactly. Cannot weaken `SatisfiesB (2*s)` (needed at
  exponent `k+l ≤ 2*s`). Cannot weaken `SatisfiesD s` (needed at
  full exponent `s`, since `1 ≤ k ≤ s`).
* **No extra hypotheses**: ✓ no `0 < s` precondition (vacuous case
  closed by `omega` inside the `hkl_hi` check).

## G. What NOT to do

* **Do NOT add `(hs : 0 < s)`** as a hypothesis. The cycle 313
  (342m) theorem proves the analogous fact without it; (342o)
  should do the same. The vacuous-case analysis (`s = 0` ⇒
  empty quantifier) closes via `omega` from the `interval_cases`
  bound contradictions.

* **Do NOT touch `OpenMath/Chapter3/Section342.lean`.** The (342o)
  clause is a *generic* RKTableau theorem that belongs in
  `Section321.lean` alongside the predicate definitions and cycle
  313's (342m). The Gauss–Legendre specialisations in
  `Section342.lean` are downstream *consumers* of these abstract
  clauses (cycles 309–312); they do not need new content this
  cycle.

* **Do NOT attempt (342n) or (342p) in the same cycle.** Those are
  the Vandermonde-converse clauses (forward direction: E ⇒ C, or
  E ⇒ D, via a non-singular `b`-weighted Vandermonde matrix). They
  require ~150 LOC of matrix-inverse infrastructure each and should
  ship as a paired cycle (the proof skeletons are symmetric). The
  cycle 313 task results explicitly flag them as a separate
  deliverable.

* **Do NOT attempt clauses (342j)/(342k)/(342l).** These involve
  `G(2s)` — the elementary-differential / B-series order condition
  — which is blocked on the unformalised `thm:314A`. Multi-cycle
  prerequisite work.

* **Do NOT pivot to `thm:344A` (Radau/Lobatto methods).** That is
  the natural cycle 315+ target, but it consumes the §321 B/C/D/E
  predicates wholesale; shipping (342o) first strengthens the
  abstract toolkit before that pivot.

* **Do NOT submit to Aristotle.** This is a single-cycle target
  with a known mechanical proof recipe. Aristotle is appropriate
  for: long-running parallel jobs (cf. cycle 273's (342a)), or
  proofs needing nontrivial premise selection. A 90-LOC port of a
  cycle 313 proof body does not need it.

* **Do NOT use `simp only [Matrix.dotProduct]`** anywhere in this
  cycle. The `dotProduct` symbol lives at root namespace (per
  `consultant_advice_cycle_167.md`); if any expansion is needed,
  use `show ∑ i, _ = _` to expose the sum form directly.

* **Do NOT raise `maxHeartbeats`.** The proof should fit
  comfortably under the default 200000.

* **Do NOT introduce `sorry`/`axiom`/`constant`.** Cycle 314's
  deliverable bar is "ship axiom-clean or skip the cycle". The
  cycle 313 proof has a clear-cut, 50-LOC body — the (342o)
  counterpart will be similar size.

* **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
  43+ consecutive GPFS timeouts since cycle 182. Skip per
  `cycle_182_gpfs_slowness.md`. (Not relevant to cycle 314 anyway —
  this cycle's deliverable lives entirely in Chapter 3.)

## H. Sizing / time budget

* **Theorem body**: ~80 LOC (matches cycle 313's 47-line body plus
  the extra sub-rewrite for the `1 - c^k` split).
* **Docstring + non-vacuity**: ~30 LOC.
* **Total file delta**: ~110 LOC inserted at `Section321.lean:255`
  (after cycle 313 block, before `namespace OpenMath.Chapter3.Section321`).
* **Estimated time**: 30–60 min, with the bulk being verifying the
  intermediate `show` rewrites elaborate cleanly. If you blow past
  90 min, the bottleneck is most likely the `Finset.sum_sub_distrib`
  direction or the inner `ring` after `pow_add`; consult the
  fallbacks in §C.

## I. After landing

* Update `plan.md`'s `thm:342C` row to reflect the (342o) addition
  (the partial `[~]` status persists — (342n)/(342p) Vandermonde
  clauses and (342j)/(342k)/(342l) `G(2s)` clauses remain open).
* Update `lean_status.json`'s `thm:342C` entry's `notes` field to
  add: "cycle 314 — (342o) `B(2s) ∧ D(s) ⇒ E(s, s)` shipped
  axiom-clean as
  `RKTableau.satisfiesE_of_satisfiesB_satisfiesD`."
* Write `.prover-state/task_results/cycle_314.md` documenting:
  worked on (342o); approach (sum-swap + D(s) + B(2s) × 2);
  result (SUCCESS, axiom-clean); faithfulness check (above);
  dead ends (any tactic snags encountered); discovery (anything
  about Mathlib's `Finset.sum_sub_distrib` direction or pow_add
  composition worth flagging); suggested next approach (cycle 315
  candidate: (342n)/(342p) Vandermonde-converse pair, OR pivot to
  `thm:344A` Radau/Lobatto, OR `thm:344A` predecessor scoping).
* Commit and push.

## J. If something goes wrong

* **Compile fails on `Finset.sum_sub_distrib`**: try
  `Finset.sum_sub_distrib`, `Finset.sum_sub_distrib`, or in the
  worst case factor the split outward:
  ```lean
  rw [show (∑ j : Fin s, (M.b j * M.c j ^ (l - 1)
                          - M.b j * M.c j ^ ((k + l) - 1)))
            = (∑ j : Fin s, M.b j * M.c j ^ (l - 1))
              - (∑ j : Fin s, M.b j * M.c j ^ ((k + l) - 1)) by
        rw [← Finset.sum_sub_distrib]]
  ```
  Then both directions are available. If still stuck, grep the
  5 files using the lemma (`OpenMath/Chapter3/Section319.lean`,
  `Section381.lean`, `OpenMath/Chapter4/Section441.lean`,
  `Section454Aux.lean`, `OpenMath/Chapter5/Section515.lean`) to
  see the exact form.

* **`field_simp` blow-up**: split the final arithmetic into named
  `have` steps. The identity
  `(1/k) · (1/l - 1/(k+l)) = 1/(l·(k+l))`
  rearranges as `(k+l - l) / (k · l · (k+l)) = 1/(l · (k+l))`, i.e.
  `k · l · (k+l) = k · l · (k+l)`. If `field_simp + ring` cannot
  navigate this, try `field_simp [hk_ne, hl_ne, hkl_ne]` after
  introducing the three non-zeroness facts (where `hl_ne` and
  `hkl_ne` are derived analogously to `hk_ne`).

* **`hkl_hi` fails**: this requires `k + l ≤ 2 * s` from `k ≤ s`
  and `l ≤ s`. `omega` should close it directly. If not, add the
  step `have : k + l ≤ s + s := by omega` then `linarith`.

* **Proof body exceeds ~100 LOC**: split into named private
  helper lemmas (e.g. one per step). The cycle 308 / 311 /
  312 / 313 examples all show this pattern. Do NOT keep grinding
  a single proof block past 100 LOC.

The proof is concrete and tractable. Ship axiom-clean, write task
results, commit, push. Cycle 314 done.
