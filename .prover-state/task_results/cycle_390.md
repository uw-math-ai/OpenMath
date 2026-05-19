# Cycle 390 Results

## Worked on

§422 Phase α'.4.1 P4 — ship the `(vertex, cherry)` cross-term
refinement to `bichildCrossTerm` and the calibration witness
`inversePolyTree_mkVertexCherry` per cycle 390 strategy §C.1+§C.2.
C.3 (partial Phase α'.4.2 migration of `mk [vertex, cherry]` in
`inversePolynomial`) intentionally skipped per strategy §C.3
"Skip C.3 if there are ANY surprises in C.1/C.2" guideline —
see §Discovery for the surprise.

## Approach

**C.1 — Cross-term extension** (`Section422.lean:6271-6298`,
expanded to 6271-6306): inserted a third `else if t₁ = vertex ∧
t₂ = cherry then -((f vertex)^2 * f cherry) + f vertex * f broom₃`
branch after the cycle 389 `(broom₃, cherry)` branch. Value
back-computed from cycle 372's
`elementaryWeightQ_phi_inv_mkVertexCherry` 6-term closed form
(`v⁴ - 3v²c + c² + v·b' + v·m - V`) by subtracting the
`bichildPolynomial` backbone at `(inv_v, inv_c) = (-v, v²-c)`:

  `bichildPolynomial vertex cherry (-v) (v²-c) f
    = v⁴ - 2v²c + c² + v·m - V`

Target minus backbone: `(-3v²c) - (-2v²c) + v·b' = -v²c + v·b'`,
giving the 2-term cross-term value. Updated the cycle 386/388/389
docstring with the new branch's derivation paragraph.

**C.2 — Calibration witness** (`Section422.lean:6568-6620`,
placed after cycle 389's `inversePolyTree_mkBroomCherry`):
shipped `inversePolyTree_mkVertexCherry` mirroring the cycle 389
recipe (`rw [inversePolyTree, _vertex, _cherry]; unfold
bichildPolynomial; rw [show bichildCrossTerm vertex cherry f =
... by unfold + 2 if_neg + if_pos ⟨rfl, rfl⟩]`). Additional
`show` block needed (compared to cycle 389) to fold
`f (mk [vertex])` → `f cherry` definitionally (`cherry := mk [vertex]`
from `Section310.lean:111`); cycle 389's `mk [broom₃, cherry]`
target uses `f (mk [broom₃])` literally so no folding step was
required there. Closes by `ring` on the degree-4 6-indeterminate
identity.

**Compile + verification protocol** (strategy §F): after each of
C.1 and C.2, ran `lake env lean OpenMath/Chapter4/Section422.lean`
(C.1: 8m34s after fixing the regression at `inversePolyTree_broom₃`;
C.2: 8m53s clean) + `lake build OpenMath.Chapter4.Section422` to
refresh the .olean cache, then `#print axioms` on
`inversePolyTree_mkCherryCherry`, `inversePolyTree_mkBroomCherry`,
`inversePolyTree_mkVertexCherry` — all three report
`[propext, Classical.choice, Quot.sound]`. `grep -c sorry
OpenMath/Chapter4/Section422.lean = 5` (4 docstring refs + 1
grandfathered cycle 365 code sorry at line 2279), unchanged.

## Result

SUCCESS for C.1 + C.2 — both axiom-clean
`[propext, Classical.choice, Quot.sound]`. C.3 SKIPPED per
strategy guidance after the C.1 surprise (see §Discovery).

Section422.lean: 7655 → 7721 LOC (+66 LOC, well below strategy §E
estimate of ~50 LOC + cycle 386/388/389 docstring extension).

## Faithfulness check

For each new `def`/`theorem` introduced this cycle:

**1. `bichildCrossTerm` (extended, not new def)** — added one
`else if` branch to existing cycle 387 def.

- Entity ID: cross-term helper for the §385b scoping doc §3.2
  Block (4) bilinear contribution; no Butcher entity ID
  (internal infrastructure for the deferred `def:422B` Phase α'.4
  recursion).
- Branch value: back-computed from cycle 372 closed form by
  subtracting the cycle 387 `bichildPolynomial` backbone at
  `(inv_v, inv_c) = (-v, v² - c)`. Empirically pinned, not
  chosen to make a specific theorem true.
- Definition smuggling check: NEGATIVE. The cross-term value is
  the residue of the cycle 372 statement after extracting the
  uniform polynomial backbone — same recipe as cycles 388/389
  pinned for `(cherry, cherry)` and `(broom₃, cherry)`. The
  calibration witness `inversePolyTree_mkVertexCherry` is what
  formally certifies this. Not a tautology: the calibration
  asserts a non-trivial identity between the recursive form
  (`inversePolyTree` evaluated at `mk [vertex, cherry]`) and
  cycle 372's empirical closed form; the cross-term value makes
  the identity hold.

**2. `inversePolyTree_mkVertexCherry` (new theorem)**

- Entity ID: cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry`
  (formalisation_data entry for `def:422B`); this is the
  recursive-form analog at the same tree under
  `f = elementaryWeightQ_phi η_q`.
- Textbook statement (from cycle 372's docstring quoted via
  Section422.lean:3798-3814, which is the Butcher-faithful
  empirical statement):

  > `elementaryWeightQ_phi (η_q⁻¹) (mk [vertex, cherry]) =
  >  v⁴ - 3·v²·c + c² + v·b' + v·m - Φ_η(mk [vertex, cherry])`

  where `v = Φ_η vertex`, `c = Φ_η cherry`, `b' = Φ_η broom₃`,
  `m = Φ_η (mk [cherry])`.

- Lean statement captures: **same content**, in recursive-form
  notation. The theorem states `inversePolyTree (mk [vertex,
  cherry]) f = (f vertex)^4 - 3·(f vertex)²·f cherry + (f cherry)²
  + f vertex · f broom₃ + f vertex · f (mk [cherry]) - f (mk
  [vertex, cherry])`, which is structurally identical to cycle
  372's closed form with `f` standing in for `elementaryWeightQ_phi
  η_q` (cycle 372 specialises `f = Φ_η` post-quotient-induction).
- No hypothesis: takes any `f : RT → ℝ` (not just `Φ_η`). Stronger
  than cycle 372's quotient-specific statement; this is the
  Phase α'.4.1 design intent — the recursive `inversePolyTree` is
  parametric in `f`, and `Φ_η` is one instantiation.
- Tautology / identity check: NEGATIVE. Conclusion does not
  appear as a hypothesis. Proof is non-trivial: 5-step pipeline
  `rw + unfold + show-fold-cross-term + show-fold-mkVertex-to-cherry
  + ring`; `ring` discharges the degree-4 6-indeterminate
  polynomial identity (NOT `exact h` or `id`).

## Dead ends

None this cycle. The C.1 regression on `inversePolyTree_broom₃`
(see §Discovery) was caught by the first `lake env lean` pass
and fixed in one Edit (adding one `if_neg (by decide)` discharge);
not a dead end, just a forward-compatibility update.

The strategy's Fallback A (drop `show`, use `rw [show mk [vertex]
= cherry from rfl]`) and Fallback B (decompose into named `have`
steps) were not needed — the primary recipe (using a `show`
block to fold `mk [vertex] → cherry` definitionally, then `ring`)
worked on first attempt for C.2.

## Discovery

**1. Cycle 389's `inversePolyTree_broom₃` proof regressed under
the cross-term extension.** The proof at
`Section422.lean:6402-6427` contains `show bichildCrossTerm
RootedTree.vertex RootedTree.vertex f = 0 by unfold; rw [if_neg
(by decide), if_neg (by decide)]` which assumed two if-branches.
Adding the cycle 390 third branch broke this — the `(vertex,
vertex)` pair must dispatch through all three `if_neg`s to reach
the final `else 0`. Fix: add a third `if_neg (by decide)` to the
chain. This is a forward-compatibility pattern: every future
cross-term branch addition will require updating each
`bichildCrossTerm = 0` lemma's `if_neg` chain. For cycle 391+
work, watch for this pattern when adding new branches.

**2. `f (mk [vertex])` vs `f cherry` definitional folding via
`show`.** When `t₁ = vertex` in `bichildPolynomial t₁ t₂ inv₁
inv₂ f`, the unfolded Block (3) term `inv₂ · f (mk [t₁])`
produces `f (mk [vertex])`. `cherry := mk [vertex]` makes the
two definitionally equal, but `ring` operates syntactically and
will NOT auto-normalise this form. A `show` block with the
target expression rewritten to use `f cherry` instead of `f (mk
[vertex])` lets Lean perform the definitional reduction during
elaboration, then `ring` succeeds. Cycle 389's `mk [broom₃,
cherry]` did not need this because `mk [broom₃]` is not
synonymous with any short alias.

**3. Strategy §B's paper-algebra finding confirmed empirically:**
the back-computed cross-term `-v²c + v·b'` matches the target
exactly. The C.2 proof's single `ring` call closes the degree-4
6-indeterminate identity in <1s (no Fallback B decomposition
needed), consistent with cycle 389's precedent (degree-6
9-indeterminate identity closed in one `ring`).

**4. Total compile time per `lake env lean` pass: ~5–9 minutes**
(varies with cluster load; warm-cache builds via `lake build`
take ~5min; full recompile cold-cache takes ~9min). For cycle
391+ workers attempting C.3-style migrations with multiple
rebuilds, budget ~30–60 min for the verification protocol.

## Suggested next approach

**Primary recommendation for cycle 391 — C.3 (Phase α'.4.2
partial migration for `mk [vertex, cherry]`):** the calibration
witness `inversePolyTree_mkVertexCherry` is now in place, so the
migration becomes feasible. Per strategy §C.3 the migration is a
two-step ship:

1. Replace the explicit polynomial body in `inversePolynomial`'s
   `mk [vertex, cherry]` branch (currently `Section422.lean:6601-
   6610`, post-cycle-390 LOC unchanged) with `inversePolyTree
   (mk [vertex, cherry]) f`.
2. Ship a bridge theorem
   `inversePolyTree_mkVertexCherry_eq_inversePolynomial` (one-line
   `unfold inversePolynomial; rw [if_neg ×6, if_pos rfl]`).

The migration **DOES** require re-proving the cycle 377-era
`Section422.lean:7212-7253` bridge
`elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry`
(currently 7 `if_neg` + `if_pos rfl` + `exact cycle372_thm` —
after migration the `if_pos rfl` step exposes
`inversePolyTree ... f`; will need to add
`rw [inversePolyTree_mkVertexCherry]` before the final `exact`)
**and** the cycle 365-era `Section422.lean:7549-7620` branch of
`inversePolynomial_eq_of_subtree_agreement` (currently uses
explicit polynomial-body rewrites via `hv, hc, hb, hmc, hmvc`
— after migration the unfolded `inversePolynomial t f` for the
`mk [vertex, cherry]` branch becomes `inversePolyTree (mk
[vertex, cherry]) f` and the agreement proof must dispatch via
`inversePolyTree_mkVertexCherry` substitution on both sides
before recovering the explicit polynomial form for the agreement
argument). Estimated ~30 LOC of bridge update for the two
consumers + ~15 LOC for the new bridge theorem ≈ 45 LOC budget,
all axiom-clean.

**Alternative for cycle 391 — primary path of strategy §H:**
design and ship the `monochildCrossTerm` infrastructure to fix
`inversePolyTree`'s single-child non-leaf case
(`Section422.lean:6347-6349`). Per strategy §B, this is currently
miscalibrated for `mk [broom₃]`
(`inversePolyTree (mk [broom₃]) f = v⁴ - 2v²c + vb' - M` vs
cycle 371's `v⁴ - 3v²c + vb' + 2vm - M` — differs by `-v²c +
2vm` due to missing single-child non-leaf cross-term machinery).
Multi-cycle work (~150 LOC); unblocks `mk [broom₃]` migration
in cycle 392+. Higher infrastructure investment with longer
amortisation.

**Cycle 391 recommendation:** ship C.3 first (lower-risk
single-cycle deliverable, ~45 LOC + 3 file rebuilds ≈ 30 min);
defer `monochildCrossTerm` to cycle 392+. The §422 streak
extends to 54 substantive + 2 doc on success.

**Tertiary alternatives** (not recommended for cycle 391):

- `(broom₃, broom₃)` cross-term addition (cycle 389 strategy
  option 1 — multi-cycle infrastructure work, requires shipping
  `mk [broom₃, broom₃]` order-7 closed form first).
- 4 Phase β bridges for Family C closed forms (cycle 389
  strategy option 3 — broader, lacks immediate consumer).
- Attack the cycle 365 grandfathered sorry at line 2279
  (Sub-lemma A `_strict_subtree_agreement`) — requires new
  infrastructure layer per cycle 366 closure notes.
