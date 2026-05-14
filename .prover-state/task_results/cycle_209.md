# Cycle 209 Results

## Worked on
- P1: §382 `RKTableau.compose` infrastructure — def + 8 axiom-clean
  structural simp lemmas (`compose_b_castAdd`, `compose_b_natAdd`,
  `compose_c_castAdd`, `compose_c_natAdd`, `compose_A_topLeft`,
  `compose_A_topRight`, `compose_A_botLeft`, `compose_A_botRight`) + 2
  non-vacuity `example`s on `paddedEuler.compose paddedEuler`.
- P2: §380 ergonomic bundled bridge
  `PReducesTo.toEquivalent_and_toPhiEquivalent` (~5 LOC).
- P3: pre-existing unused-variable linter warnings on Section381.lean:577
  and 2245 silenced by `heq` → `_heq` rename in two `∃`-binder positions.

## Approach
1. Verified HEAD `2d81622` (cycle 208) and sorry count `0`.
2. Re-read Butcher ch03.txt:8671–8742 confirming the (382a) tableau
   block structure: top-left `A = M₁.A`, top-right zero, bottom-left
   row-`b₁` constant column pattern, bottom-right `M₂.A`; bottom
   c-column `(∑ⱼ bⱼ) + M₂.cᵢ`.
3. `lean_loogle Fin.addCases` + `lean_loogle Fin.append` confirmed
   Mathlib names match strategy's: `Fin.addCases_left`/`_right` and
   `Fin.append_left`/`_right` are the canonical forms.
4. Wrote the `compose` def using nested `Fin.addCases` on the
   `i`-then-`j` axes for `A`, with `motive := fun _ => ℝ` annotations
   inside; `Fin.append` directly for `b` and `c`.
5. Wrote 8 structural simp lemmas; all closed by single-line
   `simp [compose]` (the Fin lemmas fire from default simp set).
6. Added 2 `example`s under `namespace OpenMath.Chapter3.Section381`
   exercising the new infrastructure on `paddedEuler`.
7. Shipped P2 with `.{u}` universe annotation (cycle 204/208 pattern)
   and trivial body `⟨h.toEquivalent, h.toPhiEquivalent⟩`.
8. Renamed two `heq` existential binders to `_heq` to silence the
   pre-existing unused-variable warnings without losing the
   documentation hint.

## Result
SUCCESS — all four deliverables (P1 def + 8 simp lemmas + 2
non-vacuity examples; P2 bundle; P3 linter cleanup) compile clean.
Warm rebuild ~6s.

All new theorems verify axiom-clean
`[propext, Classical.choice, Quot.sound]`:
- `RKTableau.compose` (def)
- `RKTableau.compose_b_castAdd`, `compose_b_natAdd`
- `RKTableau.compose_c_castAdd`, `compose_c_natAdd`
- `RKTableau.compose_A_topLeft`, `compose_A_topRight`,
  `compose_A_botLeft`, `compose_A_botRight`
- `RKTableau.PReducesTo.toEquivalent_and_toPhiEquivalent`

No-regression spot-checks of cycle 207/208 deliverables
(`PEquivalent.toEquivalent`, `PReducesTo.toEquivalent`,
`PEquivalent.eq_of_both_isIrreducible`,
`paddedEuler_pReduced_pairPartition_eq_of_both_isIrreducible`) all
re-verified axiom-clean.

Sorry count remains 0. Linter warnings: 0 (down from 2).

## Faithfulness check

### `RKTableau.compose` (def)
- Entity ID: no entity ID — this is internal infrastructure for the
  future `thm:382A` work; Butcher writes the composition as `m₁ · m₂`
  in §382 (p. 285, equation (382a)) but does not name it separately.
- Textbook source quoted (raw_text/ch03.txt:8678–8703):
  > [Top block: c₁, …, cₛ | A₁, 0]
  > [Bottom block: Σᵢbᵢ + c̃₁, …, Σᵢbᵢ + c̃ₛ̄ | rows of b₁ | Ã]
- Lean statement captures: **same content**.
  * `A`-top-left = `M₁.A` (verified by `compose_A_topLeft`).
  * `A`-top-right = `0` (verified by `compose_A_topRight`).
  * `A`-bottom-left row-`i` col-`j` = `M₁.b j` (verified by
    `compose_A_botLeft` — constant-across-i, depends only on j, matching
    the textbook's "row-b₁" pattern).
  * `A`-bottom-right = `M₂.A` (verified by `compose_A_botRight`).
  * `b` = `Fin.append M₁.b M₂.b` (verified by
    `compose_b_castAdd`/`_natAdd`).
  * `c`-top = `M₁.c` (verified by `compose_c_castAdd`).
  * `c`-bottom = `(∑ⱼ M₁.bⱼ) + M₂.cᵢ` (verified by `compose_c_natAdd`).
- **Definition smuggling check** (per strategy §H): `compose` is
  pure infrastructure that does not claim to be a named textbook
  concept. The docstring explicitly marks it "Internal infrastructure
  for §382 group-theoretic results; the full `thm:382A` closure remains
  blocked on `thm:381H`."

### `compose_*` simp lemmas (8 lemmas)
- All conclusions are computational unfoldings of `compose` against
  the four `Fin.append`/`Fin.addCases` left/right branches. None
  re-export a hypothesis; **tautology check** clean.
- All proofs are `simp [compose]` (single tactic). They unfold the
  definition once and let Mathlib's `Fin.addCases_left`/`_right` and
  `Fin.append_left`/`_right` simp lemmas close the goal — exactly the
  "definitional unfolding" pattern. **Identity check** clean.

### `PReducesTo.toEquivalent_and_toPhiEquivalent` (P2 bundle)
- This is an ergonomic packaging corollary, not new content. Body
  `⟨h.toEquivalent, h.toPhiEquivalent⟩` composes cycle 207 and
  cycle 187 outputs through `PReducesTo`'s structure-dot-notation.
- **Tautology check**: conclusion `Equivalent M M' ∧ PhiEquivalent M M'`
  is a strict conjunction; neither component is a hypothesis. Clean.
- **Identity check**: not a single-`exact` proof — the body packages
  two non-trivial cycle 207/187 results into a conjunction. Clean.
- **Hypothesis strength check**: hypothesis `PReducesTo M M'` is the
  minimal premise admitting both component conclusions; cannot weaken
  to `PEquivalent` because cycle 207's `PReducesTo.toEquivalent`
  consumes `PReducesTo` directly. Clean.

### P3 linter rename (Section381.lean:577, 2245)
- No new content — pure cosmetic rename of `∃ heq` binder to `∃ _heq`
  in two existing theorems. Both theorems re-verify axiom-clean
  (`[propext, Classical.choice, Quot.sound]`), so no semantic drift.

## Dead ends
None. Strategy was followed verbatim. The only minor friction:
- The strategy's signature `{M : @RKTableau.{u} s}` for P2 produced
  "too many explicit universe levels" because `RKTableau` is not
  universe-polymorphic (it's a structure of fixed `Type`). Fix: drop
  the `@…{u}` annotation on RKTableau, keep `.{u}` only on the
  universe-polymorphic `Equivalent` in the conclusion. Mirrors how
  the existing cycle 208 `PEquivalent.toEquivalent_and_toPhiEquivalent`
  (line 2157) handles the same situation.
- The new RKTableau-namespace block at the end of the file initially
  failed with "PhiEquivalent unknown" until I added the canonical
  `open OpenMath.Chapter3.Section381` directive (mirroring line 1560).
  PhiEquivalent and Equivalent both live in Section381 namespace, not
  Section312.RKTableau, so they need to be opened for dot-free
  reference in the bundle corollary's conclusion.

## Discovery
1. `Fin.addCases` accepts a `motive := fun _ => ℝ` annotation cleanly
   when the body is non-dependent in ℝ; nested two-level `Fin.addCases`
   (i-then-j) for `Matrix (Fin (s₁+s₂)) (Fin (s₁+s₂)) ℝ` elaborates
   without surprises. The `motive := fun _ => …` annotation is only
   needed because the outer addCases's branches return ℝ-valued
   functions of `j : Fin (s₁+s₂)`, which Lean wants pinned to a
   non-dependent motive.
2. `simp [compose]` alone closes all 8 structural simp lemmas — the
   `Fin.addCases_left`/`_right` and `Fin.append_left`/`_right` lemmas
   are in the default simp set, so no explicit `simp` arguments are
   needed beyond unfolding `compose` itself.
3. The `A`-bottom-left block in Butcher's (382a) tableau is literally a
   "repeat row-`b`" pattern (each row of the bottom-left s̄ × s block
   equals the vector `M₁.b`). This is NOT a rank-1 outer product —
   the entries depend on column index `j` only, not row index `i`.
   The Lean `compose` def captures this honestly via
   `fun i₂ : Fin s₂ => Fin.addCases (fun j₁ => M₁.b j₁) ...` — `i₂` is
   bound but unused in the bottom-left case, matching the textbook.
4. Linter false-positives on `∃ heq : ...` binders inside HEq pair
   types are silenced by `_heq` rename. The binder appears unused at
   the surface level because the proof closes via `⟨rfl, ...⟩` which
   doesn't reference `heq` by name — but the existential type still
   needs the equation hypothesis to be HEq-well-typed. The rename
   preserves the documentation while satisfying the linter.

## Suggested next approach
With `compose` infrastructure shipped, the next §382 cycle has
several closeable single-cycle targets:

1. **`compose_explicit_iff`** (~15 LOC): show that
   `(M₁.compose M₂).IsExplicit ↔ M₁.IsExplicit ∧ M₂.IsExplicit`
   from cycle 151. The composite `A` is block-triangular, so it's
   strict-lower-triangular iff both `M₁.A` and `M₂.A` are. The
   bottom-left block (`M₁.b`-row pattern) is strict-lower in the
   composite indexing because its column indices come from the upper
   `Fin s₁` half (via `castAdd`) and its row indices from the lower
   `Fin s₂` half (via `natAdd`) — hence rows > cols always.

2. **`compose_assoc`** (~25–40 LOC): up-to-`HEq` associativity
   `(M₁.compose M₂).compose M₃ ≃ M₁.compose (M₂.compose M₃)`. The
   stage-count side requires `Nat.add_assoc` cast; the field equalities
   reduce to the eight structural simp lemmas shipped this cycle.
   Foundational for `thm:382A`'s group-axiom proof (associativity is
   one of the four group axioms; the other three are
   identity-existence, identity-inverse, and inverse-existence).

3. **`identityElement`**: the §382 identity for composition. Butcher
   does not write it down explicitly in the textbook excerpt around
   8671–8742, but standard RK theory recognizes it as either the
   "do-nothing" 0-stage tableau or a degenerate 1-stage tableau with
   `b = 0`. Investigation cycle: figure out which form makes
   `identityElement.compose M = M` (up to HEq) work.

4. **More `paddedEuler`-composition non-vacuity witnesses**: e.g.
   `paddedEuler.compose paddedEuler |>.IsExplicit` once
   `compose_explicit_iff` ships, or
   `(paddedEuler.compose paddedEuler).c` evaluated at each Fin 4 index.

5. **§441 Phase C.2 GPFS-blocked** (29th consecutive cycle skip).
   Same loop-maintainer territory as cycles 182–208. No worker action.

Full `thm:382A`/`thm:382B` remain multi-cycle until `thm:381H` closes
— the group structure is defined on equivalence classes of methods,
and the well-definedness of `[m₁] · [m₂]` on the quotient requires
the full iff of `thm:381H`. Cycles 209–N can build up the
infrastructure (compose, associativity, identity, inverse) without
needing `thm:381H`; only the final "this descends to a group on
equivalence classes" wrap-up needs it.

§441 Phase C.2: 29th consecutive GPFS-blocked skip per strategy §A.
