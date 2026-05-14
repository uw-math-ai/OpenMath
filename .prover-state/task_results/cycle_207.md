# Cycle 207 Results

## Worked on

§380 `pReduced_equivalent` (P1, primary), `zeroReduced_equivalent` (P2,
stretch), and `PReducesTo.toEquivalent` (P3, stretch-of-stretch) in
`OpenMath/Chapter3/Section381.lean`. All three landed axiom-clean.
Together they close the deferred direction `PReducesTo → Equivalent`
of `thm:381H`.

## Approach

### P1 — `pReduced_equivalent` (~67 LOC, lift-up strategy)

Following the cycle 207 strategy §C verbatim:

1. **Block 1** — threshold construction `h₀ := 1 / (2·(L·C_M+1))` with
   `C_M := Σᵢⱼ |M.A i j|`, smallness `|h|·L·C_M < 1` via
   `le_div_iff₀` + `nlinarith`. Verbatim from cycle 203's
   `equivalent_self`.
2. **Block 2** — define `Y_lifted i := Y' (P.block i)` (lift M.pReduced's
   stages back to `Fin s` via the block-index function). Show
   `M.RKStageMap h f y₀ Y_lifted = Y_lifted` by:
   - Unfolding the stage equation for `Y_lifted i = Y' (P.block i)`
     using `hY'_stage (P.block i)`.
   - Two `congr 1` calls to peel `y₀ +` and `h •`.
   - `← Finset.sum_fiberwise (g := P.block)` to group the inner
     sum by P-blocks.
   - Per-block: rewrite `(M.pReduced P).A (P.block i) J = Σ_{j ∈ filter}
     M.A i j` via `pReduced_A_apply M hP (P.block i) J i rfl` (this is
     the load-bearing application of `hP : M.IsPReducibleVia P`).
   - `Finset.sum_smul` to pull `• f (Y' J)` inside, then
     `Finset.sum_congr` with `P.block j = J` from the filter membership
     to rewrite `f (Y' (P.block j)) = f (Y' J)`.
3. **Block 3** — extract Y = Y_lifted via cycle 204's
   `RKStageMap_fixedPoint_unique`. Verbatim from cycle 203 lines
   1813–1820.
4. **Block 4** — output collapse via second `Finset.sum_fiberwise`
   + `pReduced_b_apply` + `Finset.sum_smul`.

### P2 — `zeroReduced_equivalent` (~95 LOC, project-down strategy)

0-reduction is asymmetric (P₀ stages disappear), so the proof projects
M's stages down onto P₁ instead of lifting:

1. **Threshold** — use `C_zr := Σᵢⱼ |(M.zeroReduced inP1).A I J|`
   directly as the contracting constant (strategy §I's "C_zr ≤ C_M"
   approach was unnecessary; using C_zr is cleaner and avoids a
   separate sum-bounding lemma).
2. **Project Y onto P₁**: `Z J := Y (zeroReducedEmb inP1 J)`.
3. **Show Z is a fixed point of (M.zeroReduced inP1).RKStageMap**:
   - Split M's stage sum via `Finset.sum_filter_add_sum_filter_not`
     with predicate `inP1 j = true`.
   - P₀ part vanishes: each term has `M.A (zeroReducedEmb inP1 J) j`
     where `inP1 (zeroReducedEmb inP1 J) = true` (from
     `Finset.orderEmbOfFin_mem`) and `inP1 j = false` (derived from
     `¬ inP1 j = true` via `cases hb : inP1 j`); then `h0.2`
     gives 0.
   - P₁ part reindexes via `Finset.sum_image` with the order
     embedding's image lemma `Finset.image_orderEmbOfFin_univ`:
     `Finset.image (zeroReducedEmb inP1) Finset.univ = Finset.univ.filter
     (inP1 · = true)`.
4. **Banach uniqueness** on (M.zeroReduced inP1).RKStageMap gives
   `Z = Y'`.
5. **Output collapse**: symmetric split of M's b-sum (P₀ part vanishes
   by `h0.1`) and reindex P₁ part via the same image identity.

### P3 — `PReducesTo.toEquivalent` (10 LOC)

Induction on `PReducesTo`:
- `refl M`: `equivalent_self M`
- `step P _ hVia _ ih`: `Equivalent.trans (pReduced_equivalent hVia) ih`
- `zeroStep inP1 hP0 hVia _ ih`:
  `Equivalent.trans (zeroReduced_equivalent hP0 hVia) ih`

## Result

SUCCESS — P1, P2, P3 all axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
Sorry count 0 → 0. Warm rebuild ~6s. Cycle 203–206 theorems unaffected
(regression-checked: `equivalent_self`, `Equivalent.trans` still axiom-
clean).

## Faithfulness check

### `pReduced_equivalent`

- **Entity**: implicit consequence of `def:381D` (Butcher §380, p. 304).
  Quote: "If `i, j ∈ P_I` in a P-reducible Runge–Kutta method ... for
  any IVP, `Y_i = Y_j` for `h < h_0`."
- **Lean statement captures**: same content. The theorem is the
  Lean-level analog of the textbook claim that one P-reduction step
  preserves `def:381A` equivalence. The proof uses Banach uniqueness
  to encode "for `h` sufficiently small" verbatim (`h₀ := 1 /
  (2·(L·C_M+1))`).
- **Hypothesis strength**: matches textbook — only `IsPReducibleVia P`
  is required, exactly the def:381D content.

### `zeroReduced_equivalent`

- **Entity**: per-step consequence of `def:381C` (Butcher §380, p. 303).
  The textbook's "deleting all stages indexed by members of `P_0`"
  reduces to an equivalent method by construction; the proof here is
  the formal version (using Banach to handle the implicit case).
- **Lean statement captures**: same content.
- **Hypothesis strength**: `_hP0 : ∃ i, inP1 i = false` is included to
  match `PReducesTo.zeroStep`'s constructor signature, but the proof
  does NOT use it — it would be safe to drop. Kept for caller-site
  consistency (the `_hP0` underscore documents this is unused).

### `PReducesTo.toEquivalent`

- **Entity**: this is one of four directions of `thm:381H` (the
  forward implication `def:381F → def:381A` from p. 304's iff).
- **Lean statement captures**: same content.
- **Hypothesis strength**: no extras.

## Dead ends

1. **`rw [← hImage]` motive-not-type-correct error** in the
   project-down stage equation step of P2. The `Finset.image emb univ
   = filter (inP1·=true)` rewrite fails when the filter set appears in
   a dependent type (`RKTableau (filter.card)`); Lean can't abstract
   over the filter. Workaround: use forward rewriting (`rw [hImage]`)
   via a calc-chain that first rewrites the LHS sum into the image form
   then forwards into the filter form. Less elegant but works.
2. **`(pReduced_equivalent hVia).trans ih` fails** in P3 because
   `Equivalent` is `Prop`-valued and at that call site
   `pReduced_equivalent hVia` is still an unapplied universal-quantifier
   function (awaiting `{N}`, instances, `f`, `L`, `hL`, `y₀`); no
   `.trans` field exists on a function type. Fix: use `Equivalent.trans`
   as a function (`exact Equivalent.trans X ih`).
3. **`Finset.sum_image` higher-order metavar inference** failed in P2
   when used as a `.symm` term — Lean couldn't unify the `f` argument
   from the goal context. Fix: provide `(f := fun j : Fin s => ...)`
   explicitly.

## Discovery

1. **`Finset.sum_fiberwise`** has the exact shape for P-block
   grouping: `∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`. Use `←`
   to go from a flat sum to a sum-over-blocks. Required for the
   substantive new content in both P1 (twice — stage equation and
   output) and P2 (less directly, replaced by sum_filter_add_filter_not
   because 0-reduction's 2-block structure is simpler).
2. **Two `congr 1`s** are required to peel both `y₀ +` and `h •`
   from `y₀ + h • X = y₀ + h • Y`. One `congr 1` alone leaves
   `h • X = h • Y` (the `•` is not a field projection from a tuple,
   so a single congr stops after peeling outer `y₀ +`).
3. **`Finset.image_orderEmbOfFin_univ`** (`image (s.orderEmbOfFin h)
   Finset.univ = s`) is the key identity for `zeroReducedEmb`-based
   reindexing. Combined with `Finset.sum_image` (which takes an
   `InjOn` hypothesis, derivable from `Embedding.injective.injOn`),
   it converts sums over `Fin (#P₁)` to sums over the P₁-filter of
   `Fin s`.
4. **Strategy §I's "C_zr ≤ C_M" detour for P2's threshold is
   unnecessary.** Using `C_zr := Σᵢⱼ |(M.zeroReduced inP1).A I J|`
   directly as the contracting constant for the smaller stage map is
   cleaner and avoids the sum-bounding lemma. The strategy assumed we
   needed to use cycle 203's threshold; we don't.
5. **`Equivalent.trans` cannot be invoked as `.trans` on an unapplied
   `Equivalent`-valued function**. Since `Equivalent` is a `Prop`
   defined as `∀ {N} ... ∃ ... ∀ ..., y₁ = y₁'`, an `Equivalent` value
   is a function awaiting `{N}` and the rest; dot notation `.trans`
   tries to project a field. Use `Equivalent.trans X ih` as a regular
   function application.

## Suggested next approach

The deferred direction `PReducesTo → Equivalent` of `thm:381H` is now
closed (via cycle 207's `PReducesTo.toEquivalent`). Three remaining
deferred directions and one stretch target:

1. **Statement-only `thm:381H` scaffold** (cycle 208 candidate, from
   strategy §H): now that `PEquivalent → PhiEquivalent` (cycle 187)
   and `PReducesTo → Equivalent` (cycle 207) are both shipped, two
   of the four iff directions in `thm:381H` are closeable. The
   remaining two (`PhiEquivalent → PEquivalent` and `Equivalent →
   PEquivalent`) still block on `thm:381G` per
   `thm_381H_deferred.md`. Cycle 200's prior attempt with 3 sorries
   was rolled back; recommend NOT attempting until ≤1 sorry possible.
2. **`PEquivalent.toEquivalent`** (~3-5 LOC corollary): an immediate
   composition of `PReducesTo.toEquivalent` on both legs of
   `PEquivalent`'s existential reduct, then `Equivalent.symm` +
   `Equivalent.trans`. Trivial cycle if budget is tight.
3. **paddedEuler non-vacuity exercise**: a one-liner
   `paddedEuler_equivalent_zeroReduced` via
   `(paddedEuler_pReducesTo_zeroReduced).toEquivalent`. Exercises
   `PReducesTo.toEquivalent` on the `zeroStep` constructor path —
   no new logic, but confirms the induction fires non-vacuously on
   the `zeroStep` case (not just the `step` case).
4. **`def:382A`/`thm:382A`** (composition group of RK methods) — fresh
   §382 entity opening a new sub-cluster. Independent of all the
   `thm:381H` plumbing.

Recommend (2) + (3) as a quick cycle 208 (combined ~10-20 LOC,
sub-30-min), leaving budget for harder work. The statement-only
`thm:381H` scaffold (option 1) is appealing but still has 2 sorries
that would regress the 0-sorry invariant; defer until `thm:381G` track
is unblocked.

§441 Phase C.2 remains GPFS-blocked (27th consecutive cycle); loop-
maintainer territory per `.prover-state/issues/cycle_182_gpfs_slowness.md`.
