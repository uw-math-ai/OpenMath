# Cycle 196 Results

## Worked on

* **P0 (mandatory)**: §441 GPFS smoke test, 16th attempt — logged
  Branch A timeout to `cycle_182_gpfs_slowness.md` as the
  "Cycle 196 update (16th timeout)" entry.
* **P1 (substantive, primary deliverable)**: shipped the axiom-clean
  destructor / spec-lemma / corollary API for `IsPReducible` and
  `IsZeroReducible` in `OpenMath/Chapter3/Section381.lean` — 9
  declarations (5 P-reducible + 4 0-reducible) plus 2 non-vacuity
  examples on `paddedEuler`. This is the cycle 195 worker's Option A
  recommendation: the *extraction* side of well-foundedness for the
  deferred def:381E `reducedMethod`, complementing the cycle 195
  *measure* side (`size_le` / `size_lt_of_step` / `size_lt_of_zeroStep`).
* **P2 (stretch, attempted and landed)**: promoted the two cycle-194-
  era `example` blocks at lines 1493 and 1510 of `Section381.lean` to
  named `theorem`s — `paddedEuler_pReduced_pairPartition_eq_of_both_isIrreducible`
  and `paddedEuler_pReducesTo_pReduced_via_pEquivalent_extraction`.

## Approach

### P0 — GPFS smoke test

Pre-flight zombie scan (`ps -u $USER -o pid,stat,wchan,etime,comm |
grep -E "^[ ]*[0-9]+ +D"`) came up empty. Single `time timeout 300
lake env lean OpenMath/Chapter4/Section441.lean` invocation. EXIT=124
at real=5m0.031s, user=0m0.256s, sys=0m0.693s — CPU = (0.256 +
0.693) / 300 = 0.32% of wall, identical near-zero pattern to cycles
182–195. Pivoted to P1 per the no-retry rule.

### P1 — Destructor API

Followed the cycle 196 strategy verbatim. The `IsPReducible` and
`IsZeroReducible` predicates unfold as

```lean
def IsZeroReducible {s : ℕ} (M : RKTableau s) : Prop :=
  ∃ inP1 : Fin s → Bool,
    (∃ i, inP1 i = false) ∧ M.IsZeroReducibleVia inP1

def IsPReducible {s : ℕ} (M : RKTableau s) : Prop :=
  ∃ (sBar : ℕ) (_ : sBar < s) (P : PPartition s sBar),
    M.IsPReducibleVia P
```

Built each destructor as either `noncomputable def … := h.choose
…`-style witness extractor or a `theorem … := h.choose_spec.…`-style
spec lemma. The anonymous `(_ : sBar < s)` binder in `IsPReducible`
decoded cleanly through `h.choose_spec.choose : h.sBar < s` (the
anonymous-binder existential `∃ _ : sBar < s, …` is still a regular
`Exists`, so its `.choose` produces a proof of the witness type
which is `sBar < s`). No fallback to `Classical.choose` longhand or
`simpa`-coercion was needed.

The two corollaries (`IsPReducible.pReduced_size_lt`,
`IsZeroReducible.zeroReduced_size_lt`) thread the cycle 195
descent lemma `card_filter_true_lt_of_exists_false` (private helper
at `Section381.lean:633`, in scope within the same
`OpenMath.Chapter3.Section312.RKTableau` namespace block) through
the destructors.

The two non-vacuity `example`s on `paddedEuler` (placed at end of
the file before `end OpenMath.Chapter3.Section381` at line ~1540)
exercise the destructors end-to-end via dot notation on the cycle
186 / 188 witnesses `paddedEuler_isPReducible` and
`paddedEuler_isZeroReducible`. Each is a one-liner.

### P2 — Example promotion

Identical bodies kept; only the `example :` keyword swapped for
`theorem <descriptive_name> :`. The third cycle-194 `example`
(`paddedEuler.pReduced pairPartition = paddedEuler.pReduced
pairPartition` via `eq_of_both_isIrreducible_homogeneous`) was *not*
promoted — the strategy listed only two for P2, and the third is a
trivial `_ = _` self-equality that doesn't gain from promotion to a
named theorem.

### Verification

```bash
time lake env lean OpenMath/Chapter3/Section381.lean
# real 1m4.316s (cold), 0m3.817s (warm with P2), EXIT=0
grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean
# 0
```

All 9 P1 non-example declarations and both P2 theorems verified
axiom-clean via the `lean-lsp` MCP `lean_verify` tool — every result
came back `["propext", "Classical.choice", "Quot.sound"]` with no
warnings. `Classical.choice` appears in all of them because the
`noncomputable def` destructors descend through `h.choose`, which is
the textbook expected axiom budget.

## Result

**SUCCESS** — all P0/P1/P2 deliverables landed. Target success
criterion met (all 11 P1 declarations + both P2 promotions
axiom-clean, bookkeeping complete).

### Files touched

* `OpenMath/Chapter3/Section381.lean` — +84 LOC (9 P1 declarations
  after line 688 + 2 P1 non-vacuity examples at end of file + 2 P2
  example→theorem renames at line 1493/1510).
* `.prover-state/issues/cycle_182_gpfs_slowness.md` — 16th-timeout
  log entry.
* `.prover-state/issues/reduced_method_deferred.md` — "Cycle 196
  update — destructor infrastructure landed" block appended.
* `extraction/formalization_data/lean_status.json` — `def:381F`
  narrative bumped (`last_cycle` 195 → 196).
* `plan.md` — `def:381F` narrative bumped (matching paragraph).
* `.prover-state/task_results/cycle_196.md` — this file.

## Faithfulness check

The cycle 196 deliverables are *destructor API* over existing
predicates `IsPReducible` (def:381D) and `IsZeroReducible`
(def:381C), not new mathematical definitions. The textbook does not
introduce these predicates as "named" objects with destructors; they
arise as the witnesses to the §380 reducibility definitions. So
faithfulness is to be checked at the *spec lemma* level: do the
destructor outputs satisfy the textbook-stated conditions?

### `IsPReducible.{sBar, sBar_lt, partition, partition_isPReducibleVia}`

- Entity ID: **def:381D** (textbook: Butcher §380 Definition 381D,
  P-reducible). Quoted textbook statement from
  `extraction/formalization_data/entities/def_381D.json` (paraphrased
  for length): a method `M` is P-reducible iff there is a
  *non-trivial* P-partition (`ŝ < s`) on its stage index set such
  that for each pair of blocks `(I, J)`, the row sums `Σ_{j ∈ P_J}
  a_{ij}` are constant as `i` ranges over `P_I` (the row-sum-constancy
  condition `IsPReducibleVia`).
- Lean destructor extracts: (a) `sBar : ℕ`, (b) `sBar_lt : sBar < s`
  (the non-triviality side condition), (c) `partition : PPartition s
  sBar`, (d) `partition_isPReducibleVia : M.IsPReducibleVia
  partition` (the row-sum-constancy proof).
- Captures: **same content** as the existential `∃ (sBar : ℕ)
  (_ : sBar < s) (P : PPartition s sBar), M.IsPReducibleVia P`. The
  destructors are projections onto the four components — no smuggling,
  no extra hypothesis, no weakening.

### `IsZeroReducible.{inP1, exists_inP1_false, inP1_isZeroReducibleVia}`

- Entity ID: **def:381C** (textbook: Butcher §380 Definition 381C,
  0-reducible). Textbook statement from def_381C.json (paraphrased):
  a method `M` is 0-reducible iff its stage index set admits a
  2-block partition `{1,…,s} = P₀ ∪ P₁` with **`P₀ ≠ ∅`** such that
  `b_i = 0` for `i ∈ P₀` and `a_{ij} = 0` for `i ∈ P₁, j ∈ P₀`.
- Lean destructor extracts: (a) `inP1 : Fin s → Bool` (Boolean form
  of the partition predicate), (b) `exists_inP1_false : ∃ i, inP1 i =
  false` (the `P₀ ≠ ∅` non-triviality), (c)
  `inP1_isZeroReducibleVia` (the two zero conditions on `b` and `A`).
- Captures: **same content** as the existential `∃ inP1, (∃ i, inP1
  i = false) ∧ M.IsZeroReducibleVia inP1`. Direct projection onto
  the three components.

### Corollaries `pReduced_size_lt` / `zeroReduced_size_lt`

These are not direct textbook lemmas; they restate the existing
non-triviality conditions in the form that the future `reducedMethod`
recursion will consume. `pReduced_size_lt` is literally `sBar_lt`
under a renaming; `zeroReduced_size_lt` is a one-line application of
the cycle 195 helper `card_filter_true_lt_of_exists_false`.
**Tautology / identity check**: `pReduced_size_lt`'s body is just
`h.sBar_lt`. This isn't a vacuous re-export — `pReduced_size_lt`'s
*signature* matches the form the future `reducedMethod` recursion
needs (it states the strict-descent property under the
"pReduced-codomain stage count" naming). Documented in the docstring.

### Non-vacuity examples + P2 promotions

The two `example`s and two promoted theorems are non-vacuity
witnesses, not new mathematical content. They exercise prior cycles'
named lemmas on the canonical `paddedEuler` 2-stage tableau.

### Pre-commit checklist

- [x] **Tautology check**: no theorem conclusion equals a hypothesis
  verbatim. The destructors take `h : M.IsPReducible` /
  `h : M.IsZeroReducible` and conclude components of the underlying
  existential — semantically distinct from the hypothesis.
- [x] **Identity check**: `pReduced_size_lt` is `h.sBar_lt`; this is
  not vacuous because the signature reframes the conclusion under
  the "pReduced-codomain stage count is strictly less" naming
  needed for `reducedMethod`. Documented in docstring.
- [x] **Definition smuggling check**: no new `structure` or `class`
  introduced this cycle. The destructor predicates use the existing
  cycle 184/186 `IsPReducible` / `IsZeroReducible` definitions
  unchanged.
- [x] **Hypothesis strength check**: all destructor signatures take
  only the relevant existential hypothesis (`h : M.IsPReducible` or
  `h : M.IsZeroReducible`). No extra hypotheses beyond what the
  cycle 195 helper requires.

## Dead ends

None. All declarations elaborated on the first attempt without
fallback to `simpa` or `obtain`-tactic destructuring (the strategy's
"if the nested-`Exists` destructure shape misaligns" contingency).
The anonymous `(_ : sBar < s)` binder in `IsPReducible` decoded
cleanly through `.choose_spec.choose : h.sBar < s`.

## Discovery

* **Anonymous-binder Exists works directly with `.choose_spec.choose`**.
  The `IsPReducible` definition uses the binder pattern `∃ (sBar : ℕ)
  (_ : sBar < s) (P : …), …`, which sugars to nested `Exists`. The
  `.choose_spec` chain decodes it positionally — `h.choose_spec.choose
  : h.choose < s` works without needing `simpa` or `obtain`-tactic
  reconstruction. This is reusable plumbing for any future
  `Classical.choose`-based destructor over multi-witness existentials
  with embedded Prop-valued side conditions.
* **Destructor API decouples future recursion from `Classical.choose`
  plumbing**. Before cycle 196, any future `reducedMethod` definition
  had to inline `Classical.choose` extraction at each call site,
  duplicating the `.choose` / `.choose_spec` chain. With the cycle
  196 API, recursive callers can now write `h.partition`,
  `h.partition_isPReducibleVia`, `h.inP1`, etc. — the same shape as
  the implementation sketch in `reduced_method_deferred.md`.

## Suggested next approach

The cycle 195+196 deliverables furnish both halves of the future
`reducedMethod` recursion: the cycle 195 *measure* side
(`size_le` / `size_lt_of_step` / `size_lt_of_zeroStep`) plus the
cycle 196 *extraction* side (the destructors). The next-cycle work
on the def:381E roadmap is one of:

* **Option A — `WellFoundedRelation` via stage-count projection**.
  Define a Σ-wrapper `RKTableauSig := Σ s, RKTableau s` and a lifted
  `PReducesTo` relation on it. Equip the Σ-type with
  `WellFoundedRelation` via `WellFounded.onFun` projecting onto the
  first coordinate (stage count). This consumes cycle 195's
  `size_lt_of_step` / `size_lt_of_zeroStep` at the well-foundedness
  proof. **Multi-cycle**: at least one cycle for Σ-type ergonomics
  (push relevant lemmas through the wrapper) and a second for the
  relation lift + WF instance.

* **Option B — Decidability instances + `if hP : M.IsPReducible then
  …`-style recursion**. Provide `Decidable (M.IsPReducible)` /
  `Decidable (M.IsZeroReducible)` instances (these involve a
  decidable scan over finitely-many `PPartition s sBar` for each
  `sBar < s`, plus a decidable scan over finitely-many `Fin s →
  Bool` for `IsZeroReducible`). With decidability in hand, the
  recursive definition can use ordinary `if-then-else` branching
  and `decreasing_by` annotation citing cycle 195's descent lemmas.
  Likely *cleaner* than Option A in terms of API ergonomics —
  decidability is a more reusable artifact than a bespoke
  Σ-wrapper — but the decidability proofs themselves are non-trivial
  (`Decidable (∃ sBar … P, IsPReducibleVia M P)` requires reasoning
  over `Finset.image` of `PPartition`s).

* **Option C — `Classical.byCases` + bespoke recursion**.
  Use `Classical.byCases (M.IsPReducible)` to branch without
  needing decidability instances, and prove well-foundedness directly
  via the descent lemmas. Mathematically minimal but loses
  computability and recursion-equation hygiene compared to Option B.

Cycle 197 candidate: **Option B step 1** — provide
`Decidable (M.IsPReducible)` (the harder of the two — the
`PPartition` scan has more structure than the `Fin s → Bool` scan).
Alternative cycle 197 candidate: bundle cycle 195+196 deliverables
into a *non-recursive* witness — a lemma `reducedMethod_exists`
stating `∃ (s' : ℕ) (M' : RKTableau s'), M.PReducesTo M' ∧
M'.IsIrreducible`, proved by strong induction on `s` using the
descent lemmas + destructors. This unblocks def:381F (P-equivalent)
without committing to a recursive *function* yet — useful if the
def:381F formalisation can be cast existentially rather than
constructively.
