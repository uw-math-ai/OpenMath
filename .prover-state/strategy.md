# Cycle 209 strategy

## Current state at HEAD

* Branch `butcher-experiments` at `2d81622` (cycle 208).
* `OpenMath/Chapter3/Section381.lean`: 2358 LOC, **sorry count = 0**, axiom-clean.
* `thm:381H` status (after cycle 208): **2 of 4 iff-directions formalized** —
  `PEquivalent → PhiEquivalent` (cycle 187) and `PEquivalent → Equivalent`
  (cycle 208). Remaining two (`Equivalent → PEquivalent` and
  `PhiEquivalent → PEquivalent`) blocked on `thm:381G` per
  `.prover-state/issues/thm_381H_deferred.md`.
* `def:381A/B/C/D/E/F` all done or partial; `lem:383A/B/C` done;
  `thm:343A`, `thm:357C`, `def:357A/B`, `def:370A` done.
* §441 Phase C.2 is **28th-consecutive GPFS-blocked** per
  `cycle_182_gpfs_slowness.md`. Worker MUST NOT attempt this cycle.
* Pre-existing unused-variable linter warnings on Section381.lean:577
  and 2245 (cycle 208 noted, untouched).

## §A — Forbidden / do-not-attempt this cycle

1. **§441 Phase C.2** (`OpenMath/Chapter4/Section441.lean`). 28 consecutive
   GPFS timeouts (cycles 182–208) establish the pathology is not transient.
   Worker MUST NOT run `lake env lean OpenMath/Chapter4/Section441.lean`.
   Leave HEAD's `Section441.lean` untouched. Loop-maintainer territory.

2. **Full `thm:382A`, `thm:382B`** (group of RK methods, composition inverse).
   Both have `thm:381H` as a transitive dependency
   (verified in `entities/thm_382A.json` `transitive_dependencies`); the
   full iff is not closed yet, so attempting these will stall.

3. **Closing the remaining `thm:381H` directions** (`Equivalent → PEquivalent`,
   `PhiEquivalent → PEquivalent`). These need `thm:381G` (multi-cycle —
   needs `thm:314A` + subalgebra-of-elementary-weights infrastructure)
   per cycle 199 recon. Out of scope.

4. **Re-introducing the `thm:381H` umbrella scaffold with new sorries.**
   Supervisor scored cycle 200 at −2 for adding 3 sorries; even a 2-sorry
   version would likely score the same. Wait until ≥1 remaining direction
   becomes single-cycle closeable.

5. **`thm:306A` (Butcher's multivariate Taylor)** — NOT a thin Mathlib
   wrapper. The textbook form is a multi-index combinatorial sum
   (`∑_{I ∈ ℐ_m} f^(#I)(a) δ_I / σ(I)`) that needs multi-index types,
   symmetry factors, and multilinear derivatives. Multi-cycle. Skip.

6. **`lem:312B`, `lem:310B`** — transitively depend on `thm:306A` and/or
   `thm:311B`, neither of which is shipped. Heavy multi-cycle prerequisites.

7. **`axiom`/`constant`** declarations of any kind.
8. **`maxHeartbeats`** bumps above 200000.

## §B — Primary deliverable (P1): `RKTableau.compose` §382 infrastructure

Butcher §382 (page 285, equation (382a)) defines the composition operation
on RK methods. Given two methods `M₁ = (A, b, c)` with `s` stages and
`M₂ = (Ā, b̄, c̄)` with `s̄` stages, the composition `M₁ · M₂` is the
RK tableau with `s + s̄` stages:

```
A_composed (block (s + s̄) × (s + s̄)):
  ┌──────────┬──────────┐
  │   A      │   0      │   ← top-left  s × s    = M₁.A
  ├──────────┼──────────┤   ← top-right s × s̄   = 0
  │ rows b   │   Ā      │   ← bot-left  s̄ × s    = row-i has b_j in col j
  └──────────┴──────────┘   ← bot-right s̄ × s̄   = M₂.A

b_composed := Fin.append b b̄
c_composed := Fin.append c (fun i => (Σⱼ b_j) + c̄_i)
```

Textbook verification (from extraction/raw_text/ch03.txt:8678–8703):
* Top block c-column: `c₁, c₂, ..., cₛ`
* Bottom block c-column: `Σⱼ b_j + c̃₁, ..., Σⱼ b_j + c̃ₛ̄`
* This matches the substitution `Ỹᵢ = y₁ + h·Σ aᵢⱼ F̃ⱼ` where
  `y₁ = y₀ + h·Σ b_j F_j` (see (382c)/(382d) substitution at 8740).

### Concrete deliverables

Place new content at the END of `OpenMath/Chapter3/Section381.lean`,
inside an explicit `namespace OpenMath.Chapter3.Section312.RKTableau`
block (re-opening the namespace if needed). Don't try to interleave
with existing content elsewhere in the file — append-only is the
safest pattern for a 2358-LOC file.

`RKTableau` is defined in `OpenMath/Chapter3/Section312.lean:66` as
`structure RKTableau (s : ℕ) where A, b, c` — all three fields are
independent (no derived `c`), so the compose def must populate all
three explicitly.

#### D1. Define `RKTableau.compose`

```lean
/-- Composition of two Runge–Kutta methods per Butcher §382 (382a)
(p. 285). Given `M₁ : RKTableau s₁` and `M₂ : RKTableau s₂`, the
composition `M₁.compose M₂ : RKTableau (s₁ + s₂)` performs one full
step of `M₁` followed by one full step of `M₂` (from the result of
`M₁`). The block structure of the `A`-matrix encodes the two-substep
computation: the bottom-left block (each row equals `M₁.b`) reflects
the substitution `y₁ = y₀ + h·Σⱼ bⱼ Fⱼ` from (382c) into (382d). -/
def compose {s₁ s₂ : ℕ} (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) :
    RKTableau (s₁ + s₂) where
  A := fun i j =>
    Fin.addCases
      (motive := fun _ => ℝ)
      (fun i₁ =>
        Fin.addCases (motive := fun _ => ℝ)
          (fun j₁ => M₁.A i₁ j₁)
          (fun _  => 0)
          j)
      (fun i₂ =>
        Fin.addCases (motive := fun _ => ℝ)
          (fun j₁ => M₁.b j₁)
          (fun j₂ => M₂.A i₂ j₂)
          j)
      i
  b := Fin.append M₁.b M₂.b
  c := Fin.append M₁.c (fun i => (∑ j, M₁.b j) + M₂.c i)
```

If the `motive := fun _ => ℝ` annotations cause elaboration issues,
try dropping them (Lean often infers the motive from context). If
that fails, look up the canonical `Fin.addCases` usage with
`lean_local_search "Fin.addCases"` and mirror an existing Mathlib
pattern.

#### D2. Structural simp lemmas (axiom-clean, all `by rfl` or one-line `simp`)

Ship at least these four:

```lean
@[simp] theorem compose_b_castAdd {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (i : Fin s₁) :
    (M₁.compose M₂).b (Fin.castAdd s₂ i) = M₁.b i := by
  simp [compose, Fin.append_left]

@[simp] theorem compose_b_natAdd {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (i : Fin s₂) :
    (M₁.compose M₂).b (Fin.natAdd s₁ i) = M₂.b i := by
  simp [compose, Fin.append_right]

@[simp] theorem compose_A_topLeft {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (i j : Fin s₁) :
    (M₁.compose M₂).A (Fin.castAdd s₂ i) (Fin.castAdd s₂ j) = M₁.A i j := by
  simp [compose, Fin.addCases_left]

@[simp] theorem compose_A_topRight {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (i : Fin s₁) (j : Fin s₂) :
    (M₁.compose M₂).A (Fin.castAdd s₂ i) (Fin.natAdd s₁ j) = 0 := by
  simp [compose, Fin.addCases_left, Fin.addCases_right]
```

Optionally also ship `compose_A_botLeft` (entry = `M₁.b j`) and
`compose_A_botRight` (entry = `M₂.A i j`):

```lean
@[simp] theorem compose_A_botLeft {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (i : Fin s₂) (j : Fin s₁) :
    (M₁.compose M₂).A (Fin.natAdd s₁ i) (Fin.castAdd s₂ j) = M₁.b j := by
  simp [compose, Fin.addCases_right, Fin.addCases_left]

@[simp] theorem compose_A_botRight {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (i j : Fin s₂) :
    (M₁.compose M₂).A (Fin.natAdd s₁ i) (Fin.natAdd s₁ j) = M₂.A i j := by
  simp [compose, Fin.addCases_right]
```

If `Fin.addCases_left` / `Fin.addCases_right` names are wrong in the
current Mathlib, do a quick `lean_local_search "Fin.addCases"` to find
the actual names (might be `Fin.addCases_castAdd` / `Fin.addCases_natAdd`).
Similarly `Fin.append_left` / `Fin.append_right` may be
`Fin.append_castAdd` / `Fin.append_natAdd` — verify before use.

#### D3. Non-vacuity witness on `paddedEuler`

```lean
/-- Non-vacuity: composition of two `paddedEuler` instances yields a
4-stage tableau via `RKTableau.compose`. -/
example : RKTableau 4 := paddedEuler.compose paddedEuler
```

Plus at least one concrete coefficient check:

```lean
example : (paddedEuler.compose paddedEuler).b (Fin.castAdd 2 ⟨0, by norm_num⟩)
            = paddedEuler.b ⟨0, by norm_num⟩ := by
  exact compose_b_castAdd paddedEuler paddedEuler ⟨0, by norm_num⟩
```

(Or by `simp` if the simp lemma is registered.)

### LOC budget for P1: ≤ 80 LOC total (def + 4–6 structural lemmas + 2
witnesses). The definition is ~15 LOC, each lemma 2–5 LOC, the examples
1–3 LOC. If you blow past 80 LOC, stop and ship what you have.

### Risk and fallback for P1

* **Risk 1 (medium): `Fin.addCases` with `motive` annotation may need
  rephrasing.** If the body in §D1 doesn't elaborate, try dropping
  `(motive := ...)`. If that still fails, look up
  `Fin.addCases` in `Mathlib.Logic.Equiv.Fin.Basic` or similar and
  mirror an existing call site.
* **Risk 2 (medium): The simp lemmas might not all close by the
  proposed `simp [compose, Fin.addCases_left]` etc.** Lemma names may
  differ in current Mathlib. Use `lean_local_search "Fin.addCases"`
  and `lean_local_search "Fin.append"` early — these are 5-minute
  checks that prevent 30-minute rabbit holes.
* **Risk 3 (low): `c`-field algebra may need explicit Finset.** If
  `(∑ j, M₁.b j) + M₂.c i` is ambiguous about which Finset, write
  `(∑ j : Fin s₁, M₁.b j)` to pin it down.
* **Risk 4 (low): The `compose_A_botLeft` proof requires nested
  `Fin.addCases_*` rewrites.** If `simp` doesn't close it, try
  `unfold compose; simp only [...]`. The double-`Fin.addCases` in `A`
  may need two rewriting passes.

If P1 stalls past ~90 minutes of work, **abort to P-fallback** below
without further attempts.

## §C — Secondary deliverable (P2): bundled bridge corollary

This is the explicit suggestion from cycle 208 task results §"Suggested
next approach" item 5. Ships in ~5 LOC of pure ergonomics.

In `OpenMath/Chapter3/Section381.lean`, namespace
`OpenMath.Chapter3.Section312.RKTableau`, **immediately after** the
existing `PReducesTo.toEquivalent` (cycle 207) and
`PReducesTo.toPhiEquivalent` (cycle 187/193), add:

```lean
/-- Umbrella corollary packaging the two `thm:381H`-direction bridges
out of `PReducesTo`. Useful as a single hand-hold for downstream
consumers wanting both equivalence conclusions from one `PReducesTo`
hypothesis. -/
theorem PReducesTo.toEquivalent_and_toPhiEquivalent.{u}
    {s s' : ℕ} {M : @RKTableau.{u} s} {M' : @RKTableau.{u} s'}
    (h : PReducesTo M M') :
    @Equivalent.{u} M M' ∧ PhiEquivalent M M' :=
  ⟨h.toEquivalent, h.toPhiEquivalent⟩
```

Universe annotation `.{u}` per cycle 204/208 discovery (Equivalent is
universe-polymorphic; signature needs `.{u}` to bind universes).

`PReducesTo` IS a structure (with `refl`/`step`/`zeroStep` constructors,
per Section381.lean cycle 188 expansion), so dot-notation
`h.toEquivalent` and `h.toPhiEquivalent` resolve correctly against
`PReducesTo.toEquivalent` (cycle 207) and `PReducesTo.toPhiEquivalent`
(cycle 187/193). The cycle 208 `.symm` dot-notation pitfall does NOT
apply here — it only bit on ∀-form predicates like `Equivalent`, not
on inductive structures like `PReducesTo`.

If for any reason dot-notation fails (e.g. namespace shadowing), use
fully-qualified calls:

```lean
  ⟨PReducesTo.toEquivalent h, PReducesTo.toPhiEquivalent h⟩
```

Verify axiom-clean ([propext, Classical.choice, Quot.sound]). LOC ≤ 10.

## §D — Stretch deliverable (P3, optional): linter cleanup

Address the two unused-variable warnings on Section381.lean:577 and
2245. Cycle 208 noted these as pre-existing. The fix is either:
* Prefix the unused binder with `_` (e.g. `heq` → `_heq`), OR
* Remove the binder entirely if Lean accepts `_` in its place.

Inspect both lines, decide which is appropriate, and apply minimal
diff. Do not refactor surrounding proofs. If the binder name carries
useful documentation value (e.g. `heq` documents the hypothesis was
about an `HEq`), leave alone and document in cycle results why.

LOC ≤ 5 total. Strictly optional — skip if budget tight.

## §E — Order of operations

1. **5 min** — verify HEAD state. Run:
   ```
   git log -1 --format='%H %s'
   grep -c sorry OpenMath/Chapter3/Section381.lean
   ```
   Expect `2d81622 Cycle 208 — §380 PEquivalent.toEquivalent ...` and `0`.

2. **5 min** — re-read extraction/raw_text/ch03.txt lines 8671–8742
   to confirm the §382 composition formula matches the strategy's §B
   summary. Pay particular attention to the leftmost c-column of
   (382a): top block is `c₁, ..., cₛ`; bottom block is
   `Σⱼ bⱼ + c̃₁, ..., Σⱼ bⱼ + c̃ₛ̄`. The bottom-left A-block has
   `row-i column-j = bⱼ` for every i (NOT a rank-1 multiplication of
   bᵀ — it's literally a constant column pattern across i).

3. **5 min** — use `lean_local_search` to verify Mathlib names:
   * `Fin.addCases` (definitional)
   * `Fin.addCases_left` (or `Fin.addCases_castAdd`)
   * `Fin.addCases_right` (or `Fin.addCases_natAdd`)
   * `Fin.append_left` (or `Fin.append_castAdd`)
   * `Fin.append_right` (or `Fin.append_natAdd`)
   Adjust strategy's simp lemma proofs if names differ.

4. **45–60 min** — ship P1 (compose def + 4–6 structural lemmas + 1–2
   non-vacuity examples). Verify axiom-clean each new theorem with
   `lean_verify` MCP tool.

5. **5–10 min** — ship P2 (PReducesTo.toEquivalent_and_toPhiEquivalent
   bundled corollary). Verify axiom-clean.

6. **5–10 min** — (optional) P3 linter cleanup.

7. **5 min** — write `.prover-state/task_results/cycle_209.md` per
   CLAUDE.md format.

8. **5 min** — update `lean_status.json` only if applicable.
   `compose` is internal infrastructure with no entity ID, so likely
   no row update. `thm:381H` row stays unchanged (still 2/4 directions
   formalized). Skip if no row needs touching.

9. **5 min** — update `plan.md` if applicable (likely no row change).

10. **5 min** — commit with descriptive message per §J template.

**Total budget**: ≤ 90 minutes hands-on, ≤ 120 minutes wall-clock
(allowing for verification overhead).

## §F — Fallback plan (P-fallback) if P1 stalls

If P1 stalls past 90 min (e.g. `Fin.addCases` elaboration issues,
simp lemma proofs not closing, or composition formula details prove
fiddly), abort P1 cleanly:
* Remove the partial `compose` definition (revert to HEAD).
* Pivot to the cycle 208 task results' "cheap sanity-check filler"
  option: add 3–5 more `paddedEuler`-style non-vacuity witnesses
  exercising existing §380 theorems through their constructor paths.

Suggestions for filler non-vacuity witnesses (each is 1–3 lines):
* More `paddedEuler_pEquivalent_*` corollaries through cycle 188's
  bridges.
* A `paddedEuler.PhiEquivalent paddedEuler` witness via cycle 187's
  `PEquivalent.toPhiEquivalent` composed with cycle 184's reflexive
  `paddedEuler.PEquivalent paddedEuler`.
* Promote any remaining inline `example`/`have` witnesses in
  Section381.lean to public named theorems (use `grep -n "example :"
  OpenMath/Chapter3/Section381.lean` to find candidates).
* Bundle small corollaries like
  `paddedEuler_equivalent_and_phiEquivalent_pReduced` (combining
  cycle 187 and cycle 208 outputs).

Then still ship P2 (bundled bridge) and write cycle results.

A cycle that ships P2 + P3 + non-vacuity filler with sorry count 0
satisfies CLAUDE.md's "minimum: decompose a sorry or write an issue"
rule even without P1.

## §G — Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `Fin.addCases` elaboration trips on `motive` | medium | drop annotation; check Mathlib for existing pattern; mirror existing call site |
| `Fin.append`/`Fin.addCases` lemma names different in current Mathlib | medium | use `lean_local_search` at start of cycle (§E step 3) |
| `.toEquivalent` dot-notation fails on `PReducesTo` arg | low | `PReducesTo` is a structure — dot should work; fallback to fully-qualified call |
| GPFS slowness affects Section381.lean compile | low | Section381 has compiled healthy throughout cycles 182–208 (only Section441 is GPFS-blocked); if it stalls, abort and pivot to P-fallback |
| Worker tempted to attempt `thm:382A` after seeing the compose def | medium | strategy §A.2 explicitly forbids; flag in task results if temptation arose |
| compose c-field formula off-by-one or sign error | low | textbook re-read step (§E.2) catches before coding; the bottom c-entries are `(Σⱼ bⱼ) + c̃ᵢ`, not `(Σⱼ bⱼ)·c̃ᵢ` or similar |

## §H — Faithfulness checklist (per CLAUDE.md, before commit)

For the `compose` definition:
* Quote Butcher §382 (382a) in the docstring (one line: "Butcher §382
  equation (382a), p. 285").
* The c-field formula must match the textbook's leftmost column. Verify
  on paper.
* **Definition smuggling check**: `compose` is INFRASTRUCTURE, not a
  named textbook concept (Butcher writes `m₁ · m₂` for the resulting
  method but does not give it a separate name beyond `m₁ · m₂`).
  It's a building block for future `thm:382A` work, not a stand-alone
  textbook deliverable. Mark the docstring accordingly: "Internal
  infrastructure for §382 group-theoretic results; the full `thm:382A`
  closure remains blocked on `thm:381H`."

For each structural lemma:
* **Tautology check**: lemma conclusions should be computational
  unfoldings, not re-exports of hypotheses. The `compose_b_castAdd`
  / `compose_A_topLeft` lemmas reveal block structure; they are
  computational (`by rfl` or `simp`), not tautological.
* **Identity check**: if a proof is `by rfl`, that's fine — the lemma
  is a definitional unfolding, not an identity wrapper.

For the bundled bridge corollary (P2):
* **Tautology check**: this IS a packaging corollary, not new content.
  Its body is `⟨h.toEquivalent, h.toPhiEquivalent⟩` — both components
  do real work (cycle 207 and cycle 187 closures). Conjunction is
  the new content; document as "ergonomic packaging" in the docstring.

## §I — What to write in `task_results/cycle_209.md`

Standard format per CLAUDE.md. Specific points to cover:
* P1 deliverable: how the `compose` def was written, which `Fin.addCases`
  pattern worked, any elaboration surprises.
* P2 deliverable: confirm `.toEquivalent`/`.toPhiEquivalent` dot-notation
  works on `PReducesTo` (or note the fallback).
* P3 deliverable status (shipped, deferred with rationale, or skipped).
* §441 Phase C.2 GPFS-blocked status: 29th-consecutive skip per §A.
* Discoveries section: anything novel about `Fin.addCases` + `Matrix`
  interaction; any new simp lemmas needed; whether the textbook
  composition formula matched exactly or required minor reinterpretation.
* Suggested next approach: with `compose` in place, the next §382
  cycle could attempt structural lemmas like `compose_explicit_iff`
  (does compose preserve `IsExplicit` from cycle 151? — yes, the
  block-triangular A-matrix is strict lower triangular iff both M₁.A
  and M₂.A are), or define the identity element from Butcher §382
  (`m₀` mapping initial value to equal value — likely
  `RKTableau.identityElement` as some zero-stage or scaling). Full
  `thm:382A` remains multi-cycle until `thm:381H` closes.

## §J — Commit message template

```
Cycle 209 — §382 RKTableau.compose infrastructure + §380 bundled bridge

P1 §382 RKTableau.compose definition matching Butcher (382a) p. 285
block-tableau composition formula (A in 2x2 Fin.addCases block form
with top-left=M1.A, top-right=0, bot-left=row-of-b1, bot-right=M2.A;
b=Fin.append M1.b M2.b; c=Fin.append M1.c (sum_b1 + M2.c)), ~XX LOC.
4-6 axiom-clean simp lemmas (compose_b_castAdd, compose_b_natAdd,
compose_A_topLeft, compose_A_topRight [+ optional botLeft, botRight])
plus a paddedEuler.compose paddedEuler non-vacuity example exercising
the new infrastructure. The definition is internal infrastructure
for the future thm:382A formalization (blocked on thm:381H per
thm_381H_deferred.md cycle 208 status); thm:382A/B not attempted
this cycle.

P2 §380 bundled bridge PReducesTo.toEquivalent_and_toPhiEquivalent
(~5 LOC ergonomics) packaging the two cycle-187/207-shipped directions
of thm:381H out of a single PReducesTo hypothesis. Axiom-clean.

[P3 if shipped: linter cleanup on Section381.lean:577/2245 by _-prefix
on unused-variable warnings.]
[P3 if skipped: P3 deferred — linter warnings on Section381.lean:577
and 2245 are non-blocking and out of cycle 209 scope.]

All new theorems axiom-clean ([propext, Classical.choice, Quot.sound]).
Sorry count remains 0; cycle 208 deliverables (PEquivalent.toEquivalent,
paddedEuler_equivalent_pReduced, paddedEuler_equivalent_zeroReduced,
PEquivalent.toEquivalent_and_toPhiEquivalent) all re-verified
axiom-clean — no regressions.

§441 Phase C.2 GPFS-blocked (29th consecutive, skipped per strategy §A).
```
