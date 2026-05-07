# Cycle 184 Results

## Worked on

Two fronts:

**Front A (primary, partial):** `lem:441A` Phase C.2 — close the
cycle 182 proof draft by combining Aristotle's verification feedback
with a local compile.

**Front B (pivot, shipped):** `def:381F` (P-equivalent Runge–Kutta
methods, Butcher §380 p. 303) — definition-only deliverable +
non-vacuity witness, per cycle 184 strategy Option 3A.

## Approach

### Front A — Phase C.2 verification

1. Process janitor — confirmed no stuck `find /` zombies and no
   leftover lake/lean processes from prior cycles.
2. Polled Aristotle ONCE: project `7c4d0ffb-e6c1-4ef4-b8f5-688d256bac44`
   status `COMPLETE_WITH_ERRORS` at 12:50 PDT 2026-05-07. Aristotle's
   `ARISTOTLE_SUMMARY.md` claimed the cycle 182 draft compiles
   "with no errors" against Aristotle-authored stubs, with a single
   real change to the draft itself (a namespace-resolution fix on
   line 1529). `diff` of Aristotle's modified file vs the cycle 182
   draft confirms the only change is one line:

   ```diff
   -      M.αPoly_complex_root_norm_ge_one_of_stable hStable hψ_ne hψ_isRoot
   +      LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable
   +        M hStable hψ_ne hψ_isRoot
   ```

   The fix is genuinely correct: `αPoly_complex_root_norm_ge_one_of_stable`
   is declared in the `Section441` namespace (line 1419, after
   `namespace OpenMath.Chapter4.Section441` at line 950), but
   `M : LinearMultistepMethod k` is typed against `Section404`, so
   the dot-notation lookup
   `Section404.LinearMultistepMethod.αPoly_…` fails. The other items
   in Aristotle's summary were stub replacements for our real
   `Section404`/`410`/`451`, irrelevant here.

3. GPFS health check: `time timeout 480 lake env lean OpenMath/Chapter4/Section441.lean`
   on cycle-181 HEAD timed out at 8 min with near-zero CPU (0.271s
   user, 0.525s sys). GPFS still degraded.

4. Per Branch 1B Step 3 (apply fix + re-verify locally), backed up
   HEAD `Section441.lean`, replaced with the cycle 182 draft + the
   namespace fix on line 1529, ran `time timeout 1200 lake env lean
   OpenMath/Chapter4/Section441.lean`. Lean process at ~1% CPU
   throughout, log empty. Compile timed out at 20 min (EXIT=124).
   This is the **fourth** failed local-compile attempt for the
   cycle 182 draft (cycles 182×2, 183, 184).

5. Per Branch 1B mid-fail clause, did **not** re-submit a follow-up
   Aristotle job (no specific tactic errors to re-verify — the only
   error was the namespace fix, already applied). Reverted
   `Section441.lean` to cycle-181 HEAD (1227 LOC).

### Front B — `def:381F` pivot

6. Per cycle 184 strategy Option 3A, formalised `def:381F`
   (P-equivalent) in `OpenMath/Chapter3/Section381.lean`.

7. Read `extraction/formalization_data/entities/def_381F.json`:
   "Two Runge–Kutta methods are 'P-equivalent' if each of them
   reduces to the same reduced method." (Butcher §380 p. 303,
   `def_381F.json` `statement_text`.) Dependencies: `def:381E`
   (the reduced method = P-reduce then 0-reduce). The textbook's
   "reduced method" is a deferred concept (see
   `.prover-state/issues/reduced_method_deferred.md`) — only its
   `IsIrreducible` predicate is formalised in HEAD.

8. Captured the **P-only flavour** of the textbook definition:

   * `RKTableau.PReducesTo` — inductive type, reflexive-transitive
     closure of single-step P-reduction (`refl` + `step` taking a
     `PPartition` and `IsPReducibleVia` proof).
   * `RKTableau.PEquivalent M M'` — `∃ Mbar, PReducesTo M Mbar ∧
     PReducesTo M' Mbar` (textbook's "common reduced method"
     formulation, modulo the missing 0-reduction step).
   * `RKTableau.PEquivalent.refl` — reflexivity (5 LOC).
   * `RKTableau.PEquivalent.symm` — symmetry (3 LOC).
   * `RKTableau.PEquivalent.of_pReducesTo` — every reduction is a
     P-equivalence witness (3 LOC).
   * Non-vacuity `example`: `paddedEuler` is P-equivalent to its
     1-stage P-reduction via `pairPartition` (exercises the `step`
     constructor beyond reflexivity).

9. First compile failed with a namespace error: the witness in the
   `Section381` namespace block referred to `PEquivalent` /
   `PReducesTo` unqualified, but they live in
   `OpenMath.Chapter3.Section312.RKTableau`. Fixed by using dot
   notation `paddedEuler.PEquivalent (...)` for the type and
   explicit `RKTableau.PEquivalent.of_pReducesTo` /
   `RKTableau.PReducesTo.step` / `.refl` for the term. Recompiled
   clean.

10. `lean_verify` on the three new public declarations
    (`PEquivalent`, `PEquivalent.refl`, `PEquivalent.of_pReducesTo`):
    all axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

11. Bookkeeping:
    * `extraction/formalization_data/lean_status.json` — `def:381F`
      moved from `unformalized` to `partial` (status `partial` because
      the 0-reduction half of the reduced-method construction is
      still deferred; the current `PEquivalent` captures the P-only
      flavour). `lem:441A` notes updated with the cycle 184 outcome.
    * `plan.md` — `def:381F` row updated to `[~]` with cycle 184
      details; `lem:441A` row appended with the cycle 184 outcome
      (Aristotle namespace fix, fourth GPFS-blocked compile, pivot).
    * `.prover-state/issues/lem_441A_phase_C_scoping.md` — Phase C.2
      cycle 184 update appended (Aristotle outcome, namespace fix
      diff preserved, cycle 185 entry point).
    * `.prover-state/issues/cycle_182_gpfs_slowness.md` — cycle 184
      update appended (Aristotle returned, fourth failed compile,
      pivot).

## Result

* **Front A: BLOCKED** — Phase C.2 verification still blocked by
  GPFS slowness. The cycle 182 draft + Aristotle's namespace fix is
  one fix away from being committable; the file is
  preserved at `.prover-state/cycle_182_draft_section441.lean` and
  the one-line diff is documented in `lem_441A_phase_C_scoping.md`.
  Cycle 185 should retry the local compile if GPFS recovers.

* **Front B: SUCCESS** — `def:381F` shipped. `OpenMath/Chapter3/Section381.lean`
  compiles clean; three new public declarations are axiom-clean.

## Faithfulness check

### `RKTableau.PReducesTo` (inductive type)

Auxiliary scaffolding for `def:381F`. Captures the standard
reflexive-transitive closure of single-step P-reduction. The
textbook does not name this relation but uses it implicitly: "each
of them reduces to the same reduced method" presupposes a notion of
multi-step reduction. Our `PReducesTo` is the standard formalisation
of "reduces in zero or more P-steps". 0-reduction will be folded in
as an additional constructor once `def:381E`'s reduced-method
infrastructure lands.

Lean statement captures: same content (the standard inductive
construction of refl-trans closure, with the single-step constructor
gated by `IsPReducibleVia`).

### `RKTableau.PEquivalent` (def)

Entity: `def:381F`. Quoted from
`extraction/formalization_data/entities/def_381F.json`
(`statement_text`):

> Two Runge–Kutta methods are 'P-equivalent' if each of them reduces
> to the same reduced method.

Lean statement captures: **same content modulo the deferred
0-reduction half**.

* The textbook's "reduced method" (def:381E) means
  P-reduce-then-0-reduce iterated until irreducible. Our
  `PEquivalent` uses `PReducesTo` which currently only supports
  P-reductions. The two definitions agree on methods that are
  already 0-irreducible, and disagree on methods that differ only by
  a 0-reduction.
* The choice is **deliberate**: extending `PReducesTo` with a
  0-reduction constructor is a 5-line edit once the reduced-method
  infrastructure lands. The current definition is faithful to the
  P-side of the textbook claim and exercises the textbook's
  row-sum-constancy P-reduction (def:381D); the 0-reduction
  strengthening is a clean follow-up rather than a re-design.
* No silent strengthening: hypothesis is the existence of the common
  reduction, exactly as the textbook states.

The status in `lean_status.json` is `partial` (not `formalized`) to
flag this divergence.

### `PEquivalent.refl`, `PEquivalent.symm`, `PEquivalent.of_pReducesTo`

Standard equivalence-relation infrastructure + the
"reduction-is-an-equivalence-witness" corollary. Each follows
mechanically from the inductive definition; none introduces new
hypotheses. Lean statements capture: standard meaning.

### `paddedEuler.PEquivalent (paddedEuler.pReduced pairPartition)` (witness)

Non-vacuity check. `paddedEuler` is the 2-stage tableau with
`A = 0`, `b = ![1, 0]`, `c ≡ 0` (Section381 line 154).
`pairPartition` merges both stages into one block. Combined with
`paddedEuler.IsPReducibleVia pairPartition` (already proved as an
example in HEAD, lines 441–443), the witness exercises
`PReducesTo.step` followed by `PReducesTo.refl`, beyond pure
reflexivity. Confirms `PEquivalent` is satisfiable on a non-trivial
P-reduction step.

## Tautology check

* `PEquivalent.refl M : PEquivalent M M` — conclusion
  `PEquivalent M M` is not the same as the implicit hypothesis
  `M : RKTableau s` (one is a `Prop`, the other a tableau). No
  tautology.
* `PEquivalent.symm` — conclusion `PEquivalent M' M` differs from
  hypothesis `PEquivalent M M'` (the order of the arguments matters
  in the definition's existential formula). No tautology.
* `PEquivalent.of_pReducesTo` — converts `PReducesTo M M'` to
  `PEquivalent M M'`. The relations are different: `PEquivalent`
  requires a *common* reduction target, `PReducesTo` is asymmetric.
  No tautology.

## Identity check

* `PEquivalent.refl`: not `exact h` — constructs `⟨s, M, refl, refl⟩`
  using the `⟨...⟩` anonymous-constructor syntax for the underlying
  `∃` chain.
* `PEquivalent.symm`: not `exact h` — destructures the existential
  and reassembles with the two reduction proofs swapped.
* `PEquivalent.of_pReducesTo`: not `exact h` — wraps `h` together
  with `PReducesTo.refl M'` in the `⟨s', M', h, refl⟩` structure;
  doing real work (passing `h` as the witness and constructing the
  reflexive companion).

## Hypothesis strength check

All hypotheses are minimal:

* `PEquivalent`: takes only the two methods, no auxiliary structure.
* `PReducesTo.step`: takes the partition `P` and the
  `IsPReducibleVia` proof — exactly the textbook's row-sum-constancy
  hypothesis (def:381D, the textbook's only condition for
  P-reducibility). No extra normalisation, no hidden consistency
  assumption.
* `PEquivalent.of_pReducesTo`: takes only `PReducesTo M M'`.

No hypothesis is stronger than the textbook requires.

## Definition smuggling check

`PEquivalent` is a `def` (not a `class` or `structure`). All its
content is in the existential-quantifier formula; no `Prop` field
encodes a derivable consequence.

`PReducesTo` is an inductive type with two constructors (`refl`,
`step`); the constructors faithfully encode the standard refl-trans
closure of P-reduction. No constructor encodes a consequence that
should be derived elsewhere.

## Dead ends

* **Front A first round**: replaced HEAD `Section441.lean` with the
  cycle 182 draft + namespace fix and ran a 20-min local compile;
  timed out at EXIT=124. Reverted.
* **Front B first compile**: namespace error — the witness in
  `Section381` namespace couldn't see `PEquivalent` /
  `PReducesTo` unqualified. Fixed by using dot notation +
  explicit `RKTableau.` qualification.

## Discovery

* **Aristotle's stub fallback surfaces real bugs even with imperfect
  context.** Aristotle stubbed our `Section404`/`410`/`451` (its
  stubs are missing the `β` field on `LinearMultistepMethod` and use
  the opposite-direction `IsPreconsistent`), but the stubs were
  close enough to surface a real namespace-resolution bug that would
  have hit our real codebase too. When using Aristotle for
  verification, expect to filter stub-related "fixes" from real
  ones via `diff`; the diff reduced 4 alleged "fixes" to one real
  one in cycle 184.

* **Namespace dot-notation pitfall on cross-file structures.** The
  cycle 182 draft adds methods to `LinearMultistepMethod` (defined
  in `Section404`) from inside the `Section441` namespace block.
  Lean's dot-notation
  `M.αPoly_complex_root_norm_ge_one_of_stable` looks up
  `Section404.LinearMultistepMethod.…`, missing the `Section441.`
  declaration. The fix is to use the explicit qualified name
  `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`
  (or open `Section441` in the call site). General lesson: when
  adding new methods to a structure across namespaces, prefer
  `namespace LinearMultistepMethod` (matching the structure's home
  namespace) over `namespace Section441; theorem
  LinearMultistepMethod.foo …`.

* **GPFS slowness is sticky across cycles.** Even after killing the
  `find /` zombie in cycle 183, the 8-min HEAD compile timeout in
  cycle 184 shows the cluster's GPFS performance is still degraded.
  The Section381 compile (smaller file, ~600 LOC HEAD) took ~6 min
  to start producing output, vs the cycle 175 baseline of <1 min.
  Recommend cycle 185 retry the HEAD `Section441.lean` smoke test
  before any heavy work.

## Suggested next approach

For cycle 185:

1. **Re-attempt the cycle 182 draft compile.** If the HEAD
   `Section441.lean` smoke test completes in <5 min (GPFS recovered),
   replace HEAD with the cycle 182 draft + the namespace fix on line
   1529 (preserved at `.prover-state/cycle_182_draft_section441.lean`)
   and re-attempt the 20-min compile. The namespace fix is the only
   known issue.

2. **If still GPFS-blocked**, continue Step 3 pivot. Options:
   * **Option B1**: extend `PReducesTo` with a 0-reduction
     constructor (5-line edit) to capture the full textbook
     def:381F. This requires `def:381E`'s reduced-method
     construction to land first, OR a one-step 0-reduction
     constructor (analogous to `step` but using
     `IsZeroReducibleVia`).
   * **Option B2**: ship `PEquivalent.trans` (transitivity over
     heterogeneous size-changing reductions). Requires careful
     handling of dependent stage-count parameter, but is a clean
     ~30 LOC addition.
   * **Option B3**: investigate `def:422B` (underlying one-step
     method) — the strategy listed it as Option 3B but the entity
     JSON shows it depends on the deep G1 tree-algebra group and
     may exceed the 80–150 LOC budget. Recommend reading the entity
     JSON before committing.

3. **Once Phase C.2 ships**, Phase C.3 (real factorisation, 250–400
   LOC, highest-risk per scoping doc) is the next substantive
   target for `lem:441A`.
