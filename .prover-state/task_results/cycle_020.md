# Cycle 020 Results

## Worked on

`def:381D` — **P-reducible Runge–Kutta methods** (Butcher §380, p. 303),
together with the **P-reduced method** construction. Per the cycle-020
strategy, these are zero-dependency definitional content with high
unblock multiplicity (5 dependents: `def:370A`, `def:381A`, `def:381C`,
`def:381E`, `thm:381H`).

Deliverables added to `OpenMath/Chapter3/Section381.lean`:

* `OpenMath.Chapter3.Section381.PPartition` — structure encoding a
  partition of `Fin s` into `Fin sBar` blocks via a surjective
  block-index function.
* `OpenMath.Chapter3.Section312.RKTableau.IsPReducibleVia` — the
  row-sum-constancy condition predicating a P-partition.
* `OpenMath.Chapter3.Section312.RKTableau.IsPReducible` — the
  existential closure with non-triviality `sBar < s`.
* `OpenMath.Chapter3.Section312.RKTableau.pReduced` — the constructor
  for the P-reduced method (`A`, `b`, `c` formulae from def:381D).
* Three API lemmas: `pReduced_A_apply` (independence-of-choice under
  `IsPReducibleVia`), `pReduced_b_apply` (rfl), `pReduced_c_apply` (rfl).
* `pairPartition` and two `example`s witnessing that `paddedEuler`
  (cycle-019 2-stage tableau, A=0) is `IsPReducibleVia pairPartition`
  and `IsPReducible`. This establishes non-vacuity.

## Approach

1. Confirmed the planner-stated state (HEAD `b3bc9ad`, sorry/tautology
   scanners clean, Section381 builds clean).
2. Loaded `extraction/formalization_data/entities/def_381D.json`,
   quoted `statement_text` verbatim into the file's docstring.
3. Wrote the structure + four `def`s + three API lemmas in one pass
   (proofs were short enough not to need a sorry-first scaffold;
   `pReduced_A_apply` is one application of the hypothesis to two
   representatives, `_b_apply` and `_c_apply` are `rfl`).
4. Initial namespace placement (`def RKTableau.IsPReducibleVia` from
   inside `namespace OpenMath.Chapter3.Section381`) failed because
   dot notation looks up methods under the type's *fully qualified*
   namespace `OpenMath.Chapter3.Section312.RKTableau`. Restructured
   the file into three namespace blocks: Section381 (definitions and
   `PhiEquivalent`, `PPartition`, `paddedEuler`), Section312.RKTableau
   (the `IsPReducibleVia`/`IsPReducible`/`pReduced` methods + 3 API
   lemmas), and Section381 again (witnesses).
5. Built clean (`lake env lean OpenMath/Chapter3/Section381.lean`,
   `lake build` — 1940 jobs, success).
6. Axiom check: every new declaration depends only on the standard
   `[propext, Classical.choice, Quot.sound]` set (or none, for the
   pure-data `PPartition`).
7. Sorry scanner / tautology scanner: 0 hits across `OpenMath/`.
8. No Aristotle submissions — all proofs were short enough to do by
   hand without burning queue budget on `rfl`s. The strategy
   explicitly authorised skipping Aristotle for trivial proofs.

## Result

**SUCCESS.** `def:381D` is fully formalised. Build is clean, all new
declarations have only standard axioms, sorry scanner is at 0,
tautology scanner is at 0.

## Faithfulness check

### `PPartition` (helper structure for the partition data)

* Textbook (def:381D, statement_text):
  > the stage index set can be partitioned into
  > `{1, 2, …, s} = P_1 ∪ P_2 ∪ ⋯ ∪ P_ŝ`

* Lean: `block : Fin s → Fin sBar` together with
  `surj : Function.Surjective block`.
* **Captures**: same content (equivalent reformulation). A surjection
  `Fin s → Fin sBar` is in bijection with a partition of `Fin s` into
  `sBar` non-empty blocks, where block `I` is the preimage `block⁻¹{I}`.
  Every block is non-empty by surjectivity, matching Butcher's
  implicit assumption that the partition is genuine.
* No mathematical content is smuggled.

### `RKTableau.IsPReducibleVia` (def:381D row-sum-constancy)

* Textbook (def:381D, statement_text):
  > for all `I, J = 1, 2, …, ŝ`, `Σ_{j ∈ P_J} a_{ij}` is constant for
  > all `i ∈ P_I`

* Lean: `∀ I J : Fin sBar, ∀ i i' : Fin s, P.block i = I → P.block i' = I →
  (Σ j ∈ filter (P.block · = J), M.A i j) = (Σ j ∈ filter (P.block · = J), M.A i' j)`.
* **Captures**: same content. "Constant for all `i ∈ P_I`" is exactly
  "any two `i, i' ∈ P_I` give equal sums".
* **Tautology check**: distinct hypothesis (`P.block i = I`) and
  conclusion (sum equality). PASS.
* **Hypothesis strength**: no extra hypotheses beyond what Butcher
  states. PASS.

### `RKTableau.IsPReducible`

* Textbook: a method is P-reducible if such a partition *exists*.
* Lean: `∃ sBar < s, ∃ P : PPartition s sBar, M.IsPReducibleVia P`.
* **Captures**: same content. The side-condition `sBar < s` makes
  "non-trivial" precise (rules out the discrete partition into `s`
  singleton blocks, which is vacuously row-sum-constant for any
  tableau and gives `pReduced M = M`).
* **Hypothesis strength**: the textbook does not explicitly state
  `ŝ < s` but the use case (replacing the method "by another with
  fewer stages", per the §380 motivation paragraph) implies
  non-triviality. Documenting in the docstring; this is a
  *strengthening* of the strict reading of def:381D, but matches the
  textbook's intent. If a future cycle finds the strict reading
  needed, we can rename the strict-reading version `IsPReducibleAny`
  and keep `IsPReducible` for the non-trivial form.

### `RKTableau.pReduced` (the P-reduced method construction)

* Textbook (def:381D, statement_text):
  > `â_{IJ} = Σ_{j ∈ P_J} a_{ij}` for `i ∈ P_I`,
  > `b̂_I = Σ_{i ∈ P_I} b_i` and
  > `ĉ_I = c_i` for `i ∈ P_I`

* Lean (`A` field): `Σ j ∈ filter (P.block · = J), M.A (Classical.choose (P.surj I)) j`.
* Lean (`b` field): `Σ i ∈ filter (P.block · = I), M.b i` — verbatim.
* Lean (`c` field): `M.c (Classical.choose (P.surj I))`.
* **Captures (A field)**: same content under `IsPReducibleVia`. The
  Classical.choose makes the construction unconditional (independent
  of which `i ∈ P_I` is picked); independence-of-choice is proved
  in `pReduced_A_apply`. This is the standard Mathlib pattern for
  "well-defined modulo a choice", cf. `Quotient.lift`.
* **Captures (b field)**: verbatim.
* **Captures (c field)**: WEAKER than Butcher's "`ĉ_I = c_i` for
  `i ∈ P_I`". Butcher's formulation requires `c` to be constant on
  blocks, which `IsPReducibleVia` does not assert; under the
  *consistency condition* `c_i = Σ_j a_{ij}` (separate, not part of
  def:381D) constancy follows. We document this divergence on
  `pReduced` and *do not* silently strengthen `IsPReducibleVia` to
  include `c`-constancy.
* **Definition smuggling check**: `pReduced` is a constructor, not a
  named concept whose textbook definition we are encoding. The
  faithfulness obligation is that the formulae for `Â`, `b̂`, `ĉ`
  match Butcher's; they do (modulo the documented `c` weakening).

### `pReduced_A_apply`, `pReduced_b_apply`, `pReduced_c_apply`

* These are unfolding/well-definedness API. None has a conclusion
  that re-exports a hypothesis verbatim (tautology check PASS).
* `pReduced_A_apply` does real mathematical work (independence of
  choice under the row-sum-constancy hypothesis); `_b_apply` and
  `_c_apply` are structure-projection unfoldings (not vacuous
  re-exports — they unfold the `pReduced` constructor's fields to
  the explicit formulae).
* Identity check: `_b_apply` and `_c_apply` are `rfl`. They unfold
  a `def` projection — this is exactly what an unfolding lemma is
  for, not a vacuous re-export.

### Witness examples

* `paddedEuler.IsPReducibleVia pairPartition`: closes by
  `intro _ _ _ _ _ _; simp [paddedEuler]` because `paddedEuler.A = 0`.
* `paddedEuler.IsPReducible`: `⟨1, by decide, pairPartition, ...⟩`.
* These confirm non-vacuity: a P-reducible method exists in our
  codebase.

## Dead ends

* **First attempt at namespacing.** I initially declared the methods
  as `def RKTableau.IsPReducibleVia ...` from inside
  `namespace OpenMath.Chapter3.Section381`. This created
  `OpenMath.Chapter3.Section381.RKTableau.IsPReducibleVia`, but dot
  notation `M.IsPReducibleVia P` (where `M : RKTableau s`) looks for
  the method under `M`'s type's fully qualified namespace,
  `OpenMath.Chapter3.Section312.RKTableau.IsPReducibleVia`.
  Restructured to a three-block layout (Section381 → Section312.RKTableau
  → Section381), which works. Took one re-build to diagnose.

## Discovery

* **Dot notation pinned to type's home namespace.** When adding methods
  to a structure declared in a different file/namespace, the new
  declarations must be placed in the *structure's* namespace, not the
  current file's namespace. Future cycles adding `RKTableau` API in
  files other than `Section312.lean` should use the explicit
  `namespace OpenMath.Chapter3.Section312.RKTableau` pattern.
* **`Subsingleton.elim` for `Fin 1`.** The surjectivity proof for
  `pairPartition.surj` is `fun _ => ⟨0, Subsingleton.elim _ _⟩`. This
  is shorter and more direct than `fun I => ⟨0, by fin_cases I; rfl⟩`
  (the strategy's suggested form).
* **Stale `.olean` after `lake env lean`.** Running
  `lake env lean OpenMath/Chapter3/Section381.lean` does *not* update
  the `.olean` file; subsequent files importing `Section381` will see
  the previous build's symbols. For axiom checks via a separate file
  importing the module, run `lake build OpenMath.Chapter3.Section381`
  first to refresh the `.olean`.

## Suggested next approach

The strategy's stretch goal — `def:381C` "0-reducible" — is the
natural follow-up. It depends on `def:381D` (just landed) and is
structurally analogous: a partition `{1, …, s} = P_0 ∪ P_1` with
`b_i = 0` for `i ∈ P_0` and `a_{ij} = 0` for `i ∈ P_1, j ∈ P_0`. The
`PPartition` infrastructure can be reused (or specialised to a
two-block partition; `Fin 2` is fine).

After `def:381C`, the next §380 entity is `def:381E` "irreducible"
(layered on top of both 0-reducibility and P-reducibility).
`def:381F` "P-equivalent" combines `def:381B` (Φ-equivalence, cycle 019)
and the new P-reducibility — also a clean one-cycle target.

`def:381A` "equivalent" remains blocked on the §31x analytic bridge
(applying an RK method to a Lipschitz autonomous ODE for one step,
needing `thm:306A` Taylor's theorem — unformalised).

Outside §380, `lem:322A` "Methods of order 4" and
`thm:302C` "Rooted Tree Enumeration Formulas" are good next targets;
the latter would reuse Section301 infrastructure heavily.
