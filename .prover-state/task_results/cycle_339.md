# Cycle 339 Results

## Worked on

`def:422B` Phase B (`Group.zpow` non-vacuity on `Quotient
PhiEquivalent.setoidSigma`) per the planner strategy in
`.prover-state/strategy.md` (cycle 339 entry point per
`.prover-state/issues/def_422B_path.md` §5). Builds on cycle 338's
Phase A.0.2 capstone `D_element_elementaryWeight` and cycle 236's
`instGroup_phi` instance.

## Approach

Per the strategy's §B deliverables list:

1. **Verify Mathlib zpow names** via `lean_loogle`:
   `zpow_zero : a ^ (0 : ℤ) = 1`, `zpow_one : a ^ (1 : ℤ) = a`,
   `zpow_two : a ^ (2 : ℤ) = a * a`, `zpow_neg_one : x ^ (-1 : ℤ) =
   x⁻¹`, `zpow_natCast : a ^ ((n : ℕ) : ℤ) = a ^ n`. All five exist
   at `Mathlib/Algebra/Group/Defs.lean:1014–1069` for any
   `DivInvMonoid G`. Since cycle 236's `instGroup_phi` provides
   `Group (Quotient PhiEquivalent.setoidSigma)`, all five fire on
   the quotient group without further setup.

2. **B.1–B.4: four named theorems + one anonymous example**, each
   a single-line direct application of the corresponding Mathlib
   lemma:

   ```lean
   @[simp] theorem D_element_zpow_zero : D_element ^ (0 : ℤ) = 1 :=
     zpow_zero _
   @[simp] theorem D_element_zpow_one : D_element ^ (1 : ℤ) = D_element :=
     zpow_one _
   theorem D_element_zpow_neg_one :
       D_element ^ (-1 : ℤ) = D_element⁻¹ := zpow_neg_one _
   theorem D_element_zpow_two :
       D_element ^ (2 : ℤ) = D_element * D_element := zpow_two _
   ```

3. **B.5: `paddedEuler` non-vacuity example** confirming the
   `Group.zpow` API works for heterogeneous-stage classes (beyond
   `D_element`'s 1-stage representative):

   ```lean
   example :
       (Quotient.mk PhiEquivalent.setoidSigma
           ⟨2, OpenMath.Chapter3.Section381.paddedEuler⟩ :
             Quotient PhiEquivalent.setoidSigma) ^ (-1 : ℤ)
         = Quotient.mk PhiEquivalent.setoidSigma
             ⟨2, OpenMath.Chapter3.Section381.paddedEuler.inverse⟩ := by
     rw [zpow_neg_one]
     rfl
   ```

   `zpow_neg_one` rewrites the LHS to the group inverse class
   `⟦⟨2, paddedEuler⟩⟧⁻¹`; the residual `rfl` closes via cycle 236's
   `inverseQ_phi_mk : inverseQ_phi ⟦⟨s, M⟩⟧ = ⟦⟨s, M.inverse⟩⟧`
   definitional unfold (the same machinery exercised by the existing
   cycle 236 example at `Section381.lean:5384–5390`).

## Result

**SUCCESS**. Section422.lean compiles cleanly (`lake env lean
OpenMath/Chapter4/Section422.lean` + `lake build
OpenMath.Chapter4.Section422` both green; 220 → ~283 LOC, +~63).

All four new public theorems axiom-clean (`[propext,
Classical.choice, Quot.sound]`) per `#print axioms` from a
standalone test file after a fresh `lake build`.

## Faithfulness check

The cycle 339 ship is Phase B *infrastructure verification* on top
of cycle 236's `instGroup_phi`, **not** the textbook entity
`def:422B` itself (which remains `partial` pending Phases C–E). The
four named theorems verify Mathlib `Group.zpow` API hooks; none
introduces a new mathematical definition.

Faithfulness audit, per-theorem:

* **`D_element_zpow_zero` / `D_element_zpow_one` /
  `D_element_zpow_neg_one` / `D_element_zpow_two`** — none of these
  is a textbook-named entity; each is an instance verification that
  Mathlib's `zpow_{zero,one,neg_one,two}` fires on `D_element` (a
  particular witness in `Quotient PhiEquivalent.setoidSigma`). The
  proof in each case is a single application of the named Mathlib
  lemma `:= zpow_{…} _`, which by the cycle 336/337/338 audit is
  the correct one-liner pattern for trivial integer-power
  reductions in a `Group`. No textbook content is being claimed —
  only that the cycle 236 `Group` instance is structurally usable.

* **Hypothesis strength check**: each theorem has zero hypotheses
  beyond the implicit `Group (Quotient PhiEquivalent.setoidSigma)`
  typeclass (from cycle 236). The textbook (Butcher §387) does not
  state a hypothesis — these are formal API verifications, not
  textbook theorems.

* **Tautology / identity check**: each conclusion is `D_element ^
  (n : ℤ) = <RHS>` where the RHS is *not* a hypothesis (none
  appears as a hypothesis at all). The proof `:= zpow_{…} _` is
  *not* an `exact h` identity — it invokes Mathlib's substantive
  zpow definition unfolding. The four theorems are not vacuous; each
  fires through a different `Group.zpow` reduction path
  (`zpow_zero'` for B.1, `zpow_ofNat + pow_one` for B.2, `zpow_negSucc
  + pow_one` for B.3, `zpow_ofNat + pow_two` for B.4).

* **Definition smuggling check**: no new `def`, `structure`, or
  `class` is introduced. Phase B is theorem-only verification on
  the existing cycle 236 instance.

* **`def:422B` faithfulness status**: the textbook definition
  remains `partial` per the `def_422B_path.md` §5 phase
  decomposition (Phase B is preparation infrastructure, not the
  capstone). The Lean symbol `def:422B` ↦
  `D_element_elementaryWeight` remains the headline placeholder
  pending Phase E sealing.

## Dead ends

None. All five deliverables (B.1, B.2, B.3, B.4, B.5) shipped on
the first attempt as planned in the strategy. The strategy's §E
Mathlib hook verification (which expected possible name drift on
`zpow_neg_one`) confirmed all five canonical names at HEAD with no
drift.

The strategy's §C.2 listed two candidate B.4 closures (`zpow_add` +
arithmetic, or `zpow_natCast` + `pow_succ`); the discovery of
`zpow_two` as a direct Mathlib one-liner (also in
`Mathlib/Algebra/Group/Defs.lean`) made both alternatives moot.
This is a strict improvement on the strategy's recipe — `:= zpow_two
_` is shorter than either alternative and avoids a `by` block
entirely.

## Discovery

1. **`zpow_two` exists as a one-liner Mathlib lemma**. The
   strategy anticipated B.4 might need a `zpow_add` + `simp`
   tactic block or a `zpow_natCast` + `pow_succ` cast. In fact
   `Mathlib/Algebra/Group/Defs.lean:1066` provides
   `lemma zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by rw
   [zpow_ofNat, pow_two]` for any `DivInvMonoid`. This means B.4
   reduces to a single term-mode line `:= zpow_two _`, matching
   B.1–B.3's pattern. For Phase C work that will need `D_element ^
   (n : ℤ)` at larger numeral `n`, the analogous one-liners likely
   don't exist (only `zpow_two` is named explicitly); larger
   numerals will need the strategy's `zpow_natCast + pow_succ`
   recipe.

2. **Standalone test files need a fresh `lake build` to see new
   theorems**. After editing `Section422.lean`, `lake env lean
   <file>` recompiles in-place but does NOT update the `.olean`
   cache. A separate test file `#print axioms <new symbol>` will
   report `unknown constant` until `lake build
   OpenMath.Chapter4.Section422` refreshes the `.olean`. Documented
   here for future cycles' axiom-verification workflows.

3. **`Group.ofLeftAxioms` lift suffices for `Group.zpow`**. Cycle
   236's `instGroup_phi := Group.ofLeftAxioms composeQ_phi_assoc
   composeQ_phi_id_left composeQ_phi_inverseQ_phi_left` provides
   only the *left*-axiom obligations, but Mathlib's `Group` instance
   automatically derives the `zpow` field from `DivInvMonoid` (which
   has the default `Monoid.npow`-via-iteration construction). This
   confirms that future Phase C/D work can safely use any `Group.zpow`
   lemma on the §383 quotient group without further `npow` /
   `zpow` instance plumbing.

## Suggested next approach

Per `.prover-state/issues/def_422B_path.md` §5 and the strategy's
§G outlook, **cycle 340 should ship Phase C** — the (422a) condition
predicate `Eq422a M η_q : Prop` declaring when a quotient class
`η_q : Quotient PhiEquivalent.setoidSigma` satisfies Butcher's
equation (422a) for a given linear multistep method `M`:

```
1(u) − α₁·η⁻¹(u) − α₂·η⁻²(u) − ⋯ − α_k·η⁻ᵏ(u)
     − β₀·D(u) − β₁·η⁻¹·D(u) − ⋯ − β_k·η⁻ᵏ·D(u) = 0
```

(Butcher §422, `extraction/raw_text/ch04.txt` near line discussing
(422a); also `extraction/formalization_data/entities/def_422B.json`
`equations[0]`.)

**Phase C deliverables sketch (~50–100 LOC):**

1. `Eq422a (M : LinearMultistepMethod k) (η_q : Quotient
   PhiEquivalent.setoidSigma) : Prop` declared as the equation
   above with the `Group.zpow` API now verified by this cycle.
   Likely `:=` to a `∀ u : RootedTree, …` expression evaluating
   both sides via `elementaryWeightQ_phi` (cycle 187 + cycle 234).

2. One non-vacuity example, probably the trivial case `M = trivial
   one-step LMM` where `Eq422a M D_element` reduces to a
   tautology (or the explicit Euler / backward Euler instances
   from Section404).

3. Document in `def_422B_path.md` §C that Phase C is now closable
   and remove the dependency on Phase B.

**Recipe**: use `D_element_zpow_neg_one` + `D_element_zpow_zero` for
the `i = 0` term (which becomes `1`), and `zpow_neg` /
`zpow_natCast` for the general `η⁻ⁱ` shape. The `α_i` and `β_i`
coefficients come from `M.α : Fin k → ℝ` / `M.β : Fin (k+1) → ℝ`
in `Section404.LinearMultistepMethod`.

**Do NOT bundle Phase D (inductive η-solver)** into cycle 340 —
multi-cycle work per the scoping doc §5 and the cycle 149/150,
cycle 200/201 rollback precedents (see strategy §D).

**Stretch for cycle 340 if budget permits**: a `Decidable
(Eq422a M η_q)` instance or a `congr`-respect lemma `Eq422a M η_q
↔ Eq422a M η_q'` for `η_q ≈ η_q'` (likely trivially `rfl` since
`η_q` is already a `Quotient`).
