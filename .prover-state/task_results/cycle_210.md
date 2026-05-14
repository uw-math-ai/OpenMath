# Cycle 210 Results

## Worked on

§382 group-theoretic infrastructure track, continuation of cycle 209's
`RKTableau.compose` foundation:

- **P1 (shipped):** `RKTableau.compose_isExplicit_iff` (~30 LOC body) —
  composite is explicit iff both factors are.
- **Prerequisite (shipped):** `RKTableau.IsExplicit` predicate (3 LOC
  body) — the planner's strategy assumed this existed but it was only
  defined for `GeneralizedRungeKuttaMethod` in Section530; required
  introduction as a Lean-internal helper.
- **P3 first witness (shipped):** `paddedEuler_isExplicit` (~2 LOC)
  and `(paddedEuler.compose paddedEuler).IsExplicit` (~3 LOC),
  exercising P1's forward direction on a concrete pair.
- **P2 (deferred):** `RKTableau.compose_assoc` — aborted at the
  strategy's documented 30-LOC threshold; HEq plumbing exceeds budget.
  Issue file written: `.prover-state/issues/compose_assoc_HEq_plumbing.md`.

## Approach

### Pre-flight discovery

1. Grep confirmed `IsExplicit` is **not** defined for `RKTableau`
   anywhere in the codebase; only `GeneralizedRungeKuttaMethod.IsExplicit`
   exists (Section530:296), using the convention
   `∀ i j, i.val ≤ j.val → A i j = 0` (zero on and above the diagonal).
2. Located cycle 209's 8 `compose_A_*` / `compose_b_*` / `compose_c_*`
   simp lemmas (lines 2401-2439) and the `RKTableau` namespace closure
   at line 2452.
3. Verified `paddedEuler.A = 0` (line 156), so `paddedEuler_isExplicit`
   would close trivially.

### P1 proof structure

- Inserted `RKTableau.IsExplicit` definition immediately before the
  `compose` def (in the §382 infrastructure block), matching
  Section530's convention verbatim.
- Forward direction (composite explicit → both factors explicit):
  specialize the composite-IsExplicit hypothesis at `(castAdd s₂ i,
  castAdd s₂ j)` (for `M₁.IsExplicit`) and `(natAdd s₁ i, natAdd s₁ j)`
  (for `M₂.IsExplicit`); the inequality cast through indexing
  preserves direction (`castAdd` preserves `.val`, `natAdd` shifts by
  `+ s₁` on both sides); rewrite via `compose_A_topLeft` /
  `compose_A_botRight` simp lemmas.
- Reverse direction (both factors explicit → composite explicit):
  case-split on `i.val < s₁` and `j.val < s₁` via `lt_or_ge`. Four
  cases:
  - both `< s₁`: top-left block; rewrite `i`, `j` as `castAdd ⟨val,
    hi⟩`, `castAdd ⟨val, hj⟩` via `Fin.ext rfl`; close with `h₁`.
  - `i < s₁ ≤ j`: top-right block; rewrite `j` via `Fin.ext` with
    `j.val = s₁ + (j.val - s₁)` (omega-derived); close via
    `compose_A_topRight = 0`.
  - `s₁ ≤ i, j < s₁`: contradiction; `omega` discharges `hij : i.val ≤
    j.val` against `s₁ ≤ i.val` and `j.val < s₁`.
  - both `≥ s₁`: bottom-right block; rewrite both indices via
    `Fin.ext` + `omega`; close with `h₂` after `omega`-shifting the
    inequality through the index offset.

### P2 attempt and abort

- Confirmed via `lean_run_code` that `(a + b) + c = a + (b + c)` is
  **not** `rfl` in Lean 4 Nat. So compose_assoc requires honest HEq.
- Tried `refine HEq.symm ?_; congr 1; exact Nat.add_assoc s₁ s₂ s₃` —
  `congr 1` peeled the wrong layer, producing absurd subgoals like
  `s₁ = s₁ + s₂`.
- Tried `subst (Nat.add_assoc s₁ s₂ s₃)` — fails: equality is not of
  the form `(x = t)` since both sides are complex expressions.
- `simp [compose]` on both sides reduces to deeply nested
  `Fin.addCases` structures that are **not** syntactically equal: the
  A-fields have 9 different block-combinations of M₁.A / M₁.b / M₂.A /
  M₂.b / M₃.A entries; the b-fields differ as `Fin.append (Fin.append
  M₁.b M₂.b) M₃.b` vs `Fin.append M₁.b (Fin.append M₂.b M₃.b)` —
  Mathlib's `Fin.append_assoc` (Mathlib.Data.Fin.Tuple.Basic:341)
  shows these are equal only up to `∘ Fin.cast (Nat.add_assoc ..)`,
  not literally.
- Per cycle 210 strategy §Risk note: "If at the 30-LOC mark the
  field-by-field closure is not yet visible, STOP and ship P1 +
  Priority 3 stretch only, deferring `compose_assoc` to cycle 211."
  Aborted and wrote `.prover-state/issues/compose_assoc_HEq_plumbing.md`
  with four route options (explicit cast bridge / per-field
  associativity helpers / `Sum.elim` refactor / Equivalent-quotient
  deferral via thm:382A's direct closure).

### P3 paddedEuler witnesses

- `paddedEuler_isExplicit`: `intro _ _ _; simp [paddedEuler]` —
  `paddedEuler.A = 0`, so every entry is `0 = 0`.
- Compose witness: `(RKTableau.compose_isExplicit_iff ..).mpr
  ⟨paddedEuler_isExplicit, paddedEuler_isExplicit⟩` — pure term-mode
  application of P1's reverse direction.
- P3 second witness (compose_assoc on triple paddedEuler) skipped
  since P2 was deferred.

## Result

**SUCCESS** — partial-cycle delivery per strategy contingency plan:
- P1 shipped, axiom-clean ([propext, Classical.choice, Quot.sound]).
- `RKTableau.IsExplicit` definition shipped (Lean-internal helper).
- P3 first witness shipped, axiom-clean.
- P2 deferred with comprehensive issue file documenting four
  resolution paths.
- File compiles clean (`lake env lean OpenMath/Chapter3/Section381.lean`
  exits 0).
- Sorry count remains 0.
- Cycle 209 deliverables (`compose_A_topLeft`,
  `PReducesTo.toEquivalent_and_toPhiEquivalent`) still axiom-clean —
  no regression.

## Faithfulness check

For each new `def`/`theorem` introduced this cycle:

### `RKTableau.IsExplicit` (def, ~3 LOC)

- **Entity ID:** None — Butcher does not define a named "explicit RK"
  predicate. The textbook uses the explicit/implicit distinction
  informally throughout §38 (e.g., p. 88 "explicit methods" used as a
  description). The closest formal counterpart is Section530's
  `GeneralizedRungeKuttaMethod.IsExplicit` (cycle 151), already in
  the codebase.
- **Lean statement captures:** Lean-internal helper, parallel to
  Section530's predicate. Convention: `i.val ≤ j.val → A i j = 0`
  (zero on and above the diagonal — equivalently, `A` is strictly
  lower-triangular). Matches Butcher's informal usage exactly.
- **No textbook divergence** — Lean-internal infrastructure.

### `RKTableau.compose_isExplicit_iff` (thm, ~30 LOC body)

- **Entity ID:** None — internal §382 infrastructure lemma supporting
  the future `thm:382A` formalization. The closest textbook reference
  is Butcher ch03.txt:8671-8742 (the (382a) tableau composition),
  already cited in cycle 209's `compose` docstring.
- **Lean statement captures:** `(M₁.compose M₂).IsExplicit ↔
  M₁.IsExplicit ∧ M₂.IsExplicit`. This is a structural property of
  the block-decomposed composite tableau; the textbook does not
  state it explicitly but it is a standard observation
  (e.g., the canonical RK4 = RK1 ∘ RK1 ∘ RK1 ∘ RK1 lineage retains
  explicitness through composition).
- **No textbook divergence** — internal infrastructure.

### `paddedEuler_isExplicit` (thm, ~2 LOC body)

- **Entity ID:** None — non-vacuity witness for the new `IsExplicit`
  predicate.
- **Lean statement captures:** `paddedEuler.IsExplicit`. Direct
  consequence of `paddedEuler.A = 0`.
- **No textbook divergence.**

### Anonymous `example : (paddedEuler.compose paddedEuler).IsExplicit`

- Non-vacuity witness exercising P1's `.mpr` direction on a concrete
  pair of methods.
- Not a named theorem; no faithfulness check applies.

### Tautology / identity / smuggling / hypothesis-strength audit

- `IsExplicit` definition: structural (single `∀`-quantified
  implication). No tautology risk.
- `compose_isExplicit_iff`: conclusion `(comp).IsExplicit ↔ M₁ ∧ M₂`
  is genuinely two-directional; not a tautology.
- `paddedEuler_isExplicit`: not identity — uses `simp [paddedEuler]`
  to reduce `paddedEuler.A i j` to `0`.
- No hypotheses stronger than necessary; no `Prop` fields added to any
  `structure`.

## Dead ends

- **`refine HEq.symm ?_; congr 1; exact Nat.add_assoc s₁ s₂ s₃`** —
  `congr 1` produced four absurd subgoals (`s₁ = s₁ + s₂`, `s₂ + s₃ =
  s₃`, mixed-arity HEqs). The congr lemma `congr` invokes for `compose`
  applied to two arguments unwinds the wrong layer.
- **`subst hs` after `have hs : (s₁+s₂)+s₃ = s₁+(s₂+s₃)`** — fails
  because `subst` requires one side to be a variable.
- **`simp only [compose]; rfl`** — both sides reduce but to
  syntactically distinct deeply-nested Fin.addCases nestings; not
  rfl-closable.

## Discovery

1. **`IsExplicit` is type-specific.** Section530's `IsExplicit` lives
   on `GeneralizedRungeKuttaMethod`, NOT on `RKTableau`. The planner's
   cycle 210 strategy assumed it existed for `RKTableau` ("if absent
   in §381, check Section530 — cycle 151 was Section530's IsExplicit").
   Section530's predicate is on a different type, so cycle 210
   defined a parallel `RKTableau.IsExplicit` matching Section530's
   convention. Future planners should check the type, not just the
   name, when assuming predicate existence.

2. **`Fin.castAdd` and `Fin.natAdd` value arithmetic is rfl.** The
   pattern `i = Fin.castAdd s₂ ⟨i.val, hi⟩` and `i = Fin.natAdd s₁
   ⟨i.val - s₁, by omega⟩` close via `Fin.ext rfl` (for castAdd) and
   `Fin.ext (by ... omega)` (for natAdd, since the val arithmetic
   `s₁ + (i.val - s₁) = i.val` requires `s₁ ≤ i.val`).

3. **`Nat.add` is NOT associative by `rfl` in Lean 4.** Confirmed via
   `lean_run_code` with `import Mathlib`. Cycle 210 strategy
   anticipated this in §"What NOT to do" #5, but it bears repeating:
   `compose_assoc` cannot bypass the HEq/cast plumbing.

4. **`Fin.append_assoc` in Mathlib uses `∘ Fin.cast`.** The relevant
   lemma is at `Mathlib.Data.Fin.Tuple.Basic:341`:
   `append (append a b) c = append a (append b c) ∘ Fin.cast
   (Nat.add_assoc ..)`. Any HEq-level associativity for composite RK
   methods must carry this `Fin.cast` through the b- and c-fields.

5. **HEq decomposition through structure constructor.** For a
   structure with three fields indexed by `Fin s` where `s` differs
   between sides, `congr` does NOT peel cleanly at depth 1 — the
   first layer it tries (compose at two arguments) produces
   nonsensical subgoals like `M₁ ≍ M₁.compose M₂`. Future HEq-on-
   structure proofs should bypass `congr` and use explicit
   `RKTableau.mk.injEq` or HEq.rec-based plumbing.

## Suggested next approach

For **cycle 211** the planner should choose one of:

**Option A (preferred):** Read `extraction/formalization_data/entities/
thm_382A.json` (group of RK methods) to determine whether Butcher's
group law is stated on the *quotient* `RKTableau / Equivalent` or on
raw `RKTableau`. If quotient, `compose_assoc` may never need direct
HEq — it falls out of `Equivalent.trans` (cycle 206) on representatives.
Plan `thm:382A` directly using the quotient encoding.

**Option B:** If `thm:382A` does require literal `compose_assoc`,
plan a multi-cycle decomposition:
- Cycle 211: build the cast bridge: prove
  `RKTableau.mk_heq_iff_of_size_eq : s = s' → (HEq {A, b, c} {A', b',
  c'} ↔ HEq A A' ∧ HEq b b' ∧ HEq c c')` as a reusable HEq-structure
  helper.
- Cycle 212: ship the b-field associativity bridge `compose_compose_b
  = compose_compose_b ∘ Fin.cast` via Mathlib's `Fin.append_assoc`.
- Cycle 213: ship the c-field associativity bridge.
- Cycle 214: ship the A-field associativity bridge (9-block analysis).
- Cycle 215: combine via the structure HEq helper.

**Option C (last resort):** Refactor `compose` to use `Sum.elim` via
`finSumFinEquiv`, leveraging Mathlib's `Equiv.sumAssoc` for free
associativity. Invalidates cycle 209's 8 simp lemmas; high refactoring
cost. Not recommended unless Options A and B both fail.

**DO NOT** plan compose_assoc as a single-cycle deliverable again
without first executing Option A's investigation step. Cycle 210's
failure confirms it does not fit in a 30-LOC body, and the strategy's
soft-cap is the right boundary.

§441 Phase C.2 remains GPFS-blocked (29th consecutive cycle skip);
loop-maintainer territory.
