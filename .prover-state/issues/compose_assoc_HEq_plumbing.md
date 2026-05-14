# Issue: `RKTableau.compose_assoc` HEq plumbing exceeds 30 LOC budget

## Blocker

Cycle 210 attempted to ship `RKTableau.compose_assoc`:

```lean
theorem compose_assoc {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    HEq ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃))
```

per cycle 210 strategy Priority 2. After confirming compile setup
and exploring the goal state via `lean_multi_attempt`, the proof
structure is genuinely too large to fit in the strategy's
30-LOC body budget (which the strategy explicitly flagged as an
abort threshold). Per cycle 210 strategy §Risk note, P2 was aborted
and the cycle shipped P1 + P3 only.

## Context

The two `RKTableau` values live in different types:
- LHS: `RKTableau ((s₁ + s₂) + s₃)`
- RHS: `RKTableau (s₁ + (s₂ + s₃))`

`Nat.add_assoc` is **not** `rfl` in Lean 4 (confirmed via
`lean_run_code` with `import Mathlib`; the test `example (a b c : Nat)
: a + b + c = a + (b + c) := rfl` fails type-check). `subst` cannot
fire because neither side is a free variable.

`simp [compose]` reduces both sides to explicit `Fin.addCases` nestings
that are NOT syntactically equal:

LHS A-field:
```
fun i j ↦
  Fin.addCases (i₁ ↦
    Fin.addCases (j₁ ↦
      Fin.addCases (i₁ ↦ Fin.addCases (j₁ ↦ M₁.A i₁ j₁) 0 j₁)
                   (i₂ ↦ Fin.addCases (j₁ ↦ M₁.b j₁) (j₂ ↦ M₂.A i₂ j₂) j₁) i₁)
      0 j)
    (i₂ ↦ Fin.addCases (j₁ ↦ Fin.append M₁.b M₂.b j₁) (j₂ ↦ M₃.A i₂ j₂) j) i
```

RHS A-field:
```
fun i j ↦
  Fin.addCases (i₁ ↦ Fin.addCases (j₁ ↦ M₁.A i₁ j₁) 0 j)
    (i₂ ↦ Fin.addCases (j₁ ↦ M₁.b j₁)
      (j₂ ↦ Fin.addCases (i₁ ↦ Fin.addCases (j₁ ↦ M₂.A i₁ j₁) 0 j₂)
                         (i₂ ↦ Fin.addCases (j₁ ↦ M₂.b j₁) (j₂ ↦ M₃.A i₂ j₂) j₂) i₂)
      j) i
```

The b-field is `Fin.append (Fin.append M₁.b M₂.b) M₃.b` vs `Fin.append
M₁.b (Fin.append M₂.b M₃.b)`. Mathlib's `Fin.append_assoc`
(`Mathlib.Data.Fin.Tuple.Basic:341`) states:

```
theorem append_assoc (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) :
    append (append a b) c = append a (append b c) ∘ Fin.cast (Nat.add_assoc ..)
```

so even Fin.append is associative only up to `Fin.cast` composition,
not literal equality. The HEq closure must therefore handle this cast.

## What was tried

1. `refine HEq.symm ?_; congr 1; exact Nat.add_assoc s₁ s₂ s₃` —
   `congr 1` produced four cases: `s₁ = s₁ + s₂`, `s₂ + s₃ = s₃`,
   `M₁ ≍ M₁.compose M₂`, `M₂.compose M₃ ≍ M₃`. Wrong shape: `congr 1`
   peels the wrong layer.

2. `have hs : s₁ + s₂ + s₃ = s₁ + (s₂ + s₃) := Nat.add_assoc ..; subst
   hs` — `subst` fails: equality is not of the form `(x = t)` or `(t =
   x)`.

3. `simp only [compose]; rfl` — both sides reduce but are NOT
   syntactically equal (see above).

## Possible solutions

### Option A: Explicit cast bridge

Prove the equality by promoting LHS through `cast` to RHS's type, then
showing the casts are equal field-by-field. Roughly:

```lean
  have hs : (s₁ + s₂) + s₃ = s₁ + (s₂ + s₃) := Nat.add_assoc s₁ s₂ s₃
  have htype : RKTableau ((s₁ + s₂) + s₃) = RKTableau (s₁ + (s₂ + s₃)) := hs ▸ rfl
  rw [heq_iff_cast]
  -- now plain Eq goal in RKTableau (s₁ + (s₂ + s₃))
  ext  -- via Matrix.ext / funext
  ...
```

Each field equality then needs explicit 9-block analysis with the
appropriate `Fin.cast` chasing. Likely 50-80 LOC.

### Option B: Per-field associativity helper lemmas

Skip the HEq packaging; just ship:

```lean
theorem compose_compose_A_eq (i₁ : Fin s₁) (j₁ : Fin s₁) (...) :
    ((M₁.compose M₂).compose M₃).A (Fin.castAdd s₃ (Fin.castAdd s₂ i₁)) ... =
      (M₁.compose (M₂.compose M₃)).A (Fin.castAdd (s₂+s₃) i₁) ... := ...
```

— and analogous per-block lemmas for the other 8 block configurations.
9 lemmas × 3 fields = 27 lemmas. Heavy but decomposable. Each is a
simp lemma; downstream `thm:382A` consumers can build the HEq once
all 27 fire by simp.

### Option C: Reformulate `compose` via `Sum.elim` / `Equiv.sumAssoc`

Instead of `Fin.addCases`, define `compose` via the equivalence
`Fin (s₁ + s₂) ≃ Fin s₁ ⊕ Fin s₂` (`finSumFinEquiv`) and let Mathlib's
sum-associativity (`Equiv.sumAssoc`) carry the assoc proof. Major
refactor; should NOT be undertaken without planner approval since it
invalidates cycle 209's 8 simp lemmas.

### Option D: Defer to `thm:382A` direct closure

The strategic motivation for `compose_assoc` is `thm:382A` (group of RK
methods). If `thm:382A` can be stated in a quotient form (RK methods
mod `Equivalent`), associativity might fall out of the equivalence
relation's transitivity (`Equivalent.trans` — cycle 206) without
needing literal HEq. This is the textbook's likely encoding: Butcher
groups methods up to equivalence, not on the nose.

## Recommendation

**Option D + Option B as fallback.** Investigate whether `thm:382A`
admits an Equivalent-quotient formulation before committing to the HEq
plumbing. If the quotient route works, `compose_assoc` may never need
to be proved on the nose.

If `thm:382A`'s direct closure does require literal compose
associativity, Option B (per-field block-decomposed simp lemmas) is
the most modular path — each is ≤ 5 LOC and can be Aristotle-batched
to share cost across stages.

## Suggested next-cycle planner action

Read `extraction/formalization_data/entities/thm_382A.json` for the
textbook statement of "group of RK methods". If Butcher works with an
equivalence quotient, plan `thm:382A` directly without compose_assoc.
If Butcher works with raw RKTableau, plan a cycle to investigate
Option B vs Option C.

---

## Cycle 219 update — finessable via `Quotient.sound`

With cycle 218's `composeQ : Quotient Equivalent.setoidSigma →
Quotient Equivalent.setoidSigma → Quotient Equivalent.setoidSigma`
and cycle 219's identity element (`RKTableau.id` + four absorption
lemmas on `composeQ`), the on-the-nose `compose_assoc` HEq blocker
documented above is **finessable** through `Quotient.sound`:

- The on-the-nose statement `M₁.compose (M₂.compose M₃) =
  (M₁.compose M₂).compose M₃` requires HEq plumbing because the
  stage-count types `RKTableau (s₁ + (s₂ + s₃))` and
  `RKTableau ((s₁ + s₂) + s₃)` are NOT definitionally equal in
  Lean 4 (they require `Nat.add_assoc`).

- However, the **quotient-level** statement
  `composeQ (composeQ p q) r = composeQ p (composeQ q r)` for
  `p q r : Quotient Equivalent.setoidSigma` does NOT require any
  HEq plumbing: the stage-count Σ-projection lives *inside* the
  representative, not in the output type. So associativity reduces
  to an `Equivalent`-level claim
  `@Equivalent (s₁ + (s₂ + s₃)) ((s₁ + s₂) + s₃)
    (M₁.compose (M₂.compose M₃)) ((M₁.compose M₂).compose M₃)`,
  which can be proved by abstract-`N`-level reasoning over
  `IsRKOneStep` (the same technique cycle 217 used for
  heterogeneous-stage `compose_equivalent_compose`).

- The `Quotient`-level `composeQ_assoc` theorem then becomes a
  `Quotient.inductionOn₃` + `Quotient.sound` corollary of the
  `Equivalent`-level associativity claim — identical in shape to
  cycle 219's `composeQ_id_left`/`composeQ_id_right`.

This is the cycle 221+ entry point. Cycle 220's deliverable is the
**inverse element** (Butcher §382's inverse construction); cycle 221+
ships the `Equivalent`-level associativity + the `composeQ_assoc`
corollary; cycle 222+ packages the four (`Group`) axioms as
`instance : Group (Quotient Equivalent.setoidSigma)`.

The on-the-nose `compose_assoc` blocker documented above remains
unresolved at the `RKTableau`-level, but it is no longer load-bearing
for the §382 group structure — the quotient route bypasses it.

---

## Cycle 221 update — Equivalent-level associativity SHIPPED

The cycle 219 outlook is now realized. Cycle 221 closes both:

1. `RKTableau.compose_equivalent_compose_assoc.{u}` at the
   `Equivalent` level — heterogeneous-stage
   `@Equivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
     ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃))`
   (~35 LOC body + docstring at
   `OpenMath/Chapter3/Section381.lean` line ~3060).

2. `RKTableau.composeQ_assoc` at the quotient level — for
   `p q r : Quotient Equivalent.setoidSigma.{u}`,
   `composeQ (composeQ p q) r = composeQ p (composeQ q r)` (~10
   LOC body + docstring, immediately after deliverable 1).

Proof recipe (the abstract-`IsRKOneStep`-level technique from
cycles 217 / 219 / 220 generalized to three factors):

- Threshold = `min (min H₁ H₂) H₃` where each `Hᵢ` comes from
  `Mᵢ.equivalent_self f L hL`. The three `H ≤ Hᵢ` facts factor
  cleanly via two `min_le_*` chains.
- Apply `compose_isRKOneStep_iff` twice to each side, factoring
  the three-factor composite into three sequential single-`Mᵢ`-
  step witnesses. **LHS** unfolds as outer
  `(M₁.compose M₂) · M₃` then inner `M₁ · M₂`; **RHS** unfolds
  as outer `M₁ · (M₂.compose M₃)` then inner `M₂ · M₃`. The two
  unfoldings introduce different intermediate values:
  `y_LHS_mid23` and `y_LHS_mid12` on the LHS, `y_RHS_mid1` and
  `y_RHS_mid12` on the RHS.
- Three uniqueness chains, one per `Mᵢ`:
  - `M₁` from `y₀` forces `y_LHS_mid12 = y_RHS_mid1` (the M₁
    step appears in both decompositions).
  - `M₂` from common `mid1 = y_RHS_mid1` forces
    `y_LHS_mid23 = y_RHS_mid12` (after rewriting the LHS M₂
    step to fire from the corrected base).
  - `M₃` from common `mid12 = y_RHS_mid12` closes
    `y_final = y_final'`.

Both new symbols verified axiom-clean
(`[propext, Classical.choice, Quot.sound]`); regression checks
on `composeQ_eq_of_equivalent`, `composeQ_id_left`,
`composeQ_id_right`, `composeQ_inverse_right`,
`composeQ_inverse_left` all unchanged. Section381.lean warm
rebuild 7.6s.

The on-the-nose `compose_assoc` blocker documented above remains
unresolved at the `RKTableau`-level and is now **permanently
superseded** by the quotient route: §382 group associativity is
fully discharged via `Quotient.sound` on
`compose_equivalent_compose_assoc`. With cycles 219/220/221's
identity / inverse / associativity all closed at the quotient
level, the §382 group axioms are complete. Cycle 222+ entry
point: lift `RKTableau.inverse` to `Quotient` (needs
`inverse_equivalent_inverse`: `M ≡ M' → M.inverse ≡ M'.inverse`,
~50 LOC via step-inversion + uniqueness chain) for the `inv`
operation, then assemble the `Group` instance on
`Quotient Equivalent.setoidSigma`.
