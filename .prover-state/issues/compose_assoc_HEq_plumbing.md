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
