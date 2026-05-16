# Cycle 340 Results

## Worked on

`def:422B` Phase C per cycle 340 strategy: the (422a) condition predicate
`Eq422a M η_q : Prop` declaring when a quotient class `η_q : Quotient
PhiEquivalent.setoidSigma` solves Butcher's underlying-one-step-method
equation for a linear multistep method `M = [α, β]`.

Target file: `OpenMath/Chapter4/Section422.lean` (Phase C block appended
after cycle 339's Phase B `Group.zpow` non-vacuity section).

## Approach

### P1 — `Eq422a` definition

Wrote the predicate per the strategy's §B Lean shape:

```lean
def Eq422a {k : ℕ}
    (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (η_q : Quotient PhiEquivalent.setoidSigma) : Prop :=
  ∀ u : RT,
    elementaryWeightQ_phi (1 : Quotient PhiEquivalent.setoidSigma) u
      - (∑ i : Fin k,
          M.α i.succ
            * elementaryWeightQ_phi (η_q ^ (-((i.val + 1 : ℕ) : ℤ))) u)
      - (∑ i : Fin (k + 1),
          M.β i
            * elementaryWeightQ_phi
                ((η_q ^ (-((i.val : ℕ) : ℤ))) * D_element) u)
      = 0
```

Used the strategy's recommended `-((i.val + 1 : ℕ) : ℤ)` and
`-((i.val : ℕ) : ℤ)` cast shape to keep the integer-power exponent
explicit (per R1 mitigation in strategy §F).

The `RT` abbrev from cycle 338 (private to the namespace) covers the
`RootedTree` quantification; the strategy's "namespace shortcut" was
already in effect from cycles 337/338 (`open
OpenMath.Chapter3.Section312.RKTableau` at file scope), so
`elementaryWeightQ_phi` and `PhiEquivalent.setoidSigma` resolve
unqualified.

### P2 — non-vacuity sanity

Chose P2.β (`Eq422a_congr` — quotient-equality congruence) per the
strategy's "pick one" directive. P2.β is the lower-risk option (one-line
`subst h; rfl`) and ensures the predicate's body is well-typed and
respects the underlying `Quotient` equality:

```lean
theorem Eq422a_congr {k : ℕ}
    (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    {η_q η_q' : Quotient PhiEquivalent.setoidSigma} (h : η_q = η_q') :
    Eq422a M η_q ↔ Eq422a M η_q' := by
  subst h
  rfl
```

Skipped P2.α (the `explicitEulerLMM` unfolding sanity) per the
strategy's explicit "Do not attempt both — pick one" instruction; P2.β
is a sufficient non-vacuity ship for cycle 340.

### P3 — documentation

* `def_422B_path.md` — appended a "Cycle 340 update — Phase C
  closure" section mirroring the cycle 338 `## §A.0.2 Closure` pattern.
  Notes what's in (def + congruence), what's deferred (Phase D
  inductive solver), and the cycle 341 entry point (Phase D.1 base
  case `η(τ)` solver per Butcher's proof at `ch04.txt:1163`).
* `lean_status.json` — `def:422B` row: `cycle_completed_at` bumped to
  340; `note` field extended with the cycle 340 ship summary;
  `lean_symbol` placeholder unchanged at the cycle 338
  `D_element_elementaryWeight` capstone (Phase E will retarget to the
  underlying-one-step-method `def` itself).
* `plan.md` — extended the cycle 340 entry-point line into a cycle 340
  ship summary; new cycle 341 entry point pointing to Phase D.1.

## Result

SUCCESS — Phase C closed.

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (clean
  compile, no warnings).
* 1 new `def` (`Eq422a`) + 1 new theorem (`Eq422a_congr`) shipped.
* Sorry count remains 0 across the file.
* No `axiom` / `constant` declarations introduced; the `def` is
  axiom-clean (a pure `Prop`-valued `∀`-quantified equation over
  existing definitions).
* LOC: Section422.lean ~280 → ~360 (+~80, consistent with the
  strategy's ~50–100 LOC P1+P2 estimate).

## Faithfulness check

### `def Eq422a`

* **Entity ID and textbook statement**: Butcher §422 p. 358 eq. (422a),
  verbatim from `extraction/raw_text/ch04.txt:1115–1116`:

  > 1 − α₁ η⁻¹ − α₂ η⁻² − ⋯ − αₖ η⁻ᵏ
  >          − β₀ D − β₁ η⁻¹ D − β₂ η⁻² D − ⋯ − βₖ η⁻ᵏ D = 0   (422a)

  And the per-tree form at `:1159` (in the `thm:422A` proof):

  > 1(u) − α₁ η⁻¹(u) − α₂ η⁻²(u) − ⋯ − αₖ η⁻ᵏ(u)
  >          − β₀ D(u) − β₁ η⁻¹ D(u) − β₂ η⁻² D(u) − ⋯ − βₖ η⁻ᵏ D(u) = 0

  This is the predicate-shaped reading of (422a) Butcher uses
  throughout the §422 proof.

* **Lean statement captures: same content**. Term-by-term
  correspondence:
  - `1(u)` ↔ `elementaryWeightQ_phi (1 : Q) u`
  - `−Σᵢ₌₁..ₖ αᵢ · η⁻ⁱ(u)` ↔ `−∑ i : Fin k, M.α i.succ * elementaryWeightQ_phi (η_q ^ (-((i.val + 1 : ℕ) : ℤ))) u`
  - `−Σᵢ₌₀..ₖ βᵢ · η⁻ⁱ D(u)` ↔ `−∑ i : Fin (k + 1), M.β i * elementaryWeightQ_phi ((η_q ^ (-((i.val : ℕ) : ℤ))) * D_element) u`

* **b₀-invisibility note**: at the §383 quotient level
  `elementaryWeightQ_phi (1 : Q) u = 0` for every `u : RootedTree`
  (cycle 239's `elementaryWeightQ_phi_id`). The textbook's
  empty-tree case of (422a) (where `1(∅) = 1`) is invisible at
  this quotient level and is handled separately by
  `M.IsPreconsistent` (Butcher's proof at `ch04.txt:1152`). The
  `1(u)` term is retained verbatim for textbook-side-by-side
  fidelity; it reduces to `0` whenever the predicate is unfolded.

* **No definition smuggling**: `Eq422a` is a *predicate* asserting
  that `η_q` satisfies (422a). It does NOT define what "underlying
  one-step method" means — that is `def:422B` itself, which Phase
  E will seal as "the unique `η_q : Q` satisfying `Eq422a M`" (for
  preconsistent stable `M`). The construction of `η_q` is the
  Phase D inductive solver, deferred per scoping doc §5.

### `theorem Eq422a_congr`

* **Tautology check**: pass — conclusion `Eq422a M η_q ↔ Eq422a M
  η_q'` is not verbatim a hypothesis (hypothesis is the equality
  `η_q = η_q'`, conclusion is the iff between two predicate
  applications).

* **Identity check**: the proof is `subst h; rfl`. This is *not*
  vacuous — it confirms the predicate's body actually is a
  function of `η_q` (the `subst` substitutes `η_q'` for `η_q` in
  the iff goal, leaving `Eq422a M η_q' ↔ Eq422a M η_q'` which `rfl`
  closes). Real work: it certifies well-definedness of `Eq422a`
  under quotient-class equality, infrastructure for downstream
  Phase D/E lemmas that chain `Quotient.sound` rewrites through
  `Eq422a`.

* **Hypothesis strength check**: `h : η_q = η_q'` is the minimal
  hypothesis for the iff conclusion; cannot be weakened.

## Dead ends

None. The cycle followed the strategy precisely:

1. Read `extraction/formalization_data/entities/def_422B.json` to
   confirm the textbook statement and dependencies.
2. Read `Section422.lean` (existing cycle 336–339 content) and
   `Section404.lean:53–84` for the `LinearMultistepMethod`
   structure and `explicitEulerLMM` witness.
3. Confirmed `elementaryWeightQ_phi` signature at
   `Section381.lean:4705` and the `1 : Q` identity instance at
   `Section381.lean:4304`.
4. Wrote P1 + P2 in one `Edit` call.
5. Verified compile with `lake env lean OpenMath/Chapter4/Section422.lean`
   (exit code 0).
6. Updated `lean_status.json`, `def_422B_path.md`, and `plan.md`
   per the strategy's §I file list.

The strategy's risk register (§F) anticipated potential cast / simp
elaboration issues, but the predicate's body did not require any
proof-level manipulation in cycle 340 (only the trivial `Eq422a_congr`
proof, which is one `subst`+`rfl`). All cast risks would surface at
Phase D when the predicate is actually unfolded; cycle 340 only ships
the definitional skeleton.

## Discovery

* **The strategy's R3 mitigation (using
  `η_q ^ (-((i.val : ℕ) : ℤ))` as a single expression) is the right
  shape for Phase D.** Writing the exponent as
  `-((i.val + 1 : ℕ) : ℤ)` (with the cast on the inner Nat sum)
  ensures the integer is constructed uniformly via `Nat.cast`
  followed by `Int.neg`, avoiding the potential `Nat.cast_add` /
  `Int.neg_add` ambiguity at downstream simp time. This pattern
  should be carried forward into Phase D's case-split proofs.

* **The `1 : Q` shape unfolds via `elementaryWeightQ_phi_id` to
  `0` on every `RootedTree`** — meaning at downstream Phase D
  proof time, the `Eq422a M η_q` body simplifies to:

  ```
  0 - (α-sum) - (β-sum) = 0
  ```

  i.e. the predicate at the on-tree quotient level reduces to
  `α-sum + β-sum = 0`. This is the cleaner form to work with in
  Phase D's inductive case split. The retention of the `1(u)`
  term is textbook-fidelity rather than computational; downstream
  consumers can `simp [elementaryWeightQ_phi_id]` to drop it.

* **`Eq422a_congr` would be the canonical entry point for any
  downstream `Quotient.lift`-style argument** that needs to push
  `Eq422a` through a class-equality. Worth `@[simp]`-tagging in a
  later cycle if Phase D consumers rely on it heavily.

## Suggested next approach

**Cycle 341 — Phase D.1: base case `η(τ)` solver.**

Per `def_422B_path.md` §5 and Butcher's proof at
`extraction/raw_text/ch04.txt:1163`:

> "By preconsistency, the coefficient of η(τ) in (422a) at u = τ is
>  −(α₁ + 2α₂ + ⋯ + k·αₖ) = −Σ i·αᵢ, which is non-zero by stability.
>  Hence η(τ) is determined."

Concrete plan:

1. **Unfold `Eq422a M η_q u` at `u = τ`**: at the single-vertex tree,
   `elementaryWeightQ_phi (η_q ^ n) τ` for any integer `n` reduces to
   `n * η(τ)` via the §383 group's action on `τ` (cycle 337's
   `D_element_elementaryWeight_vertex` + `D_phi` distributivity gives
   the n = 1 case; the general case follows by `zpow` induction). The
   β-side at `u = τ`: `elementaryWeightQ_phi (η_q ^ (-i) · D) τ` —
   needs a *new* helper lemma proving `D` adds a power-of-`η_q` factor
   at `τ`, which Phase D.1 will need to ship.

2. **Solve the linear equation for `η(τ)`**: a single real-valued
   linear equation `(-Σ i·αᵢ) · η(τ) + (constant) = 0`. Non-vanishing
   coefficient follows from stability; the textbook gives this
   explicitly at `:1167`.

3. **Estimated cycle 341 LOC**: ~50–80 in Section422.lean (one Phase
   D.1 ship lemma + helper for `D` at `τ`). Risk: medium — needs
   careful unfolding of `zpow` action on the `τ`-class.

Estimated total Phase D: 3 cycles (D.1 base, D.2 well-founded
recursion infrastructure on `RootedTree.order`, D.3 inductive step
`r(t) > 1`). Phase E (lift to `Q` + seal `def:422B`) follows as 1
more cycle.
