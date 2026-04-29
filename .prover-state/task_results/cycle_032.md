# Cycle 032 Results

## Worked on

- `def:357A` (BN-stability) in `OpenMath/Chapter3/Section357.lean`.
- New non-autonomous one-step relation `IsRKOneStepNonAut` added to
  `OpenMath/Chapter3/Section381.lean` (alongside the existing
  autonomous `IsRKOneStep`).
- Witness `implicitMidpoint_isBNStable` for non-vacuity.
- Two private helper lemmas (`midpoint_norm_sq_identity`,
  `norm_le_of_norm_sq_le`) that factor out the algebraic identity and
  the square-root step, respectively.

## Approach

Followed the strategy verbatim:

1. Read `extraction/formalization_data/entities/def_357A.json`,
   `extraction/raw_text/ch03.txt:6790-6815`,
   `OpenMath/Chapter3/Section381.lean:368-373` (autonomous
   `IsRKOneStep`), and
   `OpenMath/Chapter3/Section370.lean:65-77` (`implicitMidpoint`
   tableau).
2. Added `IsRKOneStepNonAut` next to `IsRKOneStep` in
   `Section381.lean`'s `RKTableau` namespace block (so dot-notation
   `M.IsRKOneStepNonAut f x₀ y₀ h y₁` works). Same `Prop`-form
   convention as the autonomous predicate.
3. Added `IsBNStable` to `Section357.lean` as a single quantified
   `Prop`: for every real inner-product space `N`, every dissipative
   `f : ℝ → N → N`, every `h > 0`, and every `(y₀, y₁)` related by one
   non-autonomous step of `M`, `‖y₁‖ ≤ ‖y₀‖`. No matrix condition is
   smuggled in; this is the textbook semantic definition.
4. For the witness, factored the hand-derived computation into a
   reusable identity lemma:
   ```
   midpoint_norm_sq_identity h y₀ Y0 K y₁ hY0 hy1 :
     ‖y₁‖² = ‖y₀‖² + 2 * h * ⟨K, Y0⟩
   ```
   under hypotheses `Y0 = y₀ + (h/2)•K` and `y₁ = y₀ + h•K`. Proved
   by `inner_add_left/right`, `real_inner_smul_left/right`,
   `real_inner_self_eq_norm_sq`, and `ring`.
5. The square-root step uses `le_of_sq_le_sq` from
   `Mathlib.Algebra.Order.Ring.Abs` (found via `lean_loogle` —
   `abs_le_abs_of_sq_le_sq` does not exist in current Mathlib).
6. The implicit-midpoint witness proof unpacks
   `IsRKOneStepNonAut`, applies `simp [implicitMidpoint]` to the
   stage and update equations to canonical form, defines `K` as
   `f (x₀ + 2⁻¹ * h) (Y 0)` (matching the form `simp` produces),
   then invokes the algebraic identity, dissipativity, and the
   square-root packaging.

## Result

SUCCESS.

* `lake env lean OpenMath/Chapter3/Section381.lean` — clean.
* `lake env lean OpenMath/Chapter3/Section357.lean` — clean.
* `lake build` — 2845 / 2845 jobs OK (same as cycle 031 baseline).
* `#print axioms OpenMath.Chapter3.Section357.IsBNStable` →
  `[propext, Classical.choice, Quot.sound]`.
* `#print axioms OpenMath.Chapter3.Section357.implicitMidpoint_isBNStable` →
  `[propext, Classical.choice, Quot.sound]`.
* No `sorry` in the touched files.
* `extraction/formalization_data/lean_status.json` updated:
  `def:357A → formalized` with the symbol path.
* `plan.md` updated: 32 / 175 → 33 / 175, `def:357A` row marked `[x]`.

Aristotle batch was not used: the proof closed manually on the first
type-checked attempt after fixing two naming issues (`real_inner_comm`
orientation and `le_of_sq_le_sq` instead of the non-existent
`abs_le_abs_of_sq_le_sq`). Submitting an already-proved file would
have been wasted compute.

## Faithfulness check

### `IsRKOneStepNonAut` (infrastructure helper, not a Butcher entity)

* Tautology check: stage equations
  `Y i = y₀ + h • Σⱼ aᵢⱼ • f(x₀ + cⱼh, Yⱼ)` are not vacuous; they
  define a recursion on `Y`.
* Identity check: encoding mirrors autonomous `IsRKOneStep` with
  `f` replaced by the time-shifted `f (x₀ + cⱼh)`-applied form.
* Hypothesis-strength: `[NormedAddCommGroup N] [NormedSpace ℝ N]`
  matches the autonomous predicate. No `InnerProductSpace` here —
  this is general infrastructure; the inner-product structure
  belongs only on `IsBNStable`.

### `IsBNStable` (`def:357A`)

* Entity ID and textbook statement (quoted from
  `extraction/raw_text/ch03.txt:6806-6813`):
  > **Definition 357A.** A Runge–Kutta `(A, b, c)` is *'BN-stable'*
  > if for any initial value problem
  > `y'(x) = f(x, y(x)), y(x₀) = y₀`,
  > satisfying the condition
  > `⟨f(x, u), u⟩ ≤ 0`,
  > the sequence of computed solutions satisfies
  > `‖yₙ‖ ≤ ‖yₙ₋₁‖`.
* Lean statement captures: **same content**.
* Definition smuggling check: we are NOT defining BN-stability as the
  matrix condition (357d) — that is `def:357B`
  (`IsAlgebraicallyStable`). The Lean predicate IS the textbook
  semantic condition (norm-non-increase under dissipative `f`).
* Hypothesis-strength check: dissipativity is Butcher's (357c),
  not the more complicated two-solution form (357a) — explicitly
  justified by the textbook's own simplification at lines 6790–6797.
  No IVP-existence or smoothness hypotheses added. `0 < h` matches
  the textbook's "step size" convention.
* Inner-product space, not arbitrary normed space — Butcher's
  definition is intrinsically inner-product (line 6797 reverts
  notation to `⟨·, ·⟩` for "a standard semi-inner product with
  `‖·‖` the corresponding norm").

### `implicitMidpoint_isBNStable` (non-vacuity witness)

* Tautology check: conclusion `‖y₁‖ ≤ ‖y₀‖` is not a hypothesis.
* Identity check: proof actually computes `‖y₁‖²` to
  `‖y₀‖² + 2h⟨K, Y 0⟩` (via `midpoint_norm_sq_identity`) and uses
  dissipativity. Not a renamed `exact` of any hypothesis.
* Hypothesis-strength: just the predicate hypothesis; no auxiliary
  smoothness on `f` beyond Butcher's (357c).

### `midpoint_norm_sq_identity` (private helper)

* Pure algebraic identity in a real inner-product space, parametrised
  over `K`, `Y0`, `y₀`, `y₁` and `h`. Proves the textbook line
  `‖y₁‖² = ‖y₀‖² + 2h⟨K, Y0⟩` from the substitution
  `y₀ = Y0 - (h/2)•K`. No hidden dependence on the implicit-midpoint
  tableau — reusable for any 1-stage scheme of this shape.

### `norm_le_of_norm_sq_le` (private helper)

* Direct application of `le_of_sq_le_sq` plus `norm_nonneg`. Pure
  packaging.

## Dead ends

* `inner_smul_left` / `inner_smul_right` (without `real_`) produced
  goals containing `(starRingEnd ℝ) h`, which `ring` could not close
  because the conjugate is an opaque term. Switched to
  `real_inner_smul_left` / `real_inner_smul_right`, which produce
  the clean `r * inner x y` form.
* `abs_le_abs_of_sq_le_sq` does not exist in Mathlib. The right name
  is `le_of_sq_le_sq` (in `Mathlib.Algebra.Order.Ring.Abs`), with
  signature `a ^ 2 ≤ b ^ 2 → 0 ≤ b → a ≤ b`.
* `real_inner_comm` orientation is `inner ℝ x y = inner ℝ y x`
  (i.e. swaps from left to right when read as a rewrite). The
  strategy's intuitive form had it the other way; flipped the
  arguments to get the correct rewrite direction.
* `simp [implicitMidpoint, Fin.sum_univ_one]` produced a hypothesis
  containing `f (x₀ + 2⁻¹ * h)` but the strategy's hand-written
  form had `f (x₀ + h / 2)`. Defining `K` with the
  `simp`-canonical form (`2⁻¹ * h`) avoided needing
  `ring_nf` on the time argument and let `set` fold the K-definition
  cleanly into both the stage and update equations.
* Initial proof attempt mis-ordered `set K := …` before the `simp`
  on `hs` and `hy₁`, which prevented `set` from folding `K` into the
  hypotheses. Reordering — `simp` first, then `set` — fixed the
  fold.

## Discovery

* The same algebraic identity `‖y₁‖² = ‖y₀‖² + 2h⟨K, Y₀⟩` (with
  `y₀ = Y₀ - (h/2)•K, y₁ = y₀ + h•K`) is the kernel of every 1-stage
  symmetric / midpoint-style stability proof. Promoting
  `midpoint_norm_sq_identity` to a public, named lemma in a future
  cycle would let `thm:357C` (algebraic stability ⇒ BN-stability)
  re-use it for the multi-stage case (specialised to single-stage
  diagonal slices, or generalised to a sum).
* The strategy's note at the bottom about `thm:357C / thm:357D`
  needing the two-solution (357a) form is correct: BN-stability of
  the *test problem* uses (357c), but the implication
  algebraic-stable ⇒ BN-stable in general (Burrage–Butcher) requires
  computing the squared-norm difference of two RK trajectories,
  which is intrinsically (357a)-shaped. A future
  `IsBNStable_two_solution` form may be needed there.
* `IsRKOneStepNonAut` is now general infrastructure usable by all
  non-linear stability theorems. The autonomous `IsRKOneStep` for
  `def:381A` is left untouched.
* `lake build` rebuilds the staleness check before per-file
  compilation; running `lake env lean Section381.lean` did NOT
  regenerate Section381's `.olean`, so a downstream
  `lake env lean Section357.lean` initially saw the old
  (sans-`IsRKOneStepNonAut`) interface. Resolved by an explicit
  `lake build OpenMath.Chapter3.Section381` before re-checking
  Section357. Worth remembering for future cycles that add to
  pre-existing infrastructure files.

## Suggested next approach

The cycle 031 task results suggested `thm:323B` (cycle 032 then
rejected it for unformalised dependencies — see strategy Rationale).
The honest list of one-cycle-sized, genuinely-unblocked candidates
that emerge from cycle 032's work:

* **`thm:357C`** (algebraic stability ⇒ BN-stability — Burrage–Butcher).
  *Caveat*: requires the two-solution form (357a) of dissipativity,
  not (357c). A faithful formalisation would either (a) add a
  parallel `IsBNStable_pair` predicate and prove the implication
  there, or (b) generalise the existing `IsBNStable` from
  single-trajectory to two-trajectory and re-prove the implicit-
  midpoint witness. (a) is cleaner; (b) is more invasive but matches
  Butcher's eventual presentation. This is the natural §357
  follow-up.

* **`thm:357D`** (BN-stability ⇒ AN-stability) — depends on a
  faithful encoding of `def:356A`'s AN-stability, which the
  `AN_stability_deferred.md` issue notes is blocked on the matrix
  resolvent `(I − AZ)⁻¹` machinery. Don't pursue until that issue is
  resolved.

* **`thm:381G`/`thm:381H`** — still blocked by `thm:314A`
  (independence of elementary differentials), as the cycle 031
  worker noted. Skip.

* **Smaller helpers**: now that `IsRKOneStepNonAut` exists, a
  few one-step lemmas about it (existence under Lipschitz `f` at
  small `h`; uniqueness; equivalence to `IsRKOneStep` for
  autonomous `f` independent of its first argument) would be
  cheap unblocks for downstream stability work. Probably one
  cycle each.

* **Promotion of `midpoint_norm_sq_identity` to a public, named,
  multi-stage helper** — useful for `thm:357C` future cycle.

Recommended cycle 033 target: **`thm:357C` via the (a) route
(parallel `IsBNStable_pair`)**. It is genuinely unblocked, fits the
"add a Prop + a witness" mould of cycles 028/030/032, and unblocks
the §357 chain. The scoping pre-flight for that cycle should
explicitly settle the (357a) vs (357c) form question on the parallel
predicate before any Lean is written.
