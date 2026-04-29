# Cycle 032 Strategy — Formalize `def:357A` (BN-stability)

## Rationale (read this first)

The cycle 031 task results suggested **`thm:323B`** as the top
candidate for cycle 032. **Reject that suggestion.** Its
transitive dependencies (per
`extraction/formalization_data/entities/thm_323B.json`) include
`thm:315A`, `lem:311A`, `lem:312B`, `lem:313A`, `thm:311B`,
`thm:311C`, `thm:311D`, `thm:313B`, `thm:306A` — **none of which
are formalized**. We cannot even state "method has order `p`" in
our codebase yet, because the master order-conditions theorem
(`thm:315A`) and the §31x Taylor-expansion machinery underneath it
do not exist. Building that infrastructure is a multi-cycle
investment; trying to formalize `thm:323B` in one cycle will
either fail or degenerate into definition-smuggling.

The cycle 031 worker's **alternative #2 — `def:357A` (BN-stability) —
is the right cycle 032 target.** It is:

* genuinely unblocked (needs only cycle 030's `IsRKOneStep` shape
  plus inner-product norm machinery);
* a clean predicate-and-witness deliverable, like cycle 028's
  `def:357B` or cycle 030's `def:381A`;
* downstream-unblocking — once `def:357A` is formalised, `thm:357C`
  (algebraic stability ⇒ BN-stability) and `thm:357D` (BN-stability
  ⇒ AN-stability) become statable;
* one-cycle-sized (the implicit-midpoint witness uses a clean
  algebraic identity over a real inner-product space).

## Mandatory pre-flight reading

1. `extraction/formalization_data/entities/def_357A.json` — the
   entity record. Note that the extracted `statement_text` field is
   **truncated/garbled**; do not rely on it alone.
2. `extraction/raw_text/ch03.txt:6806-6815` — the full textbook
   definition. Quote it verbatim into the file docstring. The
   definition reads:

   > **Definition 357A.** A Runge–Kutta `(A, b, c)` is *'BN-stable'*
   > if for any initial value problem
   > `y'(x) = f(x, y(x)), y(x₀) = y₀`,
   > satisfying the condition
   > `⟨f(x, u), u⟩ ≤ 0`,
   > the sequence of computed solutions satisfies
   > `‖yₙ‖ ≤ ‖yₙ₋₁‖`.

   This is the non-autonomous, single-solution form of B-stability
   (the textbook explicitly notes the simplification at lines
   6790–6797: equation (357c) `⟨f(x, u), u⟩ ≤ 0` replaces the
   "formally more complicated" two-solution condition (357a)).
3. `OpenMath/Chapter3/Section381.lean:368-373` — the existing
   autonomous `IsRKOneStep` predicate. Read its docstring; the
   non-autonomous predicate must follow the same Prop-form
   convention to handle implicit-method ambiguity honestly.
4. `OpenMath/Chapter3/Section370.lean:65-77` — the
   `implicitMidpoint` tableau (1-stage, `A = [[1/2]]`, `b = [1]`,
   `c = [1/2]`). This is the witness.
5. `OpenMath/Chapter3/Section357.lean` — cycle 028's existing file
   for `def:357B`. Decide whether to **add** the new content to this
   file (preferred — keeps §357 in one place) or create a parallel
   `Section357A.lean`. Recommend adding to `Section357.lean`.

## Deliverable

Add to `OpenMath/Chapter3/Section357.lean`:

### 1. Non-autonomous one-step predicate

A non-autonomous parallel to `Section381.IsRKOneStep`. It must live
either in `Section381.lean` next to `IsRKOneStep` (preferred — it is
infrastructure, not BN-stability-specific) **or** as a private helper
in `Section357.lean`. Sketch:

```lean
namespace OpenMath.Chapter3.Section312.RKTableau

/-- Non-autonomous one-step relation. Captures the implicit stage
system `Yᵢ = y₀ + h • Σⱼ aᵢⱼ • f(x₀ + cⱼ h, Yⱼ)` and the update
`y₁ = y₀ + h • Σᵢ bᵢ • f(x₀ + cᵢ h, Yᵢ)`. As with `IsRKOneStep`,
this is a `Prop`: any `(Y, y₁)` tuple satisfying both equations
witnesses the relation. -/
def IsRKOneStepNonAut {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : ℝ → N → N) (x₀ : ℝ) (y₀ : N) (h : ℝ) (y₁ : N) : Prop :=
  ∃ Y : Fin s → N,
    (∀ i, Y i = y₀ + h • ∑ j, M.A i j • f (x₀ + M.c j * h) (Y j)) ∧
    y₁ = y₀ + h • ∑ i, M.b i • f (x₀ + M.c i * h) (Y i)

end OpenMath.Chapter3.Section312.RKTableau
```

Add this alongside `IsRKOneStep` in `Section381.lean` (place it
right after, in the same namespace block). The autonomous
`IsRKOneStep` should **not** be replaced; it remains correct for
`def:381A`.

### 2. `IsBNStable` predicate

```lean
/-- Butcher §357 Definition 357A — a Runge–Kutta method is *BN-stable*
iff for every real inner-product space `N`, every (in `x`)
right-hand side `f : ℝ → N → N` satisfying the dissipativity
condition `∀ x u, ⟨f x u, u⟩ ≤ 0`, every step size `h > 0`, every
starting time `x₀`, and every pair `(y₀, y₁)` related by one
non-autonomous step of `M`, the norm does not grow:
`‖y₁‖ ≤ ‖y₀‖`. -/
def IsBNStable {s : ℕ} (M : RKTableau s) : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (f : ℝ → N → N)
    (_hDiss : ∀ x u, inner ℝ (f x u) u ≤ 0)
    (x₀ : ℝ) (y₀ : N) (h : ℝ) (_hh : 0 < h) (y₁ : N),
    M.IsRKOneStepNonAut f x₀ y₀ h y₁ → ‖y₁‖ ≤ ‖y₀‖
```

Faithfulness notes for the docstring:

* `[InnerProductSpace ℝ N]` matches Butcher's "inner product" / "norm
  derived from inner product" wording (the textbook reverts to
  `⟨·, ·⟩` for "a standard semi-inner product with `‖·‖` the
  corresponding norm" at line 6797). Do **not** weaken to
  `NormedSpace ℝ N` — the proof needs the inner product.
* The dissipativity condition `⟨f x u, u⟩ ≤ 0` is Butcher's (357c)
  verbatim. Do not replace with the more general two-solution form
  (357a); the textbook explicitly justifies the simplification at
  lines 6790–6797.
* The continuity-in-`x` requirement is implicit in Butcher's "for
  any IVP" phrasing. We do **not** state it as a hypothesis: our
  predicate is purely about the algebraic relation between
  `(y₀, y₁)` via the stage equations, not about whether such an IVP
  has a solution. Adding a continuity hypothesis would be a
  *strengthening*, not a faithfulness improvement.
* Predicate-form, not function-form: just like `IsAlgebraicallyStable`
  in cycle 028, this is a `Prop`-valued definition with no
  computational content.

### 3. Implicit midpoint witness

```lean
theorem implicitMidpoint_isBNStable :
    IsBNStable implicitMidpoint := by
  -- See proof sketch below.
  sorry
```

**Proof sketch (this works — verified by hand):**

The implicit midpoint method has `s = 1`, `A 0 0 = 1/2`, `b 0 = 1`,
`c 0 = 1/2`. Given the predicate hypothesis, get `Y : Fin 1 → N`
with:

* `Y 0 = y₀ + h • (1/2) • f(x₀ + h/2, Y 0)`,
* `y₁ = y₀ + h • f(x₀ + h/2, Y 0)`.

Let `K := f(x₀ + h/2, Y 0)`. From the stage equation,
`y₀ = Y 0 - (h/2) • K`. From the update, `y₁ = y₀ + h • K`.

Compute `‖y₁‖²`:

```
‖y₁‖² = ‖y₀ + h • K‖²
      = ‖y₀‖² + 2h ⟨K, y₀⟩ + h² ‖K‖²       -- norm-add square in inner-product
      = ‖y₀‖² + 2h ⟨K, Y 0 - (h/2)K⟩ + h² ‖K‖²   -- substitute y₀
      = ‖y₀‖² + 2h ⟨K, Y 0⟩ - h² ‖K‖² + h² ‖K‖²
      = ‖y₀‖² + 2h ⟨K, Y 0⟩
      ≤ ‖y₀‖²                                 -- by dissipativity at (x₀+h/2, Y 0)
```

Then `‖y₁‖ ≤ ‖y₀‖` by `Real.sqrt_le_sqrt` plus
`Real.sqrt_sq_eq_abs` plus `abs_of_nonneg (norm_nonneg _)`.

**Mathlib lemmas to look up first** (use `lean_local_search` /
`lean_loogle` to confirm exact names — names below are best-guess
from Mathlib v4.28.0):

* `inner_add_left` / `inner_add_right` — bilinearity of the inner
  product.
* `inner_smul_left` / `inner_smul_right` — `⟨c•x, y⟩ = c * ⟨x, y⟩`
  over `ℝ`.
* `real_inner_self_eq_norm_sq` — `⟨x, x⟩ = ‖x‖²` over `ℝ`.
* `norm_add_sq_real` — `‖x + y‖² = ‖x‖² + 2⟨x, y⟩ + ‖y‖²` over `ℝ`.
  (cycle 010's `Section112.lean` uses the inner-product chain rule
  in the same shape; check there for the exact spelling.)
* `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `abs_of_nonneg`,
  `norm_nonneg` for the final square-root step.

If `norm_add_sq_real` is not the exact name, the standard expansion
is `‖x + y‖² = ⟨x + y, x + y⟩` then bilinearity. Don't get stuck on
naming — use `lean_multi_attempt` with several spellings.

## Workflow

1. **Read the four pre-flight files above** before writing any
   Lean. Quote the textbook definition (lines 6806–6813 of
   `ch03.txt`) into the file docstring.
2. **Write the structure with `sorry`** at every step — both the
   `IsRKOneStepNonAut` predicate (in `Section381.lean`), the
   `IsBNStable` predicate (in `Section357.lean`), and the
   `implicitMidpoint_isBNStable` witness with `sorry`. Verify the
   skeleton compiles via
   `lake env lean OpenMath/Chapter3/Section381.lean` and
   `lake env lean OpenMath/Chapter3/Section357.lean`.
3. **Aristotle batch (mandatory)**. Once the skeleton compiles,
   submit ~5 jobs to Aristotle covering:
   * The full `implicitMidpoint_isBNStable` proof (give it the
     proof sketch above as a comment).
   * The sub-step `‖y₁‖² = ‖y₀‖² + 2h ⟨K, Y 0⟩` as an isolated
     algebraic lemma (parametrise over `K, Y0, y0 : N`,
     `h : ℝ`, with hypotheses `Y0 = y0 + (h/2) • K` and
     `y1 = y0 + h • K`, conclusion the inner-product identity).
   * The sub-step `‖y₁‖² ≤ ‖y₀‖²` given the identity above plus
     `⟨K, Y 0⟩ ≤ 0`.
   * (optional) The square-root step
     `‖y₁‖² ≤ ‖y₀‖² → ‖y₁‖ ≤ ‖y₀‖`.
   * (optional) A combined `inner_add_left` / `inner_smul_right`
     simplification chain that Aristotle is good at.

   Sleep 30 minutes. Don't poll.
4. **Manual proof for whatever Aristotle missed.** Use
   `lean_multi_attempt` with several spellings of the
   `norm_add_sq_real` lemma if Aristotle stalls on the
   inner-product expansion. Don't get stuck on lemma naming —
   loogle by type pattern.
5. **Pre-commit faithfulness check** — run the checklist below.
6. **Update `extraction/formalization_data/lean_status.json`**:
   set `def:357A` to `formalized`, with
   `lean_file = "OpenMath/Chapter3/Section357.lean"` and
   `lean_symbol = "OpenMath.Chapter3.Section357.IsBNStable"`.
7. **Update `plan.md`**: change `[ ] def:357A` to
   `[x] def:357A` and bump the `Progress: 32 / 175` counter to
   `33 / 175`.
8. **Write `cycle_032.md`** with the standard format.
9. **Commit and push** on `Main/Experiments`.

## Pre-commit faithfulness checklist

Specifically for this cycle:

### `IsRKOneStepNonAut` (infrastructure, not a Butcher entity)
- [ ] Tautology check: stage equations are not vacuous
      (`Y i = y₀ + …` is a real recursion, not `Y i = Y i`).
- [ ] Identity check: encoding mirrors `IsRKOneStep` with `f`
      replaced by `(x₀ + cᵢh)`-applied form.
- [ ] Hypothesis-strength: `[NormedAddCommGroup N] [NormedSpace ℝ N]`
      matches the autonomous predicate. Don't add
      `InnerProductSpace` here — `IsRKOneStepNonAut` is general
      infrastructure; the inner-product structure belongs only on
      `IsBNStable`.

### `IsBNStable` (`def:357A`)
- [ ] Quote `extraction/raw_text/ch03.txt:6806-6813` in the
      docstring.
- [ ] Definition smuggling check: we are NOT defining
      BN-stability as the matrix condition (357d) — that is
      `def:357B` (`IsAlgebraicallyStable`). The Lean predicate IS
      the textbook semantic condition (norm-non-increase under
      dissipative `f`).
- [ ] Hypothesis-strength check: dissipativity is Butcher's (357c),
      not (357a). Document this as the textbook's chosen
      simplification. Don't add IVP-existence or smoothness
      hypotheses.
- [ ] Inner-product space, not arbitrary normed space.

### `implicitMidpoint_isBNStable` (non-vacuity witness)
- [ ] Tautology check: conclusion `‖y₁‖ ≤ ‖y₀‖` is not a
      hypothesis.
- [ ] Identity check: proof actually computes `‖y₁‖²` to
      `‖y₀‖² + 2h⟨K, Y 0⟩` and uses dissipativity. NOT just
      `exact some_lemma` from a renamed hypothesis.
- [ ] Hypothesis-strength: just the predicate hypothesis; no
      auxiliary smoothness on `f` beyond Butcher's (357c).

## What NOT to do (explicit don't-repeat list)

* **Do NOT pursue `thm:323B`.** Its prerequisite chain is
  unformalized (see Rationale). Cycle 031 suggested it but did not
  audit the dependency graph. We are auditing it now and rejecting
  it.
* **Do NOT pursue `thm:324A`, `thm:324B`, `thm:324C`** for the
  same reason — all depend on `thm:315A` ("Conditions for order"),
  which is unformalized.
* **Do NOT pursue `thm:381G`.** Its proof cites `thm:314A`
  (Independence of the elementary differentials), which is
  unformalized.
* **Do NOT pursue `def:381F` (P-equivalent).** Blocked on
  `reduced_method_deferred.md` — that issue requires a multi-cycle
  resolution of two open interpretation questions about Butcher's
  "reduced method" construction.
* **Do NOT pursue the AN-stability component of `def:356A`.**
  Blocked on `AN_stability_deferred.md` — needs complex
  matrix-resolvent infrastructure `(I − A Z)⁻¹` not in our codebase.
* **Do NOT pursue `equivalent_self M` for arbitrary `M`.** Blocked
  on `equivalent_self_general_deferred.md` — needs the Banach
  contraction infrastructure for the implicit stage system.
* **Do NOT pursue §142 Jordan/Schur work.** Per the cycle 015
  consultant note (§E "the Schur path is on the back-burner until
  §142 is back on the critical path"); §142 is not on any current
  critical path.
* **Do NOT introduce `axiom` or `constant` declarations.** If a
  proof seems to require one, write a blocker issue file in
  `.prover-state/issues/` instead of merging the axiom.
* **Do NOT raise `maxHeartbeats` above 200000.** Decompose the
  proof.
* **Do NOT use `h_<name>` / `:= h_<name>` / `exact h_<name>` as
  closer of any sub-proof.** The tautology scanner false-positive
  bug (see
  `.prover-state/issues/tautology_scanner_false_positives.md`) is
  unfixed. Use `hX` / `hinner` / `hcombine` (no underscore) to
  avoid tripping the regex. The cycle 015 / cycle 014 cosmetic
  rename precedent applies.
* **Do NOT modify `scripts/autonomous_loop.py`.** Per cycle 015's
  guidance — the scanner / prompt-builder bugs are the loop
  maintainer's responsibility.
* **Do NOT use `[NormedSpace ℝ N]` instead of `[InnerProductSpace
  ℝ N]` on `IsBNStable`.** Butcher's definition is intrinsically
  inner-product. Weakening to a general normed space would change
  the meaning.
* **Do NOT formalise `def:357A` as the matrix condition (357d).**
  That would be definition smuggling — (357d) is `def:357B` and is
  *sufficient* for BN-stability (this is `thm:357C`), not the
  primary definition.
* **Do NOT replace the autonomous `IsRKOneStep` from
  `Section381.lean`.** Add `IsRKOneStepNonAut` alongside it. The
  autonomous version is correct for `def:381A` and downstream
  consumers.

## Aristotle batch (concrete jobs)

When the skeleton compiles, submit these to Aristotle in one batch:

1. **Whole proof of `implicitMidpoint_isBNStable`** — give the
   sketch above verbatim as a comment, ask Aristotle to fill in.
2. **Algebraic identity lemma** (helper, not a Butcher entity):
   ```lean
   lemma midpoint_norm_sq_identity {N : Type*}
       [NormedAddCommGroup N] [InnerProductSpace ℝ N]
       (h : ℝ) (y₀ Y0 K : N) (y₁ : N)
       (hY0 : Y0 = y₀ + (h / 2) • K) (hy1 : y₁ = y₀ + h • K) :
       ‖y₁‖^2 = ‖y₀‖^2 + 2 * h * inner ℝ K Y0 := by sorry
   ```
3. **Norm bound from inner-product nonpositivity**:
   ```lean
   lemma norm_le_of_norm_sq_le {N : Type*} [NormedAddCommGroup N]
       (a b : N) (h : ‖a‖^2 ≤ ‖b‖^2) : ‖a‖ ≤ ‖b‖ := by sorry
   ```
4. **Dissipativity application**: a stub that takes
   `inner ℝ K Y0 ≤ 0` and the identity from (2), concludes
   `‖y₁‖^2 ≤ ‖y₀‖^2`.
5. (Optional) The `Fin 1` simplification of the implicit-midpoint
   stage equations to extract `Y 0`, `y₁ = y₀ + h • f(...) (Y 0)`.

If Aristotle solves any of (2)-(4), incorporate them directly. (1)
is the integration test — if Aristotle solves the whole thing,
great; if not, glue (2)+(3)+(4) yourself.

## Success criteria

* `lake env lean OpenMath/Chapter3/Section357.lean` succeeds.
* `lake env lean OpenMath/Chapter3/Section381.lean` succeeds (if
  `IsRKOneStepNonAut` lands there).
* `lake build` succeeds (the cycle 031 worker confirmed all 2845
  jobs — should still be ~2845 ± a handful).
* `#print axioms OpenMath.Chapter3.Section357.IsBNStable` and
  `#print axioms OpenMath.Chapter3.Section357.implicitMidpoint_isBNStable`
  return only `[propext, Classical.choice, Quot.sound]`.
* No `sorry` anywhere in the touched files.
* `extraction/formalization_data/lean_status.json` updated.
* `plan.md` updated (32/175 → 33/175).
* `cycle_032.md` written.

## If blocked

If `def:357A` turns out to require infrastructure beyond the four
Mathlib lemma families above (norm-add square, inner-product
bilinearity, real-inner self-norm, square-root monotonicity), STOP
and write a blocker issue file in `.prover-state/issues/` with
the structured format from `CLAUDE.md`. Do **not** introduce an
axiom, do **not** weaken the definition, and do **not** silently
defer the witness.

If the witness proof works but a downstream chain (`thm:357C`,
`thm:357D`) seems to need the two-solution form (357a) instead of
the simpler (357c), that is **expected**: Butcher's §357C/D are
out of scope for this cycle. Capture that observation in
`cycle_032.md`'s "Discovery" section for future cycles to
consume; don't try to upgrade `def:357A` mid-cycle.
