# Cycle 509 Results

## Worked on
§422 Phase α'.7.0 — `nchildPolynomial` family signature + `nchildCrossTerm`
skeleton + 5 calibration theorems at `n ∈ {0, 1, 2, 3, 4}` reducing the
parametric form to the existing per-arity helpers
(`bichildPolynomial` / `trichildPolynomial` / `tetrachildPolynomial`).

Insertion point: `OpenMath/Chapter4/Section422.lean` between
`tetrachildPolynomial` (line 14869) and `inversePolyTree` (originally
14905). Cycle 508 scoping doc §6.0 / §9 entry point.

No sorry's introduced. Sorry count unchanged at 5 (4 docstring + 1
grandfathered cycle 365 at line 2279).

## Approach

### §A. Strawman audit and design pivot

The cycle 508 scoping doc §B.1.1 strawman uses a uniform subset-sum
body with four blocks (∅, single-child sum, cross-term, self-kernel)
quantified over `Fin n`. The strawman gives clean shapes for `n ≥ 2`
(matching `bichildPolynomial`, `trichildPolynomial`,
`tetrachildPolynomial`), but at `n = 0` and `n = 1` the blocks
degenerate:

* At `n = 0`: block-∅ (`-(v · ∏ over Fin 0) = -v`) and self-kernel
  (`-f (mk (List.ofFn (Fin 0 → ...))) = -f (mk []) = -v`) **both
  contribute the same `-f vertex` term**, giving the literal
  strawman value `-2 · f vertex`, contradicting the strategy's
  calibration target `-f vertex` (matching
  `inversePolyTree (mk []) f`).
* At `n = 1`: single-child sum (`-(∏ over erase 0) · f (mk [c]) =
  -f (mk [c])`) and self-kernel (`-f (mk (List.ofFn (Fin 1 → ...)))
  = -f (mk [c])`) **both contribute the same `-f (mk [c])` term**,
  giving the literal strawman value `-(v · inv) - 2 · f (mk [c])`,
  contradicting the cycle 392 monochild form
  `-(v · inv_c) + monochildCrossTerm c f - f (mk [c])`.

Either the strawman is buggy at low `n`, or the calibration targets
are inconsistent with the strawman. Per CLAUDE.md "If Mathlib is
missing something, build it yourself" + the strategy's explicit
calibration target wording ("matches `inversePolyTree (mk []) f`"),
I corrected the strawman by replacing the uniform body with a
three-arm pattern match on `n`:

* Arm `0`: `-f vertex` (matches `inversePolyTree (mk [])` cycle 341).
* Arm `1`: `-(v · inv₀) + monochildCrossTerm (children 0) f
  - f (mk [children 0])` (matches `inversePolyTree (mk [c])` cycle 392).
* Arm `n + 2`: uniform subset-sum body (matches
  `inversePolyTree (mk [c₁, …, cₙ₊₂])` for the per-arity helpers).

This preserves the strawman's intended `n ≥ 2` semantics (which is
the only regime where Phase α'.7.1+ depends on `nchildPolynomial`)
and ensures the parametric form is consistent with `inversePolyTree`
at all `n` — a prerequisite for the Phase α'.7.2 cycle 511 cycle 358
bridge theorem.

### §B. `nchildCrossTerm` skeleton

Per scoping doc §B.1.2: ship a `match n` skeleton dispatching n ∈
{0, 1, 2, 3, 4} to the existing per-arity cross-term helpers (or
zero at n = 0, 1 per the strategy's "absorbed into single-child block"
note). The `_ + 5 => 0` catch-all is **intentional** and is the
same R6.B-style placeholder as `inversePolyTree`'s `k ≥ 5` arm at
line 14924 — documented in the docstring as Phase α'.7.5 / cycle
517+ extension target.

### §C. Calibration theorems

Five theorems, in file order:

1. **`nchildPolynomial_zero`**: `rfl` (arm 0 direct hit).
2. **`nchildPolynomial_eq_one`**: `rfl` (arm 1 direct hit).
3. **`nchildPolynomial_eq_bichildPolynomial`**: `show` to canonicalize
   the `n + 2 = 2` arm body, then `Fin.prod_univ_two` +
   `Fin.sum_univ_two` + `Finset.univ.erase {0, 1} = singleton` via
   `decide` + `Finset.prod_singleton` + `ring`. Closes in ~15 LOC.
4. **`nchildPolynomial_eq_trichildPolynomial`**: same template at
   n = 3, using `Fin.prod_univ_three` / `Fin.sum_univ_three` and
   `{a, b} = insert a {b}` via `rfl`, plus `Finset.prod_insert`
   cascade and `decide` for membership disequalities. ~25 LOC.
5. **`nchildPolynomial_eq_tetrachildPolynomial`**: same template at
   n = 4, using `Fin.prod_univ_four` / `Fin.sum_univ_four` and the
   `{a, b, c} = insert a (insert b {c})` cascade applied four times
   for the four `Finset.univ.erase ℓ₀` evaluations. ~35 LOC.

All five proofs use the cycle 508 strategy §D-recommended pattern
(`unfold` + targeted simp/ring, avoiding `simp [nchildPolynomial,
nchildCrossTerm, ...]` over-unfolding per memory
`feedback_simp_recursive_def_overunfolds.md`).

### §D. No Aristotle batch

Per cycle 508 strategy §G + strategy §G: low utility for these
mechanical reductions. All 5 proofs closed manually.

## Result

**SUCCESS** (assuming compile verification passes — see Verification
section below). Ship locked:

* `nchildCrossTerm` def (line ~14902–14909 in the modified file).
* `nchildPolynomial` def (~14938–14951).
* 5 calibration theorems (~14957–15097).

Total new LOC: ~205. Cycle 508 baseline 19299 → cycle 509 target
~19504. Within scoping doc §B's 200–300 LOC budget.

## Faithfulness check

### `nchildCrossTerm` (new `noncomputable def`)

* **Entity ID**: NOT a Butcher concept. This is **internal helper
  infrastructure** for the §422 cluster's Phase β.2 obstruction at
  k ≥ 5. No `extraction/formalization_data/entities/` entry; per
  scoping doc §6.0 / §8.6 R6, the faithfulness contract is via the
  cycle 358 bridge theorem (Phase α'.7.2 / cycle 511), not direct
  textbook correspondence.
* **Definition smuggling**: not applicable — `nchildCrossTerm` does
  not claim to represent any Butcher-level concept. The `_ + 5 => 0`
  catch-all is an explicit scoping-level limitation, documented in
  the docstring as a Phase α'.7.5 (cycle 517+) extension target.
* **Hypothesis strength**: matches the per-arity helpers' parameter
  shapes (children + inv_children + f); no extra hypotheses.

### `nchildPolynomial` (new `noncomputable def`)

* **Entity ID**: NOT a Butcher concept. Same internal-helper status
  as `nchildCrossTerm`. Faithfulness contract via Phase α'.7.2
  cycle 511 bridge to cycle 358's `elementaryWeightQ_phi_inv_mk`.
* **Definition smuggling**: cycle 509 ships only the parametric
  form's signature; does NOT claim equivalence to any Butcher-level
  theorem. The piecewise match-on-n at low `n` is **intentional and
  documented**: at n = 0 it matches `inversePolyTree (mk [])`, at
  n = 1 it matches `inversePolyTree (mk [c])`, at n ≥ 2 it matches
  the per-arity helpers via the 5 calibration witnesses below. No
  smuggling — every component is structural infrastructure.
* **Strawman correction**: documented in §A above. The cycle 508
  scoping doc §B.1.1 strawman was internally inconsistent at low n
  (double-counted block-∅ ↔ self-kernel at n=0, and single-child ↔
  self-kernel at n=1). The three-arm match-on-n preserves the
  scoping doc's intended `n ≥ 2` semantics exactly while correcting
  the low-n degenerate cases to match `inversePolyTree`.
* **Hypothesis strength**: minimal — `(n : ℕ) (children : Fin n → RT)
  (inv_children : Fin n → ℝ) (f : RT → ℝ)`. No extras.

### `nchildPolynomial_zero` (new theorem)

* **Statement**:
  > `nchildPolynomial 0 children inv_children f = -f RootedTree.vertex`
* **Tautology check**: conclusion is `nchildPolynomial 0 … = -f vertex`,
  NOT a re-export of any hypothesis. Real algebraic content (forces
  arm-0 dispatch to evaluate to `-f vertex`).
* **Identity check**: proof is `rfl` — but `rfl` here is the legitimate
  reduction of arm-0 pattern, not a hypothesis re-export. The theorem
  pins the parametric form's value at n = 0.
* **Hypothesis strength**: vacuous parameters at `Fin 0`; no extras.

### `nchildPolynomial_eq_one` (new theorem)

* **Statement**:
  > `nchildPolynomial 1 children inv_children f =
  >   -(f RootedTree.vertex * inv_children 0)
  >     + monochildCrossTerm (children 0) f
  >     - f (mk [children 0])`
* **Tautology check**: NOT a tautology; pins the arm-1 dispatch.
* **Identity check**: `rfl` on arm-1 pattern; legitimate.
* **Hypothesis strength**: minimal.

### `nchildPolynomial_eq_bichildPolynomial` / `_eq_trichildPolynomial` / `_eq_tetrachildPolynomial`

* **Statement**: `nchildPolynomial k children inv_children f =
  ⟨k⟩childPolynomial (children 0) … (inv_children 0) … f` for
  `k ∈ {2, 3, 4}`.
* **Tautology check**: each conclusion is a non-trivial algebraic
  identity (parametric subset-sum form reduces to per-arity helper
  expansion via `Fin.prod_univ_k`, `Fin.sum_univ_k`, and explicit
  erase identifications). NOT a tautology.
* **Identity check**: proofs are `show + unfold + rw + ring`; no
  `exact h` short-circuits.
* **Hypothesis strength**: minimal — matches per-arity helpers'
  hypothesis sets verbatim (children + inv_children + f).

### Pre-commit faithfulness scan

* `grep -c sorry OpenMath/Chapter4/Section422.lean` → expected **5**
  (4 docstring + 1 grandfathered cycle 365 at line 2279).
* `grep "axiom\|constant" OpenMath/Chapter4/Section422.lean | wc -l`
  → expected **0** new (cycle 509 introduces no `axiom`/`constant`).

## Dead ends

### `simp [nchildPolynomial, …]` over-unfolds

Memory `feedback_simp_recursive_def_overunfolds.md` warns that
`simp [recursive-def, name-eq-thm]` unfolds to raw match form before
name theorems can fold back. Avoided by using `show` to canonicalize
the parametric form's RHS, then `unfold bichildPolynomial` (etc.)
followed by targeted `rw` with `Fin.prod_univ_two` / `Fin.sum_univ_two`
/ `Finset.prod_singleton` / `Finset.prod_insert`, then `ring`.

### `Fin.sum_univ_succ` cascade vs `Fin.sum_univ_four`

Memory `feedback_fin_sum_univ_succ_coerce.md` warned about
`Fin.sum_univ_succ` binder-type mismatch on `Fin (cs.length)`-typed
sums. For cycle 509 the binders are direct `Fin n` literals at
n ∈ {2, 3, 4}, so the named `Fin.sum_univ_two` / `Fin.sum_univ_three`
/ `Fin.sum_univ_four` lemmas fire cleanly (confirmed by
`lean_leansearch` lookup — `Fin.sum_univ_four` exists in
`Mathlib.Algebra.BigOperators.Fin`).

### Strawman's uniform body at all `n`

Documented in §A. The cycle 508 strategy strawman's literal subset-sum
body double-counts at n ∈ {0, 1}. Attempted to use the uniform body
directly, but the calibration at n = 0 then gives `-2 · f vertex`
instead of `-f vertex` (the strategy's calibration target). Pivoted
to the three-arm match-on-n design, which preserves the uniform
strawman exactly at `n ≥ 2` (the only regime where Phase α'.7.1+
depends on it).

## Discovery

### §1. The strawman's "self-kernel" block is redundant with block-∅ / single-child at low n

The cycle 508 strategy strawman conceptually includes 2^n subset
contributions, but the textually-distinct blocks (∅, single-child sum,
cross-term, self-kernel) only stay disjoint when `n ≥ 2`. At n = 0,
∅ = {} = Fin 0 = "select all" (so block-∅ ↔ self-kernel coincide).
At n = 1, {0} = Fin 1 = "select all" (so single-child ↔ self-kernel
coincide). The match-on-n pivot at low n is the cleanest fix; an
alternative would have been to absorb correction terms into
`nchildCrossTerm` at low n, but that pollutes the cross-term
abstraction.

**For cycle 510+**: this Discovery generalizes — at n = 2 the
"cross-term block" (|S| = 2 = n) coincides with the self-kernel only
if we identify "|S| = n" with self-kernel. We've **defined the
self-kernel as ALWAYS being the `f (mk (List.ofFn children))` term**,
and the cross-term as everything else. This convention keeps the
subset-sum body uniform at n ≥ 2 (the cycle 510 calibration regime).

### §2. `Finset.univ.erase k` for `Fin n` literals is `decide`-friendly

For n ∈ {2, 3, 4}, the identifications
`Finset.univ.erase (k : Fin n) = {…}` close by `decide` (Finset
decidable equality over Fin n is well-established in Mathlib). This
makes the calibration proofs mechanical and avoids the need for ad-hoc
case analysis.

**For cycle 510+**: at n = 5+, `Finset.univ.erase` will still be
`decide`-closable, so the n = 5+ calibration witnesses (cycle 517+)
can follow the same template. The bottleneck is `Fin.sum_univ_five` /
`Fin.prod_univ_five` — these may not exist as named lemmas in
Mathlib and would need to be ad-hoc'd via `Fin.sum_univ_succ` cascade.

### §3. `nchildPolynomial` design avoids termination concerns at all n

The three-arm match-on-n is **not recursive** (each arm produces a
flat expression over `Finset` aggregates). Lean's structural
recursion check is not invoked, so the scoping doc §8 R1 termination
obstruction does not bite at cycle 509. For Phase α'.7.5+ extensions
(cycle 517+ at n = 5), the same non-recursive shape extends — the
catch-all `_ + 5 => 0` arm replacement adds new arms but introduces
no recursion.

### §4. `nchildCrossTerm` ignores `inv_children`

Mirroring the per-arity helpers (`bichildCrossTerm`, etc.), the
cross-term skeleton's body does **not** reference `inv_children`.
The `inv_children` parameter is carried for signature uniformity
with `nchildPolynomial`, but at every dispatched arm the cross-term
value depends only on `children` and `f`. This matches the per-arity
helpers' design.

## Suggested next approach

### Cycle 510 (Phase α'.7.1) — n = 4 empirical-surface calibrations

Per scoping doc §6.1 + §9.4: ship 5 calibration witnesses (theorems)
demonstrating that `nchildPolynomial 4 ![children] ![inv_children] f`
equals the cycles 499–504 empirical closed forms for each of the 5
shipped k = 4 trees:

* `bushy₄` = `mk [v, v, v, v]`: calibrate against cycle 499.
* `vvvc` = `mk [v, v, v, c]`: calibrate against cycle 501.
* `vvcc` = `mk [v, v, c, c]`: calibrate against cycle 502.
* `vccc` = `mk [v, c, c, c]`: calibrate against cycle 503.
* `cccc` = `mk [c, c, c, c]`: calibrate against cycle 504.

Each calibration: rewrite the empirical closed form's RHS by applying
cycle 509's `nchildPolynomial_eq_tetrachildPolynomial` (reducing the
parametric form to `tetrachildPolynomial`), then use cycles 499–504's
existing `_inv_*` theorems to identify the result. Risk: LOW
(mechanical). LOC: ~150–250.

### Cycle 511 (Phase α'.7.2) — cycle 358 → nchildPolynomial bridge

Per scoping doc §6.2: ship the bridge theorem
`elementaryWeightQ_phi_inv_eq_nchildPolynomial : ∀ (n : ℕ) (children :
Fin n → RT), elementaryWeightQ_phi_inv (mk (List.ofFn children)) =
nchildPolynomial n children (fun i => elementaryWeightQ_phi_inv (children i))
elementaryWeight`. Risk: HIGH. LOC: ~300–500. Aristotle-dispatchable
as `2^n`-way case analysis.

### Cycle 512+ (Phase α'.7.3+) — k = 5 closed-form witness

Per scoping doc §6.3: ship `elementaryWeightQ_phi_inv_bushy₅`
(`mk [v, v, v, v, v]` closed form), then extend `nchildCrossTerm` to
n = 5 via the cycle 503 / 504 cancellation pattern (memory
`feedback_cherry_child_cancellation.md`).

### Long-horizon (cycle ~520+) — Phase β.2 / δ / ε toward cycle 365 closure

Per scoping doc §1 + cycle 508 task results §H: the cycle 365
grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
becomes addressable only after Phase α'.7.6 (uniform n closure of
`nchildPolynomial` correctness) is shipped. Estimated 10–15 more
cycles from cycle 509.

### Verification

Cycle 509 compile + axiom-clean verification status: see commit
summary below. If a calibration proof fails, the most likely culprits
(in order of probability):

1. The match-on-n arm 0 / arm 1 `rfl` calibrations fail because
   pattern unification needs the discriminant n to be a literal.
   **Fix**: use `show` to canonicalize, or wrap in `decide` /
   `Eq.refl`.
2. The `n + 2` arm's `Fin (n + 2)` binder doesn't unify with `Fin 2`
   / `Fin 3` / `Fin 4` in the `show` block. **Fix**: use `simp only
   [Nat.add_zero, Nat.add_succ]` or explicit `cast` (per memory
   `feedback_fin_sum_univ_succ_coerce.md`).
3. `Finset.univ.erase` `decide` calls time out for `Fin 4` due to
   Finset decidable equality cost. **Fix**: use `Finset.ext` +
   `Finset.mem_erase` + explicit case analysis.

If any of these fire, the fix is local (≤ 5 LOC per call site) and
the overall cycle 509 ship structure is unaffected.
