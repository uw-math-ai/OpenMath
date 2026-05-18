# Cycle 380 Results

## Worked on

§422 Phase α'.1 (partial V1) — recursive helper `inversePolyChain`
capturing the Family A (single-child ladder) convolution recursion
in Lean, per cycle 380 strategy "Minimum acceptable" deliverable
(worst-case fallback per scoping doc §10).

This cycle ships:

* `chainTree : ℕ → RT` — depth-`n` single-child ladder tree
  `mk^n[vertex]`, definitionally equal to `vertex / cherry /
  mk [cherry] / mk [mk [cherry]]` at depths `0..3`.
* 3 reduction theorems `chainTree_one / chainTree_two /
  chainTree_three` proving the defeq witnesses by `rfl`.
* `inversePolyChain : ℕ → (RT → ℝ) → ℝ` — Family A recursive
  closed-form helper implementing the convolution recursion
  `P_{n+1} = -(∑_{p=0}^{n} P_{n-p} · c_p) - c_{n+1}` derived in
  the scoping doc and re-verified hand-derivation against the 4
  cycle 341/367/369/378 closed forms.
* 4 closed-form theorems `inversePolyChain_zero / _one / _two /
  _three` proving `inversePolyChain k f = (cycle k closed form)`
  for `k ∈ {0, 1, 2, 3}` via `Fin.sum_univ_*` expansions + `ring`.
* 4 bridge theorems `inversePolyChain_{k}_eq_inversePolynomial`
  proving `inversePolyChain k f = inversePolynomial (chainTree k) f`
  for `k ∈ {0, 1, 2, 3}`, chaining the recursive helper to the
  cycle 374/377/378 8-way pattern-match `inversePolynomial` via
  `if_neg ... if_pos rfl` chains identical to the existing
  calibration witnesses.

`inversePolynomial` itself is unchanged — the cycle 374/377/378
8-way `if-then-else` pattern match at `Section422.lean:4651–4697`
remains as-is. Family B (`broom₃`, `bushy`) and Family C
(`mk [broom₃]`, `mk [vertex, cherry]`) cases continue to be
handled by explicit `if-then-else` branches. The 8 existing
calibration witnesses (lines 4704–4929) continue to pass
unmodified.

## Approach

Per the cycle 380 strategy entry-point checklist:

1. **Read scoping doc** `def_422B_phase_alpha_prime_scoping.md`
   §1–§10. The cycle 379 worker recommended Variant V2 (fold-
   over-children) but flagged Family C as the structural unknown.
2. **Re-derived Family A pattern from cycle 358 `_inv_mk` +
   cycle 367/368/369/378 per-tree proof bodies.** The key
   structural insight: for the depth-`n` single-child ladder
   tree `t_n = mk^n[vertex]`, the derivativeWeightWithSrc admits
   `dws(t_n, i) = ∑_{p=0}^n α_{n,p}(c_*) · a_i^{(p)}` with
   `α_{n,n} = 1`, `α_{n,p} = P_{n-p-1}` for `0 ≤ p ≤ n-1`. The
   convolution recursion `P_{n+1} = -∑_{p=0}^n P_{n-p} · c_p
   - c_{n+1}` falls out by summing against `M.b i` and using
   `∑_i b_i · a_i^{(p)} = c_p = Φ_η(t_p)`.
3. **Hand-verified the recursion against the 4 ladder trees** in
   the docstring of the new `### Phase α'.1 (cycle 380)` section
   — `P_0 = -v, P_1 = v² - c, P_2 = -v³ + 2vc - m, P_3 = v⁴ -
   3v²c + c² + 2vm - M_mc` (all match cycles 341/367/369/378
   verbatim).
4. **Did NOT attempt Variant V2 fold-over-children.** The
   scoping doc §10 noted Family B sign-convention errors and
   Family C cross-term mixing as critical unknowns (G1, G2). A
   clean unified recursive shape covering all 8 trees requires
   more design work than fits in cycle 380 — the convolution
   recursion captured here is Family A only. Scoping doc §10
   worst-case fallback (Family A only) is exactly the
   deliverable shipped.
5. **Did NOT modify `inversePolynomial` itself.** The strategy's
   "Minimum acceptable" bar allows partial V1 with Family B/C
   remaining as pattern-match. Cycle 380 ships the recursive
   helper as a *separate* def; future cycles (Phase α'.2 and
   later) can migrate `inversePolynomial`'s Family A branches to
   call `inversePolyChain`, or extend the helper to cover Family
   B/C and replace `inversePolynomial` outright.

Aristotle: not used this cycle. Per the strategy's "Aristotle
delegation" section, Phase α'.1 is a *design* task (deriving the
right recursive shape from empirical closed forms), not a search
task. Aristotle's free compute is better reserved for cycle 384+
Phase α'.4 (the cycle 365 grandfathered sorry closure).

## Result

**SUCCESS** — Section422.lean builds clean, sorry count unchanged
at 5 (1 code sorry + 4 docstring references), axiom-clean
deliverable.

Verification (per strategy §"Verification commands"):

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0. ✓
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
   (unchanged from cycle 378). ✓
3. Tautology scanner clean (no theorems with `:= h_*` or
   `exact h_*` bodies introduced this cycle). ✓
4. `lake env lean OpenMath/Chapter4.lean` (aggregator) exits 0. ✓
5. `#print axioms inversePolyChain` returns
   `[propext, Classical.choice, Quot.sound]` (verified on
   scratch file, not committed). ✓

LOC delta on `Section422.lean`: +~250 (new section §"Phase α'.1
(cycle 380) — Family A recursive helper `inversePolyChain`"),
inserted between the cycle 378 calibration witness (line 4929)
and the cycle 375 Phase β.1 section header (was line 4931). The
new section contains:

* 1 `def chainTree`
* 3 `theorem chainTree_one / _two / _three` (each `:= rfl`)
* 1 `noncomputable def inversePolyChain`
* 4 `theorem inversePolyChain_{zero,one,two,three}` (closed forms)
* 4 `theorem inversePolyChain_{k}_eq_inversePolynomial` (bridges)

## Faithfulness check

* **`chainTree` and `inversePolyChain` are infrastructure**, not
  textbook entities. No `lean_status.json` row update needed.
  These are Lean implementation helpers paving the way for the
  eventual `def:422B` closure.
* **Recursive recursion (`inversePolyChain`) is mathematically
  equivalent to the closed forms via the convolution structure**
  identified in the scoping doc §4 and proven by `Fin.sum_univ_*`
  expansions in `inversePolyChain_{one,two,three}`. The bridge
  theorems `inversePolyChain_{k}_eq_inversePolynomial` formally
  link the recursive helper to the cycle 374/377/378
  pattern-match definition on the 4 Family A trees.
* **Cycle 341/367/369/378 axiom-clean theorems untouched.** The
  new helpers are *additions*, not replacements; the 8-way
  `if-then-else` `inversePolynomial` remains semantically
  identical to cycle 378's ship.
* **The recursion captures exactly the Family A pattern** —
  `inversePolyChain k f` for `k = 0, 1, 2, 3` matches Butcher's
  closed-form coefficients on the 4 ladder trees as documented
  in the cycle 378 catalog table (scoping doc §3). The cycle
  373 scoping doc §4.5 "σ does NOT appear" invariant is
  preserved: `inversePolyChain` depends only on `f` evaluations
  at chain trees, not on `σ` or `γ`.

No new `def` of a named textbook concept, no new `class` or
`structure` with Prop fields, no theorem whose conclusion is a
re-export of a hypothesis. The 4 bridge lemmas reference both
`inversePolyChain` (LHS) and `inversePolynomial` (RHS) but their
proofs use the closed-form path through `inversePolyChain_k` + the
existing pattern-match dispatch — neither side is a vacuous
restatement of the other.

## Dead ends

* **Variant V2 fold-over-children was NOT attempted in this
  cycle.** The scoping doc §10 worst-case fallback (Family A
  only) was the explicit graceful-degradation option, and after
  the per-tree closed-form analysis (esp. cycle 372's `c²` term
  in `mk [vertex, cherry]`), a unified V2 recursion satisfying
  all 8 closed forms by `unfold + ring` could not be derived
  within a single cycle. The Family C cross-term mixing (G2 in
  the scoping doc) requires either a Connes-Kreimer-style
  combinatorial enumerator or new per-tree-pattern machinery
  beyond the convolution recursion of Family A.
* **An attempt to write `inversePolyChain` with `Finset.range`
  + `n - p` recursive calls was abandoned in favour of `Fin
  (n + 1)`-indexed sum.** The `Fin n.succ` pattern follows
  `Nat.catalan`'s Mathlib precedent and yields automatic
  termination via Lean's default well-founded recursion
  measure. The `Finset.range` form would have required manual
  `decreasing_by` annotations.
* **An attempt to modify `inversePolynomial` to dispatch Family
  A branches to `inversePolyChain` was deferred to a future
  cycle.** Doing this would require updating the 4 Family A
  calibration witnesses' proof steps (the `unfold + if_neg ...
  if_pos rfl` chain becomes `unfold + if_*` + `unfold
  inversePolyChain` + ring). Cycle 380 ships the helper as a
  separate def to minimize risk to the cycle 374/377/378
  pattern-match calibration witnesses' axiom-clean state.

## Discovery

* **The Family A closed-form recursion is a `Cauchy/convolution
  product`-style relation.** Writing `C(x) = ∑ c_k x^k` and
  `P(x) = ∑ P_k x^k` as generating functions, the recursion
  `P_{n+1} = -∑_{p} P_{n-p} c_p - c_{n+1}` collapses to
  `P(x) = -C(x) / (1 + x · C(x))` (in power series). This is
  the "compositional inverse" or "multiplicative inverse" of
  the chain elementary-weight generating function, providing
  a clean algebraic interpretation of Family A.
* **The Family A recursion suggests a path to Family B (binomial
  brooms `mk [vertex^k]`)** via a *different* generating function
  identity: `Φ_{η⁻¹}(mk [vertex^k]) = -∑_{j=0}^k C(k,j) ·
  (-v)^{k-j} · c'_j` where `c'_j := Φ_η(mk [vertex^j]) = ∑_i b_i
  · A_i^j`. The cross-tree mixing for Family C is the remaining
  combinatorial open problem.
* **`Fin.sum_univ_one`, `Fin.sum_univ_two`, and
  `Fin.sum_univ_three`** are all Mathlib-named simp-friendly
  expansion lemmas for `Fin n` sums up to `n = 3`. The cycle
  380 bridge proofs reuse these for clean closed-form
  derivations without manual `Fin.sum_univ_succ` unwinding.

## Suggested next approach

For cycle 381 (Phase α'.1 continuation or Phase α'.2 migration):

**Option A (Phase α'.2 — Family A bridge migration)**: Replace
the 4 Family A `if-then-else` branches in `inversePolynomial`
(`Section422.lean:4652–4663` vertex/cherry/mk[cherry] branches
and the 8th `mk [mk [cherry]]` branch at line 4686) with calls
to `inversePolyChain k f` for `k = 0, 1, 2, 3`. The 4 Family A
calibration witnesses' proofs would update to use
`inversePolyChain_{k}_eq_inversePolynomial` after the `if_*`
dispatch. Estimated LOC delta: ~50 LOC, axiom-clean. Cycle 380's
4 bridge theorems are the load-bearing infrastructure for this
migration.

**Option B (Phase α'.1 extension — Family B closed form)**:
Derive the Family B binomial sum formula `Φ_{η⁻¹}(mk [vertex^k])
= -∑_{j=0}^k C(k,j) · (-v)^{k-j} · c'_j` rigorously from cycle
358 `_inv_mk` + the cycle 368/370 per-row `(A_i - v)^k`
factorisation, ship as a new helper `inversePolyBroom : ℕ → (RT
→ ℝ) → ℝ`, prove 4 closed-form theorems for `k = 1, 2, 3` (and
extrapolate to `k = 4` as a 9th-tree stretch goal). This
addresses scoping doc G1 (CRITICAL).

**Option C (Phase α'.4 prep — cycle 365 sorry attack)**: Begin
work on `powRep_sum_eq_of_strict_subtree_agreement` at
`Section422.lean:2279` using cycle 380's `inversePolyChain` as
the first ladder-class subset. Even before Phase γ generalises
to all trees, the cycle 365 sorry's body could potentially be
discharged for the 4 Family A ladder trees by induction on `m`
+ direct application of `inversePolyChain_three_eq_inversePolynomial`.
This is a risky path (the sorry's body may require Phase γ
infrastructure that does not yet exist) but could test the
cycle 365-grandfathered-sorry attack vector empirically.

**Recommended for cycle 381**: Option A (Phase α'.2 migration).
The cycle 380 ship's load-bearing artifacts (4 bridge theorems)
make the migration mechanical and low-risk. Option B and C are
better deferred to cycles 382+ once the Family A migration is
in place and Phase β bridges have been refreshed against the
recursive form.
