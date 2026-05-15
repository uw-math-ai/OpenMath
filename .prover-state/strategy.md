# Cycle 256 Strategy

## A. Setting (read carefully)

Cycle 255 shipped axiom-clean B-series partial sum infrastructure
(`TruncatedRootedTree N`, `bseriesPartialSum`, `_empty`/`_insert` simp
lemmas, `exists_truncated_of_forall_order_le`, plus two non-vacuity
witnesses). Sorry count = 0 across the repo. No Aristotle results
pending.

The §310/§311 cascade is now ripe for two follow-ups, both of which
the cycle 255 task results recommended:

* The **α-weighted partial sum companion** (~50 LOC; completes the
  cycle 255 partial-sum infrastructure to match Butcher (310i)'s
  weighted form exactly).
* `lem_311A_order_two` (~150-250 LOC, possibly 2 cycles; extends
  cycle 248's `lem_311A_order_one` to the second Taylor order).

Per the cycle 255 task results §"Suggested next approach":

> 1. **Cycle 256**: `lem_311A_order_two` — the order-2 Taylor
>    expansion bridge for `lem:311A`.
> 2. **`α`-weighted version of `bseriesPartialSum`**: a natural
>    cycle 256+ companion to cycle 255's scaffold-form partial sum
>    [...] one declaration (~5 LOC) plus singleton/insert
>    companions; could be folded into cycle 256 with no extra
>    infrastructure burden.

We take **both** in cycle 256, with the cheaper α-weighted companion
as **P1** (guaranteed ship) and `lem_311A_order_two` as **P2**
(time-boxed stretch — explicit abort plan in §G below).

GPFS Section441.lean smoke test continues to time out (43rd
consecutive cycle since 184). Do NOT attempt to compile
`OpenMath/Chapter4/Section441.lean` — skip per
`.prover-state/issues/cycle_182_gpfs_slowness.md`.

## B. Priorities

### P1 (MUST SHIP): α-weighted B-series partial sum companion

Ship into `OpenMath/Chapter3/Section301.lean` immediately after
cycle 255's `exists_truncated_of_forall_order_le` (line ~683),
**still inside the `OpenMath.Chapter3.Section310.RootedTree`
namespace** (do NOT open a new namespace block — that namespace
extends to line 684's `end RootedTree`; insert your new code
before that `end`).

**Target deliverables:**

1. **`bseriesAlphaTerm`** — the α-weighted per-tree summand of
   Butcher's (310i):

   ```lean
   /-- The α-weighted per-tree B-series summand
   `α(t) • (h^r(t)/σ(t)) • F(t)(y₀)` of Butcher's series (310i).
   This is `alphaWeight t • bseriesTerm f y₀ h t`; ship it as a
   named symbol so future cycles can rewrite α-weighted partial
   sums into their `bseriesTerm` form on demand. -/
   noncomputable def bseriesAlphaTerm
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
     alphaWeight t • bseriesTerm f y₀ h t
   ```

2. **`bseriesAlphaTerm_vertex`** — at the trivial tree
   `τ = mk []`, `α(τ) = 1` (cycle 250's `alphaWeight_vertex`)
   collapses the α-weight, so `bseriesAlphaTerm f y₀ h vertex =
   h • f y₀` (combining with cycle 254's `bseriesTerm_vertex`).

   ```lean
   theorem bseriesAlphaTerm_vertex
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       (f : E → E) (y₀ : E) (h : ℝ) :
       bseriesAlphaTerm f y₀ h vertex = h • f y₀ := by
     unfold bseriesAlphaTerm
     rw [show alphaWeight vertex = 1 from alphaWeight_vertex,
         one_smul, bseriesTerm_vertex]
   ```

   Note: `vertex` is defined in Section301 (line 92 area) as
   `mk []`. `alphaWeight_vertex` (line 311) proves
   `alphaWeight (mk []) = 1` directly; the `show ... from` bridge
   handles any definitional-equality coercion between `vertex` and
   `mk []` — see Risk §F1.

3. **`bseriesAlphaPartialSum`** — the α-weighted partial sum over
   `Finset RootedTree`:

   ```lean
   /-- Butcher's series (310i), partial-sum form: the α-weighted
   B-series approximation truncated to a hand-supplied
   `Finset RootedTree`. For small `S`, this matches the textbook
   `Σ_{t ∈ T} α(t)·(h^r(t)/σ(t))·F(t)(y₀)` exactly. -/
   noncomputable def bseriesAlphaPartialSum
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       (f : E → E) (y₀ : E) (h : ℝ) (S : Finset RootedTree) : E :=
     ∑ t ∈ S, bseriesAlphaTerm f y₀ h t
   ```

4. **`bseriesAlphaPartialSum_empty`** (`@[simp]`) and
   **`bseriesAlphaPartialSum_insert`** — straight ports of cycle
   255's `bseriesPartialSum_empty` / `bseriesPartialSum_insert`.
   Proofs are identical: `simp [bseriesAlphaPartialSum]` and
   `simp [bseriesAlphaPartialSum, Finset.sum_insert ht]`.

5. **Two non-vacuity examples** at the file's tail (after cycle
   255's two `bseriesPartialSum` examples, before
   `exists_truncated_of_forall_order_le`):

   * `bseriesAlphaPartialSum f y₀ h {vertex} = h • f y₀` —
     singleton form using `Finset.sum_singleton` +
     `bseriesAlphaTerm_vertex`.
   * `bseriesAlphaPartialSum f y₀ h {vertex, cherry} =
       h • f y₀ + bseriesAlphaTerm f y₀ h cherry` — two-element
     form mirroring cycle 255's example.

**LOC budget**: ~50 LOC total (4 new symbols + 2 examples +
documentation).

**Aristotle suitability**: low — all proofs are direct ports of
cycle 255 declarations or one-line rewrites. Manual closure is
faster than batching.

**Axiom expectation**: `[propext, Classical.choice, Quot.sound]`
across all new symbols. `bseriesAlphaPartialSum_empty` may depend
on only `propext` (mirroring cycle 255's pattern where
`bseriesPartialSum_empty` does the same).

### P2 (TIME-BOXED STRETCH): `lem_311A_order_two`

If P1 closes cleanly in < 30 minutes (which it should — see Risk
§F1), attempt the order-2 Taylor expansion analog of cycle 248's
`lem_311A_order_one` in **`OpenMath/Chapter3/Section311.lean`**.

**Target deliverable shape:**

```lean
/-- Order-2 Taylor expansion of the exact solution (p = 2 case
of the §311 Taylor expansion that `lem:311A` underwrites). -/
theorem lem_311A_order_two
    {f : ℝ → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C3 : ContDiff ℝ 3 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) -
      (y₀ + h * f y₀ + (h^2/2) * (deriv f y₀ * f y₀)))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (2 + 1))
```

(Note: this is stated for ℝ → ℝ scalars, using `deriv f y₀ * f y₀`
instead of `fderiv ℝ f y₀ (f y₀)` — equivalent over ℝ, avoids
multilinear-map plumbing. Polymorphic version is cycle 257+ scope.)

Proof recipe (extending cycle 248's `lem_311A_order_one`):

1. **Taylor expansion at degree 3** — replace cycle 248's
   `taylor_isLittleO (n := 2)` with `taylor_isLittleO (n := 3)`.
   The Taylor polynomial expansion `taylorWithinEval yex 3 Set.univ
   x₀ (x₀ + h)` will produce four summands, including the new
   `(h³/6) • iteratedDeriv 3 yex x₀` term. Absorb it as a separate
   `O(h³)` summand via `isBigO_const_mul_self` (cycle 248 used this
   pattern for the analogous `(h²/2)` term).

2. **Identify `iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀`** —
   the chain-rule extraction. Approach:
   * `iteratedDeriv 2 yex x₀ = deriv (deriv yex) x₀` via
     `iteratedDeriv_succ` (twice) or `iteratedDeriv_two` if such a
     lemma exists.
   * From `hyex_ode`, `deriv yex t = f (yex t)` pointwise.
   * Apply chain rule: `(f ∘ yex)' = (deriv f) ∘ yex · deriv yex`.
   * At `t = x₀`, using `hyex_x₀` and `deriv yex x₀ = f y₀`:
     `iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀`.

   **Mathlib hooks to verify with `lean_local_search` /
   `lean_loogle` at the start of P2**:
   * `iteratedDeriv_succ` — `iteratedDeriv (n+1) f = deriv
     (iteratedDeriv n f)`.
   * `HasDerivAt.comp` — chain rule for `HasDerivAt`.
   * `Differentiable.deriv_comp` / `deriv_comp` —
     `deriv (g ∘ f) x = deriv g (f x) * deriv f x` for ℝ → ℝ.

3. **Combine** — mirror cycle 248's `hres.isBigO.add hquad`
   pattern, this time summing **three** `IsBigO` pieces:
   * Taylor-3 residual (`o(h³)` ⇒ `O(h³)` via `IsLittleO.isBigO`)
   * `(h²/2)` coefficient term — actually NOT a new
     `O(h³)`-summand because it gets *consumed* by the cycle 256
     bseries-order-2 truncation. Re-examine cycle 248's structure:
     in `lem_311A_order_one` the `(h²/2)·iteratedDeriv 2 yex x₀`
     was an `O(h²)`-residual; here it becomes part of the *target*
     B-series truncation, so it disappears from the residual.
   * `(h³/6)` coefficient term — new `O(h³)` residual.

   Net: the cycle 256 residual is
   `Taylor-3-remainder + (h³/6)·iteratedDeriv 3 yex x₀`, both
   `O(h³)`.

**LOC budget**: 150-250 LOC. The cycle 248 baseline was 100 LOC
for the order-1 case (Section311.lean is 215 LOC total); order-2
adds the chain-rule extraction step (~50 LOC) and the extra Taylor
summand (~30 LOC).

**Aristotle suitability**: high for the chain-rule sub-lemma if
it stalls. The `iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀` claim
is a standard Mathlib idiom; Aristotle should find it in one
batch. Submit early if you sense P2 stalling.

**ABORT THRESHOLD** (§G): if P2's chain-rule step doesn't close
in 60 minutes, fall back to **P2-lite** — ship only the *sub-lemma*
`iteratedDeriv_two_via_ode` as an axiom-clean lemma (without
attempting the full `lem_311A_order_two`). Cycle 257 closes the
top-level theorem on top of that.

### P3 (BONUS, only if both P1 + P2 ship clean): cross-section bridge

Ship in `OpenMath/Chapter3/Section311.lean`:

```lean
/-- Cross-section bridge: cycle 256 `bseriesAlphaPartialSum` at
`{vertex}` equals cycle 248 `bseriesOrderOne`'s f-contribution. -/
theorem bseriesAlphaPartialSum_singleton_vertex_eq
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum
      f y₀ h {OpenMath.Chapter3.Section310.RootedTree.vertex}
      = h • f y₀ := by
  rw [OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum,
      Finset.sum_singleton,
      OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaTerm_vertex]
```

This is one declaration, ~5 LOC, axiom-clean expected. Ship only
if P1 + P2 are both green; do NOT ship if P2 is in the P2-lite
fallback.

## C. Forbidden moves (do NOT attempt)

1. **Do NOT introduce `sorry`** anywhere in cycle 256's
   deliverables. Cycle 255 shipped sorry-clean; cycle 256 must
   preserve this. For P2, the abort path (P2-lite) is to NOT ship
   the full `lem_311A_order_two` rather than scaffolding it with
   `sorry`. The P2-lite sub-lemma `iteratedDeriv_two_via_ode` must
   itself be fully proved (axiom-clean), not sorry-scaffolded.

2. **Do NOT introduce `axiom` / `constant`** anywhere.

3. **Do NOT raise `maxHeartbeats`** above 200000 (CLAUDE.md
   absolute rule).

4. **Do NOT attempt the full `lem:310B`** (the labelled-tree
   re-summation identity). This requires `thm:306A` +
   labelled-tree quotient infrastructure — multi-cycle scope per
   cycle 254's task results.

5. **Do NOT attempt to define `Fintype (TruncatedRootedTree N)`**.
   Cycle 255's task results explicitly noted this is Cayley's
   formula territory, multi-cycle.

6. **Do NOT attempt to compile or edit
   `OpenMath/Chapter4/Section441.lean`**. 43rd consecutive GPFS
   timeout; pivot to cycle 256's deliverables which are in
   `Section301.lean` / `Section311.lean` only.

7. **Do NOT cherry-pick a smaller deliverable than P1**. P1 is the
   baseline non-negotiable ship target. If P1 stalls, that itself
   is the cycle's anomaly to investigate.

8. **Do NOT touch `scripts/autonomous_loop.py`**. The tautology
   scanner false positives are loop-maintainer territory; the
   strategy is to ship clean math and accept that the score
   function may be noisy.

9. **Do NOT label the P3 bridge with a `lem:310B` or `thm:311B`
   entity ID**. P3 is a cross-section convenience theorem; it is
   NOT the textbook lemma. Per cycle 248's faithfulness
   convention, only label theorems with textbook IDs when they
   capture the textbook statement.

10. **Do NOT attempt P2 if P1 stalls**. P1 is ~50 LOC of
    mechanical port work; if it doesn't close in 30 minutes,
    something is structurally wrong (likely a Lean version drift)
    and the cycle's only deliverable should be P1. P2 is a
    stretch on top of P1.

## D. Specific Mathlib hooks to verify EARLY in cycle 256

Run these `lean_local_search` / `lean_loogle` queries **in the
first 5 minutes** to confirm symbol availability before committing
to the P2 path:

* `lean_loogle "iteratedDeriv 2"` — for the second-derivative
  identity. Mathlib has `iteratedDeriv_succ`,
  `iteratedDeriv_succ'`, `iteratedDeriv_zero`. The recursion
  unrolls to `iteratedDeriv 2 yex = deriv (deriv yex)`.
* `lean_local_search "deriv_comp"` — for the ℝ → ℝ chain rule
  `deriv (g ∘ f) x = deriv g (f x) * deriv f x`.
* `lean_loogle "HasDerivAt _ _ → HasDerivAt _ _ → HasDerivAt _ _"`
  — for the chain rule on `HasDerivAt`.
* `lean_loogle "ContDiff ℝ _ _ → ∀ _, HasDerivAt _ _ _"` — to
  extract HasDerivAt witnesses from `hyex_C3`.

If P2 hooks look uncertain after these searches, fall back to
P2-lite. Don't sink time into Mathlib spelunking — Aristotle is
better suited if hooks are missing.

## E. Verification gauntlet (run at every milestone)

After P1 lands:
1. `lake env lean OpenMath/Chapter3/Section301.lean` → exit 0.
2. `lake env lean OpenMath/Chapter3.lean` → exit 0 (catch any
   downstream regressions).
3. `lake build OpenMath.Chapter3.Section301` → refresh olean
   cache.
4. `grep -c sorry OpenMath/Chapter3/Section301.lean` → 0.
5. `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
   OpenMath/Chapter3/` → 0 hits.
6. For each new public symbol, `#print axioms
   OpenMath.Chapter3.Section310.RootedTree.<name>` →
   `[propext, Classical.choice, Quot.sound]` (or subset).

After P2 lands (if attempted):
1. `lake env lean OpenMath/Chapter3/Section311.lean` → exit 0.
2. `lake env lean OpenMath/Chapter3.lean` → exit 0.
3. `lake build OpenMath.Chapter3.Section311`.
4. `grep -c sorry OpenMath/Chapter3/Section311.lean` → 0.
5. `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_two`
   → axiom-clean.

After P3 lands (if attempted):
1. Same as P2 plus `#print axioms` on P3's theorem.

## F. Risk register (with mitigations)

### F1 — `alphaWeight_vertex` namespace resolution

`alphaWeight_vertex` is defined at `Section301.lean:311` and proves
`alphaWeight (mk []) = 1`, but `vertex` in the cycle 255 namespace
is also `mk []`. The proof of `bseriesAlphaTerm_vertex` may need a
`show alphaWeight (mk []) = 1` reframing if Lean cannot unify
`vertex` with `mk []` by definitional equality alone.

**Mitigation**: if `rw [alphaWeight_vertex]` fails, use
`show alphaWeight (mk []) = 1 from alphaWeight_vertex` to bridge.
Cycle 254's `bseriesTerm_vertex` uses the analogous trick
(`show order (mk []) = 1 from rfl`). The strategy's P1 snippet
above already uses `show ... from` defensively.

### F2 — `Finset.sum_singleton` may not fire automatically on
`{vertex}`

In cycle 255's example (lines 660–662 of Section301.lean), the
singleton form is closed by `rw [bseriesPartialSum,
Finset.sum_singleton]`. The α-weighted analogue should work the
same way: `rw [bseriesAlphaPartialSum, Finset.sum_singleton,
bseriesAlphaTerm_vertex]`.

**Mitigation**: if `Finset.sum_singleton` doesn't fire (perhaps
because `Finset.sum` is unfolded as `∑ t ∈ {vertex}, …`), use
`simp [bseriesAlphaPartialSum, Finset.sum_singleton]` instead.

### F3 — P2 chain-rule signature drift

`HasDerivAt.comp` / `deriv_comp` may have a different signature in
this Mathlib snapshot than expected. The argument order, the
multilinear coercion of `fderiv`, and the `ℝ` vs general field
parameter may all drift.

**Mitigation**: use `lean_multi_attempt` at the chain-rule
extraction point to try multiple shapes. If none fire, submit an
Aristotle batch for the chain-rule sub-lemma alone (small,
focused job; should return quickly).

### F4 — `iteratedDeriv 2` formulation

Cycle 248 used `iteratedDeriv 2 yex x₀` in the Taylor expansion
(line 144 of Section311.lean). Cycle 256 needs to extract a
concrete value for this. The relevant Mathlib lemma is
`iteratedDeriv_succ` which unrolls
`iteratedDeriv (n+1) f x = deriv (iteratedDeriv n f) x`.

**Mitigation**: chain `iteratedDeriv_succ` twice:
* `iteratedDeriv 2 yex x₀ = deriv (iteratedDeriv 1 yex) x₀ =
  deriv (deriv yex) x₀`.
* Then use `hyex_ode` to identify `deriv yex t = f (yex t)`
  pointwise (via `funext` or `HasDerivAt.deriv`).
* Then `deriv (fun t => f (yex t)) x₀ = deriv f (yex x₀) * deriv
  yex x₀ = deriv f y₀ * f y₀` via `deriv_comp` (needs `f`
  differentiable at `y₀` and `yex` differentiable at `x₀`).

### F5 — `bseriesAlphaTerm` definition style

The cycle 255 task results' §"Suggested next approach" §3 wrote:

> `bseriesAlphaPartialSum f y₀ h S := ∑ t ∈ S, alphaWeight t •
> bseriesTerm f y₀ h t`

The strategy here factors `alphaWeight t • bseriesTerm f y₀ h t`
into a named symbol `bseriesAlphaTerm`. This is a minor design
choice; either works. We pick the named-term route for downstream
ergonomics (future `bseriesAlphaTerm_cherry`, `_broom₃` lemmas
can ship in separate cycles without modifying
`bseriesAlphaPartialSum`).

**Mitigation**: if `bseriesAlphaTerm` causes any unification
issues with downstream Finset.sum tactics, fall back to inlining
`alphaWeight t • bseriesTerm f y₀ h t` directly in
`bseriesAlphaPartialSum`. This is a one-edit revert.

### F6 — Aristotle batch suitability for P2

If P2's chain-rule extraction stalls, Aristotle is the right
batch target. **Submit the sub-lemma in isolation** with the
existing `lem_311A_order_one` and `bseriesTerm_vertex` as
in-context templates:

```lean
private theorem iteratedDeriv_two_via_ode
    {f : ℝ → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C3 : ContDiff ℝ 3 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀ := sorry
```

Do NOT submit the full `lem_311A_order_two` to Aristotle — too
large a job; the chain-rule sub-lemma alone is the bottleneck.

### F7 — Tautology scanner false positive

The supervisor's tautology scanner (`scripts/autonomous_loop.py`)
has documented false-positive bugs (see
`.prover-state/issues/tautology_scanner_false_positives.md`).
Cycles 243-247 / 248 scored -1 due to scanner over-firing.

**Mitigation**: this is NOT a cycle 256 problem. Just write clean
code. The scanner regex is
`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`; rg against this
should return zero hits in cycle 256's edits. No current
deliverable in §B uses `h_<name>` identifiers.

## G. Time-box and abort plan

* **P1**: ~30 minutes target. Hard cap 60 minutes. If P1 doesn't
  close in 60 minutes, abort and ship whatever is verified
  axiom-clean of P1's deliverables (perhaps just
  `bseriesAlphaTerm` + `bseriesAlphaPartialSum` definitions
  without the simp lemmas if those stall).
* **P2**: ~90 minutes target. Hard cap 120 minutes. If the
  chain-rule extraction sub-lemma doesn't close in 60 minutes
  (within the 120 cap), shift to P2-lite: ship
  `iteratedDeriv_two_via_ode` as a standalone lemma (axiom-clean,
  no sorry) and defer `lem_311A_order_two` to cycle 257.
* **P3**: ~10 minutes. Only attempt if both P1 and P2 are green
  (not P2-lite).
* **Hard wall**: at 3 hours total elapsed in the worker phase,
  stop and write task results regardless of P2/P3 state.

## H. What the cycle 256 task results should contain

The task results file
(`.prover-state/task_results/cycle_256.md`) should document:

1. P1 ship status (mandatory).
2. P2 ship status (mandatory: SHIPPED / P2-LITE-shipped / DEFERRED
   with Aristotle queued).
3. P3 ship status (NA / SHIPPED / SKIPPED).
4. Axiom-cleanliness verification on every new public symbol.
5. Faithfulness check per CLAUDE.md (every new `def` /
   `theorem` against `entities/<id>.json` where applicable;
   `bseriesAlphaPartialSum` is the natural locus for the (310i)
   match).
6. Build status of `Section301.lean`, `Section311.lean`,
   `Chapter3.lean`.
7. Tautology scanner regex check (should be 0 hits).
8. LOC delta per file.
9. Suggested cycle 257 next approach.

## I. Cycle 257 outlook (planning hint for next cycle's planner)

* If P2 ships clean in cycle 256: cycle 257 targets are
  (a) `lem_311A_order_three` (if useful — order-2 is usually
  sufficient for textbook applications) or
  (b) attempt small-r `lem:310B` cases via the cycle 255 + 256
  α-weighted partial sum machinery.
* If P2 falls back to P2-lite (ships only
  `iteratedDeriv_two_via_ode`): cycle 257 closes the top-level
  `lem_311A_order_two` on top of the sub-lemma.
* If P2 is fully deferred with Aristotle queued: cycle 257 polls
  Aristotle once and processes results.
* If P1 + P2 + P3 all ship: consider pivoting to a fresh §31x
  entity (e.g. `lem:312B`, `thm:313B`).

The §310/§311 chain is the highest-leverage zone in Chapter 3
right now; cycle 256 advances it by the largest single step
available without committing to the multi-cycle labelled-tree
quotient work.
