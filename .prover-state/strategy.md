# Cycle 265 strategy — `lem_311A_order_one` polymorphic lift to N-space

## A. Status confirmation (do this first)

Cycle 264 shipped clean: §300 Phase A.2 heterogeneous-labelling
non-vacuity is at HEAD (`66707e5`), `OpenMath/Chapter3/Section300.lean`
~389 LOC, sorry count 0, axiom-clean. There is **no blocker**. The
"What I'm stuck on" field in this cycle's planner prompt is empty for
a reason — this is the 7th documented occurrence of the empty-stuck-on
phantom pattern (see `consultant_advice_cycle_248.md` §I,
`consultant_advice_cycle_263.md` §I).

Run these verifications at the start of your cycle (~30 seconds):

```bash
git log -1 --format='%H %s'
wc -l OpenMath/Chapter3/Section300.lean OpenMath/Chapter3/Section311.lean
grep -c sorry OpenMath/Chapter3/Section300.lean OpenMath/Chapter3/Section311.lean
# Expected: 0 / 0
```

If everything is clean, proceed to §B. If anything is unexpected,
abort and file an issue.

## B. Target — Phase D.1 partial: polymorphic `lem_311A_order_one_poly`

**Ship a polymorphic version of `lem_311A_order_one`** (currently at
`OpenMath/Chapter3/Section311.lean` line 120, scalar `ℝ → ℝ`) that
operates on arbitrary real normed spaces `N`:

```lean
theorem lem_311A_order_one_poly
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N}
    {yex : ℝ → N} {x₀ : ℝ} {y₀ : N}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) - bseriesOrderOne f y₀ h)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
```

### Why this is the right target

1. **It's the canonical next Phase D step.** The cycle 260 scoping
   doc `.prover-state/issues/lem_310B_plan.md` §C.4 identifies Phase D
   (multilinear elementary-differential lift) as the prerequisite
   before Phase E (small-`r` `lem:310B` cases). Phase D.1 is the
   polymorphic chain-rule lift. The order-1 case is the smallest
   Phase D deliverable.

2. **It was deliberately deferred.** Cycle 256 task results
   explicitly flagged "polymorphic version ... and order-1 retrofit
   are cycle 257+ scope". Cycles 257/258/259 chose to extend scalar
   orders (3, 4, 5) instead, leaving the polymorphic lift open. This
   is real deferred work, not a freelanced easy ship.

3. **Single-cycle, axiom-clean achievable.** Unlike Phase A.3
   (TreeAutomorphism strengthening, multi-cycle high-risk per the
   cycle 200/201 rollback precedent) or Phase B (multivariate Taylor,
   multi-cycle), the order-1 lift is a mechanical port. `bseriesOrderOne`
   is already polymorphic (`OpenMath/Chapter3/Section311.lean:90`); only
   the theorem statement and proof tactics need lifting.

4. **It validates the port methodology.** A clean order-1 lift opens
   the path for order-2 polymorphic (which DOES need the
   `iteratedFDeriv ↔ fderiv` bridge for the chain rule — a separately
   risky step). Order-1 lets us confirm the basic plumbing works
   before committing to the harder order-2 work.

### Why NOT the other candidates

* **Option 2 (TreeAutomorphism strengthening / Phase A.3)** —
  multi-cycle `mutual`-block work with rollback risk matching cycles
  149/200/201. Do NOT attempt as a single-cycle deliverable.

* **Option 4 (lem:342A property 342a)** — pre-flight check:
  `find .lake -name "Legendre*.lean"` returns only `LegendreSymbol`
  (number-theoretic Jacobi/Legendre quadratic-residue symbol), NOT
  orthogonal Legendre polynomials. The cycle 260 scoping doc §8.2
  assumed Mathlib's Legendre infrastructure but it doesn't exist.
  Building it from scratch is a multi-cycle Mathlib-PR-grade
  undertaking. Do NOT attempt.

* **Phase B.1 (two-variable Taylor)** — multi-cycle per the scoping
  doc; also bypassable per §4.4 of the plan if Phase D routes through
  multilinear directly. Skip.

* **Refactor / cleanup work** (e.g., Section319 helper extraction) —
  cherry-picking easy deliverables per the planner instruction's
  explicit exclusion.

## C. Proof recipe (concrete port of cycle 248's proof)

Open `OpenMath/Chapter3/Section311.lean` and read cycle 248's
`lem_311A_order_one` proof (lines 120–245) before starting. The
polymorphic port is mechanical with two substitutions:

* **`h * f y₀` → `h • f y₀`** wherever the multiplication appears
  (the `f y₀` is now `N`-valued, requiring `smul`).
* **`mul`-style lemmas → `smul`-style lemmas** where they appear.

### Step-by-step port

1. **Step 0 (function rewrite)**: cycle 248 uses
   `simp [bseriesOrderOne, smul_eq_mul]`. Drop `smul_eq_mul` (for
   general `N` it does not apply). The polymorphic `bseriesOrderOne`
   already uses `smul`, so the rewrite is just `simp [bseriesOrderOne]`.

2. **Step 1 (Taylor remainder)**: cycle 248 invokes
   `taylor_isLittleO (n := 2) convex_univ (Set.mem_univ _)
   hyex_C2.contDiffOn`. This works verbatim for `ℝ → N` — Mathlib's
   `taylor_isLittleO` (`Mathlib/Analysis/Calculus/Taylor.lean:239`)
   takes `{f : ℝ → E}` for any `[NormedAddCommGroup E]
   [NormedSpace ℝ E]`. No changes needed at this step.

3. **Step 2 (Taylor polynomial evaluation)**: cycle 248 uses
   `taylor_within_apply` + `simp_only` with `Finset.sum_range_succ`,
   `iteratedDerivWithin_univ`, `iteratedDeriv_zero`, `Nat.factorial`,
   `smul_eq_mul` (drop this), etc. For polymorphic `N`:
   - The `iteratedDeriv k yex x₀ : N` (not `ℝ`) — types still
     align because Mathlib defines `iteratedDeriv` for normed-space
     codomain.
   - The `(1 : ℝ) / (k.factorial : ℝ) • (iteratedDeriv k yex x₀)` is
     a scalar smul on `N`. The `smul_eq_mul` rewrite no longer
     applies; replace with manual algebraic massaging if needed.

4. **Step 3 (identify `iteratedDeriv 1 yex x₀ = f y₀`)**: cycle 248
   uses `iteratedDeriv_one` (Mathlib) + `(hyex_ode x₀).deriv` +
   `hyex_x₀`. Both `iteratedDeriv_one` and `HasDerivAt.deriv` work
   for normed-space codomain. Port verbatim.

5. **Step 4 (compose with `h ↦ x₀ + h`)**: cycle 248 uses
   `IsLittleO.comp_tendsto`, `congr'`, and `((x₀ + h) - x₀)^2 = h^2`
   identification via `ring`/`funext`. All these work for the
   `ℝ → N`-valued residual.

6. **Step 5 (combine + `O(h^(1+1))` collapse)**: cycle 248 uses
   `IsLittleO.add` + `Asymptotics.isBigO_const_mul_self` for the
   quadratic-coefficient term, then `IsLittleO.isBigO` to promote.
   The constant `(1/2) • iteratedDeriv 2 yex x₀ : N` is an `N`-valued
   scalar coefficient. `Asymptotics.isBigO_const_mul_self` works for
   `N`-valued functions because the `IsBigO` predicate is norm-based.

### Expected proof shape

~80–120 LOC, similar to cycle 248's scalar proof. If a specific
tactic line does not port cleanly, factor it into a private helper
`have` block and identify the exact Mathlib hook needed — DO NOT
introduce a `sorry`.

### Non-vacuity witnesses (P2 — single-cycle ship)

After the theorem, add up to three `example`s in the same file:

1. **Trivial f := 0 on ℝ²**: `f : (Fin 2 → ℝ) → (Fin 2 → ℝ) := 0`,
   `yex : ℝ → (Fin 2 → ℝ) := fun _ => 0`, exhibits the polymorphic
   shape on a vector space.
2. **Linear ODE on ℝ²**: `f := fun v => ![v 1, -v 0]` (rotation),
   `yex x := ![Real.cos x, Real.sin x]`. Verify the order-1
   residual is `O(h²)`.
3. **Sanity check that scalar case still discharges**: invoke
   `lem_311A_order_one_poly` at `N := ℝ` and confirm the resulting
   statement is equivalent to (or implies) cycle 248's
   `lem_311A_order_one`.

Witness 3 is the most useful for confirming the lift is faithful;
witnesses 1 and 2 are the "genuinely polymorphic" cases. Ship all
three if time permits, or witness 3 alone as the minimum.

## D. Mathlib hooks (verify before relying on them)

Each of these should `lean_local_search` or `lean_hover_info` cleanly
before you commit to using it. If any has drifted or doesn't exist,
file the gap as a sub-issue and adapt the proof.

| Hook | Expected signature | Used at |
|---|---|---|
| `taylor_isLittleO` | `{f : ℝ → E} ...` for `[NormedAddCommGroup E] [NormedSpace ℝ E]` | Step 1 (verified at `Mathlib/Analysis/Calculus/Taylor.lean:239`) |
| `taylor_within_apply` | `(f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) → ...` | Step 2 (verified at `Mathlib/Analysis/Calculus/Taylor.lean:114`) |
| `iteratedDeriv_one` | `iteratedDeriv 1 f = deriv f` (for `f : ℝ → E`) | Step 3 |
| `HasDerivAt.deriv` | `HasDerivAt f f' x → deriv f x = f'` (vector-valued) | Step 3 |
| `IsLittleO.comp_tendsto` | standard | Step 4 |
| `Asymptotics.isBigO_const_mul_self` | `(fun x => c • f x) =O[l] f` (verify smul form) | Step 5 |
| `IsLittleO.isBigO` | standard | Step 5 |

**Critical pre-flight check**: confirm `Asymptotics.isBigO_const_mul_self`
or its equivalent fires for the `smul`-by-`N` case (the quadratic
Taylor remainder coefficient is now a vector, not a scalar). If the
exact lemma name is different in the current Mathlib, search via
`lean_loogle "_ • _ =O[_]"` for the right form. If only the `mul`
version exists, you may need a wrapper `have : ‖(1/2 : ℝ) • c‖ ≤
(1/2) * ‖c‖ := norm_smul_le _ _` plus a scalar-bound argument on
`‖h^2 • c‖ ≤ ‖c‖ · ‖h‖^2`.

## E. What NOT to do

* **Do NOT introduce sorries.** The cycle 149/200/201/263-style
  rollback precedent is in force: sorry-first scaffolds with no
  single-cycle close path get reverted. If the polymorphic port
  stalls, fall back to §F below; do not leave a `sorry` in
  `Section311.lean`.

* **Do NOT modify `lem_311A_order_one`** (the existing scalar
  theorem at line 120). Add `lem_311A_order_one_poly` as a NEW
  theorem (with the `_poly` suffix), placed immediately after the
  scalar version. This preserves the existing 5 orders of scalar
  Taylor lemmas (cycles 248/256/257/258/259) which downstream code
  may consume.

* **Do NOT lift `lem_311A_order_two`/`_three`/`_four`/`_five` this
  cycle.** Those proofs use scalar-specific chain rule
  (`deriv f y₀ * f y₀` for order 2, Bell-polynomial expansions for
  higher orders). Lifting them to polymorphic requires the
  `iteratedFDeriv 1 ↔ fderiv` bridge (cycle 260 scoping doc §C.4 R4,
  HIGH risk). Order-1 is the only Phase D piece in scope for cycle
  265.

* **Do NOT attempt Phase A.3 (TreeAutomorphism strengthening).**
  Per the cycle 263 rollback note and `lem_310B_plan.md` §6,
  this is multi-cycle work that requires a `mutual` block through
  `List RootedTree`. Plan before attempting.

* **Do NOT attempt lem:342A property (342a).** Mathlib has no
  orthogonal-Legendre infrastructure (only `LegendreSymbol`,
  number-theoretic). Building from scratch is multi-cycle.

* **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
  44+ consecutive GPFS timeouts since cycle 182; skip per
  `cycle_182_gpfs_slowness.md`.

* **Do NOT raise `maxHeartbeats` above 200000.** If a tactic stalls,
  decompose into named intermediate identities.

* **Do NOT modify `scripts/autonomous_loop.py`.** The empty-stuck-on
  phantom that surfaced this cycle is loop-maintainer territory per
  `tautology_scanner_false_positives.md` §D3.

* **Do NOT name the deliverable as a textbook entity closure.** The
  polymorphic order-1 case is *infrastructure for* `lem:310B`, not
  `lem:311A` itself. Keep the name `lem_311A_order_one_poly` and do
  NOT update `lean_status.json` for `lem:311A` (already at `partial`
  via the scalar chain) or `lem:310B`. The entity status is unchanged.

## F. Fallback plan (only if Step 5 stalls)

If `Asymptotics.isBigO_const_mul_self` doesn't fire cleanly for the
`smul` case after 30 minutes of investigation, the fallback is to
ship a more restricted polymorphic version: require `[Module ℝ N]`
and `[NormSMulClass ℝ N]` (whichever Mathlib uses for the
`‖c • v‖ ≤ ‖c‖ · ‖v‖` bound), then close via explicit norm-bound
chase using `norm_smul_le`. This adds ~20 LOC but stays axiom-clean.

If that ALSO stalls, the absolute fallback is to leave the
polymorphic lift for cycle 266 and instead:

* **Ship three new non-vacuity examples for the EXISTING scalar
  `lem_311A_order_one`** at concrete `f`/`yex` triples (e.g.
  `f := fun y => y`, `yex := Real.exp`; `f := fun y => -y`, `yex :=
  fun x => Real.exp (-x)`; `f := fun y => 0`, `yex := fun _ => y₀`).
  This is genuine cycle content (validates the cycle 248 theorem on
  canonical small-ODE cases) and ships ~30 LOC of axiom-clean
  witnesses. NOT cherry-picking — it exercises the scalar theorem on
  real ODE examples that the existing file does not.

## G. Aristotle option

This is a clean target for Aristotle if you want to batch-submit and
focus on `simp`-set tuning manually. Submit the polymorphic theorem
statement + cycle 248's scalar proof as in-context template, with
the prompt "lift to polymorphic codomain N : Type* with
[NormedAddCommGroup N] [NormedSpace ℝ N]". Single 30-minute poll
discipline per CLAUDE.md.

If Aristotle returns clean, incorporate verbatim (after checking it
doesn't depend on Mathlib hooks that don't exist in our pinned
version).

## H. Update plan.md and lean_status.json

* `lean_status.json` for `lem:311A`: cycle reference bump to 265,
  status remains `partial` (no entity closed).
* `plan.md` `lem:311A` row: append cycle 265 note documenting the
  polymorphic order-1 lift.

DO NOT mark `lem:311A` as `formalized` — the full textbook statement
requires labelled-tree quotients (`def:300C` infrastructure, still
deferred to Phase A.2.1 of `lem_310B_plan.md`). The polymorphic
order-1 lift is one more incremental step toward Phase D.

## I. Cycle 266 outlook

Once cycle 265 ships polymorphic order-1, cycle 266's planner has
three credible directions:

1. **Polymorphic order-2** (Phase D.1 continuation) — needs the
   `iteratedFDeriv 1 ↔ fderiv` bridge; HIGH risk but is the natural
   next step.
2. **Phase E.1** — restate `lem_311A_order_two`/etc. in the
   `TruncatedRootedTree 2` partial-sum form (1 cycle if D.1
   complete).
3. **Pivot to a fresh single-cycle entity** — e.g., one of the
   short Ch.5 `[ ]` rows.

Cycle 266 should weigh the §310 roadmap velocity vs textbook
breadth — the same decision cycle 264 worker flagged.

## J. Confidence level

This strategy targets a single, well-scoped, mechanically-derivable
extension of cycle 248's already-shipped scalar proof, with all
critical Mathlib hooks verified (`taylor_isLittleO` for `ℝ → E`,
`bseriesOrderOne` already polymorphic). Single-cycle close is
high-confidence. The fallback plan (§F) ensures cycle 265 ships
non-trivial value even if Step 5 stalls. No sorry-first scaffold
should be required.

Trust the cycle 248 proof structure. Port mechanically. Verify each
Mathlib hook with `lean_local_search` before committing the line.
Ship axiom-clean.
