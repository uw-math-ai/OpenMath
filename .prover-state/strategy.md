# Cycle 302 strategy

## §A — Status check

**Cycle 301 SHIPPED `lem:342A` complete** (commit `4d07773`).
`butcherShiftedLegendre_n_distinct_real_zeros` integrated axiom-clean
into `OpenMath/Chapter3/Section342.lean` (line ~6090), with generic
polynomial-sign helpers in
`OpenMath/Chapter3/Section342DistinctRootsHelpers.lean`. All seven
clauses (342a)–(342g) of Butcher's shifted Legendre characterisation
are now formalized over cycles 271–301. `lean_status.json` correctly
shows `lem:342A` as `formalized`; `plan.md` shows `[x]`.

**Supervisor score `-1` on cycle 301 is a tautology-scanner false
positive — do not chase it.**

Direct grep verification at HEAD:

```
$ rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' \
    OpenMath/Chapter3/Section342.lean \
    OpenMath/Chapter3/Section342DistinctRootsHelpers.lean
(no matches)
```

The only `exact h_*` line in `Section342.lean` is line 1366
`exact h_diff.trans (Finset.sum_eq_zero …)` — this is genuine work
(`.trans (...)` application), NOT a vacuous closer, and the scanner
regex does NOT match (`\s*$` requires end-of-line after `h_\w+`, but
`.trans` follows). The two `h_integrand_nonzero` hits at lines 5963 /
6030 are `obtain ⟨…⟩ := h_integrand_nonzero` destructurings — none
of the three patterns fire on these.

This matches the pattern documented across cycles 010 / 013 / 014 /
015 / 121 / 154 / 243–247 / 248 (see
`.prover-state/issues/tautology_scanner_false_positives.md` and the
six "phantom verdict" consultant notes in
`.prover-state/issues/consultant_advice_cycle_*.md`). Standing
recommendation applies: do NOT modify `scripts/autonomous_loop.py`
(loop-maintainer territory); do NOT rename anything in the cycle 301
deliverables; do NOT revert any cycle 301 work.

**Cycle 302 worker: re-run the grep above to confirm no new real
tautology slipped in. If empty, the score is a phantom — pivot
directly to §B.**

## §B — Cycle 302 target: `lem:342B` Phase A.1

Per cycle 301 task results §"Suggested next approach", with `lem:342A`
closed the natural next §342 entity is **`lem:342B`** (Gaussian
quadrature exactness on `[0, 1]` with `s` nodes from the zeros of
`P_s^*`). Textbook statement (Butcher §342, p. 237, equation 342h):

> Let `c₁, c₂, …, cₛ` denote the zeros of `P_s^*`. Then there exist
> positive numbers `b₁, b₂, …, bₛ` such that
>     `∫₀¹ φ(x) dx = ∑_{i=1}^s bᵢ φ(cᵢ)`
> for any polynomial of degree less than `2s`. The `bᵢ` are unique.

The JSON's `transitive_dependencies` lists `thm:342C` (Gaussian
quadrature order conditions equivalence — unformalised, multi-cycle).
**This is a JSON extraction artifact**: the textbook proof of
`lem:342B` does NOT use `thm:342C` — it's pure polynomial division
+ orthogonality reasoning, depending only on `lem:342A` (now closed)
and Mathlib's polynomial machinery. Worker should NOT block on
`thm:342C` and should NOT try to formalise the order-conditions
framework (`B(2s)`, `C(s)`, `D(s)`, `E(s,s)`, `G(2s)`) — that's the
entirely different and much larger §321 / §310 cluster work.

### Textbook proof outline (Butcher §342)

1. Choose `b₁, …, bₛ` so (342h) holds for any `φ` of degree `< s`.
   Since `c₁, …, cₛ` are distinct, the choice is unique (Vandermonde).
2. For `φ` of degree `< 2s`, write `φ = P_s^* · Q + R` with
   `deg Q, deg R ≤ s − 1`. Then `∫P_s^* · Q = 0` by (342a)
   orthogonality (applied with `m = s`, since `deg Q < s`).
   So `∫φ = ∫R = ∑ bᵢ R(cᵢ) = ∑ bᵢ φ(cᵢ)` (last step uses
   `P_s^*(cᵢ) = 0`).
3. Positivity: set `φ(x) = (P_s^*(x) / (x − cᵢ))²`. Then `φ` has
   degree `2(s−1) < 2s`, `φ(cⱼ) = 0` for `j ≠ i`, and `φ(cᵢ) > 0`.
   So `0 < ∫₀¹ φ = bᵢ · φ(cᵢ)` ⇒ `bᵢ > 0`.

### Phase decomposition (multi-cycle scope)

This is **a multi-cycle target**. Decompose into independent
single-cycle phases. Cycle 302 deliverable is **Phase A.1 only**.
Do NOT attempt the full lemma in one cycle.

* **Phase A.1 (cycle 302 target)** — extract canonical zero
  enumeration `butcherShiftedLegendre_zeros (n : ℕ) : Fin n → ℝ`
  plus 3 spec lemmas. ~50–80 LOC.
* **Phase A.2 (cycle 303)** — define quadrature weights (via
  Lagrange interpolation integrals) and prove uniqueness for
  `deg < s`.
* **Phase A.3 (cycle 304)** — prove exactness for `deg < 2s` via
  polynomial division + (342a). Aristotle-suitable.
* **Phase A.4 (cycle 305)** — prove positivity via the
  `(P_s^*/(X − cᵢ))²` witness.
* **Phase A.5 (cycle 306)** — assemble `lem:342B` headline.

### Phase A.1 concrete deliverables for cycle 302

In `OpenMath/Chapter3/Section342.lean`, appended at the end (after
the cycle 301 `_card_le` / `_card_ge` / `_n_distinct_real_zeros`
block), ship **four new symbols**, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

1. **`butcherShiftedLegendre_zeros (n : ℕ) : Fin n → ℝ`**
   (`noncomputable def`). The canonical strictly-increasing
   enumeration of the `n` distinct real zeros of `P_n^*` in
   `(0, 1)`. Define via `Classical.choose` on cycle 301's
   `_n_distinct_real_zeros` followed by `Finset.orderEmbOfFin`
   (preferred over `Finset.equivFin` — gives strict-monotonicity
   for free).

   Recommended implementation sketch (verify Mathlib lemma names
   with `lean_local_search` before committing):

   ```lean
   noncomputable def butcherShiftedLegendre_zeros (n : ℕ) : Fin n → ℝ :=
     have h := butcherShiftedLegendre_n_distinct_real_zeros n
     have h1 : (Classical.choose h).card = n := (Classical.choose_spec h).1
     fun i => (Classical.choose h).orderEmbOfFin h1 i
   ```

   If `orderEmbOfFin` is named differently in current Mathlib (verify
   via `lean_local_search "orderEmbOfFin"` early), fall back to:

   ```lean
   noncomputable def butcherShiftedLegendre_zeros (n : ℕ) : Fin n → ℝ :=
     have h := butcherShiftedLegendre_n_distinct_real_zeros n
     have h1 : (Classical.choose h).card = n := (Classical.choose_spec h).1
     fun i => ((Classical.choose h).equivFin.symm ⟨i, h1 ▸ i.isLt⟩).val
   ```

   The `orderEmbOfFin` form is preferred.

2. **`butcherShiftedLegendre_zeros_mem_Ioo (n : ℕ) (i : Fin n) :
   butcherShiftedLegendre_zeros n i ∈ Set.Ioo (0 : ℝ) 1`** —
   destructure `Classical.choose_spec` (second conjunct) at the
   element produced by `orderEmbOfFin i`, which is by construction
   a member of the chosen `Finset`.

3. **`butcherShiftedLegendre_zeros_isRoot (n : ℕ) (i : Fin n) :
   (butcherShiftedLegendre n).eval (butcherShiftedLegendre_zeros n i)
   = 0`** — destructure `Classical.choose_spec` (third conjunct).

4. **`butcherShiftedLegendre_zeros_injective (n : ℕ) :
   Function.Injective (butcherShiftedLegendre_zeros n)`** — from
   `OrderEmbedding.injective` if using `orderEmbOfFin`, or from
   `Equiv.injective` + underlying-set distinctness otherwise.

### Non-vacuity (P2, cycle 302)

Two small `example`s exercising the new symbols on concrete `n`:

* **`n = 1`** (REQUIRED): `butcherShiftedLegendre_zeros 1 ⟨0, by omega⟩
  = 1/2`. May not be by `rfl` (depends on `orderEmbOfFin` reduction);
  if not, prove via cycle 294's `butcherShiftedLegendre_one_root`
  membership + zero-uniqueness on the singleton root set.

* **`n = 2`** (OPTIONAL, stretch): the explicit Gauss–Legendre 2-point
  nodes `(3 ± √3) / 6 ∈ (0, 1)`. Use cycle 294's
  `butcherShiftedLegendre_two_roots` for the underlying set; the
  strict-monotone order follows from `(3 − √3)/6 < (3 + √3)/6` via
  `nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)]`.

If the `n = 2` witness proves too fiddly within the cycle budget,
ship only the `n = 1` witness and flag the `n = 2` form for cycle 303
as an add-on.

### Lean tactics — Mathlib hooks to verify before use

Run `lean_local_search` / `lean_loogle` at cycle start to confirm
names; the names below are best-effort accurate but Mathlib has had
recent renaming churn:

| Goal | Candidate lemma |
|---|---|
| `Finset.orderEmbOfFin` (canonical ordered enumeration of a finset of size `n`) | `Finset.orderEmbOfFin` (`Mathlib.Order.OrderBoundedFinset`) |
| `OrderEmbedding.injective` | `OrderEmbedding.injective` or `StrictMono.injective` |
| `Classical.choose_spec` on a triple-conjunct existential | standard; destructure with `.1` / `.2.1` / `.2.2` or `obtain` |
| `Set.mem_Ioo` | standard |
| `Polynomial.IsRoot` ↔ `Polynomial.eval = 0` | `Polynomial.IsRoot.def` |
| `Finset.orderEmbOfFin_mem` (its image lies in the underlying set) | search via `lean_local_search "orderEmbOfFin"` for the membership-spec lemma |

### Risk profile

| Risk | Mitigation |
|---|---|
| `orderEmbOfFin` API drift / name change | Confirm via `lean_local_search "orderEmbOfFin"` before committing; fall back to `Finset.equivFin` if needed |
| Cycle 301's existential is over `Finset ℝ`, not `Finset (Set.Ioo 0 1)` — coercion friction | Both `card` + membership specs come from the same `Classical.choose_spec`; destructure all three conjuncts in one shot |
| `n = 0` edge case (vacuous `Fin 0`) | `orderEmbOfFin` handles `n = 0` trivially (empty function); no special-casing needed |
| `n = 1` example's `rfl` reduction fails on `orderEmbOfFin` | Use the singleton-Finset uniqueness route: `Finset.singleton_iff_unique` + `butcherShiftedLegendre_one_root` |

## §C — DO NOT attempt this cycle

1. **DO NOT attempt the full `lem:342B`** (uniqueness + exactness +
   positivity). That is 4–5 cycles of work; cycle 302 ships Phase A.1
   only.

2. **DO NOT formalise `thm:342C`** (Gaussian Quadrature Order
   Conditions Equivalence). It is listed in `lem:342B`'s
   `transitive_dependencies` but the textbook proof of `lem:342B`
   does NOT use it. `thm:342C` requires the order-conditions
   framework (`B(2s)` / `C(s)` / `D(s)` / `E(s,s)` / `G(2s)`) which
   depends on `lem:310B` Phase A.3+ — that's multi-cycle
   infrastructure scoped separately in
   `.prover-state/issues/lem_310B_plan.md`.

3. **DO NOT modify `scripts/autonomous_loop.py`.** The cycle 301
   score=-1 is a tautology scanner false positive (see §A). The
   scanner over-firing is loop-maintainer territory per
   `tautology_scanner_false_positives.md` and the six "consultant
   advice" issue files. Worker rule per CLAUDE.md.

4. **DO NOT rename any cycle 301 symbols** in response to the
   scanner verdict. The grep confirms zero real matches; renaming
   would be cosmetic churn that propagates into the codebase.

5. **DO NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
   43+ consecutive GPFS timeouts since cycle 182 (see
   `.prover-state/issues/cycle_182_gpfs_slowness.md`). Skip §441
   work entirely; it remains blocked on cluster-admin remediation.

6. **DO NOT submit Aristotle this cycle.** Phase A.1 is small
   (~50–80 LOC) and entirely mechanical — `Classical.choose_spec`
   destructuring plus a couple of order-embedding API calls.
   Aristotle has no advantage on this shape. Save the slot for
   Phase A.3 (the exactness-via-polynomial-division step is
   genuinely Aristotle-suitable — schedule for cycle 304).

7. **DO NOT introduce `sorry` / `axiom` / `constant`.** Cycles 138 /
   149 / 200 / 201 rollback precedents apply: sorry-first scaffolds
   for multi-cycle work get rolled back when they don't close.
   Phase A.1 is single-cycle axiom-clean or skipped entirely.

8. **DO NOT raise `maxHeartbeats` above 200000.** If
   `orderEmbOfFin` reduction is slow, decompose via `set` /
   `have hf := ...` rather than bumping.

9. **DO NOT delete the cycle 294–300 empirical anchors**
   (`butcherShiftedLegendre_{one,three,five,seven,nine,eleven,
   thirteen}_roots`). They are retained as defensive regression
   witnesses providing explicit closed-form sub-interval brackets
   that the existential headline lacks (per cycle 301 task results
   §D.6).

10. **DO NOT bump `lean_status.json` for `lem:342B`.** Phase A.1 is
    infrastructure, not the lemma itself. Status stays `unformalized`
    until cycle 306 Phase A.5 lands.

## §D — Faithfulness check (cycle 302)

For Phase A.1's four new symbols:

* **`butcherShiftedLegendre_zeros`** is a `def`, NOT a textbook
  entity (Butcher names the zeros `c₁, …, cₛ` informally but does
  not define them as an indexed family). Cycle 302's
  `butcherShiftedLegendre_zeros n i` realises this family via a
  noncomputable canonical choice; this is **Lean engineering, not a
  faithfulness deviation**. Document in the docstring that this is
  the canonical strictly-increasing enumeration of the n distinct
  zeros from cycle 301's existential.

* **`butcherShiftedLegendre_zeros_mem_Ioo` / `_isRoot` /
  `_injective`** are direct consequences of cycle 301's
  `_n_distinct_real_zeros` (the existential's three conjuncts) plus
  `OrderEmbedding`'s strict monotonicity. No textbook content beyond
  the (342g) clause already shipped. Stating them as separate named
  theorems is for downstream ergonomics; this is standard Lean
  practice (cf. cycle 196's `IsPReducible.sBar` /
  `IsPReducible.partition` destructor API).

* **Hypothesis-strength check**: all four symbols are unconditional
  in `n : ℕ` (matching the textbook's "n = 0, 1, 2, …" quantification).

* **Tautology / identity check**: none of the four symbols re-export
  a hypothesis or apply `exact h`. The `_zeros` def constructs a
  canonical witness via `orderEmbOfFin`; the three specs destructure
  `Classical.choose_spec` and apply `OrderEmbedding`-level lemmas.
  No `exact` closers on hypotheses with `h_` prefix anywhere.

## §E — Tooling and ordering

1. **First**: re-verify cycle 301 is at HEAD and axiom-clean:
   ```bash
   git log -1 --format='%H %s'  # expect 4d07773 Cycle 301 ...
   wc -l OpenMath/Chapter3/Section342.lean  # expect ~6090
   grep -c sorry OpenMath/Chapter3/Section342.lean  # expect 0
   echo '#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_n_distinct_real_zeros' \
     | lake env lean --stdin OpenMath/Chapter3/Section342.lean
   # expect [propext, Classical.choice, Quot.sound] only
   ```
   If any check fails, escalate; do not proceed to Phase A.1.

2. **Second**: re-grep for tautology patterns (§A above). Confirm
   zero matches. Move on.

3. **Third**: read cycle 301's
   `butcherShiftedLegendre_n_distinct_real_zeros` signature
   (~line 6090) to confirm the existential shape:
   ```
   ∃ xs : Finset ℝ,
     xs.card = n ∧
     (∀ x ∈ xs, x ∈ Set.Ioo 0 1) ∧
     (∀ x ∈ xs, (butcherShiftedLegendre n).eval x = 0)
   ```

4. **Fourth**: ship Phase A.1's four symbols + non-vacuity example(s).
   Run `lake env lean OpenMath/Chapter3/Section342.lean`; expect
   warm-rebuild ~30s (only the appended block elaborates fresh).
   Run `#print axioms` on each new symbol.

5. **Fifth**: do NOT update `extraction/formalization_data/lean_status.json`
   for `lem:342B` (status stays `unformalized`).

6. **Sixth**: do NOT update `plan.md`'s `lem:342B` row (still `[ ]`).

7. **Seventh**: write `task_results/cycle_302.md` per the standard
   format, documenting Phase A.1 deliverables + Phase A.2 entry
   point for cycle 303.

## §F — Cycle 303+ outlook (informational)

* **Cycle 303 (Phase A.2)**: Define quadrature weights via Lagrange
  interpolation integrals
  `butcherShiftedLegendre_quadratureWeights (n : ℕ) : Fin n → ℝ`
  with `bⱼ := ∫₀¹ Lⱼ(x) dx` where
  `Lⱼ(x) = ∏_{k ≠ j} (x - cₖ) / (cⱼ - cₖ)`. Prove exactness for
  `deg < n` polynomials (interpolation is exact at `n` distinct
  nodes for `deg < n` polynomials). ~100–150 LOC.

  Alternative: Vandermonde via `Matrix.det_vandermonde`. Lagrange is
  cleaner; prefer it unless Mathlib's Lagrange-interpolation lemmas
  are missing.

* **Cycle 304 (Phase A.3)**: Polynomial division `φ = P_s^* · Q + R`
  with `deg Q, deg R < s`. Apply (342a) orthogonality to
  `∫₀¹ P_s^* · Q = 0`, derive `∫φ = ∫R = Σ bᵢ R(cᵢ) = Σ bᵢ φ(cᵢ)`.
  ~150 LOC. **Aristotle-suitable** (polynomial division +
  integration + (342a) is structural).

* **Cycle 305 (Phase A.4)**: Positivity. The polynomial
  `(P_s^*(X) / (X − cᵢ))²` has degree `2(s − 1) < 2s`, so Phase A.3's
  exactness applies. Plug in and derive `bᵢ > 0`. ~80 LOC.

  Mathlib hook: `Polynomial.div_X_sub_C` or hand-rolled. Confirm
  `P_s^*(X) = (X − cᵢ) · Qᵢ(X)` factorization is exact (no
  remainder, since `cᵢ` is a root) — uses `Polynomial.dvd_iff_isRoot`.

* **Cycle 306 (Phase A.5)**: Assemble `lem:342B` headline. Existential
  packaging plus uniqueness. ~50 LOC. Update `lean_status.json` /
  `plan.md` to mark `lem:342B` `formalized`.

Total: 5 cycles. Mirrors the `lem:342A` ladder (cycles 271–301, ~30
cycles) but much shorter because the polynomial-only proof avoids
real-analysis machinery.

## §G — Summary directive

1. (5 min) Verify cycle 301 health per §E steps 1–2.
2. (rest of cycle) Ship Phase A.1 of `lem:342B` per §B: four new
   symbols (`butcherShiftedLegendre_zeros` + 3 specs) plus 1–2
   non-vacuity examples, in `OpenMath/Chapter3/Section342.lean`.
3. Axiom-clean target. ~50–80 LOC. Sorry count stays 0.
4. No `lean_status.json` / `plan.md` updates for `lem:342B`
   (still `unformalized`).
5. Write `task_results/cycle_302.md` documenting Phase A.1
   deliverables and Phase A.2 entry point.

Cycle 302 is infrastructure-only on `lem:342B`. Phase A.1 establishes
the canonical zero enumeration that Phases A.2–A.5 will consume.
