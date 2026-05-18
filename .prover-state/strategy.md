# Cycle 373 strategy

## §A. State of play

Cycle 372 shipped the **7th** closed-form witness in the §422 Phase D.3.b
Step 2 ladder:

- `elementaryWeightQ_phi_inv_mkVertexCherry` — `Φ_{η_q⁻¹}(mk [vertex, cherry])
  = v⁴ − 3v²·c + c² + v·b' + v·m − Φ_η(mk [vertex, cherry])`. The **first
  asymmetric order-4 tree** (heterogeneous children: one leaf + one
  cherry-subtree).
- `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero` — the m=0
  Sub-lemma A corollary specialised at this tree.

Witness library now has **7 trees**:

| Tree | Cycle | Order |
|---|---|---|
| `vertex` | 341 (P3, `_zpow_vertex`) | 1 |
| `cherry` | 367 | 2 |
| `broom₃` (= `mk [vertex, vertex]`) | 368 | 3 |
| `mk [cherry]` | 369 | 3 |
| `bushy` (= `mk [vertex, vertex, vertex]`) | 370 | 4 |
| `mk [broom₃]` | 371 | 4 |
| `mk [vertex, cherry]` | 372 | 4 |

§422 axiom-clean streak: **38 consecutive cycles** (336–372). Sorry
count remains 5 lines / 1 code sorry (the grandfathered cycle 365
Sub-lemma A body at `Section422.lean:2279`).

The cycle 372 worker's recommendation, in their own words:

> Cycle 372 worker strongly recommends Option 3 for cycle 373: the
> witness library is at the natural point of diminishing returns,
> and inductive scoping is the path off the treadmill toward Phase
> D.3.d and Phase E sealing of `def:422B`.

I am following that recommendation.

## §B. Cycle 373 deliverable

**Primary (markdown-only):** Write a multi-cycle scoping doc for the
**inductive Sub-lemma A proof** of `powRep_sum_eq_of_strict_subtree_agreement`,
distilling the closed-form pattern revealed by cycles 367–372's witness
ladder into a concrete phased plan.

The doc is `def:422B`'s analogue of `lem_310B_plan.md` (cycle 260), but
focused specifically on the remaining Sub-lemma A body. It will guide
cycle 374+ workers through the multi-cycle inductive attack without
re-scoping.

**No Lean code edits this cycle.** Preserve the 38-cycle axiom-clean
streak. The Sub-lemma A body remains sorry'd (grandfathered); cycle 373
ships the **plan**, not the proof.

## §C. The closed-form pattern (what cycle 373 must distill)

Reading cycles 367–372's seven witnesses end-to-end reveals a uniform
structural pattern that the inductive proof must encode:

### §C.1 Empirical pattern

For every tree `t = mk children` shipped so far, the closed form takes
the shape:

```
Φ_{η_q⁻¹}(t) = (polynomial in Φ_η at strict subtrees of t) − Φ_η(t)
```

The polynomial part depends only on `Φ_η` at trees **strictly smaller**
than `t` (in `RootedTree.order`); the `−Φ_η(t)` term is the unique
appearance of `Φ_η(t)` itself.

**Per-tree summary** (writing `v, c, b', m, B, M, V` for
`Φ_η(vertex), cherry, broom₃, mk[cherry], bushy, mk[broom₃], mk[vertex,cherry]`):

| `t` | Closed form |
|---|---|
| `vertex` | `−v` (cycle 341 P3: `Φ_{η^{-1}}(vertex) = −Φ_η(vertex)`) |
| `cherry` | `v² − c` (cycle 367) |
| `broom₃` | `−v³ + 2vc − b'` (cycle 368) |
| `mk [cherry]` | `−v³ + 2vc − m` (cycle 369) |
| `bushy` | `v⁴ − 3v²·c + 3v·b' − B` (cycle 370) |
| `mk [broom₃]` | `v⁴ − 3v²·c + v·b' + 2v·m − M` (cycle 371) |
| `mk [vertex, cherry]` | `v⁴ − 3v²·c + c² + v·b' + v·m − V` (cycle 372) |

### §C.2 Origin of the pattern

It comes from cycle 358's `elementaryWeightQ_phi_inv_mk`:

```
Φ_{η_q⁻¹}(t) = − Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t
```

where `M.inverse.A i j = M.A i j − M.b j`. Unfolding
`derivativeWeightWithSrc M.inverse i (mk children)` recursively reveals
that each child contributes a factor that mixes `M.inverse.elementaryWeight`
at the child's subtree (which closed-form-equals the inverse closed
form at that subtree) with sums against `M.A` (which collapse into
elementary weights of `t`'s strict subtrees via cycle 226's
`compose_elementaryWeight_decomp`).

So the closed form for `Φ_{η_q⁻¹}(t)` is a polynomial in:
- `Φ_η(s)` for every strict subtree `s` of `t`, AND
- `Φ_η(t)` itself, appearing once with coefficient `−1`.

### §C.3 What this means for Sub-lemma A

Sub-lemma A asks: under closed-subtree agreement (`Φ_η(s) = Φ_{η'}(s)`
for all `s.order ≤ t.order`), are the two `Φ_{η^(-(m+1))}(t)` values
equal?

For m=0 (the cycles 367/368/369/370/371/372 corollaries), the
**closed form** lets us answer immediately: both sides expand to the
same polynomial in the same elementary weight values, so they're
equal.

For general m ≥ 1, we don't have a closed form yet — but the
**same structural argument should apply** if we can:

1. Establish a recursive closed-form for `Φ_{η^(-(m+1))}(t)` at general
   `m` (likely via `Group.pow` + cycle 359's `powRep` + cycle 358's
   `_inv_mk`).
2. Argue that this closed form is polynomial in
   `{Φ_η(s) : s.order ≤ t.order}`.
3. Apply the closed-subtree agreement hypothesis to conclude equality.

This is the structure cycle 373's scoping doc must distill into a
concrete phased plan.

## §D. Concrete file to produce

**File path:** `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`

(A **new file**, distinct from `def_422B_phase_D_3_scoping.md`. The
existing scoping doc remains as the cycle-365+ Sub-lemma B / Step 2
scoping; the new doc focuses on closing Sub-lemma A's body via the
inductive route validated by cycles 367–372's witnesses.)

**Length:** 500–800 lines markdown. No Lean code (other than
illustrative signatures in fenced ```lean blocks).

**Template:** Follow `lem_310B_plan.md`'s structure verbatim
(`.prover-state/issues/lem_310B_plan.md`, cycle 260 produced). The
sections are:

1. **§1 Status** (cycle 373, scoping doc only)
2. **§2 Blocker** — distill the cycle 365 Sub-lemma A body sorry into
   one paragraph; cite the cycle 366 worker's heterogeneity analysis
   and the cycles 367–372 witness ladder
3. **§3 Textbook source** — Butcher's §422 prose is silent on this
   (the proof is in our Lean encoding, not the textbook). Cite the
   relevant pieces from the cycle 358 `_inv_mk` formula and cycle 359
   `powRep` recursive structure
4. **§4 Distilled mathematical content** — §C.1 / §C.2 / §C.3 above,
   formalised and elaborated. State the conjectured general form
5. **§5 Project-hook inventory** — list every cycle 358/359/360/361/
   362/365/367/368/369/370/371/372 deliverable that the inductive proof
   will consume. Include exact line numbers and namespaces (verify by
   `grep -n` against `OpenMath/Chapter3/Section381.lean` and
   `OpenMath/Chapter4/Section422.lean` at HEAD)
6. **§6 Gap inventory** — what infrastructure is **missing** and must
   be built before the inductive proof can close. Likely gaps:
   - A general `inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ`
     definition (recursive on `RootedTree.order` via cycle 343
     `WellFoundedRelation`)
   - A theorem
     `elementaryWeightQ_phi_inv_mk_eq_inversePolynomial`:
     `Φ_{η_q⁻¹}(t) = inversePolynomial t (Φ_η)` for all trees and
     classes
   - A monotonicity lemma: `inversePolynomial` depends only on its
     input function's values at trees of `order ≤ t.order` (the
     **load-bearing** Sub-lemma A content)
   - Extension to general m via `powRep`
7. **§7 Phase decomposition** — single-cycle deliverables, each
   axiom-clean target. Suggested phases:
   - **Phase α** (1 cycle): define `inversePolynomial` via well-founded
     recursion on `RootedTree.order`. Non-vacuity: 4–7 small-tree
     evaluations matching the cycle 341/367/368/369/370/371/372 closed
     forms.
   - **Phase β** (1–2 cycles): prove
     `elementaryWeightQ_phi_inv_mk_eq_inversePolynomial`. The proof
     mirrors the per-tree closed-form expansions but generalised to
     arbitrary trees via the well-founded recursion. Multi-step:
     - β.1: derive the recursive identity from cycle 358 `_inv_mk`
     - β.2: prove by strong induction on `t.order`
   - **Phase γ** (1 cycle): prove the strict-subtree-monotonicity
     lemma for `inversePolynomial`. This is structural induction on
     the recursion's definitional unfold; agreement on strict subtrees
     forces agreement on the recursive output.
   - **Phase δ** (1 cycle): extend to general `m` via `powRep`.
     Closed form `Φ_{η_q^(-(m+1))}(t) = inversePolynomial_pow (m+1) t (Φ_η)`
     (or equivalent), where `inversePolynomial_pow` is built from
     `inversePolynomial` and cycle 359's `powRep`.
   - **Phase ε** (1 cycle): close Sub-lemma A's body by composing
     Phases α–δ. Total: roughly 5 cycles for the full close.
8. **§8 Risk assessment** — per-phase risk, Mathlib hooks needed,
   Aristotle suitability
9. **§9 Cycle 374 entry point** — concrete starter task for the next
   worker (the Phase α deliverable)
10. **§10 Cross-references** — `def_422B_path.md`, `def_422B_phase_D_3_scoping.md`,
    `lem_310B_plan.md` (template), cycles 358/359/360/361/362/365/
    367–372 task results

### §D.1 Required cross-checks against HEAD

Before writing each numbered phase, verify by reading
`OpenMath/Chapter4/Section422.lean` and `OpenMath/Chapter3/Section381.lean`
that the cited line numbers and namespaces are correct at HEAD `b1bfe32`.

Specifically the scoping doc must cite:
- `OpenMath/Chapter3/Section381.lean` for cycle 358 `elementaryWeightQ_phi_inv_mk`,
  cycle 359 `powRep` / `powRep_quotient_eq`, cycle 362
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
- `OpenMath/Chapter4/Section422.lean` for cycle 360 `linearResidualAt`,
  cycle 361 closed forms, cycle 365 Sub-lemma A statement (the sorry'd
  one), cycle 365 Sub-lemma B (the closed headline), the 7 witnesses
  from cycles 367–372
- `OpenMath/Chapter3/Section301.lean` for cycle 343
  `RootedTree.order_lt_of_mem_children` and the
  `WellFoundedRelation RootedTree := measure RootedTree.order` instance

### §D.2 Required conjecture content (in the new doc's §4)

The scoping doc's central conjecture, which the inductive proof aims
to establish, should be stated precisely:

```
Conjecture (general inverse closed form).
There exists a function inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ,
defined by well-founded recursion on RootedTree.order, such that:

(a) for every η_q : Quotient PhiEquivalent.setoidSigma and every
    t : RootedTree,
        elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t (elementaryWeightQ_phi η_q);

(b) inversePolynomial depends only on the values of its second argument
    at trees s : RootedTree with s.order ≤ t.order. More precisely:
    if f, f' : RootedTree → ℝ agree on every s : RootedTree with
    s.order ≤ t.order, then inversePolynomial t f = inversePolynomial t f'.
```

Sub-lemma A (m=0 case) follows immediately from (a) + (b). The
m ≥ 1 case follows by combining (a) + (b) with cycle 359's `powRep`
recursion.

The seven witnesses from cycles 367–372 verify (a) on small trees.
Phase β of the scoping doc plans the general proof of (a); Phase γ
plans the proof of (b).

## §E. What NOT to do this cycle

- **Do NOT modify any Lean file.** No edits to `Section422.lean`,
  `Section381.lean`, or any other file under `OpenMath/`. The 38-cycle
  axiom-clean streak must be preserved.
- **Do NOT attempt to close the Sub-lemma A body.** That is multi-cycle
  work (Phases α through ε). Cycle 373 plans, doesn't prove.
- **Do NOT ship an 8th closed-form witness** (e.g. `mk [mk [cherry]]`
  or `mk [vertex, vertex, cherry]`). The cycle 372 worker explicitly
  ruled this out as treadmill work with diminishing returns. The
  scoping doc is the **right** next deliverable.
- **Do NOT submit anything to Aristotle.** The scoping work is pure
  markdown; Aristotle adds no value at the scoping phase. (Aristotle
  may be useful inside Phase β.2 or Phase γ in future cycles, but
  that's a cycle 374+ decision.)
- **Do NOT alter `lean_status.json` or `plan.md`.** No status changes
  this cycle; `def:422B` remains `partial`, all relevant rows unchanged.
- **Do NOT edit `scripts/autonomous_loop.py`** or any harness file
  (per CLAUDE.md and the standing
  `.prover-state/issues/tautology_scanner_false_positives.md`).
- **Do NOT spend cycle time on §441 work.** `Section441.lean` remains
  GPFS-blocked (43+ consecutive timeouts since cycle 182, per
  `cycle_182_gpfs_slowness.md`). Skip without further check.

### §E.1 Approaches explicitly known to fail for Sub-lemma A (for the doc to cite)

These are documented in the existing `def_422B_phase_D_3_scoping.md`
under the cycle 366 update; cite them in the new doc's §3 / §6:

- **Direct `Quotient.inductionOn₂` + cycle 358 `_inv_mk` expansion**
  on the two sides: after `Quotient.inductionOn₂` on `η_q` and `η_q'`,
  cycle 358's `_inv_mk` formula expresses each side as a sum over
  representative-specific stage counts (`M.1` vs `M'.1`), which are
  generally **different**. There is no direct way to bridge the two
  heterogeneous sums via cycle 362's substitution lemma (which only
  substitutes the *source* tableau `M₁`, not the *inner* tableau
  `M₂`).
- **Strong induction on `t.order` using cycle 362 alone:** cycle 362's
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` lemma
  bridges the `derivativeWeightWithSrc` sum's substitution behaviour
  but does not handle the *inner-tableau heterogeneity* between
  `M.powRep (m+1)` and `M'.powRep (m+1)`.

The scoping doc's §3 / §6 should document why the closed-form-via-
`inversePolynomial` approach **sidesteps** both of these obstructions:
by reducing both sides to the same `RootedTree → ℝ` polynomial, the
heterogeneous-stage-count issue vanishes — `inversePolynomial t f`
takes a tree and a real-valued function, no stage counts involved.

## §F. Concrete cycle 373 task list

1. **(5 min)** Read `def_422B_phase_D_3_scoping.md` end-to-end to
   understand the current state and locate the cycle 365 Sub-lemma A
   statement.
2. **(10 min)** Read `lem_310B_plan.md` to internalise the template
   structure for multi-phase scoping docs.
3. **(10 min)** Re-read the seven closed-form witnesses in
   `OpenMath/Chapter4/Section422.lean`:
   - `elementaryWeightQ_phi_inv_cherry` (cycle 367)
   - `elementaryWeightQ_phi_inv_broom₃` (cycle 368)
   - `elementaryWeightQ_phi_inv_mkCherry` (cycle 369)
   - `elementaryWeightQ_phi_inv_bushy` (cycle 370)
   - `elementaryWeightQ_phi_inv_mkBroom₃` (cycle 371)
   - `elementaryWeightQ_phi_inv_mkVertexCherry` (cycle 372)
   - Plus cycle 341 P3 `elementaryWeightQ_phi_zpow_vertex` for vertex
4. **(5 min)** Verify line numbers and namespaces for §D.1 by
   `grep -n` against HEAD.
5. **(60–90 min)** Write
   `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` per
   §D's template. Target 500–800 lines.
6. **(10 min)** Cross-check the doc: verify every cited symbol exists
   at HEAD, every line number is correct, every phase has a concrete
   single-cycle deliverable.
7. **(5 min)** Write `.prover-state/task_results/cycle_373.md`
   documenting the deliverable.

Total: ~2 hours focused scoping work. Sorry count unchanged. Axioms
unchanged. Streak preserved.

## §G. Faithfulness check (for the cycle 373 results doc)

This cycle ships no new Lean definitions or theorems, so no per-symbol
faithfulness check is needed. The faithfulness checks documented in
cycles 367–372 task results (each verifying the per-tree closed form
matches a paper-algebra derivation from cycle 358's `_inv_mk`) carry
over unchanged.

The cycle 373 task results should note: "No Lean changes this cycle;
scoping doc only. Faithfulness check N/A."

## §H. Cycle 374+ outlook

If the scoping doc lands cleanly in cycle 373, cycle 374 should ship
**Phase α** (`inversePolynomial` definition + small-tree non-vacuity
witnesses). That should be a single-cycle clean ship: well-founded
recursion via cycle 343's `WellFoundedRelation`, with the recursive
case unfolding cycle 358's `_inv_mk` structure.

If Phase α stalls or splits, cycle 375 resumes; if it lands, cycle 375
ships Phase β.1 (recursive identity from `_inv_mk`), and so on through
Phases β.2, γ, δ, ε over cycles 376–379.

After Phase ε closes Sub-lemma A's body, the cycle 365 Sub-lemma B
headline `linearResidualAt_depends_only_on_strict_subtrees` will
automatically become axiom-clean (the `sorryAx` axiom dependency drops
out). At that point Phase D.3.b is fully closed, Phase D.3.c remains
shipped (α-coefficient non-vanishing under stability — cycle 363's
`sum_i_alpha_ne_zero_of_stable_preconsistent` is already in place),
and Phase D.3.d (the `underlyingOneStepMethod_aux` recursion) can
begin. Phase E (the `def:422B` sealing) closes the chain.

Total horizon: cycles 374–380 for Sub-lemma A inductive close + Phase
D.3.d recursion. Phase E sealing of `def:422B` projected for **cycle
381 or 382**, roughly 9–10 cycles from now. The cycle 373 scoping doc
is the load-bearing prep that makes this horizon concrete.

## §I. Discovery slot

If, while reading the seven witnesses, you notice a structural pattern
not captured in §C.1's table (e.g. coefficient closed forms in terms
of tree-symmetry σ(t), or a multinomial-coefficient identity, or a
Connes-Kreimer Hopf-algebra interpretation), record it in the new
doc's §4 (distilled content) or §10 (cross-references). Such
discoveries may simplify Phase β or γ; document them even if they
don't immediately suggest a cycle 374 deliverable.

Specifically watch for:
- Whether the coefficient of `Φ_η(vertex)^k` in `Φ_{η^{-1}}(t)`
  matches the multinomial structure of `t`'s vertex labellings
- Whether the coefficient of mixed terms like `v²·c` matches the
  number of vertex-pair / subtree-pair selections in `t`
- Whether σ(t) appears anywhere in the coefficients (the witnesses
  don't suggest this so far — coefficients are all ±integer — but
  worth checking against `bushy`'s σ=6 and `mk [broom₃]`'s σ=2)

These pattern observations may suggest a closed-form *combinatorial*
recipe for `inversePolynomial` rather than the recursive recipe of
§D's conjecture. A combinatorial closed form would shorten Phase β's
proof significantly.

## §J. Single-line summary for the worker

**Write `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`,
500–800 lines of markdown distilling the inductive Sub-lemma A close
path. No Lean edits. Follow `lem_310B_plan.md`'s template. Cycle 374
ships Phase α (the `inversePolynomial` definition).**
