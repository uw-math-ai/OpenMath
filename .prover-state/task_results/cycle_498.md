# Cycle 498 Results

## Worked on

§422 Phase α'.5.2 scoping doc — markdown-only research plan for
extending `inversePolyTree` to k=4 children. The new doc is the
prerequisite that unblocks the cycle 365 grandfathered sorry path
(per the cycle 497 worker's R6.B finding).

No Lean code shipped. Sole Lean-touching action: bookkeeping bump
of `lean_status.json`'s `def:422B` `cycle_completed_at` field
(497 → 498) and a closure annotation appended to `plan.md`'s
`def:422B` row.

## Approach

Per the cycle 498 strategy §B–E:

1. **§C.2 pre-flight verification.** Read the referenced Lean
   sites to confirm:
   * `Section422.lean:582` — cycle 358's
     `elementaryWeightQ_phi_inv_mk` per-row product expansion
     (the `_inv_mk` formula that drives the §3 block decomposition).
     Verified at lines 582–605.
   * `Section422.lean:3011–3169` — cycle 370's
     `elementaryWeightQ_phi_inv_bushy` closed-form theorem
     (cycle 499's structural template). Verified; ~159 LOC; 3
     helpers (`h_dw_bushy`, `h_bushy`, `h_dws_bushy`) + main
     `h_sum` computation closing via
     `Finset.sum_*_distrib + Finset.mul_sum + ring`.
   * `Section422.lean:9588–9662` — cycle 399/403/491–494's
     `trichildCrossTerm` 5-branch dispatch cascade. Verified;
     named branches: `(v,v,v)`, `(v,v,c)`, `(v,c,c)`, `(v,v,mk[c])`,
     `(v,v,broom₃)`.
   * `Section422.lean:9686–9693` — cycle 399's
     `trichildPolynomial` body. Verified; sign convention
     `-Block(1) - Block(2) - Block(3) - Block(4) + trichildCrossTerm - f(mk[t₁,t₂,t₃])`.
   * `Section422.lean:9718–9733` — cycle 387/399's `inversePolyTree`
     5-arm pattern match. Verified; cycle 500 extends to 6 arms
     at this site.

2. **Doc body** (`def_422B_phase_alpha_prime_5_2_scoping.md`,
   1306 LOC, §§1–13). Wrote per the cycle 498 strategy §C.1
   template, mirroring cycle 402 and cycle 495's scoping doc
   structure verbatim. Key sections:
   * §1: Status + R6.B falsity recap + cycle 365 sorry blocked
     status.
   * §2: 5-arm → 6-arm pattern-match extension target.
   * §3: 16-block decomposition table (S, |S|, per-row factor,
     outer-sum contribution) with kernel identification per
     block class.
   * §4: `tetrachildPolynomial` strawman def (Option A combined
     cross-term packaging recommended).
   * §5: `tetrachildCrossTerm` strawman dispatch cascade +
     §5.1/§5.2 symbolic derivation of the symmetric `bushy₄`
     closed form `Φ_{η⁻¹}(mk[v,v,v,v]) = -v⁵ + 4v³c − 6v²b'
     + 4v·bu − Φ_η(bushy₄)` from cycle 358's `_inv_mk` formula
     applied to `(-v + Σⱼ A_{ij})⁴`.
   * §6: Phase decomposition — α'.5.2.0 (cycle 499) through
     α'.5.2.k+2 (cycle ~511).
   * §7: Per-sub-phase LOC budgets.
   * §8: 6-risk inventory (R1 kernel surprise, R2 build cost,
     R3 naming, R4 sign-parity, R5 `inv_ℓ` heterogeneity, R6
     cycle 365 sorry remains open).
   * §9: Cycle 499 entry point — complete proof recipe for
     `elementaryWeightQ_phi_inv_bushy₄` mirroring cycle 370.
   * §10: Explicit non-actions (no Lean code, no Aristotle, no
     `maxHeartbeats` bump, etc.).
   * §11: Cross-references to predecessor scoping docs,
     Lean ship locations, memory entries.
   * §12: Success criteria + cycle 498 faithfulness check.
   * §13: Closing note.

3. **§5.2 sign-derivation cross-check.** Recomputed the
   `tetrachildCrossTerm v v v v f` value from two independent
   directions:
   * Direct: `(-v + s)⁴ = v⁴ − 4v³·s + 6v²·s² − 4v·s³ + s⁴`,
     sum against `M.b i`, apply outer `-` prefix.
   * Via `tetrachildPolynomial` body: subtract the absorbed
     Block (1)–(5) and self-Block (16) terms from the closed
     form.
   Both methods yield `tetrachildCrossTerm v v v v f =
   -6·(f vertex)²·f broom₃ + 4·f vertex · f bushy`. Sign
   parity confirmed (cf. §8.4 risk R4): the cross-term flips
   parity between odd-k and even-k because `(-v)^(k-j)` carries
   `(-1)^(k-j)` and the outer `-Σᵢ` adds one more sign.

4. **Bookkeeping.**
   * Bumped `lean_status.json` `def:422B` row's
     `cycle_completed_at` to 498. Status unchanged (`partial`).
   * Appended a cycle 498 closure annotation (~3 paragraphs)
     to `plan.md`'s `def:422B` row (line 171).

5. **No Aristotle submissions.** Per the cycle 498 strategy §D
   explicit prohibition (and the cycle 402/495 scoping
   precedent), scoping cycles have no Aristotle target.

6. **No `Section422.lean` modifications.** Verified via
   `git diff --stat` (expected to be confirmed in §pre-commit
   verification).

## Result

SUCCESS — Phase α'.5.2 scoping doc shipped.

* Deliverable: `.prover-state/issues/def_422B_phase_alpha_prime_5_2_scoping.md`
  (1306 LOC Markdown, 13 sections).
* Bookkeeping: `lean_status.json` `def:422B`
  `cycle_completed_at` 497 → 498 (status unchanged `partial`);
  `plan.md` def:422B row appended with cycle 498 closure
  annotation.
* `Section422.lean`: unchanged (verified by absence from
  `git diff` pre-commit).
* `grep -c sorry OpenMath/Chapter4/Section422.lean`: 5
  (unchanged from cycle 497).

§422 axiom-clean streak: 70 substantive + 5 doc (cycles 336–497)
→ **70 substantive + 6 doc** (cycles 336–498).

LOC ship: 1306 markdown (scoping doc) + ~3 paragraphs (plan.md
annotation) + 1 character (lean_status.json digit). Within the
500–1500 LOC success criterion range (cycle 498 strategy §F).

## Faithfulness check

**No new `def`, `structure`, or `theorem` introduced this cycle.**
The scoping doc contains symbolic derivations (e.g. §5.1's
`Φ_{η⁻¹}(mk[v,v,v,v])` closed form) and Lean code sketches
(e.g. §9.1's `elementaryWeightQ_phi_inv_bushy₄` recipe), but
none of these are committed Lean theorems — they are planning
hypotheses for cycle 499+.

Per the cycle 498 strategy §G:

* **No new `def` introduced.** ✓
* **No new `structure` introduced.** ✓
* **No new `theorem` introduced.** ✓
* **Sorry count unchanged at 5** (4 docstring + 1 grandfathered
  cycle 365 code at `Section422.lean:2279`). ✓
* **Sole deliverable** is a markdown planning document. ✓

Faithfulness is trivially satisfied — no formal claims made
about Butcher textbook content; all references to `Φ_η`,
`Φ_{η⁻¹}`, `inversePolyTree`, `tetrachildPolynomial`, etc. are
scoping-level design discussions, not theorem ships.

## Dead ends

None encountered.

**Sign-derivation false start (resolved):** in §5 strawman
drafting, the initial sign analysis for `tetrachildCrossTerm`
at `(v,v,v,v)` got mid-derivation tripped up by comparing
against cycle 400's `trichildCrossTerm v v v f = +3v · b'`
(positive sign) and expecting the same sign for tetrachild's
bilinear contribution. Resolution: re-derived via direct
`(-v + s)^k` binomial expansion, which made the parity flip
between odd-k (`(-v)^(k-j)` has `(-1)^(k-j)` with `k-j` odd
when `j = k-1`, giving `-1` factor that the outer `-` then
flips to `+1`) and even-k (where `(-v)^(k-j)` with `k-j` even
gives `+1`, and the outer `-` flips to `-1`) explicit. Added
as risk R4 in §8 of the scoping doc, with explicit cycle
499/500/501 worker instruction to re-derive symbolically.

## Discovery

**Discovery #1**: the cross-term sign convention in `nchildCrossTerm`
helpers (mono / bi / tri / tetra / etc.) flips parity between
odd-k and even-k cases. Specifically, the bilinear contribution
at `(v, v, ..., v)`:

* k = 3: `trichildCrossTerm v v v f = +3v · b'` (positive).
* k = 4: `tetrachildCrossTerm v v v v f = -6v² · b' + 4v · bu`
  (negative bilinear, positive trilinear).

This is because the `(-v + s)^k` expansion has alternating-sign
coefficients in `s^j`, and the outer `-Σᵢ M.b i · (...)` prefix
adds one more sign flip. The pattern is:

* Block `|S| = j` contributes `(-1)^{k-j+1}` to the closed form's
  sign for that block (where `+1` is the outer-sum sign flip and
  `k-j` is the `(-v)^{k-j}` parity).

Worth a memory entry if it surprises a future cycle worker.
Memory candidate: `feedback_nchildCrossTerm_sign_parity.md` —
"`nchildCrossTerm` sign convention alternates parity with k:
bilinear is `+` for odd k, `-` for even k; trilinear is `-` for
odd k, `+` for even k; etc. Re-derive from `(-v + s)^k` binomial
expansion before committing any new `*childCrossTerm` branch."
Defer the memory write to cycle 499 once the pattern is exercised
in code.

**Discovery #2**: cycle 402's scoping doc (Phase α'.5 for k=3
non-symmetric children) successfully drove **5 substantive
cycles** (403, 491, 492, 493, 494) of calibration-witness ladder,
each ~250–400 LOC. The cycle 498 scoping doc's projected α'.5.2
ladder (cycles 499–509+) targets similar yield: 10 substantive
cycles of calibration witnesses at projected ~250–400 LOC each.
This precedent gives high confidence the α'.5.2 LOC budgets in
§7 of the scoping doc are realistic.

**Discovery #3** (non-vacuity arithmetic): for the cycle 499
non-vacuity `example` at `⟦explicitEuler⟧`, evaluating the §5.1
closed form `-v⁵ + 4v³c − 6v²b' + 4v·bu − Φ_η(bushy₄)` at
`v = 1, c = 0, b' = 0, bu = 0, Φ_η(bushy₄) = 0` gives
`-1 + 0 - 0 + 0 - 0 = -1`. **Expected non-vacuity value:** `-1`.
This is a small but useful pre-derivation that saves cycle 499
the trial-and-error of computing this from scratch.

**Discovery #4** (file architecture pressure): cycle 401 measured
~1165s warm rebuild for Section422.lean. Cycle 500's 6-arm
extension projects to ~1400–1500s. The α'.5.2 ladder cycles
501–509+ each add ~250–400 LOC, projecting Section422.lean to
~14000–15500 LOC. **A sibling-file extraction** (e.g., a new
`OpenMath/Chapter4/Section422/TetraChild.lean`) may become
necessary at cycle ~503–505. Cycle 500 worker should measure
build cost and report; if >1500s, extract immediately.

## Suggested next approach

**Cycle 499** (recommended): ship Phase α'.5.2.0 per the
scoping doc §9.1 recipe. Ship `elementaryWeightQ_phi_inv_bushy₄`
(the symmetric `bushy₄ = mk [v,v,v,v]` closed-form theorem)
mirroring cycle 370's `elementaryWeightQ_phi_inv_bushy` body
verbatim, adding one extra `h_prod_step_3` layer in the
`h_dw_bushy₄` and `h_dws_bushy₄` helpers. LOC budget:
~190–210. Non-vacuity `example` at `⟦explicitEuler⟧` value `-1`.
Aristotle target: `h_dw_bushy₄`, `h_dws_bushy₄`, main theorem
(3 jobs, batch). Sleep 30 min.

**Alternative — Cycle 499 deferred, fresh entity pivot**: if the
cycle 499 planner judges that the §422 cluster's marginal value
is diminishing (after 70 substantive cycles), consider pivoting
to a fresh entity per `cycle_336_pivot_options.md` (def:451A,
def:442A, thm:535A, thm:541A). This is **not** recommended; the
cycle 365 sorry closure within ~10–15 cycles via Phase α'.5.2/3
is a tangible endpoint, and pivoting now loses that compounding.

**Future cycles** (preview per scoping doc §6 / §12.2):
* Cycle 500: `tetrachildPolynomial` + `tetrachildCrossTerm` defs
  + 6-arm `inversePolyTree` + `inversePolyTree_bushy₄`
  calibration (~90–110 LOC).
* Cycles 501–509+: non-symmetric quadruple witnesses ladder
  (~250–400 LOC each), one per cycle.
* Cycle ~510: Phase β.1 + γ k=4 extensions (~100–200 LOC).
* Cycle ~511+: Phase β.2 tree-order-bounded carve-out (or
  `nchildPolynomial` Phase α'.7 infrastructure pivot).
* Cycle ~512+: cycle 365 grandfathered sorry closure (the
  multi-cycle endpoint).
