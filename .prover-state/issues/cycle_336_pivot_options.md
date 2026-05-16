# Cycle 336 pivot options (P2 scoping menu)

Produced by cycle 335 (worker). The §344 small-`s` direct-form ladder
saturated at cycle 335 with `butcherLobattoIIIDirect_three` (cycles
322–335: 14 consecutive axiom-clean §344 cycles). Cycle 336 should
break the streak. This menu lists 3–4 candidates; cycle 336's planner
does the deep scoping per their chosen target.

## Selection rules

* Pick **one** candidate.
* Read its entity JSON before writing any Lean code.
* If multi-cycle: write a scoping doc in `.prover-state/issues/`
  named `<target>_path.md` or `<target>_plan.md` (per cycle 222 /
  cycle 260 precedent).
* If single-cycle: write the Lean code directly + faithfulness check.
* **Do NOT continue the §344 ladder** (no `butcherRadauIA_three`,
  no `butcherLobattoIIIA_four`, no `butcherLobattoIIIB_two` — that
  one doesn't exist anyway). The streak ends with cycle 335.

## Candidate A — `def:422B` (underlying one-step method, §422 Ch.4)

* **Kind**: definition.
* **Page**: 359 (Butcher §422).
* **Textbook statement**: "Corresponding to a linear multistep method
  `[α, β]`, the member of `G_1` represents the underlying one-step
  method."
* **Dependencies**: `def:381B` (Φ-equivalent — already substantially
  scaffolded by cycles 232–236; see `instGroup_phi` in
  `Section381.lean`).
* **Dependents**: `thm:422A`, `thm:422C`, `thm:535A`.
* **LOC estimate**: 1–2 cycles (definition + non-vacuity witness).
  The hard work (the §383 group `instGroup_phi` instance, `Φ` as
  the map) is already done; this builds on it.
* **Risk**: low–medium. Requires §422 read for LMM `[α, β]`
  prerequisites; may need `LinearMultistepMethod` structure if not
  already present.
* **Prerequisite check (do this first)**: grep for
  `LinearMultistepMethod`, `LMM`, `preconsistent`, `stable` in
  `OpenMath/Chapter4/`. If absent ⇒ candidate is multi-cycle
  (needs LMM scaffolding); if present ⇒ single-cycle definition
  ship is plausible.

## Candidate B — `thm:302A` (Some combinatorial questions, §302 Ch.3)

* **Kind**: theorem (two equations: `α(t) = r(t)! / (σ(t) γ(t))`
  and `β(t) = r(t)! / σ(t)`).
* **Page**: 162 (Butcher §302).
* **Textbook statement**:
  > α(t) = r(t)! / (σ(t)·γ(t)),     (302a)
  > β(t) = r(t)! / σ(t).            (302b)
* **Dependencies**: `thm:301A` (Functions on trees).
* **Dependents**: `thm:302B`.
* **LOC estimate**: 1–2 cycles. Leverages cycles 254–270 rooted-tree
  infrastructure (`σ`, `γ`, `r` on `RootedTree`). Single-cycle if
  `α(t)` and `β(t)` are already defined; otherwise scope `α`/`β`
  definitions as Phase 1 and the equations as Phase 2.
* **Risk**: low. The proof is a combinatorial counting argument over
  labellings of vertices — purely structural induction on
  `RootedTree`.
* **Prerequisite check**: grep `α`, `β`, `alphaCount`, `betaCount`,
  `labellings` in `OpenMath/Chapter3/Section30*.lean`. If neither
  `α` nor `β` exists ⇒ Phase 1 is a definition ship; if both exist
  ⇒ this is a direct equation ship.

## Candidate C — `thm:302B` (Rooted Tree Generating Function Identity)

* **Kind**: theorem (formal power-series identity).
* **Page**: 163 (Butcher §302).
* **Textbook statement**:
  > θ_1 + θ_2 x + θ_3 x² + ⋯ = ∏_k (1 − x^k)^{−θ_k}.    (302c)
* **Dependencies**: `thm:302A`, `thm:302C`.
* **Dependents**: `thm:304A`.
* **LOC estimate**: 3–5 cycles minimum. Requires Mathlib
  `MvPowerSeries` or `PowerSeries` infrastructure for the formal
  identity, plus the counting argument on `Θ_k(U)` increments.
* **Risk**: high. Mathlib's `PowerSeries` API may not have the
  exact `(1 − x^k)^{−n}` series-expansion lemma needed; verifying
  the proof's `Θ_k(V) − Θ_k(U) = Θ_{k − r(t̂)}(V)` recurrence
  requires explicit `Set`-counting infrastructure that may not
  exist in Mathlib at the level of "trees that contain `t̂` at
  least m times".
* **Recommendation**: only pick if cycle 336's planner is committed
  to a multi-cycle scoping doc; otherwise prefer A or B.

## Candidate D — Continue partial entity `thm:384A`

* **Kind**: theorem (Φ as a group homomorphism §382 → §383).
* **Status (per `lean_status.json`)**: `partial`. Cycle 236 shipped
  `instGroup_phi` on `Quotient PhiEquivalent.setoidSigma`. The
  remaining work is: package Φ itself as a `MonoidHom` /
  `GroupHom` from §382 group to §383 group.
* **Blocker per cycle 236 note**: requires "the §382 → §383
  inclusion Φ" — cycle 237+ should "check whether the required
  `Equivalent → PhiEquivalent` inclusion is single-cycle closeable
  or is the deferred direction in `thm_381H_deferred.md`."
* **LOC estimate**: 1 cycle if the inclusion is direct (cycle 236
  said "very small cycle now that (★★)/(★★★) work is done"). 2+
  cycles if it hits the `thm_381H_deferred` blocker.
* **Risk**: medium. Read `thm_381H_deferred.md` first to determine
  scope.
* **Recommendation**: closes a 100+ cycle infrastructure path —
  high value if single-cycle, defer if not.

## Suggested cycle 336 default

**Candidate B (`thm:302A`)** if cycle 336 wants a clean single-cycle
ship in fresh territory: leverages existing rooted-tree infrastructure,
breaks the §344 streak in a different chapter section (§302), and
unblocks `thm:302B` for a future generating-function cycle.

**Candidate D (`thm:384A`)** if cycle 336 wants to close standing
partial work rather than start fresh.

Avoid C (multi-cycle generating-function infrastructure) unless cycle
336's planner is explicitly committed to a scoping cycle.
