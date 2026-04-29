# Cycle 579 Results

## Worked on

§386 bSeries convolution structural identities in
`OpenMath/ButcherGroup/Section386Conv.lean`:

- `bSeriesConv_add_right`
- `bSeriesConv_smul_right`
- `bSeriesConv_zero_left`

## Approach

Followed the cycle 579 pivot away from the false §388 left-cancellation
target documented in
`.prover-state/issues/butcher_section388_left_cancellation.md`.

Used the required sorry-first scaffold for the two right-slot linearity
lemmas and the zero-left sanity theorem, then verified the scaffold with
`lake env lean OpenMath/ButcherGroup/Section386Conv.lean`.

Aristotle batch attempt:

- Full `Section386Conv.lean` scaffold: HTTP 429.
- `AddRight.lean`: HTTP 429.
- `SmulRight.lean`: HTTP 429.
- `ZeroLeftTwoLeaves.lean`: HTTP 429.
- `ZeroLeftDepthTwo.lean`: HTTP 429.
- `ZeroLeftGeneral.lean`: HTTP 429.

No Aristotle project IDs were created, so there was nothing to sleep on
or poll. Proceeded under the strategy's 429 fallback.

Manual proofs:

- Proved right additivity by induction over the filtered cut list, using
  `Pi.add_apply`, `mul_add`, and `ring`.
- Proved right scalar compatibility by the same list-induction pattern.
- Proved `bSeriesConv_zero_left` by first showing that every entry of
  `τ.innerCut (fun _ => 0)` is either the canonical no-cut entry
  `(some τ, 1)` or has zero cut weight. The final sum reduces to the
  existing canonical-count lemma `innerCut_canon_count`.

## Result

SUCCESS.

Landed all scheduled minimum lemmas and the stretch general theorem:

- `bSeriesConv_add_right`
- `bSeriesConv_smul_right`
- `bSeriesConv_zero_left`

Also updated `plan.md` and appended a cycle 579 status note to
`.prover-state/issues/butcher_section388_left_cancellation.md`, recording
that these right-slot identities do not reopen the false left-inverse
claim.

## Dead ends

Aristotle was unavailable due to HTTP 429 throttling on every submitted
job. No proof output was produced.

## Discovery

The zero-left identity is clean once phrased through the canonical no-cut
entry: with the left coefficient identically zero, every proper cut has
at least one pruned subtree factor equal to zero, so only `(some τ, 1)`
contributes to `bSeriesConv`.

This reinforces the cycle 578 distinction: the second coefficient slot
is genuinely linear, while the first coefficient slot controls products
of cut-subtree weights and cannot satisfy a naive two-term additivity or
left-inverse cancellation law.

## Suggested next approach

Use `bSeriesConv_add_right`, `bSeriesConv_smul_right`, and
`bSeriesConv_zero_left` as small algebraic infrastructure for future
§386/§388 work. The next inverse step should remain a tableau-level
antipode or another genuine inverse construction, not a retry of the
false `inverseCoeff` left-cancellation theorem.
