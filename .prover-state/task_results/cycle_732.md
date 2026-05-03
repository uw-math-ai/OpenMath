# Cycle 732 Results

## Worked on

§521 Step I — ξ=0 mirror of the H ladder. Three theorems landed
plus the I.1 promotion, all in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Approach

Followed the strategy verbatim:

1. **I.1** — dropped `private` from
   `rowFAlphaResidual_eval_zero_eq_double_sum` (line 2187). 1-line
   change.
2. **I.2** — added `rowFAlphaResidual_eval_zero_closed_form` before
   `end LMM`. Mirrors H.2 (line 2693) almost character-for-character,
   then does an extra outer-`k` sum collapse via `(X^k).eval 0`.
3. **I.3** — added `D_mul_toGLM_charpoly_eval_zero_eq_zero`. Three-line
   `rw [G.3, I.2]; ring`.
4. **S.1 skipped** — only caller of the BDF analogue
   `D_mul_toGLM_charpoly_eval_zero_collapsed_of_bdf` is inside
   `StabilityCharpoly.lean` itself; no external re-export needed.
5. **S.2** — wrote scratch sketch
   `.prover-state/scratch/section521_after_h3_i3_endpoints.md`
   identifying Route A (generic-ξ closed form) as the next seam.

## Result

**SUCCESS — all three I-targets landed.**

- `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` clean (one
  unused-simp-arg warning fixed by switching the trivial branch from
  `simp [Polynomial.eval_pow, Polynomial.eval_X]` to bare `simp`).
- File size: 2957 lines (up from 2865, ≈ +92 lines), still under the
  3000 soft cap.

### Tactic-API confirmations

- `zero_pow hpos` accepts `(k : ℕ) ≠ 0` directly — no fallback needed.
  Hoisted with `intro h0; apply hk; apply Fin.ext; exact h0` exactly as
  the H.2 j-branch does.
- The trivial `(X^0).eval 0` branch closes with `simp` alone; the
  explicit `[Polynomial.eval_pow, Polynomial.eval_X]` lemmas were
  flagged unused.
- `Finset.sum_eq_single` outer-collapse works the same as the H.2
  inner one — pattern `·`-blocks are: surviving term, off-index zero,
  membership absurd.

## Dead ends

None. The H.2 template + `(X^k).eval 0` collapse described in the
strategy worked on first compile (modulo the simp-warning cleanup).

## Discovery

The H.1 last-column adjugate lemma
(`toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col`) is the
bottleneck for *any* ξ specialisation: at ξ=0 we get the constant
`(X^k).eval 0 = if k.val=0 then 1 else 0` collapse; at ξ=1 we get
`(X^k).eval 1 = 1`; and for general ξ we'd get `ξ^k`. So lifting H.1
to general ξ is the obvious next move (Route A in the scratch sketch).

## Suggested next approach

Continue along Route A: prove an H.1 analogue at general ξ
(`(adj k ⟨s-1,_⟩).eval ξ = ξ^k`), then a generic-ξ closed form for
`rowFAlphaResidual.eval ξ` (mirrors H.2 but keeps the outer k-sum),
then headline `D · charpoly.eval ξ = (stabilityPolyPoly z).eval ξ`
at full generality. After that the §521 A-stability iff bridge is
in reach, since the polynomial identity over ℂ implies pointwise
equality on |ξ| = 1.

The scratch file
`.prover-state/scratch/section521_after_h3_i3_endpoints.md` lays out
both the generic-ξ closed-form route and the alternative global
polynomial-factorisation route.
