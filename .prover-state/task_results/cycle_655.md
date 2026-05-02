# Cycle 655 Results

## Worked on
Butcher section 521 GLM A-stability transports in `OpenMath/RKAsGLM.lean`:
`rkLobattoIIIA2_stabilityFunction_eq`,
`rkLobattoIIIA2_toGLM_isAStable`,
`rkLobattoIIIC2_stabilityFunction_eq`, and
`rkLobattoIIIC2_toGLM_isAStable`. Also rotated the `plan.md` current
target from the completed Gauss-Legendre 3-stage bridge to the Lobatto
2-stage transports.

## Approach
Followed the sorry-first workflow: added the four theorem statements with
`sorry`, checked `lake env lean OpenMath/RKAsGLM.lean`, then closed them in
the requested order.

For Lobatto IIIA 2-stage, used
`!![1, 0; -(z * (1/2 : ℂ)), 1 - z * (1/2 : ℂ)]`
for `1 - z A`, with determinant `1 - z * (1/2 : ℂ)`. The nonzero
denominator follows from `z.re ≤ 0` by taking real parts and `nlinarith`,
then `Matrix.inv_def`, `Matrix.adjugate_fin_two_of`, `field_simp`, and
`ring` close the scalar bridge.

For Lobatto IIIC 2-stage, used
`!![1 - z * (1/2 : ℂ), z * (1/2 : ℂ);
   -(z * (1/2 : ℂ)), 1 - z * (1/2 : ℂ)]`
for `1 - z A`. Reused `lobIIIC_denom_ne_zero`; the determinant is
`lobIIICDenom z / 2`, and the weighted adjugate row sum is
`1 - z * (1/2 : ℂ)`.

## Result
SUCCESS. Both Lobatto IIIA and Lobatto IIIC 2-stage GLM-side stability
function bridges landed, and both A-stability transports now follow from
`ButcherTableau.toGLM_isAStable_iff` plus the existing scalar A-stability
lemmas.

## Dead ends
The direct broad `field_simp; ring` shape for the Lobatto IIIC bridge was
too slow. Splitting the proof into the determinant certificate, the
weighted adjugate sum, and the final scalar identity avoided the slowdown.
Aristotle was not used; the strategy made it optional and the SDIRK-style
manual path was direct.

## Discovery
For 2-stage Lobatto methods, the `Matrix.inv_def` plus adjugate expansion
is enough if IIIC is split before the scalar simplification. The useful
IIIC scalar identity is `lobIIICDenom z + z * (2 - z) = 2`.

## Suggested next approach
Schedule Lobatto IIIB 2-stage only if explicit mirrored coverage is wanted.
For Lobatto 3-stage methods, use the cycle 654 three-certificate split
style rather than a monolithic scalar simplification. The LMM-side
`toGLM_isAStable_iff` charpoly factorisation should remain a separate
planning target.
