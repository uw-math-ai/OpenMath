# Issue: Odd down-arrow connected support needs a rectangle zero-set crossing lemma

## Blocker
The remaining odd-only helper
`padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst`
needs one connected component of the odd-strip zero set to project onto every
small radius. The current local analytic inputs only give:
- uniform `Re > 0` on a strip,
- opposite `Im` signs on the two boundary arcs,
- hence at least one zero on each fixed-radius slice.

That is enough for pointwise cone meeting, but not enough by itself to show
that all these slice-wise zeros lie in one connected component of
`orderWeb (padeR n d)`.

## Context
The live reduction is now:
- new helper at `OpenMath/PadeOrderStars.lean:1903`
- old blocker derived from it at `OpenMath/PadeOrderStars.lean:1918`

The helper asks for:
- `∃ z0 ∈ orderWeb (padeR n d), ∃ δ > 0`
- such that for every `r ∈ Ioo (0 : ℝ) δ`
- there is `z` in `connectedComponentIn (orderWeb (padeR n d)) z0`
- with `z = r * exp ((θ0 + s) I)` and `s ∈ Icc (-r) r`

The private support theorem now closes from this helper by taking the connected
component itself as the support and proving cone meeting directly.

## What was tried
- Rechecked the local odd block only, per cycle strategy.
- Rejected the two ready Aristotle bundles because they were not transplantable
  to the live theorem surface.
- Tested the even-case shortcut numerically by checking whether the exact odd
  central ray might already lie in the order web. It does not in general.
- Searched the local file and Mathlib for an existing connected continuation /
  rectangle crossing theorem that could be reused immediately. I did not find a
  ready local formalization.
- Searched theorem databases for the mathematical pattern; the matching result
  is the standard rectangle crossing statement:
  a continuous `f : [a,b] × [c,d] → ℝ` with opposite signs on the horizontal
  edges has a compact connected subset of `f⁻¹(0)` whose projection is `[a,b]`.

## Possible solutions
- Formalize the rectangle zero-set crossing lemma directly for continuous real
  functions on `Icc a b ×ˢ Icc c d`, then specialize it to the odd strip
  imaginary-part function.
- Prove an equivalent theorem-local compact connected zero-set statement using
  connected components of the zero set plus a separation argument in the
  rectangle.
- If a local implicit-function route is preferred, it still needs a clean way
  to globalize the local zero branches into one connected subset reaching every
  radius; that globalization is the missing step.
