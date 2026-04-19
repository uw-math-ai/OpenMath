# Cycle 139 Results

## Worked on
- Replaced the vacuous `IsAStablePadeApprox` interface in `OpenMath/OrderStars.lean` with the four-field Aristotle decomposition required by the planner.
- Updated `lean_status.json` so `thm:355D`, `thm:355E`, and `thm:355G` are marked `done`.
- Added `OpenMath/CollocationBN.lean` with BN-stability corollaries for the already-formalized algebraically stable collocation families: GL2, GL3, Radau IA2, Radau IA3, and Radau IIA3.
- Submitted an Aristotle scratch file for the BN-stability corollaries: project `418fbdf8-473a-498a-b14c-6dc23fe7db52`.

## Approach
- Read the completed Aristotle result from cycle 137 and copied its corrected non-circular Ehle-barrier interface into `OrderStars.lean`, keeping the project-facing name `IsAStablePadeApprox`.
- Removed the fake `orderStarPlusOnImagAxis` bookkeeping field and the dead theorem depending on it.
- Reproved `ehle_barrier` directly from sector-count bounds plus arrow-vanishing equalities.
- Verified `OpenMath/OrderStars.lean` after the interface replacement.
- Checked the extracted metadata for `thm:358A` before updating status. The extraction data says `358A` is the algebraic-stability characterization theorem for collocation methods, not the BN-stability corollary suggested by the planner text.
- Added concrete BN-stability corollaries instead of mislabeling `thm:358A` as done.

## Result
- SUCCESS: `OpenMath/OrderStars.lean` compiles with the corrected A-stability interface and no vacuous field.
- SUCCESS: `OpenMath/CollocationBN.lean` builds, and `OpenMath.lean` imports it after building the new module.
- SUCCESS: `lean_status.json` now reflects the sorry-free 355D/355E/355G status.
- PARTIAL: Aristotle submission was created successfully, but at the single status check it was still `QUEUED`, so there was nothing to incorporate this cycle.

## Dead ends
- The planner’s suggested `358A` target is mismatched with the extracted entity metadata. `extraction/formalization_data/entities/thm_358A.json` names the subsection “BN-stability of collocation methods” but the theorem statement itself is the shifted-Legendre characterization of algebraic stability. I did not mark `thm:358A` done on the basis of the newly added BN corollaries because that would be inaccurate.
- `lake env lean OpenMath.lean` initially failed after adding `OpenMath/CollocationBN.lean` because the new module had no `.olean` yet; `lake build OpenMath.CollocationBN` fixed that.

## Discovery
- The Aristotle cycle-137 result was correct: the old `IsAStablePadeApprox` carried no information beyond `IsPadeApproxToExp`.
- The 355G proof in our codebase is now explicitly non-circular: sector inequalities and A-stability arrow-vanishing are separate assumptions.
- The repository already had enough algebraic-stability coverage to derive several BN-stability corollaries immediately.

## Suggested next approach
- If cycle 140 wants to continue with subsection 358, formalize the actual extracted `thm:358A` statement from `entities/thm_358A.json` rather than the subsection title.
- Check Aristotle project `418fbdf8-473a-498a-b14c-6dc23fe7db52`; if it completed, compare its proof terms against `OpenMath/CollocationBN.lean` and harvest anything useful.
- If the planner still wants BN-stability work, extend `CollocationBN.lean` to Lobatto IIIC concrete methods or package a more general “algebraically stable collocation family implies BN-stable” interface once a precise collocation predicate exists in Lean.
