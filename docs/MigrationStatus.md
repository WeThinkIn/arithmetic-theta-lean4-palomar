# Migration checkpoint — 2026-10-20

This is a work-in-progress repository snapshot, not a successful full build or Palomar submission.

- Human author and responsible maintainer: Jue Ding. Original Lean code: Apache-2.0; third-party notices are retained.
- Original scope: 13 requirements and 103 exact endpoint types.
- Original source closure: 1,199 delivery modules plus 2,713 local-library modules. One source was split to meet the per-file line limit; two oversized files remain.
- Lean: 4.35.0-rc2. Mathlib: 065356127b1dc0016f66b7283ce0ce2c4055aa55.
- 39 of 103 original exact endpoint types passed a partial Lean and axiom audit. This is not a semantic review of the paper or a Comparator result. The other 64 endpoints remain pending.
- Latest completed broad build (root46) exited 1: 152 modules newly built in that run; 40 modules had diagnostics. Later standalone checks passed repairs for Miller pairing base change, root-cover generic rank, Weierstrass group-law vocabulary, tensor/cohomology shifts, smooth proper curve construction, descent characters and additional dependency modules. The next full integration build is in progress. Counts of built modules are not counts of mathematical claims verified.
- Full GoalRoot build, Solution bridge, full-scope Challenge packages, Comparator, official preflight and Palomar review remain pending. The current comparator.json covers only the pilot finite-determination statement.
- Original delivery files were checked against the preserved SHA-256 baseline; all 1,207 files were unchanged.

The original Lean 4.33.1 delivery and the new Lean port are distinct artifacts. Compatibility edits preserve the intended statements but must pass the Lean kernel in the target environment. Lean compatibility options do not substitute for checking proof terms.

Reproduction: install the toolchain in lean-toolchain, fetch the pinned dependencies with Lake, obtain the matching Mathlib cache, then run `lake build +GoalRoot`. The full build currently reports migration errors. See Coverage.md and SourceObligations.json for the retained obligations.

## Private development phase

The owner requested private visibility and authorized continued commits and builds in this private repository. Keep it private until the owner explicitly requests publication. PalomarSubmission commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` requires a public source repository for its official reusable preflight and intake. Local builds and audits continue; they are not official Palomar preflight results. Official preflight and submission are deferred until local preparation is complete and the owner authorizes publication.
