# Migration checkpoint — 2026-10-20

This is a work-in-progress repository snapshot, not a successful full build or Palomar submission.

- Human author and responsible maintainer: Jue Ding. Original Lean code: Apache-2.0; third-party notices are retained.
- Original scope: 13 requirements and 103 exact endpoint types.
- Original source closure: 1,199 delivery modules plus 2,713 local-library modules. Three sources have now been split to meet the per-file line limit; no Proof file exceeds 10,000 lines. The latest relative doubled-torsion split (8,849/8,407 lines) still awaits compilation after its original upstream dependencies are built, and is not a verified port yet. The rational-function residue theorem split passed standalone checks for its 8,486-line Prelude and 4,707-line main file, with original outer compiler options restored. Both modules and their downstream theorem wrapper also passed in the subsequent full-root build; the complete GoalRoot is still pending.
- Lean: 4.35.0-rc2. Mathlib: 065356127b1dc0016f66b7283ce0ce2c4055aa55.
- 40 of 103 original exact endpoint types passed a partial Lean and axiom audit. This is not a semantic review of the paper or a Comparator result. The other 63 endpoints remain pending.
- Latest completed broad build (root112) exited 1: 3 modules newly built in that run and 4 diagnosed failures. The root102/root107/root110 runs newly built 32/14/6 modules respectively; their diagnosed failures have since been repaired. Root114 is integrating the latest fixes. Partial audit 110 jointly rechecks 40 exact endpoints, including the arbitrary formal-cover constant theorem. Counts of built modules are not counts of mathematical claims verified.
- Full GoalRoot build, Solution bridge, full-scope Challenge packages, Comparator, official preflight and Palomar review remain pending. The current comparator.json covers only the pilot finite-determination statement.
- Original delivery files were checked against the preserved SHA-256 baseline; all 1,207 files were unchanged.

The original Lean 4.33.1 delivery and the new Lean port are distinct artifacts. Compatibility edits preserve the intended statements but must pass the Lean kernel in the target environment. Lean compatibility options do not substitute for checking proof terms.

Reproduction: install the toolchain in lean-toolchain, fetch the pinned dependencies with Lake, obtain the matching Mathlib cache, then run `lake build +GoalRoot`. The full build currently reports migration errors. See Coverage.md and SourceObligations.json for the retained obligations.

## Private development phase

The owner requested private visibility and authorized continued commits and builds in this private repository. Keep it private until the owner explicitly requests publication. PalomarSubmission commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` requires a public source repository for its official reusable preflight and intake. Local builds and audits continue; they are not official Palomar preflight results. Official preflight and submission are deferred until local preparation is complete and the owner authorizes publication.

## Local CPU scheduling

The isolated workspace runner now sizes LEAN_NUM_THREADS to the available CPU affinity (96 logical CPUs on the current 48-core host). Callers can override it. A single Lake build schedules the dependency graph; independent diagnostic checks can run concurrently without writing build artifacts. Narrow dependency chains still limit usable parallelism.
