# Local three-kernel acceptance of the complete split interfaces

Both scoped comparators completed successfully using the unmodified pinned comparator and frozen exports of the actual named Challenge/Solution roots. Each run reports acceptance by con-ron, NanoDa, and the Lean default kernel, followed by `Your solution is okay!` and exit code 0.

| Scope | Original endpoint | Full local comparator time | Kernels |
| --- | --- | --- | --- |
| Split discriminant | accepted-073 | 4286.07 s (71.43 min) | All three pass |
| Split square degree | accepted-074 | 4478.53 s (74.64 min) | All three pass |

The Challenge exports are the exact named-root exports from audit 558; the Solution exports are the export-preserving pruned versions from audit 561. Their hashes were rechecked at publication. The target names, modules and permitted axioms equal the current repository configurations. The local configurations explicitly select `nanoda_bin` and `con-ron --jobs=2`; this execution override is retained in the archived configuration and summary. The four root source files, optimized node proof, Lean pin, and dependency manifest are byte-identical to commit `2c85e9b977f3d8e91570235a68534c945d69ff28`. The current Lake configuration also contains subsequently added scopes; this does not change the frozen inputs checked here.

The prior exact structural and axiom comparisons and original-endpoint recovery checks remain available in the integration audits. This record adds the completed stock kernel replay verdicts. There was no proof or interface modification for this publication.

These are local mechanical results for the two stated scopes. They do not establish official cold-build success, whole-paper semantic acceptance, or registry registration. The original 13 requirements and 103 endpoints remain the objective. The four remaining independent interfaces retain their full original statements.

Each subdirectory contains the original comparator configuration, output log, input hash bindings and terminal receipt. Large export files are identified by SHA-256 and are not committed. `summary.json` binds these receipts to the current published roots. `run.py` records the local runner and resource configuration used.
