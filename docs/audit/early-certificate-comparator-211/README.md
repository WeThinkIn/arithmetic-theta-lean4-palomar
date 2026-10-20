# Earlier-certificate local export Comparator check, attempt 211

The local bundled Lean 4.35.0-rc2 Comparator accepted ArithmeticThetaPalomarEarly205.earlierCertificate with exit 0 in 182.44 seconds. It used both supplied exports, the normal bubblewrap sandbox, the three permitted standard axioms, bundled con-ron --jobs=2, bundled NanoDa and bundled Lean's own kernel. The final log says Your solution is okay! Con-ron explicitly accepted 59,459 declarations in its default verified mode. NanoDa and Lean default each accepted the Solution.

This result is a LOCAL CHECK OF HASH-BOUND EXPORTS. It is not official Palomar preflight or submission, and it does not reproduce the official isolated source provenance audit. The --*-from-export options themselves do not prove that an export came from a repository source. Here the locally compiled 205 sources, existing .olean files, actual leanexport command and resulting NDJSON bytes are bound with SHA256; the source hashes match the earlier successful 205 compilation receipt, and sources/objects were rechecked unchanged after export. That is the documented local provenance limit.

The exporter ran inside the project's lake env to obtain the known dependency LEAN_PATH, then prepended evidence/early-certificate-205 so Challenge and Solution resolve to that package's actual objects. The target list includes the named theorem plus permitted axioms, Quot primitives and the primitive target list read from this exact toolchain's Lake/CLI/Check.lean, matching the official verifier's construction. No Challenge or Solution rebuild, Lake target build, dependency resolution or Mathlib rebuild ran during this task.

The Comparator ran from an independent empty project directory with both exports supplied; no lakefile or project manifest was needed, and no project code was evaluated. Each export had a 300-second budget. The modern-sandbox Comparator had a finite 600-second total budget and finished before it.

## Sandbox repair

The first attempt used the pre-existing workspace bubblewrap 0.4.0 and failed with Unknown option --clearenv before any kernel actually checked a proof. This is retained as comparator.log and comparator-receipt.json (exit 1); it is an infrastructure failure, not a mathematical rejection.

The official pipeline's install script at commit d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44 pins bubblewrap 0.12.0 and tarball SHA256 9760d007363e3abba7c747489910f9f82d9fca53ba3bd3282e396fa3c97a3314. That exact tarball was downloaded and verified, then built entirely inside this evidence directory using locally installed Meson/Ninja and locally extracted libcap-dev. No system package was installed, no system file was edited, no setuid bit was set, and no sandbox parameter was removed. The resulting binary passed a real --clearenv/user-namespace smoke test. The successful Comparator used that binary via COMPARATOR_BWRAP.

Reusable modern sandbox binary:

    evidence/early-comparator-211/bubblewrap-0.12.0/build/bwrap

See bubblewrap-receipt.json for its content hash and mode; tool-digests.json binds all judging binaries.

## Evidence

- comparator-modern.log and comparator-modern-receipt.json: final successful full local run.
- export-receipts.json and export-targets.json: exact commands, object/source/export hashes, sizes and exit codes.
- source-export-binding.json: connection to the previously compiled 205 sources and limitations.
- comparator-external.json: unmodified 205 target/permitted axioms, augmented with NanoDa and con-ron --jobs=2.
- Challenge.ndjson (49,551,579 bytes) and Solution.ndjson (460,988,413 bytes): exact judged exports; keep as local evidence, not source assets to upload automatically.
- receipt.json: combined result and evidence hashes.

This covers only accepted-017's earlier-certificate subpackage in the Algorithms/examples group. It does not cover the other 102 endpoints, the rest of that group, the main explicit bound, source-paper semantic review, or the full paper. Do not label the entire preparation complete on the basis of this check.
