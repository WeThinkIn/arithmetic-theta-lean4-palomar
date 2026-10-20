# Migration checkpoint — 2026-10-21 (Asia/Shanghai)

This is an active migration snapshot, not a successful full build or Palomar submission.

- Human author and responsible maintainer: Jue Ding. Original Lean code: Apache-2.0; third-party notices are retained.
- The repository is public following the owner’s explicit authorization to publish it, run official preflight and submit when ready. The earlier temporary-private instruction has been superseded.
- Original scope: 13 requirements and 103 exact endpoint types. The original delivery and its dependency closure remain in scope.
- Lean4.35.0-rc2 and Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 are pinned.
- Partial audit 273 jointly checks 62/103 original exact endpoint types and standard axiom closures. The remaining 41 endpoints are pending. This is migration evidence, not full semantic coverage.
- Root197 built39 new modules; root206 built37; root215 built14. Each root ended with remaining migration errors. These counts describe successful module builds, not percentages of mathematics completed. Subsequent integration passed scheme Kato characterization, coefficient maps and unary power realization. Root243 reached Hodge tensors and origin Taylor; minimal repairs passed targeted build247 and isolated check245 and are integrated into root248, which ended with two compatibility errors; targeted build 271 passed both repairs.
- New checked modules include ramified polygon towers and generic base change, compatible level subcovers and cyclic quotients, faithful annular evaluation, geometric boundary Tate disks, completed local parameters, normal discriminant independence and actual scheme discriminant existence/naturality.
- The independent main-explicit Solution compiled against the actual LatticeGlobalSectionsDefinitionsR0188 and ConservativeMatrixKernelR0189 modules. Its 600-second local three-kernel attempt timed out during con-ron; a longer, 12-worker attempt reuses identical source-bound exports. This is not a proof rejection or a pass.
- The accepted-017 early-certificate subpackage has a proved independent Solution. Local Comparator on hash-bound exports passed statement/definition matching, axiom checks, con-ron(--verified,--jobs=2), NanoDa and Lean default kernel in a normal bubblewrap0.12.0 sandbox, exit0. Official full mechanical preflight39455278417 at commit12f83ea subsequently passed, including source provenance and all three kernels; this still covers only accepted-017.
- Official full preflight run39450500400 failed before Lean due the caller’s invalid request identifier. The identifier was repaired. Pilot run39451125672 at fb7ebe8 was cancelled because the immutable source was superseded by required compatibility repairs. Early-certificate run39455278417 at12f83ea passed; its exact mechanical report is archived. See PalomarPreflight.md and the linked run for its terminal result.
- Full GoalRoot, the legacy pilot Solution, full-scope independent configurations and official formal intake remain incomplete. The main-and-components combined interface has compiled and passed 43 target axiom checks; root integration and official checks follow. No registration has occurred.
- All1207 original delivery files were rechecked against their preserved SHA-256 baseline and remain unchanged.

The original Lean4.33.1 audit and the migrated Lean4.35 checks are distinct artifacts. Compatibility changes preserve the original mathematical statements; compiler options are not substitutes for kernel validation. The exact scope is in SourceObligations.json and Coverage.md.

The isolated runner uses up to96 logical CPUs on the48-core host, with one Lake writer. Independent checks use bounded thread counts. Real dependency chains limit parallelism.
