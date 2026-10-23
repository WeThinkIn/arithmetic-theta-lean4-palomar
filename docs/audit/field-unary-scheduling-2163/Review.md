# FieldUnary build scheduling and verification scope

The prior [official FieldUnary run 39957989305](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39957989305) exhausted memory during Solution compilation. It did not reach a Solution export or a kernel verdict. The [source-bound diagnosis](prior-official-oom.json) records five OOM kills. The complete original accepted-069 endpoint and its 32 configured obligations remain the verification target.

## Scheduling change

The Lake configuration introduces 16 build prerequisite edges. Fourteen edges serialize 15 measured high-memory modules; two additional edges separate `GlobalFamilyDiscriminantR0180` from `LocalComparisonFamilyR0067`, and `OpenUnaryDesignatedExpansionR0182` from `SchemeDiscriminantExistenceR0244`. Each added prerequisite waits for an existing local `.olean` target. The edges add no Lean imports or mathematical assumptions.

All existing compiler settings, the pinned Lean/Mathlib versions, and every mathematical source file are preserved. The complete 3,951-module dependency graph is acyclic and each module has exactly one owning library. The 178,659-byte Lake configuration passes the pinned official regular-file, configuration-size and TOML checks. The [static review](candidate-static-review.json) and [candidate configuration record](candidate-configuration.json) bind the exact configuration and source checks.

## Completed local evidence

The preceding 14-edge configuration completed a cold project build of the full 3,153-module FieldUnary closure in 10,087.108 seconds under four CPUs and an approximately 15.3 GiB memory limit. Existing canonical dependency caches were reused. Its memory peak approached the limit, and sampling found two additional late-stage overlap pairs, motivating the two edges above. Shared mapped dependency pages mean this local cgroup experiment is not a fresh official host reproduction.

The [full raw-object audit](baseline-exact-object-audit.json) remains **failed**: two generated proposition proofs in `FieldUnarySolution` differ from the older baseline, while all 3,152 dependency modules and the other root declarations compare exactly. Lean confirmed both differing auxiliary types are propositions and definitionally equal; the helpers are used and have not been ignored. The scheduling change has not been established as the cause of these differences.

A fresh export using the actual 14-edge cold-build objects is byte-identical to the historical complete configured Solution export: SHA-256 `caa74a077fe81cc5f1d246b56b6355789f006231eb8829f506e381108db4221a`, 2,577,828,799 bytes. The [full target-closure and standard-axiom comparison](baseline-full-strict.json) passed. This does not turn the raw-object audit into a pass and is not a new independent-kernel replay.

## Completed verification of the published configuration

The published 16-edge configuration completed the [full local cold FieldUnary build](cold-build-16-edges.json): 3,153 project modules and 12,083 Lake jobs, with exit code 0 in 10,182.244 seconds. The build used four CPUs, an approximately 15.3 GiB memory limit, and the existing canonical dependency cache. All 3,955 source bindings were [rechecked](cold-confirmation-16-edges.json). Memory pressure occurred (17,273 cgroup limit events), the recorded peak reached the limit, and the OOM-kill count was zero. This run establishes successful completion under the recorded local conditions; it does not establish spare memory capacity or a speed improvement over the preceding run.

The [complete exact-object comparison](exact-object-audit-16-edges.json) passed for all 3,153 modules and 67,489 constants against the source-identical 14-edge cold-build objects. Generated helper proofs and their bodies were included. This comparison uses a different baseline from the older failed raw-object audit above; that historical failure remains recorded.

The [fresh complete Solution export](cold-export-16-edges.json), produced from the actual 16-edge cold-build objects, contains 2,577,828,799 bytes and has SHA-256 `caa74a077fe81cc5f1d246b56b6355789f006231eb8829f506e381108db4221a`. It is byte-identical to the historical complete configured export. The [full target-closure and standard-axiom comparison](full-strict-16-edges.json) passed with unchanged input bindings. These results are not a new independent-kernel replay.

## Official verification boundary

[Official full preflight 40018009456](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/40018009456) tests the scheduling configuration at source commit `ede49ba93f1fce85660412ce31baaa8476a772f4`. At the time this local result was recorded, the official run was still in progress. It performs its own fresh build and verification; the local result does not establish official acceptance. No worker quota, timeout or Challenge limit is relaxed.

The original endpoint, Challenge, Solution and comparator configuration remain unchanged. The recorded official union remains 97/103 at previously verified revisions until an exact new official report is confirmed. Whole-paper semantic acceptance and registration remain incomplete.
