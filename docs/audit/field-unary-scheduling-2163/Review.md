# FieldUnary build scheduling and verification scope

The prior [official FieldUnary run 39957989305](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39957989305) exhausted memory during Solution compilation. It did not reach a Solution export or a kernel verdict. The [source-bound diagnosis](prior-official-oom.json) records five OOM kills. The complete original accepted-069 endpoint and its 32 configured obligations remain the verification target.

## Scheduling change

The Lake configuration introduces 16 build prerequisite edges. Fourteen edges serialize 15 measured high-memory modules; two additional edges separate `GlobalFamilyDiscriminantR0180` from `LocalComparisonFamilyR0067`, and `OpenUnaryDesignatedExpansionR0182` from `SchemeDiscriminantExistenceR0244`. Each added prerequisite waits for an existing local `.olean` target. The edges add no Lean imports or mathematical assumptions.

All existing compiler settings, the pinned Lean/Mathlib versions, and every mathematical source file are preserved. The complete 3,951-module dependency graph is acyclic and each module has exactly one owning library. The 178,659-byte Lake configuration passes the pinned official regular-file, configuration-size and TOML checks. The [static review](candidate-static-review.json) and [candidate configuration record](candidate-configuration.json) bind the exact configuration and source checks.

## Completed local evidence

The preceding 14-edge configuration completed a cold project build of the full 3,153-module FieldUnary closure in 10,087.108 seconds under four CPUs and an approximately 15.3 GiB memory limit. Existing canonical dependency caches were reused. Its memory peak approached the limit, and sampling found two additional late-stage overlap pairs, motivating the two edges above. Shared mapped dependency pages mean this local cgroup experiment is not a fresh official host reproduction.

The [full raw-object audit](baseline-exact-object-audit.json) remains **failed**: two generated proposition proofs in `FieldUnarySolution` differ from the older baseline, while all 3,152 dependency modules and the other root declarations compare exactly. Lean confirmed both differing auxiliary types are propositions and definitionally equal; the helpers are used and have not been ignored. The scheduling change has not been established as the cause of these differences.

A fresh export using the actual 14-edge cold-build objects is byte-identical to the historical complete configured Solution export: SHA-256 `caa74a077fe81cc5f1d246b56b6355789f006231eb8829f506e381108db4221a`, 2,577,828,799 bytes. The [full target-closure and standard-axiom comparison](baseline-full-strict.json) passed. This does not turn the raw-object audit into a pass and is not a new independent-kernel replay.

## Current verification boundary

The complete local cold build of the published 16-edge configuration is still running. Its full object comparison against the 14-edge cold build and subsequent fresh export/strict comparison are queued behind successful prerequisites. No successful 16-edge resource result is claimed here.

One fresh official full preflight may run in parallel with that local experiment. This replaces the earlier plan to wait for the entire local resource experiment before official testing: the mathematical inputs and compiler settings are unchanged, the full build graph and official configuration constraints have been checked, and the added edges address observed memory overlaps. The official run performs its own fresh build and complete verification; publication and dispatch do not imply acceptance. No worker quota, timeout or Challenge limit is relaxed.

The original endpoint, Challenge, Solution and comparator configuration remain unchanged. The recorded official union remains 97/103 at previously verified revisions until an exact new official report is confirmed. Whole-paper semantic acceptance and registration remain incomplete.
