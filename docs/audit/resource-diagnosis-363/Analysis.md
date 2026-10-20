# Confirmed diagnosis

Official run39461299032 (submission8427cc7ebd18, source commit2bd02cf8a38d686dc7a56012b1ca0291443816c9) stopped in solution-build with infrastructure/resource-exhausted, exit137, systemd_result=oom-kill and memory_events.oom_kill=9. deadline_fired and supervisor_timeout are false. The protected Challenge had already exported successfully. The report does not contain a Lean proof-error diagnostic, and the Solution export / external-kernel phases had not been reached. This run therefore neither refutes the proofs nor establishes that they compile under the official cold-build resource budget.

The exact failed commit lakefile was fetched read-only and its SHA256 matches the report:2556e31e095553d1e89a7adde54f462abea72302dd0809ae0cc847150c7bb073. It contains neither weakLeanArgs nor moreLeanArgs. The downloaded failed workflow log confirms the resource-failure message and does not expose a per-module compiler trace identifying a unique offending module.

Measured solution-build cgroup peak:15824445440bytes. Reported host capacity:16759308288bytes, effective CPUs4. Profile-derived memory.high:15921342873bytes, memory.max:16424122122bytes. The peak is BELOW both reported thresholds, and the recorded oom counter is0 although oom_kill is9. It is therefore too strong to assert that this precise leaf cgroup's memory.max was proven exceeded. The evidence establishes OOM killing within the workload; ancestor/global host pressure or sampling/accounting details may explain the observed limit/peak relation. Peak memory alone does not identify the largest individual Lean process or actual concurrent compiler count. Aggregate CPU use is28901.138016seconds; there is no evidence of a deadline firing.

# Immutable pipeline and approved resources

The pipeline source was fetched at d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44. fetch-receipt.json binds Git blob ids and the receipt binds content SHA256. No latest-branch assumptions were used.

verification-profile.json defines palomar-standard-v1:GitHub-hosted ubuntu-24.04, minimum host memory15032385536bytes (14GiB), memory.high95%, memory.max98%,32768tasks,19800seconds execution budget and350minutes job timeout. The source cache policy explicitly requires fresh submitted .lake state and permits pinned Mathlib cache artifacts. verify_submission.py removes untrusted Lake state and rejects prebuilt output outside that fresh state.

execution-profiles.json separately approves palomar-namespace-16x32-v1 and makes it the catalogue DEFAULT. Its required labels are nscloud-ubuntu-24.04-amd64-16x32-with-features and namespace-features:container.privileged=true. Minimum memory is30064771072bytes (28GiB), and verification_profile.py explicitly checks at least16effective CPUs. It inherits the same standard verification policy and remaining limits. It changes capacity, not the kernels, axioms, comparator or source checking. No64GB profile is present at this fixed revision.

The current caller explicitly selects standard, overriding that default. Selecting the approved Namespace profile would be a supported capacity change if its runner is actually available to the calling repository. A reusable workflow runs on runners available to the caller; an approved label does not create a runner or entitlement automatically.

Read-only authenticated API evidence,2026-10-20 19:13:36UTC:

- GET repos/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runners:HTTP200,total_count0,runners[].
- GET users/WeThinkIn:HTTP200,type=User.
- GET orgs/WeThinkIn/actions/runner-groups:HTTP404; this owner is a personal account, so this is not evidence of an accessible organization runner group.

These results establish no currently registered repository self-hosted runner. They do not exclude an unobserved on-demand/JIT integration. There is no positive evidence that the Namespace labels are usable here. Do not dispatch to them merely on the assumption that Palomar's own runners are inherited, install an app or purchase capacity automatically. A future confirmed available Namespace runner or operator-owned official verification could use execution_profile:palomar-namespace-16x32-v1 without altering verification semantics.

# Which concurrency controls actually reach the build

At verify_submission.py:6226–6238 the fixed verifier runs exactly lake build <solution_module> in its sandbox. There is no jobs option in that call and no workflow input for a Lake worker limit. Its SANDBOX_ENVIRONMENT allowlist at278–295 excludes LEAN_NUM_THREADS, LAKE_JOBS and LAKE_NUM_JOBS; supervisor_command only passes listed variables. Thus adding caller-level LEAN_NUM_THREADS is NOT an effective way to throttle this fixed official sandbox.

The pinned Lean runtime object.cpp:1095–1110 confirms LEAN_NUM_THREADS configures the default task manager (otherwise hardware concurrency). This applies to a Lake executable's runtime initialization. The Lean compiler shell separately defaults its processing threads to hardware concurrency (Lean/Shell.lean:220–238), and -j/--threads overrides that value. Do not conflate these two controls.

The pinned Lake source has no normal build CLI -j or package maxJobs/worker setting in the inspected CLI/Config/Load APIs. Lake build jobs run on runtime tasks; buildLean calls rawProc, which calls IO.Process.output. The latter blocks reading stderr and then Child.wait, with a dedicated task reading stdout. Ordinary active compiler jobs consequently occupy worker tasks while subprocesses run, although internal task waits can temporarily grow the pool and dedicated tasks are separate. A thread-pool setting is not a rigorous universal process semaphore. There is no phase task-count measurement in the failed report sufficient to reconstruct its exact width.

There are two project-controlled Lean-compiler argument fields:

- moreLeanArgs participates in build traces.
- weakLeanArgs is expressly documented as not participating in traces, for runtime arguments which should not force rebuilds. It comes before moreLeanArgs.

Lake/Config/LeanConfig.lean:173–180 documents the latter; LeanLib.lean:225–226 combines package and library weak arguments; Build/Module.lean:996 prepends them to strong arguments; Build/Actions.lean:36 forwards them to the actual Lean compiler. Therefore the preferred initial repository change is the PACKAGE-TOP-LEVEL TOML entry, before any[[require]]or[[lean_lib]]table:

```toml
weakLeanArgs = ["-j1"]
```

This limits each Lean compiler's internal worker count, without triggering needless invalidation of existing local build traces. It does NOT limit the number of simultaneous Lake compiler subprocesses. It applies to the submitted package's libraries; it does not rewrite Mathlib or dependency package configurations. A later strong -j argument could override it, so the actual argv must be inspected. The failed commit has no conflicting argument field.

The fixed pipeline has no weakLeanArgs/moreLeanArgs field whitelist and does not filter Lake-generated compiler arguments in solution-build. The environment whitelist does not block Lake reading this committed TOML field. This is an ordinary build-scheduling change that preserves trust level, proof bodies and all later mandatory validation. The requested tiny isolated Lake verbose-build argv check has now PASSED in0.565seconds. The three actual compiler invocations for LeafA, LeafB and Probe each contain `/bin/lean -j1`. See tiny-lake-argv.log and tiny-lake-compiler-argv.json. The local Lake runtime was explicitly limited to2threads to keep this probe small; the compiler -j1 arguments were supplied by the package-top-level TOML field, not by that environment variable. No production project was modified and this tiny package is not a cold-build capacity test.

A second, separately measured candidate is strong argument -DElab.async=false (or the equivalent leanOptions field) to disable asynchronous elaboration explicitly. CoreM.lean documents the option and the CLI's default override to true. Its generated proof/build behavior can change, so do not silently treat it as an already-tested weak trace-neutral adjustment. Several existing source modules already set it false locally. Do not use trust-level changes, axioms, prebuilt submitted .olean files, kernel skipping or replacing required outputs as memory remedies.

# First actionable plan and honest success criteria

1. Validate weakLeanArgs=["-j1"] in an isolated tiny package by observing the exact compiler argv; confirm the option is package-wide, not accidentally scoped under one library or dependency table.
2. Commit that runtime-only setting after the local check, preserving statements and proofs. An official retry at the resulting immutable commit is a RESOURCE-DIAGNOSTIC retry, not a claim that OOM has been solved. Do not restart unchanged source/resource conditions repeatedly. Leave currently running39469688913 and39479248485 alone.
3. Before claiming16GB cold-build viability, run the actual target with all submitted-project objects absent in a NEW isolated workspace, while retaining only the verified pinned Mathlib cache permitted by official policy. Use a4-vCPU VM or a carefully documented equivalent Lake-thread/CPU constraint, impose the reported memory ceiling, and record complete process-tree RSS/cgroup memory peak, concurrent Lean children and module argv over time. A taskset on a large host alone may not make hardware-concurrency detection equal to a4-vCPU VM; record the detected runtime threads. Do not delete or reuse shared warm project .lake artifacts as the experiment.
4. If a single compiler or the aggregate still approaches the limit, use the measured culprit to split large implementation files along genuine proof dependencies and prune unnecessary imports while preserving theorem types and exact semantic closure. Validate each refactor and the whole target. If four simultaneous large Lean processes remain the problem, obtain a supported provider-level Lake-runtime throttle or confirmed larger approved runner. The fixed standard profile currently exposes no caller-controlled Lake-width setting.
5. After a successful cold build, run the unchanged official pipeline, which must still perform Solution export, comparator, axiom closure and all required kernels. Local warm-build success, local imported-object audits, and the new-j1 argv check do not establish those outcomes or a16GB cold-build pass.

# Why smaller Challenges alone are insufficient

The current-source static import scan (not the old submitted commit's exact graph) finds3130project-local modules and597657source lines for MainAndComponentsSolution;3130/597695 for CompleteMainAndComponentsSolution;3123/603735 for SharpAdaptiveImageSolution. More than1700modules in each closure directly import Mathlib. Shared heavy dependencies include ProperTowerAutomorphismEffectivityPreludeR0137 (9113lines) and several large residue/Riemann–Roch proof modules. These counts are literal source import traversal, excluding external Mathlib closure; they do not measure simultaneous memory or prove which module caused OOM. They do show that shrinking only the public Challenge or splitting arithmetic output groups leaves almost the same underlying cold-build work. The verifier builds the selected Solution module, not all defaultTargets indiscriminately, so deleting a GoalRoot default target is not a demonstrated remedy either.

# Scope and safety of this investigation

Read-only GitHub API/log fetches and local source/report reads were performed, followed by the explicitly requested tiny isolated three-module Lake build. New evidence files are confined to evidence/resource-diagnosis-363. No credentials were printed or read from configuration content. No external messages were sent; no workflow, project file, shared .lake, existing run or official request was changed. Existing run39469688913/39479248485 were neither cancelled nor restarted. The proposed weakLeanArgs fix now has direct compiler-argv evidence; its full-project resource effect remains unmeasured and is not a verified16GB solution.
