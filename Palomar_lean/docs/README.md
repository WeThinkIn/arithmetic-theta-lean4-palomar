# Palomar documentation and verification records

These documents describe the Lean 4.35.0-rc2 adaptation, its mathematical scope,
and the verification performed at recorded source revisions. For the original
Lean 4.33.1 proof and reproducibility instructions, use
[`ArithmeticTheta_Lean4/`](../../ArithmeticTheta_Lean4/REPRODUCE.md).

| Read about | Document |
| --- | --- |
| Exact original theorem statements | [SourceObligations.json](SourceObligations.json) |
| Mapping of the thirteen original requirements | [RequirementCoverage.json](RequirementCoverage.json) |
| Independent interface coverage and remaining scope | [Coverage.md](Coverage.md) |
| Recorded official Palomar results | [PalomarPreflight.md](PalomarPreflight.md) |
| Porting status and local verification | [MigrationStatus.md](MigrationStatus.md) and [VerificationPlan.md](VerificationPlan.md) |
| Mathematical recovery interfaces | [ArithmeticRecovery.md](ArithmeticRecovery.md) and [ProjectiveRecovery.md](ProjectiveRecovery.md) |
| Authors, AI contributions and third-party attribution | [AIContributions.md](AIContributions.md) and [ThirdParty/README.md](ThirdParty/README.md) |
| Build receipts, probes and verification evidence | [audit/](audit/) |
| Repository organization | [Layout migration](maintenance/palomar-layout-20261106.md) and [main-branch policy](../../CONTRIBUTING.md) |

## Reading historical evidence

The four former root directories `Proof/`, `challenges/`, `docs/` and
`submissions/` now reside under `Palomar_lean/`. Prefix a path from the former
layout with `Palomar_lean/` to find its current location. The
[layout migration record](maintenance/palomar-layout-20261106.md) describes this
mapping and the checks performed for the move.

Historical JSON receipts, logs, proof probes, source maps and audit scripts
retain their recorded paths, hashes and source revisions. Their contents are
evidence of those revisions; moving their containing directory does not turn
them into a new verification run. Commands embedded in historical scripts can
also depend on the original checkout or server layout. Use the
[current build instructions](../../README.md#reproduce-the-formal-proof) for
the maintained layout, or check out an evidence record's original commit when
replaying that historical workflow.

Local compilation, mechanical checking, semantic review and registry acceptance
have distinct scopes. Each report's recorded status and source revision govern
what it establishes.
