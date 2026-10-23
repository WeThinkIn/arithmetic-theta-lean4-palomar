# Complete interfaces above the current Palomar size cap

These four source packages preserve the complete mathematical endpoints while making the remaining Palomar packaging constraint explicit. The complete development under `Proof/` has passed the recorded local Lean verification. Preparing a small independently auditable Challenge is a separate requirement for official Palomar verification.

## Published source snapshots

| Complete interface | Challenge bytes | Lines | Bytes above the cap |
| --- | ---: | ---: | ---: |
| [accepted-075](accepted-075/README.md) | 144,147 | 577 | 41,747 |
| [accepted-076](accepted-076/README.md) | 160,220 | 600 | 57,820 |
| [conservative-image-consumer](conservative-image-consumer/README.md) | 147,894 | 581 | 45,494 |
| [accepted-087](accepted-087/README.md) | 320,833 | 1,311 | 218,433 |

All four packages passed local compilation, shared-declaration checks, direct obligation accounting, original-endpoint recovery, and full serialized target-closure comparison. Their individual pages distinguish these checks from fresh export comparison, rendering, independent kernel replay, and official acceptance. Auxiliary obligation counts are not counts of original paper endpoints.

## Current submission constraint

The official [Challenge requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#L247-L256) impose both a 100 KiB (102,400-byte) cap and a 1,000-line cap. The [verifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/c02bbeaed888df45c4e28c4e99dba540ad21552a/scripts/verify_submission.py#L6171-L6181) rejects either excess. The separate preferred size of 32 KiB / 300 lines produces a warning. The hard cap concerns the Challenge file, not the total proof repository.

Challenge imports must also satisfy the official [canonical dependency rule](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#L300-L318). Moving project-specific definitions into another imported file does not remove this restriction.

Dependency pruning and reuse of standard definitions have reduced these interfaces, but the validated complete snapshots remain above the cap. This is not a proof that no smaller equivalent presentation exists. Further aggressive compression is deferred to preserve a maintainable presentation, the original quantifiers and hypotheses, actual level and geometric realization data, and the complete formal-series statements. No larger-Challenge exception has been assumed or requested. These sources are not being submitted as if they already met the cap.

The packages are outside the default Lake targets and the official preflight dispatch configurations. Each `Challenge.lean` is paired with its actual `Solution.lean` and explicit comparator configuration. Source availability does not add official endpoint coverage.

## Local reproduction

Use the repository's pinned Lean 4.35.0-rc2 toolchain and Mathlib manifest. From the repository root, first obtain the Mathlib cache and build the required proof dependencies:

```sh
lake exe cache get
lake build +FullSourceIntegrationR0268 +ArithmeticRecoveryLevelBridge669 +ArithmeticRecoveryConormalBridge +ArithmeticRecoveryZeroBridge +ArithmeticRecoveryTensorBridge +ArithmeticRecoveryPullbackBridge +ArithmeticRecoveryRemainingBridges
python3 interfaces/size-limited/compile-local.py accepted-075
```

Replace `accepted-075` with `accepted-076`, `accepted-087`, or `conservative-image-consumer` as needed. The helper compiles the selected Challenge, the shared support theorem when required, and its Solution under separate `.lake/size-limited` output directories. It checks the source snapshot hashes before compiling. This command is a compilation check; it does not run the complete Comparator/export/kernel/render pipeline or submit anything to Palomar. The published audit receipts specify which additional checks were completed for each snapshot.

The exact original paper statements remain in [`docs/SourceObligations.json`](../../docs/SourceObligations.json). The full proof remains under [`Proof/`](../../Proof/). The [manifest](manifest.json) binds the published Lean source files, comparator configurations, and audit records.
