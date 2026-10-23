# Complete interface: accepted-076

Original endpoint: `ArithmeticThetaExtendedMetaplecticR0241.cyclotomic_extended_modularity`.

This is a source snapshot of the complete independent verification interface. The original endpoint remains part of the complete formal proof under `Proof/`. Its precise statement is recorded in [`docs/SourceObligations.json`](../../../docs/SourceObligations.json).

The Challenge contains **160,220 bytes and 600 lines**, with **45 theorem obligations** and **5 definition obligations**. It exceeds Palomar's current 102,400-byte Challenge cap by **57,820 bytes**. It is published for inspection and local reproduction, and is not configured as an eligible official submission.

Compilation, shared-declaration checks, direct proof-obligation accounting, original-endpoint recovery, and the official Comparator's `compareAt` algorithm on the full serialized target closure passed locally. Fresh NDJSON export comparison, a separate three-kernel replay for this interface, and official Palomar verification have not been completed for this snapshot.

`Challenge.lean` deliberately uses `sorry` for the configured obligations. `Solution.lean` imports the actual proofs. The Challenge alone is a specification, not a proof; inspect the comparator configuration and the Solution together. The three arithmetic interfaces retain five constrained definition obligations and their original-recovery checks. The projective-ratio interface retains the actual full geometric statement and complete-series interpretation.

The files in [`audit/`](audit/) record the scope of each completed local check. Absolute paths in archival receipts identify the original local run; the repository-relative files and SHA-256 values in the [snapshot manifest](../manifest.json) identify the published source. Historical receipts do not certify a fresh clean build of every later repository commit.

See the [shared reproduction instructions](../README.md#local-reproduction). The generic `Challenge` and `Solution` module names are intentional; each interface is built in a separate output directory.
