# Audited instance proof optimization and baseline scheduling

This candidate replaces two expensive typeclass searches in
`P2M.Sol.S_AlgebraicCurve_tateTraceCompat_of_isSeparable` with explicit existing
instances. It restores the original Lake scheduling configuration after a local
comparison found that the added MemoryStage scheduling made the full Roots build
slower. Original libraries, challenge files, solution entry points and comparator
targets are preserved.

The complete module compiled in 195.014 seconds, compared with a historical
700.063-second module measurement with dependencies already available. This is
not a full-build or GitHub speedup claim. The declaration audit compared all 316
original declarations: exact type expressions, ordered universe parameters and
axiom sets are unchanged; no declarations were added or removed; no sorryAx is
present. Only the two intended theorem proof bodies changed. The accompanying
logs are local evidence and do not constitute a Palomar official report.

The earlier three-edit candidate was rejected because its explicit instance in
integralBasisDataOf changed a generated declaration type. That edit is absent.
An independent ProperTower reassociation candidate was also rejected by its
exact type audit and is absent.

A complete SharpAndRootsSolution cold project build passed on 2026-10-26 UTC,
using the same source files and Lake configuration as this candidate. It completed
12,099 Lake jobs in 8,483.099 seconds with four CPU cores and a memory limit of
16,431,083,520 bytes. Project build objects were initially absent; the existing
dependency cache was reused. All bound inputs remained unchanged, and the memory
controller recorded no OOM kills. See `cold-build-receipt.json`.

The historical build with the same original scheduling took 8,563.620 seconds;
the observed whole-build reduction is 0.94%. Relative to the historical version
with added MemoryStage scheduling (9,686.980 seconds), the reduction is 12.43%.
These measurements were not contemporaneous. The much larger improvement of the
individual TateTrace module must not be substituted for whole-build performance.

The Roots full-pipeline model estimates 20,037.787 seconds against the official
19,800-second allowance, exceeding it by about 237.787 seconds. It uses a historical
comparator duration and transfers a local build ratio to GitHub; neither is a
proven bound for the new revision. The official resource problem remains open.
See `budget-assessment.json` and `cold-build-assessment.json`.

A complete local FieldDiscriminant replay for the source candidate
`d65f577e4bfbe5a90116c7b20298ddb5b02118b1` is in progress. It preserves all 32
configured targets, reuses 2,980 source-bound modules from the successful Roots
build, and compiles 172 missing modules before full export and independent
Con-ron checking. No acceptance is inferred while this replay is incomplete.
The budget model identifies FieldDiscriminant as a candidate for a fresh full
standard-runner preflight; it does not justify repeating all six scopes.

GitHub standard ubuntu-24.04 runners and palomar-standard-v1 remain configured.
The four documented size-limited interfaces remain included. A new exact-revision
official report is required before ordinary intake. These local results do not
increase official endpoint coverage or establish semantic-review approval.
