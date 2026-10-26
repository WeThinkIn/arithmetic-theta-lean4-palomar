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

A complete SharpAndRootsSolution cold project build is running in the local
workspace, using the same source files and Lake configuration as this candidate.
Publication and official preflight remain pending evaluation of that result.
GitHub standard ubuntu-24.04 runners and palomar-standard-v1 remain configured.
The four documented size-limited interfaces remain included.
