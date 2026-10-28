# Arithmetic modularity and image recovery components

The recovery theorems retain the original geometric witnesses, complete-series
identities and quantification over all field extensions. Their entry points are
`PalomarFactored882.original_cyclotomic_matrix_modularity`,
`PalomarSquare918.original_cyclotomic_extended_modularity` and
`PalomarConsumer897.original_conservative_image_consumer`.

The separately scoped interfaces below support those recoveries. Verification
of any one component is not verification of the complete original endpoint or
the whole paper. Original statement recovery, component provenance, official
mechanical checks and whole-paper semantic review remain distinct obligations.

The recovery dependency closure uses dedicated `ArithmeticRecovery*` modules.
`FactorBridge` imports `ArithmeticRecoveryBase`, which supplies the recovery
providers through their explicit module names. The repository-level `Solution`
module remains the finite-determination interface. These distinct module paths
preserve the recovery declaration namespaces and avoid resolving a provider
through an unrelated interface with the same module name.

Rebuild the recovery roots with
`lake build +FactorBridge +SquareFactorBridge +ConsumerFactorBridge`.

| Component | Configuration | Statement source |
| --- | --- | --- |
| Arithmetic matrix geometry over a cyclotomic field | [Palomar_lean/comparator-arithmetic-matrix.json](../Palomar_lean/comparator-arithmetic-matrix.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticMatrixChallenge.lean) |
| Actual compact cyclotomic level structure | [Palomar_lean/comparator-arithmetic-compact.json](../Palomar_lean/comparator-arithmetic-compact.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticCompactChallenge.lean) |
| Conservative cutoff with complete kernel and image data | [Palomar_lean/comparator-arithmetic-consumer.json](../Palomar_lean/comparator-arithmetic-consumer.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticConsumerChallenge.lean) |
| Transfer of section image data to the same geometric family | [Palomar_lean/comparator-arithmetic-transfer.json](../Palomar_lean/comparator-arithmetic-transfer.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticTransferChallenge.lean) |
| Standard extension of the arithmetic level structure | [Palomar_lean/comparator-arithmetic-standard.json](../Palomar_lean/comparator-arithmetic-standard.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticStandardChallenge.lean) |
| Transport of interior geometric data under field extension | [Palomar_lean/comparator-arithmetic-interior.json](../Palomar_lean/comparator-arithmetic-interior.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticInteriorChallenge.lean) |
| Transport of the elliptic-family classifier | [Palomar_lean/comparator-arithmetic-classifier.json](../Palomar_lean/comparator-arithmetic-classifier.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticClassifierChallenge.lean) |
| Transport of normalized comparison arrows | [Palomar_lean/comparator-arithmetic-arrow.json](../Palomar_lean/comparator-arithmetic-arrow.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticArrowChallenge.lean) |
| Transport of the Tate disk under field extension | [Palomar_lean/comparator-arithmetic-disk.json](../Palomar_lean/comparator-arithmetic-disk.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticDiskChallenge.lean) |
| Certificates for the exact rational solver | [Palomar_lean/comparator-arithmetic-solver.json](../Palomar_lean/comparator-arithmetic-solver.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticSolverChallenge.lean) |
| Complete-series output certificate | [Palomar_lean/comparator-arithmetic-output.json](../Palomar_lean/comparator-arithmetic-output.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticOutputChallenge.lean) |
| Compatibility of square comparisons under field extension | [Palomar_lean/comparator-arithmetic-triangle.json](../Palomar_lean/comparator-arithmetic-triangle.json) | [Challenge](../Palomar_lean/ArithmeticThetaArithmeticTriangleChallenge.lean) |
