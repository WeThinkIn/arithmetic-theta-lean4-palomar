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

Rebuild the recovery roots with
`lake build +FactorBridge +SquareFactorBridge +ConsumerFactorBridge`.

| Component | Configuration | Statement source |
| --- | --- | --- |
| Arithmetic matrix geometry over a cyclotomic field | [comparator-arithmetic-matrix.json](../comparator-arithmetic-matrix.json) | [Challenge](../ArithmeticThetaArithmeticMatrixChallenge.lean) |
| Actual compact cyclotomic level structure | [comparator-arithmetic-compact.json](../comparator-arithmetic-compact.json) | [Challenge](../ArithmeticThetaArithmeticCompactChallenge.lean) |
| Conservative cutoff with complete kernel and image data | [comparator-arithmetic-consumer.json](../comparator-arithmetic-consumer.json) | [Challenge](../ArithmeticThetaArithmeticConsumerChallenge.lean) |
| Transfer of section image data to the same geometric family | [comparator-arithmetic-transfer.json](../comparator-arithmetic-transfer.json) | [Challenge](../ArithmeticThetaArithmeticTransferChallenge.lean) |
| Standard extension of the arithmetic level structure | [comparator-arithmetic-standard.json](../comparator-arithmetic-standard.json) | [Challenge](../ArithmeticThetaArithmeticStandardChallenge.lean) |
| Transport of interior geometric data under field extension | [comparator-arithmetic-interior.json](../comparator-arithmetic-interior.json) | [Challenge](../ArithmeticThetaArithmeticInteriorChallenge.lean) |
| Transport of the elliptic-family classifier | [comparator-arithmetic-classifier.json](../comparator-arithmetic-classifier.json) | [Challenge](../ArithmeticThetaArithmeticClassifierChallenge.lean) |
| Transport of normalized comparison arrows | [comparator-arithmetic-arrow.json](../comparator-arithmetic-arrow.json) | [Challenge](../ArithmeticThetaArithmeticArrowChallenge.lean) |
| Transport of the Tate disk under field extension | [comparator-arithmetic-disk.json](../comparator-arithmetic-disk.json) | [Challenge](../ArithmeticThetaArithmeticDiskChallenge.lean) |
| Certificates for the exact rational solver | [comparator-arithmetic-solver.json](../comparator-arithmetic-solver.json) | [Challenge](../ArithmeticThetaArithmeticSolverChallenge.lean) |
| Complete-series output certificate | [comparator-arithmetic-output.json](../comparator-arithmetic-output.json) | [Challenge](../ArithmeticThetaArithmeticOutputChallenge.lean) |
| Compatibility of square comparisons under field extension | [comparator-arithmetic-triangle.json](../comparator-arithmetic-triangle.json) | [Challenge](../ArithmeticThetaArithmeticTriangleChallenge.lean) |
