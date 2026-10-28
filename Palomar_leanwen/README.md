# Palomar Lean verification interfaces

本目录集中存放 Palomar 验证使用的 **154 个 Lean 入口文件**和 **77 个 comparator JSON 配置**。每个配置对应一个 Challenge/Solution 模块对；下表可直接查看配置、独立命题和证明入口。

## Build and verification

Run commands from the repository root with the pinned Lean **4.35.0-rc2** toolchain:

```bash
lake build +CompleteMainAndComponentsSolution
lake comparator --config Palomar_leanwen/comparator-main-complete.json
```

The comparator command requires the Palomar comparator tooling described in the [repository verification instructions](../README.md#reproduce-the-formal-proof). For the official pipeline, open [Palomar official mechanical preflight](../.github/workflows/palomar-preflight.yml), select `main`, and choose a `Palomar_leanwen/comparator-*.json` configuration. The default `comparator.json` is a legacy, narrower specification; select the named scope you intend to verify.

Lean module names, imports, declarations and comparator contents are preserved. The root [Lake configuration](../lakefile.toml) uses this directory as the source root for these modules, so existing `lake build +ModuleName` targets remain valid. The shared mathematical development is in [`Proof/`](../Proof/), with scope descriptions in [`challenges/`](../challenges/) and submission metadata in [`submissions/`](../submissions/).

The independent [local Lean 4.33.1 reproduction](../local-reproduction/REPRODUCE.md), its dependency files and its release assets are unchanged. Historical audit records retain their original paths and source revisions; moving files does not confer a new Palomar acceptance.

## Scope index

| Configuration | Challenge | Solution |
| --- | --- | --- |
| [arbitrary-rigidification](comparator-arbitrary-rigidification.json) | [ArbitraryRigidificationChallenge](ArbitraryRigidificationChallenge.lean) | [ArbitraryRigidificationSolution](ArbitraryRigidificationSolution.lean) |
| [arithmetic-arrow](comparator-arithmetic-arrow.json) | [ArithmeticThetaArithmeticArrowChallenge](ArithmeticThetaArithmeticArrowChallenge.lean) | [ArithmeticThetaArithmeticArrowSolution](ArithmeticThetaArithmeticArrowSolution.lean) |
| [arithmetic-classifier](comparator-arithmetic-classifier.json) | [ArithmeticThetaArithmeticClassifierChallenge](ArithmeticThetaArithmeticClassifierChallenge.lean) | [ArithmeticThetaArithmeticClassifierSolution](ArithmeticThetaArithmeticClassifierSolution.lean) |
| [arithmetic-compact](comparator-arithmetic-compact.json) | [ArithmeticThetaArithmeticCompactChallenge](ArithmeticThetaArithmeticCompactChallenge.lean) | [ArithmeticThetaArithmeticCompactSolution](ArithmeticThetaArithmeticCompactSolution.lean) |
| [arithmetic-consumer](comparator-arithmetic-consumer.json) | [ArithmeticThetaArithmeticConsumerChallenge](ArithmeticThetaArithmeticConsumerChallenge.lean) | [ArithmeticThetaArithmeticConsumerSolution](ArithmeticThetaArithmeticConsumerSolution.lean) |
| [arithmetic-disk](comparator-arithmetic-disk.json) | [ArithmeticThetaArithmeticDiskChallenge](ArithmeticThetaArithmeticDiskChallenge.lean) | [ArithmeticThetaArithmeticDiskSolution](ArithmeticThetaArithmeticDiskSolution.lean) |
| [arithmetic-interior](comparator-arithmetic-interior.json) | [ArithmeticThetaArithmeticInteriorChallenge](ArithmeticThetaArithmeticInteriorChallenge.lean) | [ArithmeticThetaArithmeticInteriorSolution](ArithmeticThetaArithmeticInteriorSolution.lean) |
| [arithmetic-matrix](comparator-arithmetic-matrix.json) | [ArithmeticThetaArithmeticMatrixChallenge](ArithmeticThetaArithmeticMatrixChallenge.lean) | [ArithmeticThetaArithmeticMatrixSolution](ArithmeticThetaArithmeticMatrixSolution.lean) |
| [arithmetic-output](comparator-arithmetic-output.json) | [ArithmeticThetaArithmeticOutputChallenge](ArithmeticThetaArithmeticOutputChallenge.lean) | [ArithmeticThetaArithmeticOutputSolution](ArithmeticThetaArithmeticOutputSolution.lean) |
| [arithmetic-solver](comparator-arithmetic-solver.json) | [ArithmeticThetaArithmeticSolverChallenge](ArithmeticThetaArithmeticSolverChallenge.lean) | [ArithmeticThetaArithmeticSolverSolution](ArithmeticThetaArithmeticSolverSolution.lean) |
| [arithmetic-standard](comparator-arithmetic-standard.json) | [ArithmeticThetaArithmeticStandardChallenge](ArithmeticThetaArithmeticStandardChallenge.lean) | [ArithmeticThetaArithmeticStandardSolution](ArithmeticThetaArithmeticStandardSolution.lean) |
| [arithmetic-transfer](comparator-arithmetic-transfer.json) | [ArithmeticThetaArithmeticTransferChallenge](ArithmeticThetaArithmeticTransferChallenge.lean) | [ArithmeticThetaArithmeticTransferSolution](ArithmeticThetaArithmeticTransferSolution.lean) |
| [arithmetic-triangle](comparator-arithmetic-triangle.json) | [ArithmeticThetaArithmeticTriangleChallenge](ArithmeticThetaArithmeticTriangleChallenge.lean) | [ArithmeticThetaArithmeticTriangleSolution](ArithmeticThetaArithmeticTriangleSolution.lean) |
| [common-half-hodge](comparator-common-half-hodge.json) | [CommonHalfHodgeChallenge](CommonHalfHodgeChallenge.lean) | [CommonHalfHodgeSolution](CommonHalfHodgeSolution.lean) |
| [common-unary](comparator-common-unary.json) | [CommonUnaryChallenge](CommonUnaryChallenge.lean) | [CommonUnarySolution](CommonUnarySolution.lean) |
| [compact-alpha-half-line](comparator-compact-alpha-half-line.json) | [CompactAlphaHalfLineChallenge](CompactAlphaHalfLineChallenge.lean) | [CompactAlphaHalfLineSolution](CompactAlphaHalfLineSolution.lean) |
| [compact-alpha](comparator-compact-alpha.json) | [CompactAlphaChallenge](CompactAlphaChallenge.lean) | [CompactAlphaSolution](CompactAlphaSolution.lean) |
| [compact-unary](comparator-compact-unary.json) | [CompactUnaryChallenge](CompactUnaryChallenge.lean) | [CompactUnarySolution](CompactUnarySolution.lean) |
| [component-cusp](comparator-component-cusp.json) | [ComponentCuspChallenge](ComponentCuspChallenge.lean) | [ComponentCuspSolution](ComponentCuspSolution.lean) |
| [component-discriminant](comparator-component-discriminant.json) | [ComponentDiscriminantChallenge](ComponentDiscriminantChallenge.lean) | [ComponentDiscriminantSolution](ComponentDiscriminantSolution.lean) |
| [component-hodge-degree](comparator-component-hodge-degree.json) | [ComponentHodgeDegreeChallenge](ComponentHodgeDegreeChallenge.lean) | [ComponentHodgeDegreeSolution](ComponentHodgeDegreeSolution.lean) |
| [conservative-matrix-geometry](comparator-conservative-matrix-geometry.json) | [ConservativeMatrixGeometryChallenge](ConservativeMatrixGeometryChallenge.lean) | [ConservativeMatrixGeometrySolution](ConservativeMatrixGeometrySolution.lean) |
| [discriminant-twist-root](comparator-discriminant-twist-root.json) | [DiscriminantTwistRootChallenge](DiscriminantTwistRootChallenge.lean) | [DiscriminantTwistRootSolution](DiscriminantTwistRootSolution.lean) |
| [early](comparator-early.json) | [EarlyCertificateChallenge](EarlyCertificateChallenge.lean) | [EarlyCertificateSolution](EarlyCertificateSolution.lean) |
| [even-point-evaluation](comparator-even-point-evaluation.json) | [EvenPointEvaluationChallenge](EvenPointEvaluationChallenge.lean) | [EvenPointEvaluationSolution](EvenPointEvaluationSolution.lean) |
| [field-discriminant](comparator-field-discriminant.json) | [FieldDiscriminantChallenge](FieldDiscriminantChallenge.lean) | [FieldDiscriminantSolution](FieldDiscriminantSolution.lean) |
| [field-unary-naturality](comparator-field-unary-naturality.json) | [FieldUnaryNaturalityChallenge](FieldUnaryNaturalityChallenge.lean) | [FieldUnaryNaturalitySolution](FieldUnaryNaturalitySolution.lean) |
| [field-unary](comparator-field-unary.json) | [FieldUnaryChallenge](FieldUnaryChallenge.lean) | [FieldUnarySolution](FieldUnarySolution.lean) |
| [formal-cover](comparator-formal-cover.json) | [FormalCoverChallenge](FormalCoverChallenge.lean) | [FormalCoverSolution](FormalCoverSolution.lean) |
| [full-scheme-discriminant](comparator-full-scheme-discriminant.json) | [FullSchemeDiscriminantChallenge](FullSchemeDiscriminantChallenge.lean) | [FullSchemeDiscriminantSolution](FullSchemeDiscriminantSolution.lean) |
| [isogeny-alpha-cusps](comparator-isogeny-alpha-cusps.json) | [IsogenyAlphaCuspsChallenge](IsogenyAlphaCuspsChallenge.lean) | [IsogenyAlphaCuspsSolution](IsogenyAlphaCuspsSolution.lean) |
| [isogeny-half-line](comparator-isogeny-half-line.json) | [IsogenyHalfLineChallenge](IsogenyHalfLineChallenge.lean) | [IsogenyHalfLineSolution](IsogenyHalfLineSolution.lean) |
| [key-tate](comparator-key-tate.json) | [KeyTateNormalizationChallenge](KeyTateNormalizationChallenge.lean) | [KeyTateNormalizationSolution](KeyTateNormalizationSolution.lean) |
| [main-and-components](comparator-main-and-components.json) | [MainAndComponentsChallenge](MainAndComponentsChallenge.lean) | [MainAndComponentsSolution](MainAndComponentsSolution.lean) |
| [main-complete](comparator-main-complete.json) | [CompleteMainAndComponentsChallenge](CompleteMainAndComponentsChallenge.lean) | [CompleteMainAndComponentsSolution](CompleteMainAndComponentsSolution.lean) |
| [multiplier-fourth](comparator-multiplier-fourth.json) | [MultiplierFourthChallenge](MultiplierFourthChallenge.lean) | [MultiplierFourthSolution](MultiplierFourthSolution.lean) |
| [period-one](comparator-period-one.json) | [PeriodOneChallenge](PeriodOneChallenge.lean) | [PeriodOneSolution](PeriodOneSolution.lean) |
| [phase-free-alpha-descent](comparator-phase-free-alpha-descent.json) | [PhaseFreeAlphaDescentChallenge](PhaseFreeAlphaDescentChallenge.lean) | [PhaseFreeAlphaDescentSolution](PhaseFreeAlphaDescentSolution.lean) |
| [phase-free-key](comparator-phase-free-key.json) | [PhaseFreeKeyChallenge](PhaseFreeKeyChallenge.lean) | [PhaseFreeKeySolution](PhaseFreeKeySolution.lean) |
| [phase-free-multiplier](comparator-phase-free-multiplier.json) | [PhaseFreeMultiplierChallenge](PhaseFreeMultiplierChallenge.lean) | [PhaseFreeMultiplierSolution](PhaseFreeMultiplierSolution.lean) |
| [projective-alignment](comparator-projective-alignment.json) | [ArithmeticThetaProjectiveAlignmentChallenge](ArithmeticThetaProjectiveAlignmentChallenge.lean) | [ArithmeticThetaProjectiveAlignmentSolution](ArithmeticThetaProjectiveAlignmentSolution.lean) |
| [projective-commutator](comparator-projective-commutator.json) | [ArithmeticThetaProjectiveCommutatorChallenge](ArithmeticThetaProjectiveCommutatorChallenge.lean) | [ArithmeticThetaProjectiveCommutatorSolution](ArithmeticThetaProjectiveCommutatorSolution.lean) |
| [projective-faithfulness](comparator-projective-faithfulness.json) | [ArithmeticThetaProjectiveFaithfulnessChallenge](ArithmeticThetaProjectiveFaithfulnessChallenge.lean) | [ArithmeticThetaProjectiveFaithfulnessSolution](ArithmeticThetaProjectiveFaithfulnessSolution.lean) |
| [projective-fieldnormal](comparator-projective-fieldnormal.json) | [ArithmeticThetaProjectiveFieldnormalChallenge](ArithmeticThetaProjectiveFieldnormalChallenge.lean) | [ArithmeticThetaProjectiveFieldnormalSolution](ArithmeticThetaProjectiveFieldnormalSolution.lean) |
| [projective-genericdual](comparator-projective-genericdual.json) | [ArithmeticThetaProjectiveGenericdualChallenge](ArithmeticThetaProjectiveGenericdualChallenge.lean) | [ArithmeticThetaProjectiveGenericdualSolution](ArithmeticThetaProjectiveGenericdualSolution.lean) |
| [projective-geometry](comparator-projective-geometry.json) | [ArithmeticThetaProjectiveGeometryChallenge](ArithmeticThetaProjectiveGeometryChallenge.lean) | [ArithmeticThetaProjectiveGeometrySolution](ArithmeticThetaProjectiveGeometrySolution.lean) |
| [projective-induceddual](comparator-projective-induceddual.json) | [ArithmeticThetaProjectiveInduceddualChallenge](ArithmeticThetaProjectiveInduceddualChallenge.lean) | [ArithmeticThetaProjectiveInduceddualSolution](ArithmeticThetaProjectiveInduceddualSolution.lean) |
| [projective-intertwining](comparator-projective-intertwining.json) | [ArithmeticThetaProjectiveIntertwiningChallenge](ArithmeticThetaProjectiveIntertwiningChallenge.lean) | [ArithmeticThetaProjectiveIntertwiningSolution](ArithmeticThetaProjectiveIntertwiningSolution.lean) |
| [projective-invariantline](comparator-projective-invariantline.json) | [ArithmeticThetaProjectiveInvariantlineChallenge](ArithmeticThetaProjectiveInvariantlineChallenge.lean) | [ArithmeticThetaProjectiveInvariantlineSolution](ArithmeticThetaProjectiveInvariantlineSolution.lean) |
| [projective-inversion](comparator-projective-inversion.json) | [ArithmeticThetaProjectiveInversionChallenge](ArithmeticThetaProjectiveInversionChallenge.lean) | [ArithmeticThetaProjectiveInversionSolution](ArithmeticThetaProjectiveInversionSolution.lean) |
| [projective-inversionchange](comparator-projective-inversionchange.json) | [ArithmeticThetaProjectiveInversionchangeChallenge](ArithmeticThetaProjectiveInversionchangeChallenge.lean) | [ArithmeticThetaProjectiveInversionchangeSolution](ArithmeticThetaProjectiveInversionchangeSolution.lean) |
| [projective-midpoint](comparator-projective-midpoint.json) | [ArithmeticThetaProjectiveMidpointChallenge](ArithmeticThetaProjectiveMidpointChallenge.lean) | [ArithmeticThetaProjectiveMidpointSolution](ArithmeticThetaProjectiveMidpointSolution.lean) |
| [projective-model](comparator-projective-model.json) | [ArithmeticThetaProjectiveModelChallenge](ArithmeticThetaProjectiveModelChallenge.lean) | [ArithmeticThetaProjectiveModelSolution](ArithmeticThetaProjectiveModelSolution.lean) |
| [projective-naturality](comparator-projective-naturality.json) | [ArithmeticThetaProjectiveNaturalityChallenge](ArithmeticThetaProjectiveNaturalityChallenge.lean) | [ArithmeticThetaProjectiveNaturalitySolution](ArithmeticThetaProjectiveNaturalitySolution.lean) |
| [projective-orbit](comparator-projective-orbit.json) | [ArithmeticThetaProjectiveOrbitChallenge](ArithmeticThetaProjectiveOrbitChallenge.lean) | [ArithmeticThetaProjectiveOrbitSolution](ArithmeticThetaProjectiveOrbitSolution.lean) |
| [projective-pointedgroup](comparator-projective-pointedgroup.json) | [ArithmeticThetaProjectivePointedgroupChallenge](ArithmeticThetaProjectivePointedgroupChallenge.lean) | [ArithmeticThetaProjectivePointedgroupSolution](ArithmeticThetaProjectivePointedgroupSolution.lean) |
| [projective-quotient](comparator-projective-quotient.json) | [ArithmeticThetaProjectiveQuotientChallenge](ArithmeticThetaProjectiveQuotientChallenge.lean) | [ArithmeticThetaProjectiveQuotientSolution](ArithmeticThetaProjectiveQuotientSolution.lean) |
| [projective-ratiogenerator](comparator-projective-ratiogenerator.json) | [ArithmeticThetaProjectiveRatiogeneratorChallenge](ArithmeticThetaProjectiveRatiogeneratorChallenge.lean) | [ArithmeticThetaProjectiveRatiogeneratorSolution](ArithmeticThetaProjectiveRatiogeneratorSolution.lean) |
| [projective-square](comparator-projective-square.json) | [ArithmeticThetaProjectiveSquareChallenge](ArithmeticThetaProjectiveSquareChallenge.lean) | [ArithmeticThetaProjectiveSquareSolution](ArithmeticThetaProjectiveSquareSolution.lean) |
| [projective-testexists](comparator-projective-testexists.json) | [ArithmeticThetaProjectiveTestexistsChallenge](ArithmeticThetaProjectiveTestexistsChallenge.lean) | [ArithmeticThetaProjectiveTestexistsSolution](ArithmeticThetaProjectiveTestexistsSolution.lean) |
| [projective-transport](comparator-projective-transport.json) | [ArithmeticThetaProjectiveTransportChallenge](ArithmeticThetaProjectiveTransportChallenge.lean) | [ArithmeticThetaProjectiveTransportSolution](ArithmeticThetaProjectiveTransportSolution.lean) |
| [relative-alpha](comparator-relative-alpha.json) | [RelativeAlphaChallenge](RelativeAlphaChallenge.lean) | [RelativeAlphaSolution](RelativeAlphaSolution.lean) |
| [scheme-alpha-character](comparator-scheme-alpha-character.json) | [SchemeAlphaCharacterChallenge](SchemeAlphaCharacterChallenge.lean) | [SchemeAlphaCharacterSolution](SchemeAlphaCharacterSolution.lean) |
| [scheme-initial](comparator-scheme-initial.json) | [SchemeInitialChallenge](SchemeInitialChallenge.lean) | [SchemeInitialSolution](SchemeInitialSolution.lean) |
| [scheme-kato](comparator-scheme-kato.json) | [SchemeKatoChallenge](SchemeKatoChallenge.lean) | [SchemeKatoSolution](SchemeKatoSolution.lean) |
| [scheme-miller-phase](comparator-scheme-miller-phase.json) | [SchemeMillerPhaseChallenge](SchemeMillerPhaseChallenge.lean) | [SchemeMillerPhaseSolution](SchemeMillerPhaseSolution.lean) |
| [scheme-tate-unit](comparator-scheme-tate-unit.json) | [SchemeTateUnitChallenge](SchemeTateUnitChallenge.lean) | [SchemeTateUnitSolution](SchemeTateUnitSolution.lean) |
| [sharp-adaptive-image](comparator-sharp-adaptive-image.json) | [SharpAdaptiveImageChallenge](SharpAdaptiveImageChallenge.lean) | [SharpAdaptiveImageSolution](SharpAdaptiveImageSolution.lean) |
| [sharp-and-coordinates](comparator-sharp-and-coordinates.json) | [SharpAndCoordinatesChallenge](SharpAndCoordinatesChallenge.lean) | [SharpAndCoordinatesSolution](SharpAndCoordinatesSolution.lean) |
| [sharp-and-roots](comparator-sharp-and-roots.json) | [SharpAndRootsChallenge](SharpAndRootsChallenge.lean) | [SharpAndRootsSolution](SharpAndRootsSolution.lean) |
| [sharp-matrix-geometry](comparator-sharp-matrix-geometry.json) | [SharpMatrixGeometryChallenge](SharpMatrixGeometryChallenge.lean) | [SharpMatrixGeometrySolution](SharpMatrixGeometrySolution.lean) |
| [split-cusp](comparator-split-cusp.json) | [SplitCuspChallenge](SplitCuspChallenge.lean) | [SplitCuspSolution](SplitCuspSolution.lean) |
| [split-discriminant](comparator-split-discriminant.json) | [SplitDiscriminantChallenge](SplitDiscriminantChallenge.lean) | [SplitDiscriminantSolution](SplitDiscriminantSolution.lean) |
| [split-square-degree](comparator-split-square-degree.json) | [SplitSquareDegreeChallenge](SplitSquareDegreeChallenge.lean) | [SplitSquareDegreeSolution](SplitSquareDegreeSolution.lean) |
| [tate-alpha](comparator-tate-alpha.json) | [TateAlphaChallenge](TateAlphaChallenge.lean) | [TateAlphaSolution](TateAlphaSolution.lean) |
| [unary-geometric](comparator-unary-geometric.json) | [UnaryGeometricChallenge](UnaryGeometricChallenge.lean) | [UnaryGeometricSolution](UnaryGeometricSolution.lean) |
| [legacy default](comparator.json) | [Challenge](Challenge.lean) | [Solution](Solution.lean) |
