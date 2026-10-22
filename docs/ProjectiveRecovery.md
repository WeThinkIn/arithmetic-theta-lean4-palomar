# Projective theta recovery components

The development reconstructs the original global arithmetic projective-ratio
theorem using actual marked models, normalized scheme lifts, section actions,
fiber evaluations and invariant component ratios. The proof entry point is
`PalomarOriginal1413.original087` in `Proof/Original087Recovery2.lean`.
To rebuild the recovery entry point with the pinned toolchain, run
`lake build +Original087Recovery2`.

Its local audit checks the exact original statement and universe parameters,
standard axiom dependencies and absence of the original complete-theorem proof
shortcuts. This reconstruction introduces no additional hypotheses.

The 21 configurations below expose separately scoped mathematical components.
Their Challenge sources retain the audited definitions and statements. Each
configuration has its own metadata and selected targets. Component verification
does not by itself establish official verification or registration of the
complete original endpoint or whole paper. Complete interface provenance and
whole-paper semantic review remain required.

| Component | Configuration | Statement source |
| --- | --- | --- |
| Transfer of projective ratios through a line quotient | [`comparator-projective-quotient.json`](../comparator-projective-quotient.json) | [Challenge](../challenges/projective-quotient/ArithmeticThetaProjectiveQuotientChallenge.lean) |
| Arithmetic level geometry for projective theta ratios | [`comparator-projective-geometry.json`](../comparator-projective-geometry.json) | [Challenge](../challenges/projective-geometry/ArithmeticThetaProjectiveGeometryChallenge.lean) |
| Pointed Cartesian group law | [`comparator-projective-pointedgroup.json`](../comparator-projective-pointedgroup.json) | [Challenge](../challenges/projective-pointedgroup/ArithmeticThetaProjectivePointedgroupChallenge.lean) |
| Primitive theta commutator | [`comparator-projective-commutator.json`](../comparator-projective-commutator.json) | [Challenge](../challenges/projective-commutator/ArithmeticThetaProjectiveCommutatorChallenge.lean) |
| Invariant theta line | [`comparator-projective-invariantline.json`](../comparator-projective-invariantline.json) | [Challenge](../challenges/projective-invariantline/ArithmeticThetaProjectiveInvariantlineChallenge.lean) |
| Scheme Schroedinger orbit | [`comparator-projective-orbit.json`](../comparator-projective-orbit.json) | [Challenge](../challenges/projective-orbit/ArithmeticThetaProjectiveOrbitChallenge.lean) |
| Pushforward intertwining of theta actions | [`comparator-projective-intertwining.json`](../comparator-projective-intertwining.json) | [Challenge](../challenges/projective-intertwining/ArithmeticThetaProjectiveIntertwiningChallenge.lean) |
| Naturality of invariant components | [`comparator-projective-naturality.json`](../comparator-projective-naturality.json) | [Challenge](../challenges/projective-naturality/ArithmeticThetaProjectiveNaturalityChallenge.lean) |
| Existence of an arithmetic invariant ratio test | [`comparator-projective-testexists.json`](../comparator-projective-testexists.json) | [Challenge](../challenges/projective-testexists/ArithmeticThetaProjectiveTestexistsChallenge.lean) |
| Existence of a marked algebraic Tate model | [`comparator-projective-model.json`](../comparator-projective-model.json) | [Challenge](../challenges/projective-model/ArithmeticThetaProjectiveModelChallenge.lean) |
| Global sign alignment of theta lifts | [`comparator-projective-alignment.json`](../comparator-projective-alignment.json) | [Challenge](../challenges/projective-alignment/ArithmeticThetaProjectiveAlignmentChallenge.lean) |
| Unique transport of normalized lifts | [`comparator-projective-transport.json`](../comparator-projective-transport.json) | [Challenge](../challenges/projective-transport/ArithmeticThetaProjectiveTransportChallenge.lean) |
| Scheme theta inversion | [`comparator-projective-inversion.json`](../comparator-projective-inversion.json) | [Challenge](../challenges/projective-inversion/ArithmeticThetaProjectiveInversionChallenge.lean) |
| Midpoint theta lift | [`comparator-projective-midpoint.json`](../comparator-projective-midpoint.json) | [Challenge](../challenges/projective-midpoint/ArithmeticThetaProjectiveMidpointChallenge.lean) |
| Faithfulness of model lift comparison | [`comparator-projective-faithfulness.json`](../comparator-projective-faithfulness.json) | [Challenge](../challenges/projective-faithfulness/ArithmeticThetaProjectiveFaithfulnessChallenge.lean) |
| Square identity from faithful global action | [`comparator-projective-square.json`](../comparator-projective-square.json) | [Challenge](../challenges/projective-square/ArithmeticThetaProjectiveSquareChallenge.lean) |
| Symmetric change of inversion lift | [`comparator-projective-inversionchange.json`](../comparator-projective-inversionchange.json) | [Challenge](../challenges/projective-inversionchange/ArithmeticThetaProjectiveInversionchangeChallenge.lean) |
| Generic dual compatibility with global section action | [`comparator-projective-genericdual.json`](../comparator-projective-genericdual.json) | [Challenge](../challenges/projective-genericdual/ArithmeticThetaProjectiveGenericdualChallenge.lean) |
| Dual compatibility of the induced ideal lift | [`comparator-projective-induceddual.json`](../comparator-projective-induceddual.json) | [Challenge](../challenges/projective-induceddual/ArithmeticThetaProjectiveInduceddualChallenge.lean) |
| Normalization from a fixed section over a field | [`comparator-projective-fieldnormal.json`](../comparator-projective-fieldnormal.json) | [Challenge](../challenges/projective-fieldnormal/ArithmeticThetaProjectiveFieldnormalChallenge.lean) |
| Component ratios from a generator over a field spectrum | [`comparator-projective-ratiogenerator.json`](../comparator-projective-ratiogenerator.json) | [Challenge](../challenges/projective-ratiogenerator/ArithmeticThetaProjectiveRatiogeneratorChallenge.lean) |
