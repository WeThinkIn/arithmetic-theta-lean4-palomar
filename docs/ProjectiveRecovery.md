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
| Transfer of projective ratios through a line quotient | [`Palomar_lean/comparator-projective-quotient.json`](../Palomar_lean/comparator-projective-quotient.json) | [Challenge](../challenges/projective-quotient/ArithmeticThetaProjectiveQuotientChallenge.lean) |
| Arithmetic level geometry for projective theta ratios | [`Palomar_lean/comparator-projective-geometry.json`](../Palomar_lean/comparator-projective-geometry.json) | [Challenge](../challenges/projective-geometry/ArithmeticThetaProjectiveGeometryChallenge.lean) |
| Pointed Cartesian group law | [`Palomar_lean/comparator-projective-pointedgroup.json`](../Palomar_lean/comparator-projective-pointedgroup.json) | [Challenge](../challenges/projective-pointedgroup/ArithmeticThetaProjectivePointedgroupChallenge.lean) |
| Primitive theta commutator | [`Palomar_lean/comparator-projective-commutator.json`](../Palomar_lean/comparator-projective-commutator.json) | [Challenge](../challenges/projective-commutator/ArithmeticThetaProjectiveCommutatorChallenge.lean) |
| Invariant theta line | [`Palomar_lean/comparator-projective-invariantline.json`](../Palomar_lean/comparator-projective-invariantline.json) | [Challenge](../challenges/projective-invariantline/ArithmeticThetaProjectiveInvariantlineChallenge.lean) |
| Scheme Schroedinger orbit | [`Palomar_lean/comparator-projective-orbit.json`](../Palomar_lean/comparator-projective-orbit.json) | [Challenge](../challenges/projective-orbit/ArithmeticThetaProjectiveOrbitChallenge.lean) |
| Pushforward intertwining of theta actions | [`Palomar_lean/comparator-projective-intertwining.json`](../Palomar_lean/comparator-projective-intertwining.json) | [Challenge](../challenges/projective-intertwining/ArithmeticThetaProjectiveIntertwiningChallenge.lean) |
| Naturality of invariant components | [`Palomar_lean/comparator-projective-naturality.json`](../Palomar_lean/comparator-projective-naturality.json) | [Challenge](../challenges/projective-naturality/ArithmeticThetaProjectiveNaturalityChallenge.lean) |
| Existence of an arithmetic invariant ratio test | [`Palomar_lean/comparator-projective-testexists.json`](../Palomar_lean/comparator-projective-testexists.json) | [Challenge](../challenges/projective-testexists/ArithmeticThetaProjectiveTestexistsChallenge.lean) |
| Existence of a marked algebraic Tate model | [`Palomar_lean/comparator-projective-model.json`](../Palomar_lean/comparator-projective-model.json) | [Challenge](../challenges/projective-model/ArithmeticThetaProjectiveModelChallenge.lean) |
| Global sign alignment of theta lifts | [`Palomar_lean/comparator-projective-alignment.json`](../Palomar_lean/comparator-projective-alignment.json) | [Challenge](../challenges/projective-alignment/ArithmeticThetaProjectiveAlignmentChallenge.lean) |
| Unique transport of normalized lifts | [`Palomar_lean/comparator-projective-transport.json`](../Palomar_lean/comparator-projective-transport.json) | [Challenge](../challenges/projective-transport/ArithmeticThetaProjectiveTransportChallenge.lean) |
| Scheme theta inversion | [`Palomar_lean/comparator-projective-inversion.json`](../Palomar_lean/comparator-projective-inversion.json) | [Challenge](../challenges/projective-inversion/ArithmeticThetaProjectiveInversionChallenge.lean) |
| Midpoint theta lift | [`Palomar_lean/comparator-projective-midpoint.json`](../Palomar_lean/comparator-projective-midpoint.json) | [Challenge](../challenges/projective-midpoint/ArithmeticThetaProjectiveMidpointChallenge.lean) |
| Faithfulness of model lift comparison | [`Palomar_lean/comparator-projective-faithfulness.json`](../Palomar_lean/comparator-projective-faithfulness.json) | [Challenge](../challenges/projective-faithfulness/ArithmeticThetaProjectiveFaithfulnessChallenge.lean) |
| Square identity from faithful global action | [`Palomar_lean/comparator-projective-square.json`](../Palomar_lean/comparator-projective-square.json) | [Challenge](../challenges/projective-square/ArithmeticThetaProjectiveSquareChallenge.lean) |
| Symmetric change of inversion lift | [`Palomar_lean/comparator-projective-inversionchange.json`](../Palomar_lean/comparator-projective-inversionchange.json) | [Challenge](../challenges/projective-inversionchange/ArithmeticThetaProjectiveInversionchangeChallenge.lean) |
| Generic dual compatibility with global section action | [`Palomar_lean/comparator-projective-genericdual.json`](../Palomar_lean/comparator-projective-genericdual.json) | [Challenge](../challenges/projective-genericdual/ArithmeticThetaProjectiveGenericdualChallenge.lean) |
| Dual compatibility of the induced ideal lift | [`Palomar_lean/comparator-projective-induceddual.json`](../Palomar_lean/comparator-projective-induceddual.json) | [Challenge](../challenges/projective-induceddual/ArithmeticThetaProjectiveInduceddualChallenge.lean) |
| Normalization from a fixed section over a field | [`Palomar_lean/comparator-projective-fieldnormal.json`](../Palomar_lean/comparator-projective-fieldnormal.json) | [Challenge](../challenges/projective-fieldnormal/ArithmeticThetaProjectiveFieldnormalChallenge.lean) |
| Component ratios from a generator over a field spectrum | [`Palomar_lean/comparator-projective-ratiogenerator.json`](../Palomar_lean/comparator-projective-ratiogenerator.json) | [Challenge](../challenges/projective-ratiogenerator/ArithmeticThetaProjectiveRatiogeneratorChallenge.lean) |
