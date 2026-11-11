# Formalization mapping

The original paper, proof sources, exact endpoints and mathematical assumptions are unchanged. New exports are additive, with the original richer construction witnesses retained. The two main review statements are proved projections, not claimed equivalent replacements for all MatrixData fields.

## Main paper correspondence

| Paper location (publication/Paper.tex) | Review entry | Original provider |
| --- | --- | --- |
| Arithmetic finite-coefficient determination, label main; One modular family for all certified conservative prefixes | ArithmeticThetaReview.Geometry.conservative_image_review | ArithmeticThetaFullSourceR0268.conservative_image_consumer |
| A smaller arithmetic finite-coefficient bound, label sharper-bound | Original ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel remains unchanged; public parameter bridges give the same bound | computed_sharp_cutoff and finite_full_level_count |
| Arithmetic modularity and the image basis, label arithmetic-modularity; Scope of the arithmetic modular-form conclusion, label scope | ArithmeticThetaReview.Geometry.cyclotomic_modularity_review | ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity |
| Algebraic sections and every cusp; Arithmetic normalization on torsion-level moduli | Actual compact sections and canonical FrameNormalization | Original MatrixData, CoverFrame, model/classifies/canonical and diskGenericIso |

## Interface boundary

FiniteLevel retains actual all-test finite etale representability, projections, naturality and a rank bound. Original torsor/fiber construction witnesses, conditional surjectivity and the exact rank equation are used to prove it and remain available in the original theorem. Complete theta expansions, structural scalars, canonical square/normalization linkage, the prescribed coefficient field and the order of the family/cutoff quantifiers remain explicit in the new main result. The complete dependency index and internal technical review document this scope; mechanical checks do not constitute independent human semantic acceptance.

## Frozen exported obligations

### arithmetic-norms-agree

`ArithmeticThetaReview.Arithmetic.norms_agree` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

The same finite set of orthogonal norms is used by both original APIs.

### arithmetic-normcount-agree

`ArithmeticThetaReview.Arithmetic.normCount_agree` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

The number of distinct norms agrees in both APIs.

### arithmetic-commonnorm-agree

`ArithmeticThetaReview.Arithmetic.commonNorm_agree` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

The norm-set LCM equals both historical common-modulus definitions.

### arithmetic-level-agree

`ArithmeticThetaReview.Arithmetic.level_agree` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

Both historical levels are exactly 24 times the squared common norm.

### arithmetic-exponent-agree

`ArithmeticThetaReview.Arithmetic.exponent_agree` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

Both conservative construction exponents agree; no identification of conservative and sharp cutoffs is made.

### arithmetic-index-agree

`ArithmeticThetaReview.Arithmetic.index_agree` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

The geometric count formula and executable arithmetic index have the same definition.

### arithmetic-index-eq-card

`ArithmeticThetaReview.Arithmetic.index_eq_card` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

At levels at least three, the index formula is the cardinality of SL2 over Z/LZ.

### arithmetic-sharpcutoff-eq

`ArithmeticThetaReview.Arithmetic.sharpCutoff_eq` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

The review sharp cutoff is exactly the original sharp cutoff, including empty and zero-rank inputs.

### arithmetic-sharpcutoff-computed

`ArithmeticThetaReview.Arithmetic.sharpCutoff_computed` — [Lean/ReviewArithmeticBridges.lean](Lean/ReviewArithmeticBridges.lean)

For valid Gram families, the sharp cutoff agrees with the executable bound and with the exact rational floor in the paper.

### review-relation-equality

`ArithmeticThetaReview.Relations.equality_of_same_relations` — [Lean/ReviewRelationLinear.lean](Lean/ReviewRelationLinear.lean)

Two additive coefficient-combination maps with exactly the same zero relations have exactly the same equalities between combinations. This is a generic algebraic result, independent of any lattice or geometric presentation.

### review-relation-coordinates

`ArithmeticThetaReview.Relations.coordinates_of_same_relations` — [Lean/ReviewRelationLinear.lean](Lean/ReviewRelationLinear.lean)

The same parametrization of coefficient vectors gives injective selected combinations and unique coordinates for one additive combination map if and only if it does for the other, whenever the two maps have the same zero relations.

### review-section-image-transfer

`ArithmeticThetaReview.Relations.section_image_of_series_image` — [Lean/ReviewRelationSections.lean](Lean/ReviewRelationSections.lean)

For any actual scheme over k, sheaf and sections, full-series relation equivalence plus the certified series image transfers all six SectionImage clauses: full relations, finite prefix kernel, pivot independence, unique coordinates, the computed rational coordinates and their uniqueness. Scalars are the actual baseScalar induced by the displayed structure morphism b. No MatrixData, cover or modularity hypothesis is included or silently replaced.

### finite-level-projection

`ArithmeticThetaReview.Geometry.finite_level_of_original` — [Lean/ReviewFiniteLevel.lean](Lean/ReviewFiniteLevel.lean)

Project the existing actual finite metaplectic level to its presentation-independent semantic content on every scheme-valued test. Preserve the existing classifying map, anchored comparison, actual marked elliptic families and square-line maps, both fiber projections and naturality. Deduce finite etale fibers of rank at most twice the original bound from the existing exact-rank formula. This does not replace or weaken the original theorem, which remains available unchanged.

### normalization-source-chart-comparison

`ArithmeticThetaReview.Normalization.source_chart_comparison` — [Lean/ReviewNormalizationBridges.lean](Lean/ReviewNormalizationBridges.lean)

The generic pointed Cartesian Tate comparison is the exact original diskGenericIso, with no scalar replacement.

### normalization-source-normalization-preserves

`ArithmeticThetaReview.Normalization.source_normalization_preserves` — [Lean/ReviewNormalizationBridges.lean](Lean/ReviewNormalizationBridges.lean)

The normalized review family retains the original compact map, compact square, regular Hodge generator, normalized Tate differential, and the full canonical disk comparison.

### same-source-family

`ArithmeticThetaReview.Geometry.matrix_family_review` — [Lean/ReviewMainTheorems.lean](Lean/ReviewMainTheorems.lean)

Project the same original geometry, structure map, half line, disk, frame, sections, compact square and normalized generator; preserve every SectionImage clause at every cutoff and the complete expansion.

### sharp-modularity-review

`ArithmeticThetaReview.Geometry.cyclotomic_modularity_review` — [Lean/ReviewMainTheorems.lean](Lean/ReviewMainTheorems.lean)

Over the prescribed finite cyclotomic field, one normalized actual finite metaplectic family realizes the full theta expansions and their exact section image at every prefix at or above the sharp cutoff.

### conservative-modularity-review

`ArithmeticThetaReview.Geometry.conservative_image_review` — [Lean/ReviewMainTheorems.lean](Lean/ReviewMainTheorems.lean)

Preserve the exact conservative cutoff specification, all prefix kernels and image data, zero-rank formula, and one normalized cyclotomic geometric family valid at every permitted cutoff.

Exact expected types are recorded in [metadata/obligations.json](metadata/obligations.json); the four development contracts and combined contract preserve their reviewed signatures.
