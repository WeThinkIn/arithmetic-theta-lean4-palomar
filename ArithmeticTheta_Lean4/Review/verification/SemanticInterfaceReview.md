# Internal technical review of the semantic interface

**Finding:** no blocking defect was found in the inspected review interfaces with
respect to the retained mathematical conditions listed below. The new main
statements are proved projections of the original richer construction results;
they are not advertised or verified as equivalent replacements for every field
of the original construction records.

This is a source-level technical review by a supporting coding agent that did
not implement the new geometry/normalization interfaces. It is **not human
mathematician acceptance**, a fresh independent proof of the original paper, or
a substitute for the compiler, frozen-type, axiom and source-preservation audits.
The reviewing agent implemented the separate relation-transfer and reproduction
utilities, so this report does not claim independence for those utilities.

## Scope and reference statements

The review compared `ReviewGeometryDefinitions`, `ReviewFiniteLevel`,
`ReviewGeometryBridges`, `ReviewNormalizationDefinitions`,
`ReviewNormalizationSource`, `ReviewNormalizationBridges`, `ReviewFramedFamily`
and `ReviewMainTheorems` with these original endpoints and their relevant input
definitions:

- `ArithmeticThetaFullSourceR0268.conservative_image_consumer`;
- `ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel`;
- `ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity`.

The reference for the reviewer's concerns was
`1109 Theta级数算数刻画审查v1(1).md`. That document reports that the previously
inspected finite-kernel statement semantics revealed no mathematical error. It
explicitly leaves the geometric part unreviewed; this report does not expand the
scope of that human finding.

Nine inspected original endpoint/interface files matched their recorded hashes
at baseline commit `598b5e305fcc4a385ee45a6c2687d90acbb763d8`:
`ConservativeImageConsumerR0268`, `SharpMatrixKernelR0195`,
`CyclotomicMatrixModularityR0239`, `ArithmeticFieldDefinitionsR0231`,
`ActualLevelDefinitionsR0208`, `CompactModularityDefinitionsR0209`,
`BoundaryHodgeDefinitionsR0182`, `SchemeHodgeDefinitionsR0205` and
`SharpKernelDefinitionsR0195`. This spot check is separate from the coordinator's
full preservation audit. No original or review Lean source was edited during
this review.

## Conditions inspected

| Condition | Source-level finding |
| --- | --- |
| Actual modular level | `CompactCurve.object` is the original `Object L`, containing an actual marked elliptic family and a root of its actual identity cotangent. `Coherence` uses the original object groupoids and geometric pullbacks. `AnchoredMap`, `PullbackComparison`, `ForgetData` and the actual stack predicate are retained. |
| Every scheme-valued test | `FiniteLevel` quantifies over every `T : Over (Base k)` and every strong transformation from its representable functor. `FiberPresentation` retains both projections, equivalence of the categorical fibers, and naturality. The resulting projection to the test scheme is genuinely finite and étale. This is not merely a check on field-valued points. |
| Compact regular sections | `CompactCurve` carries an actual integral scheme, a proper smooth relative curve morphism, an invertible line and a dense open immersion. `FramedFamily.sections` are global sections of the nth tensor power of that line on this compact curve. |
| Actual structural scalars | `Realizes` and `SectionImage` use the existing `combination k F.curve.structureMap F.sections`, hence the actual `baseScalar` induced by the displayed morphism. No arbitrary k-module action is substituted. |
| The same square root | `root_eq` identifies the interior root line with the restriction of the compact line. `InteriorLink.square_eq` identifies the full square map after that specified transport, the actual compact square restriction, and the canonical cotangent comparison. A line equality alone is not used to stand in for this square equation. |
| Canonical cotangent comparison | `CanonicalCotangent` retains the actual identity ideal, compatibility with its inclusion, and the conormal comparison equation. `sourceInteriorLink` fills it with the existing model's `M.canonical`. It is not a free scalar-valued comparison. |
| Prescribed Tate normalization | `TateChart` contains the actual `TateCurve k L`, its full marking, a pointed Cartesian test, and the existing normalized differential condition. `TateChart.comparison` composes actual pullbacks and the canonical pointed differential map. `source_chart_comparison` identifies this comparison with the original `diskGenericIso`. |
| The actual frame and its square | `NormalizedFrame.generic_eq` identifies the punctured Hodge generator with the normalized Tate differential; `square_eq` identifies it with the square of the displayed half-weight frame. `source_normalization_preserves` identifies the original compact square, generator, differential and comparison without a scalar change. |
| Complete q-series | `Realizes F A` is an equality of full power series in the actual pulled-back frame, with the literal `PowerSeries.subst (PowerSeries.X ^ L)` substitution. It is not only equality of a finite coefficient prefix. |
| Prescribed coefficient field | Both main geometric conclusions use the unchanged `CoefficientField A = CyclotomicField (level (commonN A)) ℚ` and retain finite dimensionality over ℚ. An arbitrary algebraically closed coefficient field is not substituted. |
| One family for every cutoff | Both main geometric conclusions have `∃ F, Realizes F A ∧ ∀ B, ...`. The existential family is outside the universal cutoff quantifier. The same sections and geometric data serve every admissible cutoff. |
| Positive and zero rank scopes | The sharp modularity statement retains `0 < n` and `0 < h`. The conservative statement retains its rank-zero constant-series formula and places geometry under `0 < n`. It retains the original conservative cutoff, kernel and certified image conclusions. |
| Concrete connection to the old witness | `familyOfData` takes one original `G` and the same universality witness `u` for the interior and square comparison. `matrix_family_review` gives eight explicit equality/heterogeneous-equality witnesses for the compact space, scalar map, half line, disk, frame, sections, compact square and Hodge generator. Its `SectionImage` comparison is definitional equality. |

The proof of each new unconditional main conclusion obtains its original
witness from the corresponding old theorem and applies `matrix_family_review`.
The geometric facts are therefore constructed conclusions, not new assumptions
added to those main theorems. The generic adapters do have the genuine old
geometric data and properties as inputs; their application supplies those inputs
from the old endpoints. No circular conclusion-as-assumption was found.

## Projection boundary that must remain explicit

`FiniteLevel` is **not equivalent to the entire original `FiniteEtaleLevel`
record**. The adapter retains actual categorical-fiber representability,
projection/naturality data, finite étaleness and the bound on the test projection.
It does not expose the original auxiliary geometric fiber construction,
`Represents`, `PairTorsor`, `UsesFiber`, conditional surjectivity, or the exact
rank identity in the review-facing predicate. The degree bound is derived from
that exact identity. Its factor of two is the original square-root-torsor factor;
the original sharp coefficient cutoff is unchanged.

Likewise, the review-facing family does not expose the original algorithmic
indexing, unary sections, coset tensor decomposition, special one-norm cover
property or every divisor-degree construction field. Those stronger construction
results remain in the unchanged original witnesses. The new statements and
module comments correctly call themselves projections. They must not be
presented as a proof of an equivalence between arbitrary `FramedFamily` and
`MatrixData` values, nor as a lossless rewriting of every original record field.

This is compatible with the intended additive approach: the original result and
proof stay available, while a separately proved interface states the required
mathematical conclusion with fewer construction-specific prerequisites.

## Interpretation of complexity measurements

The definition-closure tool follows elaborated custom definition bodies and
structure constructor field types, including aliases, predicates and proof-field
types. It does not obtain a smaller count merely by hiding a definition behind an
abbreviation or a structure. Its explicit boundary excludes proof terms and the
internal bodies of external library definitions.

A reduced count for `cyclotomic_modularity_review` or `conservative_image_review`
is a claim about reading these projected mathematical statements. It is not an
assertion that the entire old proof closure is smaller, that the old and new
construction records are equivalent, or that the missing human semantic review
has been completed. The retained conditions and the original-to-review adapters
must accompany the numerical comparison. This review did not independently
rerun the metric or replace the separate formal validation.

## Reviewed source snapshot

The following hashes identify the new geometry/interface source read in this
review. The final build and delivery audits must bind these same sources, or this
review should be revisited for subsequent semantic changes.

| Source under `Review/Lean/` | SHA-256 |
| --- | --- |
| [ReviewGeometryDefinitions.lean](../Lean/ReviewGeometryDefinitions.lean) | `cc2eda50186d55e25ab3844fc06feb4201cf0fd5097eb7dd8c80eead9ab53b5b` |
| [ReviewFiniteLevel.lean](../Lean/ReviewFiniteLevel.lean) | `496e1adc46d5a7f5131a2a18e15c5a56ab1e547badf6da068b84b95e80403bbb` |
| [ReviewGeometryBridges.lean](../Lean/ReviewGeometryBridges.lean) | `71b5b6d92b263cd3ea9620513a70d3c9c4d5545a9a89b7b072df878c2d1ff788` |
| [ReviewNormalizationDefinitions.lean](../Lean/ReviewNormalizationDefinitions.lean) | `79f12703328301a3ee6b8ef1f21129802fab765745997760b54d7328a43a26ec` |
| [ReviewNormalizationSource.lean](../Lean/ReviewNormalizationSource.lean) | `f8d328767cdb8f7c5bb9bcc9bc4125858e9e04b070b5ddf34d5a78a24d8eb944` |
| [ReviewNormalizationBridges.lean](../Lean/ReviewNormalizationBridges.lean) | `4ebe7d3966c620ac3fdcd7b333eedfbf1979b368cc92cc5deee517063454ea4e` |
| [ReviewFramedFamily.lean](../Lean/ReviewFramedFamily.lean) | `633c7f4cbab6c1befe9cd829b74e32c674512d12ceee377f5274d99dbcc00fc0` |
| [ReviewMainTheorems.lean](../Lean/ReviewMainTheorems.lean) | `003a771654a10d7def2d030855bef1a8355323472e7f1bcbedaf99f7e7fd6a32` |
| [ReviewRoot.lean](../Lean/ReviewRoot.lean) | `e9dfa4e0ba4f91952c32533a3cbcf6d5f64e88c1951d0e8850fbd40016aef1ab` |

Review recorded in UTC: 2026-11-11T09:29:52.584255+00:00
