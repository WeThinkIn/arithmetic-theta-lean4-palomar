# Arithmetic theta: interfaces for mathematical review

This additive Lean 4.33.1 library exposes the mathematical conclusions of the
original proof without making the reader first unpack its atlas, quotient and
root-cover construction records. **The original 1,199 modules, all 103 frozen
checks and the entire `Palomar_lean/` edition are unchanged.**

Start with the [mathematical guide](REVIEW_GUIDE.zh-CN.md), then the
[review theorems](Lean/ReviewMainTheorems.lean). The
[definition index](DEFINITION_INDEX.md) gives the complete recursive definition
list and source links. [Reproduction](Reproduce.md) and the
[verification reports](verification/README.md) distinguish the original proof,
the additive library and the limits of mechanical verification.

| Mathematical entry point | Statement |
| --- | --- |
| [`conservative_image_review`](Lean/ReviewMainTheorems.lean) | The original conservative bound, every larger prefix kernel and image, the rank-zero case, and one normalized compact cyclotomic family for all those prefixes |
| [`sharp_matrix_kernel`](../Lean/SharpMatrixKernelR0195.lean) | The original sharp finite-coefficient characterization; retained verbatim |
| [`cyclotomic_modularity_review`](Lean/ReviewMainTheorems.lean) | Over the prescribed cyclotomic field, a normalized actual finite metaplectic level and the section image for every prefix above the sharp bound |

The new main statements are **proved projections of richer original construction
results**. They are not claimed to be type-equivalent replacements for the full
`MatrixData` records. All original construction witnesses, exact fiber ranks,
torsor descriptions and intermediate identities remain in the original results.
The [source-preservation theorem](Lean/ReviewMainTheorems.lean) keeps the actual
curve, structure morphism, half line, disk, frame, sections, compact square and
normalized generator. The [normalization bridges](Lean/ReviewNormalizationBridges.lean)
prove that the canonical comparison maps are definitionally the originals.

## What the public interface retains

- A smooth proper integral curve, its invertible half-weight line and global
  regular sections on that compact curve.
- A dense open and a classifying map to the **actual** stack of marked elliptic
  families with a root of their actual cotangent line. Every scheme-valued
  test has a finite étale representing fiber, with its actual projections,
  naturality and rank bound.
- The canonical cotangent comparison, the compact square and its restriction
  to the same metaplectic object; no freely rescaled comparison is substituted.
- The actual dominant Tate disk, normalized differential and frame; the
  complete expansion is obtained by geometric pullback with `q = t^L`.
- The original coefficient field and the scalar action induced by the actual
  structure morphism. One family is chosen **before** quantifying over cutoffs.

## Measured statement dependencies

The [reproducible measurement](verification/DefinitionDependencyReport.json)
recursively follows elaborated custom definitions and structure-field types,
including aliases and non-proof definition bodies. It excludes theorem proof
terms and records external Lean/Mathlib definitions as a separate boundary.
See the [counting convention](scripts/DEFINITION_METRIC.md).

| Statement | Original | Review statement | Change |
| --- | ---: | ---: | ---: |
| Conservative kernel, image and geometric family | 340 | 224 | 116 fewer, 34.1% |
| Cyclotomic modularity and image | 317 | 188 | 129 fewer, 40.7% |
| Original sharp kernel theorem | 23 | 23 | unchanged |

These numbers measure **definitions needed to interpret the displayed
statements**, not the size of their proof closures or a percentage of human
review completed. The two new main statements share a union of 225 definitions;
there is still substantial algebraic geometry to review. The mathematical
reviewer's earlier informal count of “over one hundred” used a different
counting convention. No claim of independent human semantic acceptance is made.

## Reusable components

| Component | Role |
| --- | --- |
| [Arithmetic parameters](Lean/ReviewArithmeticDefinitions.lean) and [nine equality bridges](Lean/ReviewArithmeticBridges.lean) | One public description of norms, counts, common modulus, level, exponent, index and sharp cutoff; keeps conservative and sharp cutoffs distinct |
| [Generic relation transfer](Lean/ReviewRelationLinear.lean) | Equal kernels of additive coefficient-combination maps give the same equalities and unique coordinates; no custom geometric definitions in these statement types |
| [Actual section-image transfer](Lean/ReviewRelationSections.lean) | Transfers all six original image clauses using the actual structural scalar action and complete theta series |
| [Geometry interface](Lean/ReviewGeometryDefinitions.lean) | Compact curve, actual finite level, normalized framed family and complete expansion |
| [Canonical normalization](Lean/ReviewNormalizationDefinitions.lean) | Actual elliptic families, pointed differential comparison, identity-ideal normalization and the same square maps |
| [Joint root](Lean/ReviewRoot.lean) | Imports the untouched original `GoalRoot` and every additive review module |

There are **13 additive Lean modules and 18 new frozen type/axiom checks**.
The larger source count is intentional: the original proofs remain available,
while the review interface separates conclusions from construction machinery.
