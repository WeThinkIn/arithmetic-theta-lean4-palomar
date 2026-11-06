# Reading the arithmetic theta formalization

这份导读面向审阅数学证明的读者。建议先阅读总定理及其透明简称，再按需要追踪几何构造和算法。原始 103 项精确类型检查保留完整展开的陈述，可用于逐项核对。

The readability edition keeps the original theorem names, hypotheses and
conclusions. Transparent Lean abbreviations name repeated constructions; they
can be unfolded to recover the original expressions. The 1,199 proof modules,
fixed external libraries and 103 original endpoints remain the verification
scope. Historical verification reports describe their recorded source revisions.

## Where to start

| Mathematical question | Source to read |
| --- | --- |
| Complete conservative kernel, image and reconstruction theorem | [`conservative_image_consumer`](Lean/ConservativeImageConsumerR0268.lean) |
| Meaning of the kernel basis, image basis and reconstruction assertions | [`CertifiedImageData` and its constituent definitions](Lean/EarlyCertificateAssembly.lean) |
| Exact conservative cutoff and its rank-zero case | [`CutoffSpecification` and `conservative_matrix_kernel`](Lean/ConservativeMatrixKernelR0189.lean) |
| Sharper coefficient bound for all complete-series relations | [`sharp_matrix_kernel`](Lean/SharpMatrixKernelR0195.lean) |
| Modular realization over the prescribed cyclotomic field | [`CoefficientField` and `cyclotomic_matrix_modularity`](Lean/CyclotomicMatrixModularityR0239.lean) |
| Extension of scalars with the same computed output and complete expansions | [`cyclotomic_extended_modularity`](Lean/CyclotomicExtendedModularityR0241.lean) |
| Adaptive algorithm, stopping certificate and exact output | [`adaptive_universal_solver`](Lean/AdaptiveUniversalSolverR0230.lean) |
| A concrete binary lattice and its two orthogonal cosets | [`binary_orthogonal_example`](Lean/BinaryOrthogonalExampleR0268.lean) |
| Every original endpoint and its defining file | [Index of all 103 endpoints](THEOREM_INDEX.md) |

`GoalRoot.lean` imports every delivered proof module. It is the joint compilation
entry point; the table above gives a more useful order for mathematical reading.

## Basic notation

The elementary definitions are in [`IntegrationDefinitions.lean`](Lean/IntegrationDefinitions.lean).

| Lean expression | Mathematical meaning |
| --- | --- |
| `n`, `h` | Rank of each lattice and number of lattices in the family |
| `Fin h` | The index set with elements `0, …, h - 1` |
| `Matrices n h` | A family of `h` integral `n × n` Gram matrices |
| `validGram A` | Symmetry, even diagonal entries and positive definiteness of the associated rational quadratic form |
| `theta A` | The complete formal theta series with coefficients in `ℂ` |
| `thetaMap A` | The complex linear map sending coefficients to the sum of the corresponding theta series |
| `coefficientMatrix A B` | The computed rational matrix of coefficients of degrees `0, …, B`, including both endpoints |
| `LinearMap.ker`, `LinearMap.range` | Kernel and image of a linear map |
| `LinearIndependent ℂ v` | Linear independence of the indexed family `v` over `ℂ` |
| `Submodule.span ℂ (Set.range v)` | Complex span of the vectors in `v` |

The nonempty-family hypothesis is `0 < h`. The conservative and sharp kernel
theorems also treat rank zero. Conclusions requiring actual positive-rank
modular geometry explicitly retain `0 < n`.

## The main result, one component at a time

[`conservative_image_consumer`](Lean/ConservativeImageConsumerR0268.lean) produces
a bound `B` and five conclusions:

1. `CutoffSpecification A B` gives the exact conservative bound. At positive rank
   it includes an actual unary indexing, its validity, and its complete formal
   factorization; it also gives the exact rational formula for the bound.
2. For every `B' ≥ B`, `PrefixDeterminesKernel A B'` identifies the full theta
   kernel with the kernel of the finite coefficient matrix over `ℂ`.
3. At rank zero, the theta combination is the constant series whose coefficient
   is the sum of the input scalars.
4. For every `B' ≥ B`, `CertifiedImageData A B'` gives the kernel basis, image basis
   and unique rational reconstruction described below.
5. At positive rank, one family `G` over `CoefficientField A` has an actual finite
   metaplectic level and the required `SectionImage` properties at every larger
   prefix. The structural scalar map and the same geometric sections remain
   explicit in the statement.

The abbreviations in [`EarlyCertificateAssembly.lean`](Lean/EarlyCertificateAssembly.lean)
expose the repeated elimination data:

| Abbreviation | Definition and role |
| --- | --- |
| `relationCount A B` | Number of free columns in rational elimination |
| `relationBasis A B` | The computed rational nullspace vectors, embedded in `ℂ` |
| `imageDimension A B` | Number of pivot columns in that same elimination |
| `imageBasis A B` | The original complete theta series selected by those pivots |
| `reconstructionCoordinates A B j` | Computed rational coordinates of input column `j` |
| `imageCombination A B c` | The full-series linear combination with rational coefficients `c` |
| `RelationBasisCorrect A B` | Independence and spanning of the full relation kernel |
| `ImageBasisCorrect A B` | Independence and spanning of the full theta image |
| `ReconstructionCorrect A B` | The computed full-series identities and uniqueness over `ℚ` |
| `CertifiedImageData A B` | The conjunction of the three preceding correctness assertions |

These are `abbrev` declarations, not additional hypotheses or axioms. For
example, `ReconstructionCorrect A B` unfolds to

```lean
∀ j : Fin h,
  theta (A j) = imageCombination A B (reconstructionCoordinates A B j) ∧
    ∀ c : Fin (imageDimension A B) → ℚ,
      theta (A j) = imageCombination A B c → c = reconstructionCoordinates A B j
```

The field abbreviation is equally concrete:

```lean
abbrev coefficientLevel {n h : ℕ} (A : Matrices n h) : ℕ :=
  level (commonN A)

abbrev CoefficientField {n h : ℕ} (A : Matrices n h) :=
  CyclotomicField (coefficientLevel A) ℚ
```

Here `commonN A` comes from the unary lattice data. The coefficient field retains
this dependence on `A`; it is not an arbitrary field substituted for the
prescribed cyclotomic field.

## Following the proof

The body of `conservative_image_consumer` follows the same components as its
statement. It obtains the bound and kernel equality from
`conservative_matrix_kernel`, applies `certified_theta_image_data` to obtain
the basis and reconstruction conclusions, and obtains the geometric family from
`cyclotomic_matrix_modularity`. The private lemma `section_image_of_certificate`
transfers the finite coefficient certificate to those actual sections through
the complete-expansion relation equivalence.

Names ending in `R0189`, `R0239`, and similar suffixes are historical module and
namespace identifiers. They are retained so existing imports, references and
verification probes continue to identify the same declarations.

## Checking preservation and reproducing the result

Follow [`REPRODUCE.md`](REPRODUCE.md) for the portable Lean 4.33.1 build. The
original contract and all 103 probes are unchanged, so the readable types are
checked against the original expanded statements, including their quantifiers,
universe parameters and hypotheses. The endpoint checks also inspect transitive
axiom dependencies.

[`scripts/check_declarations.lean`](scripts/check_declarations.lean) provides a
broader comparison against a separately compiled original revision. It loads
both complete Lean environments with the same pinned external dependencies;
the candidate environment cannot fall back to baseline proof objects. It checks
all original non-internal named declarations for unchanged kinds, universe
parameters and definitionally equal types, and also compares definition bodies.
Proof terms may have different presentations; theorem conclusions must remain
definitionally equal. The script compares Lean expressions directly, avoiding
printed, potentially shortened types and large intermediate text snapshots.
See the preservation report for the exact tested revision and counts.
