# Arithmetic determination of relations among lattice theta series

*Exact Tate normalization and common finite covers*

Human author and responsible maintainer: **Jue Ding**.

This repository presents the research manuscript, the complete Lean 4 formalization, and a reproducible verification environment for the arithmetic determination of relations among lattice theta series. **Jue Ding first publicly released both the accompanying paper and the original Lean 4 code as part of this project.** The manuscript records the full author and contributor list; third-party mathematical libraries retain their own authorship and attribution.

**The complete formalization has passed local Lean verification for all 13 source requirements, represented by 103 exact theorem endpoints.** The original delivery was verified with Lean **4.33.1**. The Palomar-compatible edition published here has also passed the complete `GoalRoot` build and all 103 original endpoint type and axiom checks with Lean **4.35.0-rc2**. The [main-result Palomar official mechanical preflight](docs/audit/official-main-complete-1477/Review.md) and the [ordinary submission’s official mechanical verification](docs/audit/official-ordinary-main-complete-1509/Review.md) have passed for the same 40 original endpoints, with stock Lean, NanoDa, and Conron acceptance. Whole-paper Palomar semantic acceptance and registration have not yet been established.

[Paper (PDF)](paper/Arithmetic%20determination%20of%20relations%20among%20lattice%20theta%20series%20-%20Exact%20Tate%20normalization%20and%20common%20finite%20covers.pdf) · [Original mathematical specification](paper/OriginalTask.tex) · [Formal theorem specification](docs/SourceObligations.json)

## Main mathematical result

Let $A_1,\ldots,A_h$ be a nonempty finite family of positive-definite, even integral Gram matrices of a common rank $n$. Write

$$
\theta_{A_i}(q)=\sum_{x\in\mathbb Z^n}q^{\frac12 x^{\mathsf T}A_i x},
\qquad
\Theta_A(c)=\sum_{i=1}^{h}c_i\theta_{A_i}.
$$

Here the theta series are interpreted as complete formal power series. The formalization constructs an explicit finite coefficient bound $B$ such that, for every $B'\geq B$,

$$
\ker(\Theta_A)=\ker\bigl(M_{B'}(A)\otimes_{\mathbb Q}\mathbb C\bigr),
$$

where $M_{B'}(A)$ is the exact matrix of theta coefficients through the specified cutoff. This determines **all complex linear relations among the complete theta series** from finitely many rational coefficients.

The development also constructs and verifies:

- a rational basis whose complex span is the full relation kernel;
- an independent selection of the original theta series spanning the image, with unique rational reconstruction coordinates for every input series;
- conservative and sharper arithmetic bounds, together with the geometric sections and complete expansions that justify them;
- exact coefficient enumeration, rational elimination, and an adaptive algorithm with proved stopping certificates;
- the rank-zero case, dependent families, an explicit binary factorization, the determinant-80 example, and the rank-16 equal-theta example.

The proof proceeds through integral orthogonal sublattices and actual rational preimage cosets, formal unary theta products, algebraic Tate geometry and normalized Kato units, compact Hodge sections, and finite covers. Divisor degrees and finite jets yield the coefficient bounds; exact linear algebra then recovers the full kernel and image. The arithmetic construction includes actual global sections and their complete formal expansions.

### Principal formal theorems

The following declarations provide entry points to the principal results. Each linked module contains the complete quantified statement and its Lean proof.

| Result | Lean declaration and source |
| --- | --- |
| Conservative bound, complete kernel and image, unique reconstruction coordinates, and compact cyclotomic modular family | [`ArithmeticThetaFullSourceR0268.conservative_image_consumer`](Proof/ConservativeImageConsumerR0268.lean) |
| Sharp coefficient bound determining the full complex relation kernel, including rank zero | [`ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel`](Proof/SharpMatrixKernelR0195.lean) |
| Actual finite metaplectic level and section image over the prescribed cyclotomic field | [`ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity`](Proof/CyclotomicMatrixModularityR0239.lean) |
| Modularity, solver output, and complete expansions under coefficient-field extension | [`ArithmeticThetaExtendedMetaplecticR0241.cyclotomic_extended_modularity`](Proof/CyclotomicExtendedModularityR0241.lean) |
| Adaptive solver correctness, termination, and first-certified stopping on its schedule | [`ArithmeticThetaAdaptiveSolverR0230.adaptive_universal_solver`](Proof/AdaptiveUniversalSolverR0230.lean) |

The joint proof entry point is [`Proof/GoalRoot.lean`](Proof/GoalRoot.lean), with final integration in [`Proof/FullSourceIntegrationR0268.lean`](Proof/FullSourceIntegrationR0268.lean). The [formal specification](docs/SourceObligations.json) records the exact statements, hypotheses, and source correspondence of all **103 endpoints**, and the [requirement map](docs/RequirementCoverage.json) relates them to the **13 original requirements**.

## Local formal verification

**Local verification is complete for the specified formal development.** The verified results are:

| Verification result | Outcome |
| --- | --- |
| Original formal delivery under Lean 4.33.1 | **PASS** — delivery audit and exact theorem checks |
| Complete Palomar-compatible proof under Lean 4.35.0-rc2 | **PASS** — `lake build +GoalRoot` |
| Preservation of all 103 original endpoint types | **PASS** — checked together against the frozen specification |
| Transitive axiom dependencies of all 103 endpoints | **PASS** — only standard Lean logical axioms |

The permitted logical dependencies are:

```text
propext
Classical.choice
Quot.sound
```

The audited theorem proofs have no `sorryAx` dependency and introduce no additional mathematical axioms. The exact-type audit checks the original quantified statements; the axiom audit checks their transitive proof dependencies. Evidence is provided by the [complete root-build receipt](docs/audit/full-root-build-342/receipt.json), the [103-endpoint audit result](docs/audit/partial-endpoint-audit-431-result.json), and the [optimized full-project build and preservation audit](docs/audit/direct-hodge-integration-856/Review.md). The latter also checks 54,522 original non-internal named declarations and 13,670 definition bodies across all 3,915 project modules. The [resource-limited build and independent-kernel record](docs/audit/direct-hodge-integration-1092/Review.md) documents the completed staged build and the verified CommonUnary and CompleteMain scopes.

### Verified toolchains and dependencies

| Component | Original verified delivery | Palomar-compatible edition |
| --- | --- | --- |
| Lean | **4.33.1** | **4.35.0-rc2** |
| Lean compiler commit | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | `11acb17ec6b07a8f9e9173e6845197929540936b` |
| Lake | `5.0.0-src+819816b` | `5.0.0-src+11acb17` |
| Mathlib commit | `0df444a360eaa60ab8c11dca51a86af692955474` | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Compiler platform | `x86_64-unknown-linux-gnu` | `x86_64-unknown-linux-gnu` |

The repository selects its compiler through [`lean-toolchain`](lean-toolchain), pins Mathlib in [`lakefile.toml`](lakefile.toml), and locks the dependency graph in [`lake-manifest.json`](lake-manifest.json). The version table distinguishes the original verified artifact from the edition reproduced by this checkout.

## Adaptation for Palomar

The Palomar edition ports the locally verified development from **Lean 4.33.1 to Lean 4.35.0-rc2**, together with the corresponding pinned Mathlib revision. It preserves the original **13 requirements and 103 theorem endpoints**, including their hypotheses, universe parameters, quantified conclusions, and complete-series interpretation.

The resulting edition incorporates the following compatibility and engineering work:

| Area | Adaptation in the published edition | Verification basis |
| --- | --- | --- |
| Compiler and Mathlib compatibility | Updated module headers, declaration exposure, private-declaration visibility, library interfaces, and explicit parameters where elaboration changed | Complete `GoalRoot` build and exact checks of all 103 original endpoint types and their axiom dependencies |
| Dependency packaging | Required local library sources included under `Proof/Definitions`, `Proof/Theorems`, and `Proof/P2M`, with a locked dependency graph | Recorded [source provenance, licenses, and attribution](docs/ThirdParty/README.md) |
| Independent verification interfaces | Scoped Challenge/Solution pairs and explicit comparator configurations specifying mathematical targets and permitted axioms | Package-specific checks of statement types, universes, proof dependencies, original-endpoint recovery, and exported interfaces |
| Compilation and kernel efficiency | Replaced broad Mathlib imports with required dependencies; preserved the original elaboration instances; simplified descent, congruence, and Hodge transport proofs to reduce compilation and kernel work | [Complete build and original-declaration preservation audit](docs/audit/direct-hodge-integration-856/Review.md), covering all 3,915 modules and 103 original endpoints; separate independent-kernel receipts record their verified scopes |
| Build scheduling | Added prerequisites between high-memory modules without adding Lean imports or changing mathematical source | [Completed FieldUnary cold build and preservation checks](docs/audit/field-unary-scheduling-2163/Review.md): 3,153 modules built; all 67,489 constants matched the preceding cold build; the complete export and target-closure checks passed |

These engineering changes retain the original mathematical specification. In the independent verification interfaces, Challenge proof holes identify the propositions to be checked; the corresponding Solution supplies the proofs subject to the configured axiom checks. The complete local development and its verification evidence remain available alongside these interfaces.

## Independent Palomar verification

**The main-result official mechanical preflight and ordinary submission verification have passed.** Their 43 selected targets cover the same 40 original endpoints at commit `57c6842d63e4860c7978dbc32307380415bcce1c`; stock Lean, NanoDa, and Conron accepted the solution, and the Challenge received high-trust provenance. The [ordinary submission report](docs/audit/official-ordinary-main-complete-1509/Review.md) records the official service result. The recorded official mechanical results now cover **99 of the 103 original endpoints** at their respective exact revisions. The [complete arithmetic common cover](docs/audit/official-ordinary-common-2326/Review.md) adds original endpoint 071 through ordinary official verification: all 39 configured obligations passed, with stock Lean, NanoDa and Conron acceptance and high-trust provenance. The [complete arbitrary-field unary realization](docs/audit/official-field-unary-2238/Review.md) adds original endpoint 069, with all 32 obligations and stock Lean, NanoDa and Conron acceptance. The previously passed [conservative matrix geometry scope](docs/audit/official-conservative-matrix-2158/Review.md) adds original endpoints 035 and 036, covering geometric realization for arbitrary finite valid Gram families and the conservative coefficient cutoff. The union also includes the [prescribed roots](docs/audit/official-roots-2132/Review.md), [algebraic Tate coordinates](docs/audit/official-coordinates-repaired-2189/Review.md), and [sharp-bound, adaptive-solver and image](docs/audit/official-sharp-adaptive-image-2079/Review.md) scopes. The sharp-bound, adaptive-solver and image scope has also passed [ordinary submission mechanical verification](docs/audit/official-ordinary-sharp-adaptive-2168/Review.md), with stock Lean, NanoDa and Conron acceptance; that submission has entered the semantic-review queue. Shared endpoints are counted once. It combines independently verified scopes and does not represent a single whole-paper run. The [official report and precise scope](docs/audit/official-main-complete-1477/Review.md) provide the verification evidence.

**Whole-paper Palomar verification remains incomplete; registration has not been completed.** Palomar adds official mechanical preflight, independent kernel replay, semantic review of the correspondence with the manuscript, and registry acceptance to the completed local Lean verification.

The repository provides [scoped verification packages](challenges/), named `comparator-*.json` configurations, and an [official preflight workflow](.github/workflows/palomar-preflight.yml). Each official result applies to its selected mathematical scope and immutable source revision. The [coverage map](docs/Coverage.md), [verification records](docs/PalomarPreflight.md), and [official workflow runs](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/workflows/palomar-preflight.yml) document those scopes and their results.

### Complete interfaces above the current size cap

The complete local formalization retains all **13 source requirements and 103 original endpoints**. Independent interfaces satisfying the current Challenge size limits have been prepared for **99 of the 103 endpoints**; this preparation count is distinct from official verification coverage. The four remaining complete interfaces are published with their Lean sources, comparator configurations, and local validation records in [`interfaces/size-limited`](interfaces/size-limited/README.md).

| Complete interface | Challenge size | Lines | Current constraint |
| --- | ---: | ---: | --- |
| [Cyclotomic matrix modularity (`accepted-075`)](interfaces/size-limited/accepted-075/README.md) | 144,147 bytes | 577 | Byte cap |
| [Extended cyclotomic modularity (`accepted-076`)](interfaces/size-limited/accepted-076/README.md) | 160,220 bytes | 600 | Byte cap |
| [Global arithmetic projective ratios (`accepted-087`)](interfaces/size-limited/accepted-087/README.md) | 320,833 bytes | 1,311 | Byte and line caps |
| [Conservative image consumer](interfaces/size-limited/conservative-image-consumer/README.md) | 147,894 bytes | 581 | Byte cap |

Palomar currently limits each Challenge to **100 KiB (102,400 bytes) and 1,000 lines** and restricts its transitive imports to approved canonical dependencies. These limits concern the independent statement interface, rather than the size of the full proof development. All four published snapshots passed local compilation, declaration and original-endpoint checks, obligation accounting, and full serialized target-closure comparison; their individual records specify the additional export, rendering, and kernel checks completed. The complete `accepted-087` Solution export has also passed local stock Lean, Conron, and NanoDa typechecking; its [binding record](interfaces/size-limited/accepted-087/audit/kernel-binding.json) identifies the exact checked scope and records a separate NanoDa axiom-printing error. They have not passed official Palomar verification as complete interfaces.

The validated interfaces remain above the cap after dependency pruning and engineering optimization. Further aggressive compression is deferred to preserve the complete mathematical statements and a maintainable presentation. The corresponding Lean code is available for inspection and local reproduction; no exception to the current official limits is assumed, and no expansion request is being pursued at this stage. The complete proof and the eligible independent interfaces remain available alongside these source snapshots.

For a future policy discussion, [`docs/PalomarSizeExpansionMaterial.md`](docs/PalomarSizeExpansionMaterial.md) records the exact sizes, retained dependencies, completed local checks, and the additional review resources that would be needed for an explicitly supported larger-Challenge path. It is informational only; no oversized submission or implied exemption is made.

## Reproduce the formal proof

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar.git
cd arithmetic-theta-lean4-palomar
lake exe cache get
lake build +GoalRoot
```

Elan selects the pinned compiler automatically. Use the committed dependency manifest to reproduce the verified environment. The full proof includes a substantial algebraic geometry dependency closure; allow sufficient memory and time for a clean build.

To inspect the active tool versions and repeat the published exact-type and axiom probe after building:

```sh
lean --version
lake --version
lake env lean docs/audit/PartialEndpointAudit431.lean
```

The probe must complete successfully, and its reported axiom dependencies must be contained in the three standard axioms listed above. Its frozen [selection](docs/audit/partial-endpoint-audit-selection-431.json) and [reference output](docs/audit/partial-endpoint-audit-431.log) document the audited endpoints.

To run the independent main-and-components comparison, use its explicit configuration:

```sh
lake build CompleteMainAndComponentsChallenge CompleteMainAndComponentsSolution
lake comparator --config comparator-main-complete.json
```

The selected statements and scope are documented in [`challenges/main-and-components-complete`](challenges/main-and-components-complete/README.md). The legacy default `comparator.json` selects an earlier, narrower specification; use a named configuration for the intended scope.

## Repository guide

| Path | Contents |
| --- | --- |
| [Research manuscript (PDF)](paper/Arithmetic%20determination%20of%20relations%20among%20lattice%20theta%20series%20-%20Exact%20Tate%20normalization%20and%20common%20finite%20covers.pdf) | Accompanying research manuscript |
| [`paper/OriginalTask.tex`](paper/OriginalTask.tex) | Original mathematical specification |
| [`Proof/`](Proof/) | Formal proof modules and required local library sources |
| [`Proof/GoalRoot.lean`](Proof/GoalRoot.lean) | Joint import of the complete delivered proof closure |
| [`docs/SourceObligations.json`](docs/SourceObligations.json) | Exact statements and source correspondence of all 103 endpoints |
| [`docs/RequirementCoverage.json`](docs/RequirementCoverage.json) | Mapping of the original source requirements |
| [`challenges/`](challenges/) | Scoped independent verification interfaces and metadata |
| [`docs/audit/`](docs/audit/) | Build receipts, statement-preservation checks, and proof audits |
| [`docs/ThirdParty/`](docs/ThirdParty/README.md) | Library provenance, licenses, and attribution |

## Mathematical scope

The formalized result concerns arithmetic determination of relations among complete lattice theta series for arbitrary nonempty finite valid Gram families. It includes the actual geometric constructions, exact coefficient bounds, and certified algorithms needed for that result, with rank zero and deficient rank handled explicitly.

The modularity statements use the arithmetic geometric formulation specified in the manuscript. Analytic comparison theorems, principal-congruence domination, a prescribed Shimura multiplier, and classification of an unsupplied order are outside this specification. Algorithmic termination is proved; practical complexity depends on the input family.

## Attribution and citation

For the mathematical result, cite the accompanying manuscript using its recorded author list and title:

> *Arithmetic determination of relations among lattice theta series: Exact Tate normalization and common finite covers.* See [the manuscript](paper/Arithmetic%20determination%20of%20relations%20among%20lattice%20theta%20series%20-%20Exact%20Tate%20normalization%20and%20common%20finite%20covers.pdf) for authorship and version information.

For the Lean formalization, cite this repository together with the exact Git commit used for verification:

> Jue Ding, maintainer. *Arithmetic theta formalization in Lean 4 — Palomar-compatible edition.* https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar.

AI contributions to mathematical construction, Lean proof development, and Palomar adaptation are disclosed in the [contribution account](docs/AIContributions.md) and the scope-specific formalization metadata. Third-party source attribution is preserved separately from the authorship of this project.

## License

The original Lean code is licensed under the [Apache License 2.0](LICENSE). Mathlib and the included local library sources retain their respective licenses, copyright notices, and attribution; see [`docs/ThirdParty`](docs/ThirdParty/README.md).
