# Result

accepted-080 and accepted-081 remain pending as independent Palomar packages. This diagnostic does not deliver a passing Challenge/Solution pair or a Comparator result. It does establish why a short literal copy of the specification is insufficient and gives a mathematically faithful way to refactor the specification. The full 13 requirements / 103 endpoint scope remains unchanged.

# Measured closure

ClosureProbe.lean starts with the exact TYPES of scheme_discriminant_existence and scheme_discriminant_naturality and recursively traverses project constant types and available definition values. It stops at non-project modules. The successful attempt 04 finds 323 project declarations in 28 modules. There are 168 definitions, 7 inductive declarations, 2 constructors and 146 declarations whose bodies are hidden in the imported module frontend; 125 of the latter are generated `_proof_` auxiliaries. Those frontend placeholders are NOT new mathematical axioms. The separate ProviderAudit prints real theorem axiom closures.

The 28 containing source files total 15,424 physical lines / 760,427 bytes. This is a containing-file size, NOT a minimal required-source lower bound. Unused declarations and unrelated proofs inflate it. Conversely the visible 323 declarations omit hidden proof-body dependencies, so it does not measure the full proof closure. These measurements do not prove that every mathematically equivalent specification exceeds 1,000 lines or 100 KiB. They establish that the present definitions cannot be copied as a short, self-contained block without extracting and redesigning their supporting constructions.

closure-analysis.json contains every declaration and source-file hash. selected-source-inventory.json gives a second human-selected source inventory. ClosureProbe-04.log is the real kernel-environment probe output. MathlibOnlyProbe-02.log confirms the actual missing API names using only Mathlib, while also confirming that Scheme, IsProper, SmoothOfRelativeDimension, GeometricallyConnected and Modules.pullback are present.

# Concrete blockers

1. Family and the ambient geometry are actual objects, not an abstract carrier. LocalWeierstrassDefinitionsR0203 defines SchemeLaw by natural multiplication/inversion on every scheme-valued point, and Family by its actual scheme curve, structural morphism and proper/smooth-relative-dimension-one/geometrically-connected predicates. SchemeHomOver is a project extension, but it can be redefined as the concrete subtype of commuting scheme morphisms. This first layer is small and feasible.

2. The Hodge line is the real identity conormal: Cotangent E = E.zero* (E.zero.ker.module). The ideal's module realization is a local extension (Definitions/Def_AlgebraicGeometry_IdealSheafModule.lean, 48 lines). tensorPower is an actual iterated sheafification of the tensor product of module presheaves; the custom monoidal infrastructure and section maps must be supplied. Scheme kaehler, pullbackLocalSection and projective Weierstrass carrier/origin are also local extensions, absent from Mathlib-only imports. Replacing any of these by an arbitrary Type, module carrier or line with a property field would lose the required source geometry.

3. SchemeDiscriminantDefinitionsR0244.cotangentIso selects an ideal isomorphism from cartesian_identity_ideal, whose conclusion is existence and uniqueness of an isomorphism preserving inclusion into the structure sheaf. Its construction is already a proved geometric result. powerIso additionally uses the constructed tensor pullback isomorphism. A Mathlib-only challenge cannot import those proofs or introduce their existence as a new premise.

4. weierstrassFamily includes real properness, smooth relative dimension and geometric connectedness proofs for the actual projective Weierstrass model. weierstrassHodgeIso uses the proved invertibility of the actual conormal derivative. The source definitions therefore embed substantial proof dependencies even before the target theorem begins. The projective carrier's construction uses the homogeneous quotient grading, Proj, its structure map, and the actual [0:1:0] zero section.

5. The normalization predicate has a particularly important dependency chain:

   Scheme IsD2 -> every affine Weierstrass test -> Arbitrary IsD2 -> every NormalModel -> value -> pull of localD -> Classical.choose(local_discriminant_exists).

   local_discriminant_exists itself first obtains a normalized c=5 Kato function, proves its uniqueness, and constructs its initial Hodge section. It is not a harmless abbreviation for a polynomial in the Weierstrass coefficients. Supplying localD as a parameter, assuming its existence, or replacing it by an unspecified section would weaken the source statement. A direct claim that it equals Delta(W)^2 times a chosen differential power also needs the exact normalization constant and a proved equality; that equality was not established in this diagnostic.

# Faithful redesign

A redesign can avoid embedding chosen proof terms in the Challenge without assuming the desired objects. It must keep actual objects and separately prove an equivalence to the original exact predicates.

A. Define the actual pointed family using Scheme, HomOver as a commuting-morphism subtype, the natural group law, and the three geometric predicates. Define the conormal by the actual identity ideal kernel, and tensor powers by actual sheafification. Define the canonical comparison RELATION by the equation preserving the ideal inclusion into O and the induced tensor maps. Put existence and uniqueness of the comparison isomorphism in the theorem conclusion. Naturality then quantifies over every comparison satisfying this concrete equation; uniqueness proves independence. Do not ask the caller to supply an unexplained iso or add an isomorphism-existence hypothesis.

B. Replace the selected normal-model section localD by a universal characterization: the section is a frame and represents the c=5 normalized Kato initial term in every actual identity-ideal coordinate, using the exact scalar 5, exponent 5^2-1=24, function-field germ equation, unit coefficient evaluated at the zero section, and the genuine relative differential tensor. Define normalized Kato functions from their actual divisor orders and determinant norm identities. Include existence of the normal models and normalized functions among the proved conclusions (or prove them in a separately composed target); otherwise a universal test can become vacuous.

C. State the scheme-global conclusion as existence of a section of the actual 24th conormal tensor power satisfying B on ALL affine tests over ALL coefficient algebras, and naturality for ALL pointed Cartesian comparisons. Retain arbitrary nonflat base changes, nilpotent rings, empty schemes, all universes and no normality/Noetherianity assumption on the target. Build explicit translations between the independent Family/Comparison and the accepted ones, and prove the normalization predicate iff the original IsD2. These are equivalence proofs, not expected rfl bridges.

# Smallest useful package boundaries

1. Genuine scheme module/conormal/tensor infrastructure: actual ideal-kernel module, actual tensor section maps and canonical inclusion-compatible comparison existence/uniqueness. This can be stated for arbitrary morphisms/ideals with the exact necessary geometric hypotheses, and proved from the real implementation. It is reusable infrastructure and must not be labelled accepted-080/081 completion.

2. Normal Weierstrass c=5 initial normalization: explicit projective curve, actual group law, identity/torsion ideals, exact normalized function and initial coefficient equations; prove existence and unique frame and identify it with localD. This is the essential bridge currently hidden behind the choice. It is still a sub-result, not all arbitrary-scheme descent.

3. Arbitrary affine normalization and all-test descent: prove passage through every normal model and arbitrary ring maps, then the global section existence and all-base-change naturality. Only after the precise equivalence to the original predicates is compiled and audited should this package count accepted-080/081 as independently checked.

Each final Challenge must itself obey the official allowed imports and size limits. Merely moving definitions into a sibling non-Mathlib Challenge import is not an established way around those limits. The three boundaries are a proof-development plan; they do not automatically solve the final Challenge budget. Build the independent canonical definitions, measure the actual necessary source, and check the supported Palomar packaging rules before claiming fit. If the fully expanded independent description remains too large, retain the original endpoint as pending and present the compiled sub-results transparently.

# Evidence and limitations

The project and original delivery were read-only throughout. All diagnostic sources, scripts, failed attempts, logs and hashes are under evidence/scheme-discriminant-package-266. Lean probes use the pinned Lean 4.35.0-rc2 / Mathlib manifest, 12 threads and a 300 second per-probe bound. No shared Lake build, GitHub operation, official preflight, formal submission or VPN operation was started here.

A successful original-provider axiom audit is evidence about the original theorem, not an independent specification comparison. The new mathematical redesign above is pending work and has no Challenge, Solution, Comparator success or official report attached.
