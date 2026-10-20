# Complete-scope verification plan

The goal is to verify the paper's actual mathematics, not only that some Lean
files compile. The original requirement set has thirteen entries and 103 frozen
endpoints. `RequirementCoverage.json` and `SourceObligations.json` retain this scope.

## Required evidence layers

1. **Source identity.** Identify the paper, original task, original Lean delivery,
   copied local dependency sources, compiler and Mathlib revisions by content
   hashes. Preserve the original delivery separately from this port.
2. **Complete migrated build.** Build `GoalRoot` with the supported toolchain and
   include all required source dependencies. Diagnose failed dependencies before
   interpreting downstream failures. No `sorry`, custom axiom, evaluation axiom,
   weakened hypothesis or empty substitute is a porting fix.
3. **Endpoint preservation.** Elaborate each frozen proposition and use the
   migrated original declaration to prove it; inspect the transitive axiom
   closure. Confirm the jointly imported environment, not only isolated leaves.
4. **Independent mathematical statements.** Write small Challenge files using
   canonical library concepts and explicit local mathematical definitions. The
   Challenge must not import this proof library. Match the paper's quantifiers,
   hypotheses, normalizations, effective bounds and actual objects.
5. **Mechanical comparison.** Prove the corresponding statements in Solutions
   using the migrated implementation. Run Comparator and the official full
   mechanical preflight at a pinned public Git commit for each configuration.
6. **Semantic and proof-account review.** Supply the paper and an explicit proof
   account, ask Palomar to assess both statement fidelity and the actual proof
   route, and reconcile each finding with the exact requirement it concerns.
   A clean partial record does not discharge other configurations. Permanent
   registration is a later, separately consented publication step.

## Independent statement packages

The final packaging may use multiple Comparator configurations to keep each
Challenge within Palomar's limits. Each configuration is a separate submission;
their union must cover all required mathematical claims.

| Package | Mathematical statement that must remain visible |
|---|---|
| Main finite determination | Actual integer-shell theta series; arbitrary valid finite Gram families; the explicit conservative cutoff; all larger cutoffs; rank-zero branch; complex relation kernel |
| Orthogonal factorization | Actual rational preimage quotient and determinant index; complete unary product identities; the specified binary example |
| Formal comparison and norm | Actual proper formal model, all no-pole hypotheses, Kato divisors and every required norm identity, intrinsic normalization |
| Discriminant and roots | Actual conormal tensor, prescribed complete expansion, simultaneous roots in one specified ambient field, degree and regularity |
| Four-torsion and character | Actual torsion sections, nonzero denominators, signed frames, all-cusp orders, inverse-character descent and naturality |
| Projective ratios and sharper bound | Same global family and canonical disk, exact projective unary ratios, distinct norm count, common line and exact sharper coefficient bound |
| Arithmetic modularity and image | Actual arithmetic/cyclotomic family, structure maps and sections, complete expansions, nullspace, pivot basis and unique coordinates |
| Algorithms and examples | Exact shell enumeration and LDL, stopping-certificate hypotheses and correctness, full relation certificates, universal termination and the original determinant-80 and rank-16 claims |

These are packaging groups, not replacements for the thirteen source requirements.
The final mapping must identify a compared declaration, definitions and a proof
bridge for every required claim. A theorem of the form “if all desired geometric
objects exist, then the bound holds” does not discharge their construction.
An existential finite bound alone does not discharge the explicit-bound or
algorithm requirements.

## Statements requiring special care

- `Nat.card` is zero for an infinite type. Cardinality-based theta definitions
  therefore require the finite-shell theorems for positive-definite input.
- Equality of finite prefixes does not by itself give equality of full series.
- The geometric sections must live in the actual line bundles on the specified
  schemes. A named arbitrary proposition is not a replacement.
- The expansion `F̂ = U^K` must use the prescribed completion map and frame,
  with the original normalization, rather than an unconstrained scalar factor.
- Rational elimination and complex relations require explicit scalar-extension
  bridges; the modular-section statement must retain its actual structure map.
- Early stopping requires a proved certificate. Numerical stability or a failed
  rank test is not independently sufficient.
- Compilation, Comparator, automated semantic review and human mathematical
  review provide different evidence; none should be reported as another.

## Current status

Complete GoalRoot migration build342 and joint audit343 passed all103 exact original endpoint types with standard axiom closures. No original delivery file was changed (baseline344,1207 files). The full source build is no longer pending.

The stronger complete-main configuration specifies40 complete original endpoints with43 targets and is undergoing official full preflight39469688913 at35c8d4a. Its main theorem preserves FormalIdentity for the same U and bound B. The older39-endpoint run39461299032 ended with infrastructure/resource-exhausted in Solution build; no mathematical rejection was reported. accepted-017 and the separate accepted-050 formal-cover scope have passed their respective official mechanical checks; the formal-cover submission has a private review available, without registration.

The sharp/adaptive/image configuration `comparator-sharp-adaptive-image.json` adds seven disjoint endpoints: accepted-046/049/064/065/066/067/088. Its Mathlib-only Challenge has485 lines/31089bytes. Local standalone checks and the actual named root-pair build passed; all225 non-internal Solution declarations have standard axiom closures. It preserves the exact distinct-norm cutoff, full kernels for larger prefixes, actual first-stop algorithm, checked integral changes, full null/image/unique-coordinate results and singleton-zero behavior. Scope and evidence are under `challenges/sharp-adaptive-image/` and `docs/audit/sharp-adaptive-image-351/`. This new configuration still requires its own official full preflight before ordinary intake.

Together, complete-main and sharp/adaptive/image specify47 distinct original endpoints; the separate formal-cover package adds accepted-050 for48. These are independent interface coverage counts, not48 official semantic approvals. The roots package described below adds two further endpoints. Original scope remains13 requirements/103 endpoints.

No full-paper Palomar result is available. The legacy default comparator.json is an earlier pilot and should not be confused with these explicit configurations. Independent geometric specifications, including the full sharp geometric family, remain open; the complete scheme-discriminant interface is now available separately, despite their migrated original-type proofs passing.

The additional `comparator-sharp-and-roots.json` pairs the full accepted-049 principal sharp theta conclusion with complete accepted-056/057 actual ambient/smooth-point root constructions. Its990-line/66941-byte Mathlib-only Challenge retains all original fields and the actual canonical tensor comparison; all local checks and the actual named root build361 passed. It adds two distinct endpoint IDs, bringing prepared independent interface coverage to50/103 (the remaining53 still need interfaces). This is not50 official passes. Official preflight39482676946 for this package is running as a controlled resource experiment; it has not been ordinary-submitted or registered.

Official resource report362: older run39461299032 failed during `solution-build`, with15824445440bytes (~14.74GiB) recorded peak memory, `oom_kill:9` and `deadline_fired:false`. Challenge provenance was high/Mathlib-only. This is a failed mechanical attempt due to infrastructure resources, not a proof rejection. Preserve ongoing complete-main39469688913 and sharp/adaptive/image39479248485; do not retry unchanged resource conditions. See `audit/official-older-main-362/`.


Resource experiment364 sets package-level `weakLeanArgs = ["-j1"]`, confirmed in actual compiler arguments by isolated Lake probe363. This limits internal Lean threads per compiler, not simultaneous Lake compiler processes; unchanged theorem types, proof bodies, Comparator and kernel checks are retained. The official cold-build memory effect remains unverified. Larger Namespace runner availability was not established. See `audit/resource-diagnosis-363/Analysis.md`.

The additional `comparator-sharp-and-coordinates.json` specifies complete accepted019/020/021/022 coordinates, poles, cubic and global normalized differential together with the accepted049 principal sharp theta conclusion. Its670-line/40226-byte Mathlib-only Challenge, Solution,38-declaration standard-axiom audit and actual named root build384 passed. It adds four distinct endpoint IDs, bringing prepared independent interface coverage to54/103, with49 remaining. This is not54 official passes. Official dispatch is deferred pending the existing resource experiment39482676946. See challenges/sharp-and-coordinates/ and docs/audit/sharp-and-coordinates-384/coverage.json.

The complete scheme-discriminant configuration `comparator-full-scheme-discriminant.json` adds original accepted080/081 existence and arbitrary-base-change naturality, with eight explicit canonical-construction support targets. Its976-line/54781-byte Mathlib-only Challenge and883-line/50878-byte Solution passed local compilation;115 Solution declarations have only standard axioms,23 independent definitions/imports were audited, and both original full endpoint types were recovered exactly. Actual named root build392 passed. SchemeSpecification retains all affine tests and arbitrary nonreduced rings/nonflat maps, with exact factor5/exponent24 normalization and actual conormal tensor comparisons. Prepared interface coverage is now56/103 (47 remaining), not56 official passes. Official preflight for this configuration is pending. See challenges/full-scheme-discriminant/ and docs/audit/full-scheme-integration-392/.

The `comparator-scheme-kato.json` configuration adds complete original accepted083/086, scheme Kato unit naturality and intrinsic Cartier-divisor/norm characterization. Its827-line/43286-byte independent Challenge and280-line/16121-byte Solution passed local checks;37 Solution declarations have standard axioms,17 independent definitions/imports were audited and both original types recovered. Five targets include three actual existence supports. Norm families are existentially constructed on all opens with exact determinant normalization and restriction compatibility. Actual root build400 passed. Prepared independent interface coverage is58/103, with45 remaining; official full preflight for this package is pending. See challenges/scheme-kato/ and docs/audit/scheme-kato-integration-400/coverage.json.

The period-one and scheme-initial packages add complete original accepted-082 and accepted-085. Both independent specifications retain all original quantified objects and conclusions, have exact original-type recovery and standard-axiom Solution audits, and passed their actual repository root builds (audit412). Their 14 targets each include 13 explicit support obligations. Prepared independent interface coverage is now 60/103, with 43 remaining; this counts locally checked interfaces, not official passes. Official preflight and semantic review for these new configurations remain pending. See docs/audit/new-geometric-interfaces-412/coverage.json.

Two Weierstrass polynomial proofs now use smaller kernel proof terms, with unchanged theorem type ASTs and universes. Actual GoalRoot and all 12 Comparator Solution roots passed Lake validation, all 103 original endpoint type/axiom checks passed audit415, and all declarations of each Solution root have only standard axioms. Ordinary downstream caches remained valid because public module artifacts were byte-identical; 12857 build jobs does not mean 12857 recompilations. A fresh export of the same main target was about 3.28% smaller (2,650,647,630 bytes). This is not a three-kernel or official Palomar pass, nor proof that official resource limits are now sufficient. Detailed measurements and cache behavior are in docs/audit/proof-optimization-407/Review.md.

The complete scheme Kato–Tate unit interface adds original accepted-084: one unique actual unit with full normalization, Cartier divisor, every positive coprime norm and full period-one Tate expansion through the same actual pullback. Its863-line independent Challenge and227-line Solution passed local compilation, all-declaration axiom/import audits and exact original-type recovery; the actual repository root build424 passed. The7 targets include the inherited394 obligations and explicit gamma-limit existence. Prepared independent coverage is61/103,42remaining; this is local interface coverage, not official passes. See docs/audit/scheme-tate-unit-integration-424/coverage.json. Official preflight and semantic review remain pending.

The complete scheme Miller-phase interface adds original accepted-051 at arbitrary universe u: a unique global phase with its unit and square identities, primitive order4 conditional on nontrivial global sections, and actual moved-divisor pairing on every affine test and characteristic-zero field fiber. Its660-line independent Challenge and23-line Solution passed compilation; all341 Challenge and4 Solution declarations were axiom-audited,208 non-proof declarations have original definitionally equal types and available bodies, and the complete original051 type is recovered. The three targets include explicit local-data and arbitrary-ring fiber-basis existence. Actual root build435 passed. Prepared independent coverage is62/103,41remaining; these are local interfaces, not official passes. Original052 remains pending. See docs/audit/scheme-miller-phase-integration-435/coverage.json.

The complete scheme alpha-character interface adds original accepted-052 at arbitrary universe u, retaining the same global phase, actual cotangent and all even-stabilizer matrices. The canonical differential and conormal maps are specified by unique local derivative formulas and proved equal to the originals. Full affine/global RealizesAlpha equivalences and the exact original052 reverse bridge compile. Its732-line independent Challenge and257-line Solution passed all-declaration audits (349 Challenge,85 Solution),199 Challenge/Solution semantic checks and actual root build439. All seven support/main targets are explicit, including global alpha existence. Prepared independent coverage is63/103,40remaining; these are local interfaces, not official passes. See docs/audit/scheme-alpha-character-integration-439/coverage.json.

The complete relative-alpha interface adds full original accepted-038 and accepted-039 at arbitrary universe u and every positive level divisible by4. It retains actual root data, the unique realizing alpha frame and all original base-change/marking conditions. Canonical pointed comparison is uniquely specified on local derivatives and proved equal to the original, including exact alpha pullback. Original reverse bridges and rfl type checks pass, with all-declaration axiom and Challenge/Solution definition audits and actual root build444. Prepared independent coverage is65/103,38remaining; these are local interfaces, not official passes. Inherited052 is not counted twice. See docs/audit/relative-alpha-integration-444/coverage.json.

The complete Tate-alpha interface adds full original accepted-040 for every positive level divisible by4: actual full marking on the actual Tate cubic, original normalized boundary differential, full power-series-unit expansion of exact order0 or L/4 and the exact signed thetaAt squared identity for every primitive root and canonical marking. Literal full series and all nonidentity point coordinates are retained. Boundary predicate/generator rfl bridges, full original theorem recovery, all-declaration axioms,240 semantic-definition comparisons and actual root build447 pass. Prepared independent coverage is66/103,37remaining; these are local interfaces, not official passes. Inherited052 is not counted twice. See docs/audit/tate-alpha-integration-447/coverage.json.

The complete phase-free multiplier interface adds full original accepted-095 and accepted-097 at arbitrary universe u. It retains actual all-scheme marked Cartesian tests, local invertibility and frame generation, all test-map naturality, inverse character for every actual Miller phase and even-stabilizer change, and the exact reversal law. Existence and uniqueness of the multiplier and the full base-change isomorphism are proved with literal canonical pullback compositions. Full original statements/rfl recovery, all-declaration axiom audits,275 semantic-definition comparisons and actual root build452 pass. Prepared independent coverage is68/103,35remaining; these are local interfaces, not official passes. Inherited052 is not counted twice. See docs/audit/phase-free-multiplier-integration-452/coverage.json.

Official preflight39479248485 for historical088eff2 completed with solution-build OOM (exit137), not a kernel verdict. Genuine report and resource analysis: docs/audit/official-sharp-adaptive-image-result-453/Review.md. Complete-main and sharp-and-roots preflights remain active at snapshot448; no whole-paper official acceptance or ordinary submission claimed.

The complete multiplier-fourth interface adds full original accepted-100 at arbitrary universe u: actual fourth tensor power trivialization uniquely normalized to1 on every prescribed multiplier frame. Canonical pullback comparison is uniquely fixed on all local sections and opens and proved equal to the original; unit pullback and full normalization predicate are recovered. Invertibility is extracted from original IsMultiplier, not an extra assumption. Full original statement/rfl recovery, all-declaration axioms,300 semantic-definition comparisons and actual root build457 pass. Prepared independent coverage is69/103,34remaining; these are local interfaces, not official passes. Inherited052095097 not recounted. See docs/audit/multiplier-fourth-integration-457/coverage.json.

The complete phase-free alpha descent interface adds full original accepted-096 at arbitrary universe u: unique section of the actual cotangent tensor multiplier line and frame generation on every subopen. Every marked test retains both nonvacuity existentials and full tensor equality for every compatible cotangent map and realizing alpha. Canonical binary tensor comparison is uniquely fixed on all local pure tensors and proved equal to original. Full Descends/original statement recovery, all-declaration axioms, semantic-definition checks and actual root build461 pass. Prepared independent coverage is70/103,33remaining; these are local interfaces, not official passes. Inherited052095097 not recounted. See docs/audit/phase-free-alpha-descent-integration-461/coverage.json.
