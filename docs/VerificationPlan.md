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

No full-paper Palomar result is available. The legacy default comparator.json is an earlier pilot and should not be confused with these explicit configurations. Independent geometric specifications, including actual scheme-discriminant existence/naturality and the full sharp geometric family, remain open despite their migrated original-type proofs passing.

The additional `comparator-sharp-and-roots.json` pairs the full accepted-049 principal sharp theta conclusion with complete accepted-056/057 actual ambient/smooth-point root constructions. Its990-line/66941-byte Mathlib-only Challenge retains all original fields and the actual canonical tensor comparison; all local checks and the actual named root build361 passed. It adds two distinct endpoint IDs, bringing prepared independent interface coverage to50/103 (the remaining53 still need interfaces). This is not50 official passes. Official preflight for this new package is the next controlled resource experiment; it has not been ordinary-submitted or registered.

Official resource report362: older run39461299032 failed during `solution-build`, with15824445440bytes (~14.74GiB) recorded peak memory, `oom_kill:9` and `deadline_fired:false`. Challenge provenance was high/Mathlib-only. This is a failed mechanical attempt due to infrastructure resources, not a proof rejection. Preserve ongoing complete-main39469688913 and sharp/adaptive/image39479248485; do not retry unchanged resource conditions. See `audit/official-older-main-362/`.


Resource experiment364 sets package-level `weakLeanArgs = ["-j1"]`, confirmed in actual compiler arguments by isolated Lake probe363. This limits internal Lean threads per compiler, not simultaneous Lake compiler processes; unchanged theorem types, proof bodies, Comparator and kernel checks are retained. The official cold-build memory effect remains unverified. Larger Namespace runner availability was not established. See `audit/resource-diagnosis-363/Analysis.md`.

The additional `comparator-sharp-and-coordinates.json` specifies complete accepted019/020/021/022 coordinates, poles, cubic and global normalized differential together with the accepted049 principal sharp theta conclusion. Its670-line/40226-byte Mathlib-only Challenge, Solution,38-declaration standard-axiom audit and actual named root build384 passed. It adds four distinct endpoint IDs, bringing prepared independent interface coverage to54/103, with49 remaining. This is not54 official passes. Official dispatch is deferred pending the existing resource experiment39482676946. See challenges/sharp-and-coordinates/ and docs/audit/sharp-and-coordinates-384/coverage.json.
