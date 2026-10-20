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

The current `comparator.json` is a pilot for existential finite determination
only. Its Solution has not yet passed Comparator. No full-paper Palomar result
is available. The port has a partial exact-type/axiom check for 50 endpoints (audit 242),
with the remaining endpoints and the full joint build still pending.
