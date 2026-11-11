# Verification of the additive review interfaces

The reports describe separate checks. They do not claim independent human
acceptance of the mathematical semantics.

| Evidence | Scope |
| --- | --- |
| [OriginalPreservationReport.json](OriginalPreservationReport.json) | All 20,724 protected files unchanged; all 1,199 original source/object pairs revalidated before and after a fresh run of the original 103 exact-type and axiom probes; zero original proof modules recompiled |
| [PortableReproductionReport.json](PortableReproductionReport.json) | End-to-end use of the portable runner: source compilation of all 13 additive modules, joint ReviewRoot importing the original GoalRoot, 18 new exact-type/axiom checks and all 103 original checks |
| [PortableBuildBindings.json](PortableBuildBindings.json) | Exact additive source/object hashes, import graph and pinned reproduction inputs |
| [AuditReport.json](AuditReport.json) | Wujie's independent audit of the frozen combined 18-obligation contract and the current additive source snapshot |
| [ProofStatus.json](ProofStatus.json) and [DeliveryManifest.json](DeliveryManifest.json) | Status and bindings emitted by that auditor, with manifest paths relative to its recorded staged delivery directory |
| [DefinitionDependencyReport.json](DefinitionDependencyReport.json) | Joint measurement of original and new elaborated statement-definition dependencies; not a proof-compression or human-acceptance metric |
| [SemanticInterfaceReview.md](SemanticInterfaceReview.md) | Internal agent review of actual geometric/scalar/normalization links and quantifiers; explicitly not a mathematician's independent semantic acceptance |

The original **1,199 modules and 103 endpoints** retain their original inventory.
The new library adds **13 modules and 18 checked exports**. Its combined root has
a distinct name so that the original `GoalRoot.lean` remains byte-for-byte
unchanged. The authority audit uses a leaf contract for this additive library
and compiles its actual `ReviewRoot`, which imports both complete inventories.

Only the standard logical axioms `propext`, `Classical.choice` and `Quot.sound`
are allowed. Type checks elaborate and synthesize the expected statements,
reject residual metavariables and compare actual declaration types. The original
preservation report, portable build and authority audit serve different
purposes; no historical success flag substitutes for current bindings.

The new finite-level predicate and main statements project a mathematically
useful interface from richer original witnesses. Original explicit torsor/fiber
construction data, conditional surjectivity and exact ranks remain in the old
theorems. No reverse reconstruction or equality of those complete record types
is claimed. See the [formalization mapping](../FormalizationMapping.md).

Use [Reproduce.md](../Reproduce.md) and the
[portable instructions](../scripts/REPRODUCE_REVIEW.md) to repeat the checks.
Local absolute paths and timestamps in reports record provenance; new runs may
have different object hashes and paths. The explicit fresh-build route records
those new source/object bindings instead of assuming the author's paths.
