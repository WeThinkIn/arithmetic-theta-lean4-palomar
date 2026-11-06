# Local Lean 4.33.1 verification

The subsequent **statement-readability pass of 6 November 2026** changes seven
supporting modules. It separates dependent witnesses, hypotheses and conclusions,
uses scoped short names and standard notation, and introduces two private,
transparent abbreviations for Čech chart sections and overlap compatibility.
All seven mathematical lines previously exceeding 500 characters have been
reorganized into shorter statements; the remaining 20 such lines are unchanged
namespace helper commands.

This pass verified the complete **1,199-module** development with the Wujie
dependency-cone builder: **699 modules recompiled** and
**500 modules reused after source, dependency, compiler and
object checks**. `GoalRoot` was rebuilt. All **103 frozen exact-type and
transitive-axiom probes passed**. Comparison with the immediately preceding
source revision, `75c1e12918084e8c34a387deb29ef11125e160cd`, preserved
**23,783 previous non-internal named declaration types** and
**6,773 definition bodies**, including declaration kinds and
universe parameters. These counts include transparent abbreviations added by
the earlier readability pass. The comparison excludes generated internal names,
theorem proof terms and opaque bodies.

| Current evidence | What it verifies |
| --- | --- |
| [Statement preservation report](StatementReadabilityPreservationReport.json) | Current input-manifest hash, scope, metrics, builder identity, and hashes of the following reports |
| [Complete build report](StatementReadabilityBuildReport.json) | All module source/object bindings, compiler results, and the distinction between fresh and reused objects |
| [Frozen endpoint report](StatementReadabilityEndpointReport.json) | All 103 original exact-type checks and their permitted axiom closures |
| [Declaration comparison](StatementReadabilityDeclarationReport.json) | The previous complete environment compared with the current complete environment using the same pinned dependencies |
| [External environment comparison](StatementReadabilityEnvironmentReport.json) | All 11,403 resolved external objects match the reproduction bundle's fixed hashes |
| [Completion audit](StatementReadabilityCompletionAudit.json) | Current source/report bindings, unchanged protected inputs and historical reports, documentation links, and the seven-module scope |

The original contract, probes, import graph, dependency pins and reproduction
scripts are unchanged. [The source change record](../metadata/statement-readability-source-changes.json)
lists the seven modules and their before/after hashes. Reproduction from source
still uses [REPRODUCE.md](../REPRODUCE.md). The reports below retain the earlier
revisions and are historical evidence, not new compilation claims for this pass.

## Earlier readability build and directory rename

The **6 November 2026 readability edition** passed a complete build of all
**1,199 proof modules**, including `GoalRoot`, and all **103 original exact-type
and transitive-axiom checks**. Comparison against the original compiled sources
also preserved **23,768 original non-internal named declarations** and
**6,759 definition bodies**. The baseline source commit is
`2df5f396b6d325f74ae6733612df2c5af1b915e6`.

本次可读性修订已完成全量构建和原始检查。新增的透明简称可以展开为原有表达；
原始合同、全部 103 个检查探针和外部依赖保持不变。阅读源码可从
[导读](../READING_GUIDE.md)和 [103 项定理索引](../THEOREM_INDEX.md)开始。

| Evidence | What it verifies |
| --- | --- |
| [ReadabilityPreservationReport.json](ReadabilityPreservationReport.json) | Combined result, baseline commit, recorded input-manifest hash, builder and declaration-checker hashes, and preservation counts |
| [ReadabilityBuildReport.json](ReadabilityBuildReport.json) | All 1,199 modules freshly compiled with Lean 4.33.1; per-module source and object hashes; successful source, object and environment rechecks |
| [ReadabilityEndpointReport.json](ReadabilityEndpointReport.json) | All 103 unchanged probes passed against the completed build, with their actual transitive axiom dependencies |
| [ReadabilityDeclarationReport.json](ReadabilityDeclarationReport.json) | Direct comparison of the complete baseline and candidate Lean environments; original declaration kinds, universe parameters, types and definition bodies preserved |
| [ReadabilityNegativeTests.json](ReadabilityNegativeTests.json) | The declaration comparator rejected an isolated changed theorem type and an isolated changed matrix definition |

The build used the dependency-cone builder from
`wujie-ai-lean4-proof-agent-program`, with eight parallel compilation slots and
the pinned external libraries. It freshly compiled **1,199 modules** and reused
**zero cached proof modules**. External `.olean` modules were checked against
the reproduction bundle before building. No speedup from proof-cache reuse is
claimed.

The portable `scripts/reproduce.py --verify-only` command then checked that
complete build and ran the original 103 probes. Consequently, its endpoint
report records `fresh_modules: 0` and `verified_existing_modules: 1199`; the
separate build report records the fresh compilation. These two reports describe
consecutive stages of the same verification.

All checked endpoints have only the permitted logical axioms:

```text
propext
Classical.choice
Quot.sound
```

The declaration comparison checks all original **non-internal named** constants
from the 1,199 local modules. Types must be structurally or definitionally equal;
seven types require unfolding the new transparent abbreviations. Every original
`defnInfo` body is also compared. The comparison does not inspect theorem proof
terms or opaque bodies, and excludes generated internal identifiers. Both
environments use the same pinned external dependencies, and candidate imports
cannot fall back to baseline proof objects. The checker is delivered as
[`scripts/check_declarations.lean`](../scripts/check_declarations.lean).

The two negative tests used disposable objects outside this reproduction tree.
Their expected rejection messages identify `binary_orthogonal_example` after a
theorem-type change and `binaryGram` after a definition-body change. Those
deliberately altered proof objects are not part of the delivered sources or the
successful build.

`LocalRebuildReport.json` and `LocalRebuildSummary.json` retain the **historical
original-source verification**: a fresh 1,199-module rebuild and 103 checks,
together with dependency packaging evidence. They keep their original input
hashes. The reports in `publication/` likewise describe their recorded original
delivery. Use the `Readability*` reports above for the first readability revision.
Use the `StatementReadability*` reports for the current source edition.

All verification reports are generated outputs, outside the input
`SHA256SUMS`. The preservation and endpoint reports bind the manifest recorded
for the readability build. The subsequent rename from `local-reproduction/`
to `ArithmeticTheta_Lean4/` adds a landing README and updates the reproduction
instructions, so the current manifest has new documentation hashes. Proof,
dependency, contract, probe and script hashes remain unchanged. The
[directory-rename report](DirectoryRenameReport.json) records these static
checks and the old/new manifest hashes; this rename performs no new compilation.
Historical reports retain their original path names and verification results.
Follow [REPRODUCE.md](../REPRODUCE.md) to repeat the full build and endpoint
checks, or to compare against an independently compiled original revision.
These results concern the local Lean 4.33.1 formal development; they do not
claim a cold rebuild of the external libraries, a new paper-contract audit,
or completion of the separate Palomar review.
