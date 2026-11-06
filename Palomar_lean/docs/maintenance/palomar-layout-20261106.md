# Palomar directory consolidation — 6 November 2026

The repository groups the Palomar development under `Palomar_lean/` so readers
can find the adapted proof, verification scopes, evidence and submission metadata
from one entry point. The baseline is commit
`5a5637a4bef96eaa4ef94842158e23c5a47bad96`.

| Former repository path | Current repository path | Tracked files moved |
| --- | --- | ---: |
| `Proof/` | `Palomar_lean/Proof/` | 3,950 |
| `challenges/` | `Palomar_lean/challenges/` | 575 |
| `docs/` | `Palomar_lean/docs/` | 3,066 |
| `submissions/` | `Palomar_lean/submissions/` | 77 |

All 7,668 files are retained. The existing Challenge/Solution entry points and
77 comparator configurations remain directly under `Palomar_lean/`. The shared
proof directory retains the case-sensitive name `Proof`.

## Build and workflow paths

Build commands still run from the repository root. In `lakefile.toml`, the
`ThetaProof` library's `srcDir` is now `Palomar_lean/Proof`. Library names,
module names, import statements, root targets, toolchain and dependency pins
are unchanged. The official preflight workflow selects scoped metadata from
`Palomar_lean/submissions/`.

```sh
lake build +GoalRoot +CompleteMainAndComponentsChallenge +CompleteMainAndComponentsSolution
lake env lean Palomar_lean/docs/audit/PartialEndpointAudit431.lean
```

The [Palomar guide](../../README.md) and [documentation guide](../README.md)
provide navigation for the current layout. The root README, active scope notes,
submission metadata and relative links have been adjusted accordingly.

## Preservation of proof and evidence

All 4,662 Lean source, interface and probe files in the affected directories
are byte-identical to the baseline, as are all 77 comparator configurations.
The independent `local-reproduction/` tree remains unchanged, including its
Lean 4.33.1 readability edition, dependency information and verification reports.

Historical JSON reports, logs, Lean probes, audit scripts and source-provenance
records retain their original content. Three Markdown documents bound by
historical receipts also retain their original bytes. Their old `Proof/`,
`challenges/`, `docs/` and `submissions/` references describe the recorded
revision; the table above maps them to the maintained layout. One relative
navigation link in an audit Markdown report was adjusted for the extra
directory level. Its verification conclusions were not changed.

Five README files outside this subtree, under `interfaces/size-limited/`, now
link to the relocated documentation. Their five hashes were updated in that
directory's current `manifest.json`, with a dated documentation-only note.
Its Lean, comparator and verification-data hashes retain their original values.

This maintenance change reorganizes the existing development. Historical
official Palomar results remain attached to their original commits and scopes;
the directory move does not imply a new official or semantic acceptance.

## Migration checks

The [migration validation record](palomar-layout-20261106.json) records the file
inventory, byte-preservation checks, working documentation links, all 77
workflow choices and the resolved Lake source paths. Git tree comparison also
confirms that the relocated `Proof/` contents and the independent
`local-reproduction/` tree match the baseline exactly.

The user requested migration without recompilation. The incremental build was
stopped at that request, before completion; the follow-on endpoint check was
not started. This record establishes the directory and configuration migration
and does not claim a new completed build or theorem audit.
