# Main consolidation — 28 October 2026

`main` is the sole maintained branch. The 16 former development branches are retired. New changes and new GitHub preflight dispatches use `main`; temporary working branches, if needed, must be integrated and removed rather than maintained as parallel editions.

Consolidation starts from `b6be950031232ec20b28f06e5c45185391d62c06`. Every recorded branch tip is an ancestor of the consolidated main history. Each retired tip is also preserved by the annotated tag `archive/20261028/<former-branch-name>` before its branch reference is removed. Tags are historical snapshots, not maintained branches.

## Integrated results

- Seven tips were already ancestors of the original main. Their results remain intact.
- Standard GitHub runner restoration is included in history; the final workflow retains `ubuntu-24.04` and `palomar-standard-v1`. The intermediate Namespace profile selection is superseded.
- Six metadata repairs disclose the supplied geometric inputs and selected character law in FieldUnary, CompactUnary, IsogenyAlphaCusps, RelativeAlpha and TateAlpha, and correctly describe the conservative cover degree as an upper bound.
- The audited TateTrace change replaces two theorem proof bodies with explicit existing instances. Baseline Lake scheduling and its audit evidence are included. All Palomar proof sources and the Lake configuration match the previously audited `2c23d546a2bfd11ad6cbe5f49a58ac6c047d546d` revision.
- No discarded, unpublished performance experiments are included. Historical evidence remains revision-bound; historical resource failures are not converted into successes.

## Protected local reproduction

The complete `local-reproduction/` tree is identical to the original main, including all sources, embedded dependencies, scripts, fixed manifests, probes, publication files and existing verification reports. The root `README.md`, `.gitignore`, `paper/`, `lean-toolchain` and `lake-manifest.json` also remain unchanged.

The local reproduction uses its own Lean 4.33.1 toolchain and directory-local dependencies. Its scripts do not consume the top-level Palomar Lake configuration. The existing `local-lean4331-reproduction-20261027` release tag and all six binary dependency assets are preserved. The Palomar edition remains on Lean 4.35.0-rc2.

## Validation and evidence limits

- All 16 branch tips are reachable from the consolidated main; merges completed without conflicts.
- Protected Git trees and every tracked local-reproduction file are checked against the baseline main.
- The existing compiled TateTrace artifact is hash-bound to the merged source. A fresh Lean declaration audit rechecks 316 declarations against the baseline: exact type expressions, universe parameters and axiom sets agree, with only the two intended theorem proof bodies changed.
- The four existing local-reproduction unit tests pass; comparator JSON, scope JSON, submission YAML and Lake TOML parse; comparator configurations and challenge/solution Lean entry points remain unchanged.
- The historical `candidate.patch` is retained verbatim. Its two blank context lines are excluded from the general whitespace check because their leading spaces are required unified-diff syntax.
- This consolidation does not claim a new full cold build or a new Palomar semantic acceptance. Official reports remain tied to their original commits.

Previously prepared submission attempts pinned to an exact historical commit remain historical attempts. Archiving their former branches does not rebind them to main or authorize reusing their reports for the merged revision. Future source development and new preflight scheduling use main.

## Retired branch inventory

| Former branch | Exact tip | Disposition at consolidation |
| --- | --- | --- |
| `palomar-approved-profile-retries-2475` | `55736935d2f4470a0c46bf7d88255c15d1f0be7b` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-audited-standard-followup-2553` | `2c23d546a2bfd11ad6cbe5f49a58ac6c047d546d` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-compact-unary-scope-2563` | `47e210382a7b265c2d7013728a102b5be3f5044a` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-conservative-scope-repair-2561` | `4d3e823f3bdea889c5cbc484a10589d0188b194e` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-coordinates-full-2371` | `2e59b748d5e40772e9cb77f2ce804b10a8984898` | Already in baseline main |
| `palomar-field-unary-scope-repair-2560` | `edcf55fb5201f5a9e1abc59ed5148c024fb26958` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-five-full-2399` | `dd78dc68a833e255ae034552e002c228a8e54803` | Already in baseline main |
| `palomar-formal-cover-full-2432` | `039b06cb8e9c1f6c230ea51e841c44b60fbafe2a` | Already in baseline main |
| `palomar-formal-cover-full-2474` | `4ee6883625fdbbc3e4eaacf3c548ef7bb4731d68` | Already in baseline main |
| `palomar-four-required-full-2440` | `7517ab6862e467913025ac47198e209624b306b8` | Already in baseline main |
| `palomar-github-standard-restoration-2512` | `04e1a807abc0d04a8ea22f1567a0484066f23b30` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-isogeny-alpha-input-scope-2627` | `134e589f3e8a3c557d0d35b8cc5f719ecdf124dc` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-relative-alpha-character-repair-2581` | `c4abbfbf37646bd365aa23a56ce53fb220240baf` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-tate-alpha-character-repair-2585` | `08d9dafdd873e7e884eb8df95df561a1e7640507` | Merged, including inherited commits; superseded runner choice stays superseded |
| `palomar-thirteen-full-2372` | `381f2ccf9a101e4f7090874f51e7b1061adbdaa4` | Already in baseline main |
| `palomar-unary-geometric-full-2391` | `7ede2df8416954f2e5633d67814973747eb97628` | Already in baseline main |
