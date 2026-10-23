# Official Palomar preflight record

## Current recorded mechanical coverage

Official mechanical evidence covers **97 of 103 original endpoints**, counted once across their exact verified scopes and revisions. The [conservative matrix geometry preflight](audit/official-conservative-matrix-2158/Review.md) passed at `8f25de079ade1664370872d258174ff00aa90fd6`, adding original endpoints 035 and 036. Stock Lean, NanoDa and Conron accepted the Solution, and Challenge provenance is high trust. The [endpoint ledger](audit/official-conservative-matrix-2158/endpoints.json) records source and scope bindings. Whole-paper semantic acceptance and registration remain incomplete.

The [common-unary preflight](audit/common-unary-timeout-2133/Review.md) exhausted worker time in the comparator stage after successful Solution compilation and export. It adds no coverage; the rendering repair alone is not treated as a remedy for that resource failure.

The repaired complete CommonUnary interface subsequently passed [official preparation checks](audit/common-preparation-2147/Review.md) at `f953715c31be0e30d6e8a2e8877bfcee191ce9ae`. Preparation is recorded as `pending / prepared`, not complete mechanical acceptance, and adds no endpoint coverage. External full preflight reports are advisory; ordinary submissions undergo their own official verification on the production service. See the [resource-profile distinction](audit/official-resource-profiles-2140/Review.md).

The [FieldUnary scheduling change](audit/field-unary-scheduling-2163/Review.md) addresses the earlier Solution-build OOM through build prerequisites only. Its complete local resource experiment and a new official full preflight are being pursued in parallel. No additional endpoint coverage is claimed before an exact successful official report.

## Main-result verification record

The official complete-main preflight [39709205904](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39709205904)
**passed** at `57c6842d63e4860c7978dbc32307380415bcce1c`. Stock Lean,
NanoDa and Conron accepted the solution; the Mathlib-only Challenge has
high-trust provenance. Its43selected targets cover40original complete
endpoints. [Report, checksum and exact scope](audit/official-main-complete-1477/Review.md).

Ordinary submission `q0fcj6z7esrd` was successfully authenticated for that exact
revision and configuration. Service verification is
[39738618013](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39738618013).
Whole-paper semantic acceptance and permanent registration are not established.
The current reusable workflow is pinned to
`PalomarRegistry/PalomarSubmission@7a08c1da8e0558d330b9b3c244896c175d373303`.

The historical runs below retain their original results and pipeline revisions.
Their older failures do not describe the newer successful run above.


The repository is public following explicit authorization from its responsible
maintainer. Its original code is licensed under Apache-2.0. The accepted-050 scoped entry has been formally submitted and passed official
mechanical verification; semantic review is available privately. This record does not claim
complete verification of the paper.

The earlier reusable workflow recorded below was pinned to
`PalomarRegistry/PalomarSubmission@d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`,
with `mode: full` and `execution_profile: palomar-standard-v1`.
The current root `comparator.json` checks the finite-determination pilot only.
The 13 original requirements and 103 exact endpoints remain in scope;
complete GoalRoot migration and103 original endpoint checks now pass; full-paper independent coverage still requires the remaining Challenge interfaces.

The complete split-discriminant (accepted-073) and split-square-degree
(accepted-074) interfaces have also passed the **local stock comparator with all
three kernels**: con-ron, NanoDa, and Lean default. The terminal receipts,
unchanged export hashes, and source bindings are recorded in
[`audit/split-stock-kernels-574/Review.md`](audit/split-stock-kernels-574/Review.md).
These local results supplement the official record; official preflight,
whole-paper semantic review, and registration remain separate gates.

| Run | Source commit | Result |
| --- | --- | --- |
| [39450500400](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39450500400) | `8a0354835326074f74e8a0efc6ac116a8bf29cde` | Failed before Lean execution. The request identifier did not satisfy the official parser's exact twelve-character lowercase alphanumeric requirement. The report finalizer replaced this preparation error with a generic reporting diagnostic. |
| [39451125672](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39451125672) | `fb7ebe8a1cb6f7cd8e3728aaa3d184d004723ba9` | Cancelled after its immutable source was superseded by verified compatibility fixes. No mechanical pass. |
| [39455278417](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39455278417) | `12f83ea0c4570555a88349850507ff1d06f2c6dd` | **Official mechanical pass**, configuration `comparator-early.json`, accepted-017 only. Report status `pass`, stage `complete`, checked 2026-10-20T16:21:32Z. |

The passing early-certificate report checked3929 committed Lean source files, accepted the Challenge's allowlisted Mathlib provenance with no untrusted source, built the Solution from source, and accepted it in con-ron, NanoDa and Lean default kernel. The report and download receipt are preserved under `docs/audit/official-early-preflight-256/`. This early-certificate result is scoped mechanical evidence. It does not establish a semantic review, complete-paper pass or registration.

The request-format repair uses a separate job to generate a twelve-character
hexadecimal identifier. The original rejected input and corrected input were
also checked locally against the pinned official `submission_request` parser.
That local diagnosis is not an official mechanical pass.

This project's earlier intake tooling required a passing full reusable mechanical
report for the exact source commit and Comparator configuration. That was a local
conservative gate, not an official Palomar intake requirement: official documentation
describes third-party preflight reports as advisory. Ordinary submission must still
complete its own official mechanical verification. A pilot pass covers only its
stated pilot theorem. Permanent registry publication is a separate later action
after the review is available.

Two additional scoped configurations are prepared for official full preflight:
`comparator-main-and-components.json` (43 targets, the main explicit bound and 39 complete prior endpoints) with `submissions/main-and-components/formalization.yaml`, and
`comparator-formal-cover.json` (accepted-050) with `submissions/formal-cover/formalization.yaml`.
All four root modules were genuinely rebuilt in Lake (build 276, exit 0); no isolated object was renamed. Their source bindings are in `docs/audit/root-packages-276/receipt.json`. Their official outcomes are recorded below; the source bindings remain historical evidence for build276.

After correcting the required metadata basename, scoped official full runs were dispatched at commit `2bd02cf`:
- Main and components: https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39461299032
- Formal cover: https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39461300608

Both passed the initial intake preparation. Main-and-components subsequently ended with Solution-build memory exhaustion, as recorded in the [terminal report](audit/official-older-main-362/summary.json); formal-cover passed as recorded below. The earlier ced6305 attempts stopped before Lean with a metadata filename error, archived in docs/audit/official-intake-format-282. No statement or proof was changed to correct that format.

Formal-cover official run39461300608 completed with mechanical status pass, stage complete, high-trust Mathlib-only provenance and all three kernels accepting. The exact result binds2bd02cf, comparator-formal-cover.json and submissions/formal-cover/formalization.yaml. Report and receipt: docs/audit/official-formal-cover-306/. This covers accepted-050 only. Ordinary intake subsequently succeeded as recorded below; no semantic result or registration is yet claimed.

Ordinary intake for accepted-050 succeeded with submission ID `86n83vqdajt2`. The responsible-maintainer GitHub tag/gist proof completed and both temporary artifacts were removed. The submitted revision remains2bd02cf with comparator-formal-cover.json and submissions/formal-cover/formalization.yaml. This initiates official verification/review; it does not claim a semantic pass or permanent registration. Credentials remain outside Git.

Submission86n83vqdajt2 subsequently passed Palomar's own verification run39466419289 and entered review-ready. This is an official verification success for accepted-050; the semantic review is available privately, and no permanent registration has occurred.

The stronger complete-main configuration was dispatched as
[39469688913](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39469688913)
at `35c8d4a1ed4ad19ac879a31a912ab5fcd707f558`, with
`comparator-main-complete.json` and `submissions/main-complete/formalization.yaml`.
Its 43 targets cover40 complete original endpoints, including the same-B/same-U
FormalIdentity field of accepted-037. This run completed its Solution build and
export successfully, then exhausted the execution time budget in the comparator.
The [terminal report](audit/official-complete-main-result-500/Review.md) provides no
completed per-kernel verdict. It has not passed the full official preflight or
been submitted through ordinary intake.

The later repository migration checkpoint passed full GoalRoot build342 and all103 original exact endpoint/standard-axiom checks in audit343. These local results do not change the immutable source revisions or the terminal outcomes of the official checks. See MigrationStatus.md and audit/full-root-build-342/.

## Official split-discriminant result (21 October 2026)

[Run 39552053781](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39552053781) at `2c85e9b` ended with Solution-build memory exhaustion (`exit 137`, `oom-kill`). No official comparator or independent-kernel pass is inferred. The [report and assessment](audit/official-split-discriminant-result-581/Review.md) distinguish this result from the complete local three-kernel acceptance. Resource diagnosis is in progress; no unchanged retry has been dispatched.


## Official compact-unary result (21 October 2026)

[Run 39541709031](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39541709031) at `effce987` completed its Solution build successfully, then exhausted memory in the comparator stage (`exit 137`, `oom-kill`). The report does not isolate the comparator substage or establish any independent-kernel pass. The [authoritative report and assessment](audit/official-compact-unary-result-592/Review.md) distinguish this result from the separate Solution-build failure 581. No unchanged retry has been dispatched; current proof-replay resource diagnosis is separate from this older source revision.


## Official split-square-degree result (21 October 2026)

[Run 39552048056](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39552048056) at `2c85e9b` exhausted memory during Solution build (`exit 137`, `oom-kill`, recorded peak 15,828,697,088 bytes). The [authoritative report and assessment](audit/official-split-square-result-596/Review.md) distinguish the failed official cold build from the completed local three-kernel verification. No official comparator or kernel pass is inferred, and no unchanged retry has been dispatched.


## Official common-unary result (21 October 2026)

[Run 39557005985](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39557005985) at `77c9bff` exhausted memory during Solution build (`exit 137`, `oom-kill`, recorded peak 15,876,751,360 bytes). The [mechanical report and assessment](audit/official-common-unary-result-601/Review.md) do not establish any official comparator or kernel acceptance. The subsequent local stock Lean replay also terminated with a system-confirmed OOM kill; con-ron and NanoDa accepted the same solution export. The local cold-build diagnostic failed as well. [Terminal diagnostic evidence](audit/terminal-resource-analysis-611/Review.md) separates these results from the official failure; import reduction and targeted proof profiling are in progress. No unchanged retry has been dispatched.

## Local rigidified-descent optimization (21 October 2026)

An isolated proof refactor preserves the original theorem and reduces measured module peakRSS by43.06%. Its targeted export passes the pinned stock Lean checker, con-ron and NanoDa; see [the scoped result and receipts](audit/rigidified-descent-621/Review.md). The full affected dependency rebuild and103endpoint audits are in progress. This is not a complete common-unary, official preflight or whole-paper verdict, and public proof sources have not yet incorporated the candidate.
