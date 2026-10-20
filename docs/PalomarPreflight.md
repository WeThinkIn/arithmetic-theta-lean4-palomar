# Official Palomar preflight record

The repository is public following explicit authorization from its responsible
maintainer. Its original code is licensed under Apache-2.0. Official submission
has not occurred, and this record does not claim complete verification.

The reusable workflow is pinned to
`PalomarRegistry/PalomarSubmission@d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`,
with `mode: full` and `execution_profile: palomar-standard-v1`.
The current root `comparator.json` checks the finite-determination pilot only.
The 13 original requirements and 103 exact endpoints remain in scope;
full-paper coverage requires the remaining migration and independent interfaces.

| Run | Source commit | Result |
| --- | --- | --- |
| [39450500400](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39450500400) | `8a0354835326074f74e8a0efc6ac116a8bf29cde` | Failed before Lean execution. The request identifier did not satisfy the official parser's exact twelve-character lowercase alphanumeric requirement. The report finalizer replaced this preparation error with a generic reporting diagnostic. |
| [39451125672](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39451125672) | `fb7ebe8a1cb6f7cd8e3728aaa3d184d004723ba9` | Cancelled after its immutable source was superseded by verified compatibility fixes. No mechanical pass. |
| [39455278417](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39455278417) | `12f83ea0c4570555a88349850507ff1d06f2c6dd` | **Official mechanical pass**, configuration `comparator-early.json`, accepted-017 only. Report status `pass`, stage `complete`, checked 2026-10-20T16:21:32Z. |

The passing early-certificate report checked3929 committed Lean source files, accepted the Challenge's allowlisted Mathlib provenance with no untrusted source, built the Solution from source, and accepted it in con-ron, NanoDa and Lean default kernel. The report and download receipt are preserved under `docs/audit/official-early-preflight-256/`. This is one scoped mechanical result; no formal intake, semantic review, complete-paper pass or registration is claimed.

The request-format repair uses a separate job to generate a twelve-character
hexadecimal identifier. The original rejected input and corrected input were
also checked locally against the pinned official `submission_request` parser.
That local diagnosis is not an official mechanical pass.

Palomar requires a passing full reusable mechanical report for the exact source
commit and Comparator configuration before formal intake. A pilot pass would
cover only its stated pilot theorem. Permanent registry publication is a
separate later action after the review is available.

Two additional scoped configurations are prepared for official full preflight:
`comparator-main-and-components.json` (43 targets, the main explicit bound and 39 complete prior endpoints) with `submissions/main-and-components/formalization.yaml`, and
`comparator-formal-cover.json` (accepted-050) with `submissions/formal-cover/formalization.yaml`.
All four root modules were genuinely rebuilt in Lake (build 276, exit 0); no isolated object was renamed. Their source bindings are in `docs/audit/root-packages-276/receipt.json`. Official checks and formal intake for these configurations remain pending.
