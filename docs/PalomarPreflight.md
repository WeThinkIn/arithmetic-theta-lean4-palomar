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
| [39451125672](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39451125672) | `fb7ebe8a1cb6f7cd8e3728aaa3d184d004723ba9` | In progress at this checkpoint. Request generation and immutable-source preparation passed. No mechanical pass claimed. |

The request-format repair uses a separate job to generate a twelve-character
hexadecimal identifier. The original rejected input and corrected input were
also checked locally against the pinned official `submission_request` parser.
That local diagnosis is not an official mechanical pass.

Palomar requires a passing full reusable mechanical report for the exact source
commit and Comparator configuration before formal intake. A pilot pass would
cover only its stated pilot theorem. Permanent registry publication is a
separate later action after the review is available.
