# Official preparation checks and execution resources

The external full preflight and the ordinary Palomar submission use different
execution resources. An external preflight resource failure does not establish
that the ordinary submission will fail, and a preparation-only pass is not proof
verification.

The official [submission documentation at c02bbea](https://github.com/PalomarRegistry/PalomarSubmission/blob/c02bbeaed888df45c4e28c4e99dba540ad21552a/README.md#L58-L81)
describes ordinary production as normally using 16 CPU / 32 GiB. The existing
ordinary submission's [workflow 39998168880](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39998168880)
was observed running its verification job with the corresponding Namespace
16x32 labels. This observation is not a completed resource measurement or a
verification result.

External reusable-workflow callers must select `palomar-standard-v1`, as the
[official instructions](https://github.com/PalomarRegistry/PalomarSubmission/blob/c02bbeaed888df45c4e28c4e99dba540ad21552a/README.md#L85-L119)
require. The failed CommonUnary external run recorded four effective CPUs and
approximately 16 GiB of host memory. Its Solution build and export succeeded,
but its comparator exhausted the execution budget; see the
[exact failure diagnosis](../common-unary-timeout-2133/Review.md).

The approved 32 CPU / 64 GiB tier is operator-controlled. The official service
may authorize one retry for an allowlisted authenticated account after validating
a resource failure. This repository assumes neither eligibility nor permission
to select that tier. Both published Namespace profiles retain the same
19,800-second execution budget; a larger profile does not relax Challenge size
limits or proof checks.

The repository workflow now accepts `verification_mode`:

| Mode | Meaning |
| --- | --- |
| `full` (default) | Existing full mechanical preflight, including compilation and proof checking |
| `preflight` | Official preparation checks only; no proof or independent-kernel acceptance is inferred |

The mode is passed to the same pinned official reusable workflow. The standard
external execution profile, exact source commit, scoped comparator and metadata
selection remain bound as before. Preparation reports must be recorded separately
from complete mechanical reports and do not add original-endpoint coverage.

This permits checking the current complete CommonUnary source and submission
metadata before an ordinary submission on the normal production service. The
local exact-statement, axiom, rendering and independent-kernel evidence remains
necessary evidence about the submitted scope; the official ordinary run must
still establish its own mechanical result before semantic review. No new
CommonUnary ordinary submission or passing preparation result is claimed here.
