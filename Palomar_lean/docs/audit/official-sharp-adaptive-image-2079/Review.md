# Official sharp-bound, adaptive-solver and image verification

The [official full mechanical preflight 39962911648](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39962911648) passed for commit `561a253f79bc11127fb0a4bc72865f23470e0ca6`, using `comparator-sharp-adaptive-image.json`. Stock Lean, NanoDa and Conron accepted the Solution. The Challenge received high-trust provenance; its 31,350 bytes and 488 lines satisfy the hard limits. The report retains the advisory warning for exceeding the preferred 300-line review surface.

The seven configured verification targets cover these seven original endpoints. Their counts happen to agree: the combined sharp target supplies two original results, while `shellFinite` supplies an auxiliary counting-series obligation.

| Original endpoint | Mathematical result |
| --- | --- |
| accepted-046 | Distinct-norm sharp arithmetic cutoff |
| accepted-049 | Complete theta-kernel determination at the sharp cutoff and every larger prefix, including rank zero |
| accepted-064 | Verified integral changes yield full-series relations |
| accepted-065 | Adaptive solver correctness, termination and first-certified scheduled stopping |
| accepted-066 | End-to-end solver with internally checked candidate changes |
| accepted-067 | Singleton input stops correctly at cutoff zero |
| accepted-088 | Certificate-derived full nullspace, image basis and unique rational coordinates |

The committed [scope specification](../../../challenges/sharp-adaptive-image/Scope.json) was checked against the exact original statements and type hashes in the 103-endpoint inventory. The [verification receipt](verification.json) records the immutable revision, configured target names, report digest and scope digest. The [original official report](mechanical-report.json) has SHA-256 `7fdc70a5c5ff77482793b21417b5b357ed1417ee318caaad6381973a2b2e336b`.

These seven endpoints were absent from the previous verified union of 82. The [updated endpoint ledger](endpoints.json) therefore records **89 of 103 original endpoints with official mechanical evidence at their respective exact revisions**. This is a union across verified scopes and revisions. It does not assert that all 89 were checked in one run or that a later repository revision inherits every prior result automatically. The ledger preserves historical local evidence paths and supplies immutable commits and official run identifiers for the recorded results.

The complete local proof retains all 13 requirements and 103 original endpoints. Size-compliant independent interfaces remain prepared for 99 endpoints; the four complete oversized interfaces are published separately. Whole-paper semantic acceptance and permanent registration remain incomplete. This record adds mechanical evidence and does not perform ordinary intake or registration.
