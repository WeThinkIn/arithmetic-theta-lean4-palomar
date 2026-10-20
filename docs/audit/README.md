# Partial endpoint audit

This directory preserves a partial audit of 40 of the 103 frozen endpoint types under Lean 4.35.0-rc2. It is historical evidence for a migration checkpoint, not a passing full-source build or Palomar Comparator report.

`partial-endpoint-audit-selection-110.json` contains the exact selected original types and provider imports. `PartialEndpointAudit.lean` checks each type with an `example` whose proof is the original named declaration, then prints that declaration’s transitive axioms. `partial-endpoint-audit-110.log` is the successful output; the result JSON records exit status and SHA-256 values of the probe and log. Audit 110 adds the arbitrary formal-cover constant theorem and rechecks the previous 39 endpoints in the same environment. The older audit 03 files remain historical receipts. Only `propext`, `Classical.choice`, and `Quot.sound` appeared.

After building the imported provider modules with the pinned toolchain, run:

```sh
lake env lean docs/audit/PartialEndpointAudit.lean
```

The old result is not automatically a receipt for later source edits. A release must rebuild its source closure and rerun all 103 exact-type and axiom checks, as well as the independent Challenge/Solution comparison and scope review.
