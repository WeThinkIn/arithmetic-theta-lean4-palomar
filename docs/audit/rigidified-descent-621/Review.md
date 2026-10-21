# Optimized rigidified descent: local target verified by three kernels

A private theorem now proves the descent-isomorphism construction for general rigidified data, and the original asm_b theorem specializes it to the original rigidified line bundles. The original hypotheses and full conclusion are retained. This candidate is isolated and has not yet been integrated into the public proof sources.

The module compiles in383.60seconds versus818.04seconds for the baseline. PeakRSS falls from10,662,248,448bytes to6,070,689,792bytes (43.06%). The generic helper takes36.503seconds in the kernel and original asm_b0.00478seconds, compared with455.037seconds for the original proof. Different concurrent system load limits timing precision. The exact audit preserves297original named declaration types and universe parameters,87definition bodies, and standard-only transitive axioms.

The valid target export is315,104,126bytes with SHA256 bb315bebd8cbed756831becb871fc8aad35866abb31d80e8ac3da486fed67480. Its requested target declaration is verified present, no exporter PANIC occurs, and all bound inputs remain unchanged. All three local kernels accept this export:

| Checker | Result | Time |
| --- | --- | --- |
| Pinned unmodified Lean default | PASS; peakRSS3,489,943,552bytes |591.65seconds |
| con-ron, verified mode | PASS;33042declarations |51.43seconds |
| NanoDa, three standard permitted axioms | PASS;35063declarations, no typechecker errors |44.58seconds |

NanoDa additionally reports a pretty-printer error (Unable to print axioms), recorded in its log; this is not a typechecker rejection. The initial export01 used an incorrect target namespace and is explicitly rejected in export-01-assessment.json. Only export02 supports the results above.

These results concern asm_b and its dependency closure. They do not establish acceptance of the complete common-unary interface or the whole manuscript, nor do they solve official cold-build capacity by themselves. The next gates are the complete192-module affected dependency rebuild, all103original endpoint audits, and full common-unary interface comparison and kernel checks. Official preflight, semantic review and registration remain separate.
