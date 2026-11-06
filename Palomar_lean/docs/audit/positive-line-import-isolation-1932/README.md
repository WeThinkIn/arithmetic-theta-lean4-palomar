# Positive-line dependency isolation

The positive-line definitions module no longer imports AffineMarkedComplementR0133. Every declaration in the module is unchanged. This removes an unused build dependency while retaining the original theorem statements and implementation.

The isolated candidate was rebuilt across 776 affected modules. Exact serialized declaration comparison checked 25,775 declaration records, including types, ordered universe parameters, data bodies, relevant metadata, and standard proposition axiom closures. A batch with mutually conflicting compatibility imports was checked one module at a time; every module passed.

The combination with the current root-descent optimization reuses 655 source-bound module artifacts and recompiles 121 modules. Its declaration comparison and frozen 103-endpoint type/axiom audit are separate release gates. The machine-readable receipt records whether those gates have completed. This optimization does not itself add official endpoint coverage or assert whole-paper acceptance.
