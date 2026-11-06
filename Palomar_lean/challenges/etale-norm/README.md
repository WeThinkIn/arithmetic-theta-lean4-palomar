# Independent finite étale norm-family package, attempt 259

This is an independent specification and proof transport of accepted-098 only. It retains the original endpoint and does not replace the full task inventory of 13 requirements and 103 endpoints. There is no full-paper completion claim.

`Challenge.lean` imports only Mathlib and defines actual section rings of arbitrary schemes, their restriction maps, the determinant norm with the algebra induced by the specified scheme morphism `f.app`, free affine tests, and multiplicative maps on every open. The target asserts existence and uniqueness of the entire family for every finite étale morphism between arbitrary universe-polymorphic schemes. It retains every section including zero and all empty/rank-zero cases. The single `sorry` is the intentional independent challenge placeholder.

`Solution.lean` repeats the independent definitions and imports the real compiled provider `FiniteEtaleNormFamilyR0251`. The proof uses the original theorem without any extra hypothesis. Seven kernel-checked defining equalities show that Sections, restrict, affineNorm, AffineFree, IsNormSection, NormFamily, and IsNormFamily agree with the actual implementation. The target and all seven bridges have axiom closures containing only propext, Classical.choice, and Quot.sound. No sorry, admit, or new axiom is present in Solution.

The norm family consists of monoid homomorphisms on the full section rings (not merely their units). Such homomorphisms induce maps on units, but no separate unit-norm theorem is claimed by this single endpoint. No additive ring-homomorphism law for the determinant norm is asserted. IsNormFamily explicitly gives determinant normalization and the restriction equality on every pair of opens. No arbitrary predicate or assumed norm witness replaces these laws.

`Scope.json` preserves the original accepted-098 exact type and source statement. `checkpoint.json` binds the original definition sources, provider source/object, manifest, toolchain and prepared independent source files. `compile-receipt.json` records both actual isolated compiler exits and inherited import path; the full logs record the axiom closures. Outputs are only in this evidence directory. Project sources and the original delivery remain untouched.

To reproduce from the main project directory:

```bash
python3 ../tools/run.py lake env python3 ../evidence/etale-norm-package-259/compile.py
python3 ../tools/run.py lake env python3 ../evidence/etale-norm-package-259/export.py
python3 ../tools/run.py python3 ../evidence/etale-norm-package-259/compare.py
```

The compile script uses 12 threads and 300 seconds per source; the export uses 8 threads with 300 seconds per module. The Comparator uses normal bubblewrap 0.12.0 isolation, con-ron with --jobs=2, NanoDa and Lean's default checker, with a 600 second total budget. Its actual result is in comparator-modern-receipt.json and comparator-modern.log once finished. Hash-bound from-export checking is local verification, not the official isolated challenge source-provenance audit. No official preflight, submission, or registry action is performed by this package worker.
