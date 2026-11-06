# Joint independent Palomar candidate 296

This candidate combines the unchanged first twelve packages from frozen joint274 with stronger main package295. Challenge.lean has 969 physical lines and 62,283 bytes, within the 1,000-line and 100-KiB official limits, and imports only Mathlib. Solution.lean has 1,333 lines and 86,227 bytes. The configuration has 43 targets: the first 42 names are unchanged, and the last target is ArithmeticThetaPalomarMainFormal295.explicitFiniteDeterminationWithFormalIdentity.

## Scope

The independent targets represent 40 complete existing source endpoints, with additional supporting conclusions. In particular, the main target now includes every accepted-037 field: positive-rank Indexed and FormalIdentity, cutoff equality and the exact rational bound all refer to the SAME existential U and B. Kernel equality at every larger cutoff, coefficient-vanishing equivalence, and the rank-zero constant-series formula use that same B. Shell finiteness is also supplied. The proof invokes the original conservative_matrix_kernel result once and transports its actual witness through fieldwise and defining-equality bridges; it does not combine separately chosen existential witnesses or add an unproved existence premise.

The forty source identifiers are accepted-000 through accepted-018, accepted-023 through accepted-027, accepted-037, accepted-058 through accepted-063, accepted-077 through accepted-079, accepted-089 through accepted-092, accepted-098, and binary-orthogonal-example. Scope.json retains the full source mapping and lists 63 identifiers outside this package. In particular accepted-080/081 remain pending independent packaging. The full project has 13 requirements and 103 obligations; this candidate is not a full-paper verification claim.

“Complete endpoint” here describes the mathematical fields represented by the independent statement and checked bridges. The independent statement has its own actual definitions and additional conclusions, so this is not a claim that its elaborated type is literally identical to the original declaration. No fresh Comparator equivalence result or official acceptance is claimed.

## Assembly and provenance

assemble.py retains every source definition, theorem type and proof line verbatim, moves unique imports into one header, strips duplicate headers and blank lines, and wraps bodies in separate named sections with anonymous noncomputable sections closed. No theorem renaming or mathematical compression occurs. SourceMap.json records the original file, original line number and line hash for every retained output line. inheritance-check.json verifies that all first twelve package records, bodies and line maps exactly match frozen274, the first 42 target names remain unchanged, and the Challenge hash equals the earlier read-only replacement prediction in295. The checkpoint additionally binds the frozen274 sources, configuration, maps, scope and receipts.

All original sources and frozen evidence remain unchanged. The old weaker274 main target is not retroactively upgraded, and no report generated for274 can be used as a report for296.

## Validation

Both complete source files compile with Lean 4.35.0-rc2 and the pinned Mathlib environment: Challenge exits 0 in 5.27 seconds; Solution exits 0 in 7.62 seconds. All 43 configured targets and 27 supporting declarations have only propext, Classical.choice and Quot.sound as printed axiom dependencies. Solution has no sorry/admit or new axiom declaration. Challenge contains 43 intentional target placeholders.

This attempt performs source compilation and target/support axiom checks only. It creates no exports and runs no new three-kernel Comparator, official workflow, or intake. It does not cancel or modify the current official run. The final published source/configuration/commit must undergo its own official validation before the stronger scope is attributed to an official result.

## Integration and reproduction

The parent owns project integration. Copy sources to chosen new root modules, update configuration module paths and Lake entries, preserve all 43 target names, and compile the newly named sources. Do not rename existing object files. Bind any future report and submission to the actual final commit/configuration and metadata.

From the project directory, run these sequentially:

```bash
python3 ../evidence/joint-package-296/assemble.py
python3 ../evidence/joint-package-296/verify_inheritance.py
python3 ../tools/run.py lake env python3 ../evidence/joint-package-296/compile.py
python3 ../evidence/joint-package-296/finalize.py
```

The compiler uses 12 threads with a 300-second limit per file and reuses existing dependency objects. All outputs are in evidence/joint-package-296. No project source, original delivery, shared Lake object, GitHub state or VPN state was changed by this worker.
