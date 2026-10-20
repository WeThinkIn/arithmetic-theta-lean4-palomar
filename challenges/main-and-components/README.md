# Joint independent Palomar package, attempt 274

This package combines all thirteen requested independent package source pairs into ONE Challenge/Solution configuration. Challenge.lean is 953 physical lines and 61,095 bytes, below the 1,000 line / 100 KiB Challenge limits, and imports only Mathlib. Solution.lean is 1,295 lines and 83,386 bytes. comparator.json contains the exact union of 43 configured theorem names, without dropping or renaming a target.

Both complete joint files compiled successfully in isolation with the pinned Lean 4.35.0-rc2 / Mathlib environment: Challenge exit 0 in 5.47 seconds and Solution exit 0 in 7.82 seconds. All 43 configured Solution targets, plus 22 existing supporting bridge checks, have only the permitted standard axioms propext, Classical.choice and Quot.sound. Solution has no sorry/admit/new axiom declarations. Challenge has 43 intentional target placeholders; a prose comment also contains the word sorry.

## Exact assembly

assemble.py moves all unique imports to the module header, removes duplicate module/expose-public-section directives and blank lines, and encloses each original source body in its own named section. Original anonymous noncomputable sections are explicitly closed. This preserves namespace names and keeps universe, noncomputability, local option and open scopes within their original package body. Every retained line of definitions, types and proof bodies is byte-for-byte unchanged. No compression of mathematical formulas or replacement of declarations is used.

SourceMap.json binds every original Challenge/Solution/config and available scope/receipt/log, and records the original path, line number and line hash for every retained output line. Scope.json preserves the target union and source-scope mapping. Original package sources and receipts were not edited.

## Scope distinction

There are 43 independent theorem targets representing 39 previously packaged full source endpoints plus ONE independent main arithmetic interface derived from accepted-037. The resulting 40 source identifiers MUST NOT be described as 40 complete original exact theorem types independently compared.

The main interface preserves the precise conservative cutoff, actual representatives/residues/indexing and U.count, the full kernel equality for every larger truncation, the rank-zero branch, and shell finiteness. It does not include the original accepted-037 positive-rank FormalIdentity conjunct. That extra formal factorization evidence remains separately tracked by the orthogonal package and the full original-type audit. Therefore the main interface is not a replacement for the full exact accepted-037 statement. The original accepted-037 exact type was checked separately by the root's audit273; this package makes no claim to have independently repeated that original-type audit.

The 39 prior source identifiers are accepted-000 through accepted-018, accepted-023 through accepted-027, accepted-058 through accepted-063, accepted-077 through accepted-079, accepted-089 through accepted-092, accepted-098, and binary-orthogonal-example. accepted-037 is represented only by the main arithmetic interface described above. Scope.json lists all 63 unrepresented source identifiers; in addition the full original accepted-037 type is not independently compared by the main interface. accepted-080/081 remain pending. The complete program retains 13 requirements and 103 original obligations.

## Validation level

This attempt is a fresh JOINT SOURCE COMPILATION and target-axiom check. It is NOT a new joint three-kernel Comparator result. The previous independent subpackage receipts are preserved; the main265 three-kernel run belongs to its separate owner. This worker deliberately did not produce another giant export or repeat the separate package kernel checks. The official full preflight must check the final published joint source/config/commit and its source provenance before any submission claim.

For root integration, copy the sources to the chosen new root module names, add the corresponding lean_lib entries, update only comparator challenge_module/solution_module to those module names, and actually compile those newly named modules. Keep all theorem_names unchanged. Do not rename existing .olean files. The final official report must bind the actual commit and final configuration path.

## Reproduction

From the main project directory:

```bash
python3 ../evidence/joint-package-274/assemble.py
python3 ../tools/run.py lake env python3 ../evidence/joint-package-274/compile.py
python3 ../evidence/joint-package-274/finalize.py
```

The compile script uses 12 threads and a 300-second limit for each source. All outputs stay within evidence/joint-package-274. No shared Lake writer, project edits, GitHub calls, VPN operation, official preflight or intake submission was performed by this worker.
