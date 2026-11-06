# Main finite-determination definition bridges, attempt 198

All four Lean modules passed with exit 0. No module imports the Challenge theorem, and all four sources have no sorry, admit or custom axiom declarations. The printed transitive axiom closures contain only propext, Classical.choice, Quot.sound. Inputs, exact prefix hashes, commands and terminal receipts are in receipt.json and progress.jsonl.

## Ready bridges against actual compiled implementation

MainIndependentDefinitions198.lean contains exactly the independent Challenge definitions preceding its target, without importing or copying its sorry theorem. ReadyBridges198.lean imports that file and the actual already-built original modules. It checks validGram, theta, thetaMap, all seven deterministic orthogonalization definitions, castVec, integerVectors, the actual preimage lattice, period subgroup, rational quotient, coset class and representative predicate, and the displayed levelIndex product. These equality bridges are proved by rfl.

It additionally proves shell_finite from the actual exact_shell_finite theorem and coefficientMatrix_complex_eq from the actual computed_coefficient_matrix theorem. The latter is a substantive enumeration-correctness bridge between independent actual-shell counts and the original executable coefficient list, not a definitional equality. ReadyBridges198 has 20 lemmas and compiles in 2.77 seconds.

## Exact-prefix indexing bridge, awaiting real-module integration

At inspection time LatticeGlobalSectionsDefinitionsR0188.olean did not exist. No dependency build was started. OriginalArithmeticPrefix198.lean therefore reproduces verbatim only the original arithmetic declarations from abbrev Matrices through Indexed, in the original namespace, under imports whose objects already exist. The receipt records and asserts exact byte equality of that extracted declaration slice.

IndexingBridges198.lean checks commonN_eq and centered_eq, constructs both fieldwise conversions fromOriginal/toOriginal, proves count preservation, Indexed iff preservation in both directions, and both roundtrip identities. It compiles in 2.32 seconds, with only standard axioms. This is a checked proof against the exact original arithmetic declaration slice; it is not evidence that the unavailable full original geometric module has compiled.

When that module is available, copy the bridge into an integration location and replace its `public import OriginalArithmeticPrefix198` with `public import LatticeGlobalSectionsDefinitionsR0188`. Do not jointly import both: they deliberately have the same original declaration names. Recheck the resulting bridge against the real module before consuming it in a final Solution. The definitions/proof bodies of the fieldwise bridge can otherwise remain unchanged.

## Remaining dependencies and work

- Real-module recheck of IndexingBridges198 requires LatticeGlobalSectionsDefinitionsR0188 and its actual geometry dependency closure.
- level/exponent bridges to the original constants require CompactUnaryDefinitionsR0183 (not available at inspection).
- cutoff bridge requires ConservativeKernelDefinitionsR0189 (not available at inspection), plus the indexing count/commonN bridge.
- Full main theorem assembly requires accepted-037 conservative_matrix_kernel, the exact rational cutoff equality, all larger cutoffs and rank-zero formula. It is not assumed or proved here.
- The independent matrix bridge is already available, as is shell finiteness. The coefficient-prefix equivalence remains to be assembled with the full kernel statement.
- No full Solution, Comparator, official preflight, or publication has been completed by this worker.
