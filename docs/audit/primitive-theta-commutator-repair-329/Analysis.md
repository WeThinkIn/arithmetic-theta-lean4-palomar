# Primitive theta commutator repair 329

The complete 1,920-line isolated module compiled with exit 0 in 32.454 seconds, using 12 threads and a 600-second wall-clock budget. A separate audit completed in 3.018 seconds, checked all 158 non-internal module declarations for transitive axioms, and elaborated the exact original pullback_left_unit and final relative_primitive_theta_commutator types. Every axiom closure is a subset of propext, Classical.choice and Quot.sound. No sorryAx remains.

The original root326 failure is a deterministic typeclass timeout, not the absence of a mathematical instance. At line 349, cancel_mono requires Mono for the composite of the inverse pullback-composition isomorphism and the pullback-identity isomorphism. The standard search for this real composite exceeded its default 20,000 heartbeats. The line345 unsolved goal and downstream sorryAx reports followed that failed elaboration.

The exact patch inserts only `set_option synthInstance.maxHeartbeats 100000 in` before pullback_left_unit. The setting remains finite and local to that lemma. Removing that one line reproduces the original source byte for byte: no theorem type, definition, proof body, scalar map, morphism, assumption or object has changed. The kernel still checks the original proof. No new axiom, sorry, target premise, or surrogate commutator was introduced.

Audit.lean independently consumes the unchanged helper type and the literal final source theorem type. The final endpoint still has the full arbitrary base ring hypotheses, doubled-level FamilyLevel, actual lifts, unique actual commutator unit and PrimitiveUnit conclusion. The exact type text was extracted from the untouched original source rather than inferred from a summary.

All 18 directly imported public/private dependency objects were hash-bound and rechecked unchanged. The original project source remained unchanged. Only this evidence directory was written; there was no dependency rebuild and no shared Lake mutation. Parent integration and root verification remain separate. These checks are not official Palomar validation or a semantic audit of the entire paper.
