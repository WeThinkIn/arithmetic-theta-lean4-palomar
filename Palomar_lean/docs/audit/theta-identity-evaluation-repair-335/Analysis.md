# Theta identity evaluation visibility repair 335

The complete 457-line module compiled with exit 0 in 6.322 seconds using 12 threads and a finite 600-second budget. A separate audit passed in 2.918 seconds: all 28 non-internal module declarations have only standard transitive axioms, and the precise source interface types and defining equations were checked.

The genuine provider is the recursive unitPowerIso definition in the same source file at line 317. Its public exposed consumer chartHodgePowerFrame at line 326 needs this definition to construct the actual tensor power frame of the conormal Hodge line. The original declaration was explicitly private despite the surrounding exposed public section; Lean reports that the private declaration exists but needs public visibility here. A different module's similarly named isomorphism is not substituted.

The exact repair is a single private-to-public modifier change for unitPowerIso. Reversing that modifier reproduces the entire original file byte for byte. Its zero and successor clauses, right unitor, tensor-map construction, chart family, comparison, and all proof bodies remain untouched. There is no new assumption, arbitrary frame, alternate isomorphism, axiom or admitted proof.

Audit.lean checks the actual unitPowerIso type, both recursive defining equations by reflexivity, the chartHodgePowerFrame type with its actual chart-family Hodge power, and the literal original full scheme_theta_identity_evaluation theorem type. The latter retains all characteristic-zero scheme bases, degree at least two and the actual evaluation morphism's epimorphism conclusion. The full-file compile checks the genuine provider and consumers together; a separate provider recompilation is neither needed nor applicable.

All six direct dependency public/private objects were bound before compilation and verified unchanged afterward. Original project source was unchanged and no shared Lake objects were written. The root may integrate the exact patch once its current writer is finished; target/root checks and official Palomar verification remain separate from this isolated repair.
