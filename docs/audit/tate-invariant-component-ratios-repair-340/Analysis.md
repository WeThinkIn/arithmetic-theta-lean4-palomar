# Result

The full TateInvariantComponentRatiosR0265 module compiles after adding exactly one direct `import all GenericThetaBasisR0140`. Every original declaration, theorem statement, proof body, actual Tate family/lift/action and sheaf-component conclusion remains byte-identical. The original dependent `obtain` is retained.

# Diagnosis and controlled experiments

Root339 reported a dependent generalize failure at the destructuring of `generic_theta_basis` in `model_fixed`. Experiment01 replaced only that destructuring with `ExistsUnique.choose` and `choose_spec.1`; its complete module compile failed after 64.143 seconds with the more precise kernel error `unknown constant _private.GenericThetaBasisR0140.0._proof_48`. The failed variant and log are retained. This is the same private elementary proof of `0 < 2` in the basis theorem's dependent public type documented independently in evidence/generic-theta-visibility-292/Analysis.md.

Experiment02 restored the original proof completely and added only the direct import-all directive. Its full module compile passed in 65.246 seconds. Thus the dependent matching failure was a consequence of provider private-proof visibility, and no change to proof transport or coefficient construction is needed. Import-all loads the existing checked proof; it adds no axiom or mathematical hypothesis. Ordinary public imports through intermediary modules do not re-export that provider's private environment.

# Verification

The isolated module was compiled using pinned Lean 4.35.0-rc2, 12 threads and a 600-second per-compile budget. Its existing three endpoint print-axiom commands show only propext, Classical.choice and Quot.sound. An independent imported-module audit passed in 3.068 seconds and inspected all 17 non-internal module declarations through the direct module constant table; every closure is a subset of those three standard axioms, with zero unexpected axioms. It also type-checked an example with the original model_fixed statement and an example with the literal original final tate_invariant_component_ratios statement. The latter retains the actual TateLevel, marked model, scalarLiftFacts, shiftLiftFacts, both actual IsAction premises and actual ComponentRatios conclusion.

The source hash and all ten bound direct dependency public/private object hashes were unchanged before and after the checks. The candidate differs from the captured source by exactly the one import line. No project source, shared Lake output, original delivery or other agent's directory was written.

# Scope

This is a local isolated full-module compatibility repair with kernel compilation and axiom/type auditing. Parent-owned integration and actual target rebuild are still required. It is not an official Palomar validation, semantic-comparator result or a new research-significance judgment.
