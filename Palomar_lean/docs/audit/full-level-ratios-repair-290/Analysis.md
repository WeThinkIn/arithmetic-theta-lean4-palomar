# FullLevelProjectiveRatiosR0194 isolated repair 290

The full isolated module compiled successfully with exit 0 in 121.27 seconds, using the pinned Lean 4.35.0-rc2 compiler, 12 threads and a 600-second finite budget. All 190 existing printed transitive axiom closures contain only propext, Classical.choice and Quot.sound; no sorryAx or compiler error remains. The project source was not modified by this worker.

## Exact repair

The final repair adds only two commands:

- `import all GenericThetaBasisR0140` after the module header.
- `set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in` immediately before the docstring/declaration of `origin_eulerChar`.

Removing those added commands reproduces the original file byte for byte. Every original definition, theorem statement and proof body is unchanged. The exact project-relative unified diff is `repair.patch` and the replacement source is `FullLevelProjectiveRatiosR0194.lean`.

## Cause and justification

The original line 1107 failed to synthesize the module on the actual Cech higher-cohomology group over the actual component function field. The module already exists in the Cech definition; this is a definitional-equality transparency issue while relating the local aliases F and C to their presented types. The localized instance-search transparency option allows Lean to transport those existing instances. It neither introduces a new action nor changes the structural morphism or the mathematical theorem. In particular the original `change Module.finrank F (C.HSucc ...) = 0` and original proof are retained.

The original line 3744 failed in the kernel on `_private.GenericThetaBasisR0140.0._proof_48`. Independent diagnostic 292 confirmed that this is the compiler-generated proof of `0 < 2` embedded by `Nat.mul_pos (by decide) hm` in the precise public type of `generic_theta_basis`. An ordinary import did not expose that private proof constant to the downstream kernel; importing all exposes it without changing the theorem or its standard axiom closure. Existing GeometricShiftLiftR0141, GeometricScalarLiftR0141 and SymmetricMarkingFiniteSignsR0142 already use this same import. No new axiom, admitted proof, replacement basis assumption, or weakened target was introduced. Diagnostic 292 also checked that the saved official verifier header parser accepts Lean's importAll metadata; this is a syntax diagnostic, not official submission validation.

## Validation and historical attempts

`check-04.log` and `result-04.json` contain the successful entire-module result. `axiom-closures.json` records all 190 printed closures, including origin_eulerChar, induced_symmetric and the final full_level_projective_ratios. The receipt binds original and patched source, the compiler command/path, logs, patch, generated objects and 28 direct imported public/private object artifacts. Those dependency artifacts were unchanged across the successful attempt. Parent target integration and the full-source audit remain separate checks.

Failed development evidence is retained. Attempt 01 used import-all and cechFinrank_succ rewriting: the private constant failure vanished, but rewriting exposed a Nontrivial inference problem for the overly reduced function-field colimit. Prefix attempt 02 explicitly cached Nontrivial F, which still did not match the overly reduced type. Prefix attempt 03 restored the original proof with the localized transparency option: the proof passed with standard axioms, but the inserted command was incorrectly between a docstring and its lemma. Moving the command before the docstring fixed that syntax error in the final attempt. No failed run is reported as a pass.

This is an isolated compatibility repair and compile/axiom check, not a complete source-semantic audit or an official Palomar preflight/comparator result. The parent should apply the exact patch and run the target build against current shared source, then continue its full integration.
