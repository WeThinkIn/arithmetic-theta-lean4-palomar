# Proof

For every finite étale morphism f : X → Y, the accepted implementation first glues a uniquely specified norm section from local determinant norms on free affine covers. Applying that result to every open U and every section a constructs a function n_U(a). Uniqueness of norm sections proves n_U(1)=1 and n_U(a*a')=n_U(a)*n_U(a'), so these functions are actual multiplicative homomorphisms. The same uniqueness proves their restriction law. Pointwise uniqueness then proves uniqueness of the entire family.

The independent Solution transports this theorem across seven definitionally checked equalities to an independent Mathlib-only Challenge. Its target retains the complete accepted-098 type. This transport introduces no mathematical premise and all target/bridge axiom closures contain only the three permitted standard axioms.

# Dependencies

The accepted provider is `ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family` from `Proof/FiniteEtaleNormFamilyR0251.lean`, using the existing `finite_etale_norm_section` construction. Independent definitions use actual Mathlib schemes, structure sheaves, open preimages, restriction maps, algebra norm, free modules and monoid homomorphisms. The source, immediate compiled provider, manifest and toolchain bindings are in `checkpoint.json`; compiler commands and axiom logs are retained. Export receipts additionally bind exact checked object and complete exported declaration closures.

# Limitations

This package covers accepted-098 only. It does not itself prove any Kato invariant is fixed by the constructed norm, nor the full arithmetic theta theorem. The original 13 requirements and 103 endpoints remain the task scope. Local Comparator from-export checking does not perform the official public source-provenance audit or a formal Palomar submission.
