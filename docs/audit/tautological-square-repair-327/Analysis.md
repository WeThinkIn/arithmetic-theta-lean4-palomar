# Isolated tautological-square repair 327

The root326 error at line 85 has the same cause as checked repair318. The local hp goal equates morphisms in Points, whose object universe is lifted but whose actual morphisms are Discrete.Hom structures in the pinned Mathlib API. ULift.ext consequently cannot match that equality.

The patch replaces the two lines `apply ULift.ext` and `apply Subsingleton.elim` with `exact congrArg Discrete.Hom.mk rfl`. This is the same constructor/proof-irrelevance argument used by Mathlib Discrete.hom_eq. It proves the original hp equation between the original pointId, representable.mapComp and precompose arrows. No declaration signature, object, morphism, naturality direction, functor, geometric map or hypothesis changes; every other source byte is unchanged.

The complete module compiled with exit 0 in 11.98 seconds. A separate importer Audit compiled with exit 0 in 3.07 seconds, reading the repaired object first on LEAN_PATH. All eleven module declarations from pointId through tautological_square_pullback have only propext, Classical.choice and Quot.sound dependencies. An explicit application checks the final theorem at its exact original type: any anchored ClassifiedMap yields a Nonempty TautologicalComparison with the actual square-line components and all-test naturality. No sorryAx occurs.

The source and direct dependency source/object bindings were checked unchanged after validation. This used Lean 4.35.0-rc2, 12 threads and a 300-second limit per file. All writes are confined to this evidence directory. No shared project/.lake mutation, export, Comparator or official workflow occurred, and the active root326 build was not touched. Parent owns later integration.
