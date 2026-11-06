# Isolated categorical-root-fiber repair 333

Five original sites incorrectly apply ULift.ext to equalities of morphisms in Points, whose actual arrow type is Discrete.Hom under the current Mathlib API. They are pointsDiscrete.subsingleton (line152), the two comma-morphism components in fiberDiscrete.subsingleton (line158), identity comparisons for f.left and f.right (lines167/168), and the two comma components of presentation naturality (line307).

Each arrow-equality proof now uses `exact congrArg Discrete.Hom.mk rfl`, the same constructor/proof-irrelevance argument as Mathlib Discrete.hom_eq. The existing CommaMorphism.ext step remains unchanged at both comma sites. Three other ULift.ext uses at original lines153/161/162 prove object equalities and are correct; all three are preserved verbatim. Thus the patch distinguishes object and arrow representations instead of globally replacing ULift.ext.

All mathematical signatures, categorical objects, geometric maps, square-isometry data, equivalences, naturality directions and original hypotheses remain unchanged. The two discrete-category instances prove the same statements; the actual comma fiber, arrows and both projections remain intact. No axiom, additional premise, dummy proposition, typeclass registration or compiler-option change is introduced.

The complete repaired module compiled successfully in36.61seconds with exit0. An independent importer Audit compiled in3.12seconds with exit0, loading the isolated repaired object first. All29 explicit declarations (including Geo, both discrete instances, the equivalence/presentation and the final categorical_root_fiber endpoint) have only propext, Classical.choice and Quot.sound dependencies. The final endpoint is also applied at its exact copied original signature. No sorryAx occurs.

The source and direct dependency source/object bindings were verified unchanged after compilation. All writes are confined to this evidence directory, with Lean4.35.0-rc2,12 threads and a300-second limit per file. No project/shared .lake mutation, export, Comparator or official workflow occurred; the running root330 was untouched. Parent owns integration after its termination.
