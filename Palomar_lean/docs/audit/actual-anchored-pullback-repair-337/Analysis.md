# Isolated actual anchored pullback repair 337

The original line59 hp goal is an equality of representable Points morphisms, involving the same pointId, representable.mapComp and precompose as checked repair327. The actual arrow type in the pinned Mathlib environment is Discrete.Hom, not ULift. Replacing the two-line ULift.ext/Subsingleton.elim block with `exact congrArg Discrete.Hom.mk rfl` proves precisely that original equality using the constructor and proof irrelevance, as in Mathlib Discrete.hom_eq.

No object, map, declaration signature, selected anchor, composition direction or hypothesis is changed. The actual family/root isomorphisms and both the identity and naturality coherence equations remain intact. No new instance, compiler option or axiom is introduced. Every other source byte is unchanged.

Validation uses a complete isolated source compile and an independent importer printing all eight explicit declaration axiom closures and applying actual_anchored_pullback at its exact original signature. The actual final results and times are recorded in receipt.json. The importer prioritizes this evidence directory on LEAN_PATH. Each compile uses 12 threads and a 300-second bound with existing dependency objects.

The original project source and direct dependency source/object hashes are verified at finalization. No shared project or .lake write, export, Comparator or official workflow is performed. Parent owns integration after receiving the completed receipt.
