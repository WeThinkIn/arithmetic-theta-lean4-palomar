module

public import ExtendedMetaplecticDefinitionsR0241

@[expose] public section

/-! The interior of the literal coefficient extension of the compact cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaExtendedMetaplecticR0241
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ExtendedInteriorGeometryProof

private lemma old_interior_over
    {k : Type} [Field k] [CharZero k] {n h : ℕ}
    {A : ArithmeticThetaLatticeSectionsR0188.Matrices n h}
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    ArithmeticThetaCompactModularityR0209.interiorInclusion G.root ≫
        ArithmeticThetaArithmeticFieldR0231.structureMap G =
      (ArithmeticThetaCompactModularityR0209.interiorBase G.root).hom := by
  change ArithmeticThetaCompactModularityR0209.interiorInclusion G.root ≫
    (ArithmeticThetaCompactModularityR0209.compactMap G.root ≫ G.root.compact.projection) = _
  rw [← Category.assoc, pullback.condition, Category.assoc, G.root.compact.over_eq]
  rfl

end ExtendedInteriorGeometryProof

/-- The prescribed interior is Cartesian over the new coefficient field and
is a dense open subscheme of the same scalar-extended compact cover. -/
theorem extended_interior_geometry
    (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (hG : ArithmeticThetaCompactModularityR0209.ActualLevel G.root) :
    IsPullback (toOldInterior ι G) (interiorBase ι G).hom
      (ArithmeticThetaCompactModularityR0209.interiorBase G.root).hom
      (ArithmeticThetaScalarExtensionR0240.fieldMap ι) ∧
    IsOpenImmersion (inclusion ι G) ∧ DenseRange (inclusion ι G).base := by
  have hs := (IsPullback.of_hasPullback
    (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)).flip.paste_vert
      (IsPullback.of_hasPullback
        (ArithmeticThetaArithmeticFieldR0231.structureMap G)
        (ArithmeticThetaScalarExtensionR0240.fieldMap ι))
  rw [ExtendedInteriorGeometryProof.old_interior_over G] at hs
  letI : IsOpenImmersion (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root) :=
    hG.1.1
  letI : IsOpenImmersion (inclusion ι G) := inferInstance
  refine ⟨hs, inferInstance, ?_⟩
  have hg := ArithmeticThetaScalarExtensionR0240.scalar_extension_geometry
    k l ι n h hn hh A hA G
  letI : GeometricallyIntegral (ArithmeticThetaScalarExtensionR0240.structureMap ι G) :=
    hg.2.2.2.1
  letI : IsIntegral (ArithmeticThetaScalarExtensionR0240.Space ι G) :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (ArithmeticThetaScalarExtensionR0240.structureMap ι G)
  letI : IsIntegral G.root.cover.space := G.root.cover.integral
  haveI : Nonempty (ArithmeticThetaCompactModularityR0209.Interior G.root) :=
    hG.1.2.1.nonempty
  letI : Surjective (ArithmeticThetaScalarExtensionR0240.fieldMap ι) := inferInstance
  haveI : Nonempty (Interior ι G) :=
    (toOldInterior ι G).surjective.nonempty
  exact (inclusion ι G).isOpenMap.denseRange_of_isPreirreducibleSpace

#print axioms extended_interior_geometry
end ArithmeticThetaExtendedMetaplecticR0241
