import ProperFunctions

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace ArithmeticThetaConstantDescent

/-- The actual base morphism induced by a field extension. -/
noncomputable abbrev fieldMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- Scalar extension of an actual scheme, formed by the categorical fibre product. -/
noncomputable abbrev baseChange (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) : Scheme.{u} :=
  pullback f (fieldMap K L)

/-- The projection to the original scheme. -/
noncomputable abbrev projection (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) : baseChange K L X f ⟶ X :=
  pullback.fst f (fieldMap K L)

/-- The structure morphism of the scalar extension. -/
noncomputable abbrev structureMap (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) :
    baseChange K L X f ⟶ Spec (CommRingCat.of L) :=
  pullback.snd f (fieldMap K L)

/-- Pullback of genuine global regular functions along the projection. -/
noncomputable abbrev pullbackSections (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) :
    (X.presheaf.obj (Opposite.op ⊤)) →+*
      ((baseChange K L X f).presheaf.obj (Opposite.op ⊤)) :=
  (projection K L X f).appTop.hom

/-- The first genuine pullback of sections to the self fibre product. -/
noncomputable abbrev leftOverlapMap (X Y : Scheme.{u}) (f : X ⟶ Y) :
    (X.presheaf.obj (Opposite.op ⊤)) →+*
      ((pullback f f).presheaf.obj (Opposite.op ⊤)) :=
  (pullback.fst (C := Scheme.{u}) f f).appTop.hom

/-- The second genuine pullback of sections to the self fibre product. -/
noncomputable abbrev rightOverlapMap (X Y : Scheme.{u}) (f : X ⟶ Y) :
    (X.presheaf.obj (Opposite.op ⊤)) →+*
      ((pullback f f).presheaf.obj (Opposite.op ⊤)) :=
  (pullback.snd (C := Scheme.{u}) f f).appTop.hom

end ArithmeticThetaConstantDescent
