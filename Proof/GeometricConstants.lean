module

public import ConstantDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ArithmeticThetaConstantDescent

open ArithmeticThetaProperFunctions

theorem proper_geometrically_integral_constants_bijective
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : Scheme.Hom X (Spec (CommRingCat.of K))) [IsProper f]
    [GeometricallyIntegral f] :
    Function.Bijective (constantMap K X f) := by
  let L := AlgebraicClosure K
  let g : Scheme.Hom (baseChange K L X f) (Spec (CommRingCat.of L)) :=
    structureMap K L X f
  letI : IsAlgClosed L := AlgebraicClosure.isAlgClosed K
  haveI : GeometricallyIntegral g := by
    dsimp [g, structureMap, baseChange]
    infer_instance
  haveI : IsIntegral (baseChange K L X f) :=
    GeometricallyIntegral.isIntegral_of_subsingleton g
  haveI : IsProper g := by
    dsimp [g, structureMap, baseChange]
    infer_instance
  haveI : Nonempty X := by
    letI : Surjective f := inferInstance
    let y : Spec (CommRingCat.of K) := Classical.choice
      (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    obtain ⟨x, _⟩ := f.surjective y
    exact ⟨x⟩
  have hsurj : Function.Surjective (constantMap K X f) := by
    intro s
    let sb := pullbackSections K L X f s
    obtain ⟨a, ha⟩ :=
      (ArithmeticThetaProperFunctions.proper_constant_map_bijective L
        (baseChange K L X f) g).surjective sb
    obtain ⟨c, hc, hcs⟩ :=
      constant_descends_along_field_extension K L X f s a (by simpa [sb] using ha.symm)
    exact ⟨c, hc.2⟩
  have hinj : Function.Injective (constantMap K X f) := by
    intro c d hcd
    let sbc := pullbackSections K L X f (constantMap K X f c)
    have hbc : sbc = constantMap L (baseChange K L X f) g (algebraMap K L c) :=
      base_change_constant_naturality K L X f c
    have hbd : pullbackSections K L X f (constantMap K X f d) =
        constantMap L (baseChange K L X f) g (algebraMap K L d) :=
      base_change_constant_naturality K L X f d
    have hEq : constantMap L (baseChange K L X f) g (algebraMap K L c) =
        constantMap L (baseChange K L X f) g (algebraMap K L d) := by
      calc
        _ = sbc := hbc.symm
        _ = pullbackSections K L X f (constantMap K X f d) := by
          dsimp [sbc]
          rw [hcd]
        _ = _ := hbd
    have : algebraMap K L c = algebraMap K L d :=
      (ArithmeticThetaProperFunctions.proper_constant_map_bijective L
        (baseChange K L X f) g).injective hEq
    exact (algebraMap K L).injective this
  exact ⟨hinj, hsurj⟩

theorem proper_geometrically_integral_unique_constant
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : Scheme.Hom X (Spec (CommRingCat.of K))) [IsProper f]
    [GeometricallyIntegral f] :
    ∀ s : (X.presheaf.obj (Opposite.op ⊤)), ∃! c : K, constantMap K X f c = s := by
  intro s
  obtain ⟨c, hc⟩ :=
    (proper_geometrically_integral_constants_bijective K X f).2 s
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (proper_geometrically_integral_constants_bijective K X f).1 (hd.trans hc.symm)

end ArithmeticThetaConstantDescent
