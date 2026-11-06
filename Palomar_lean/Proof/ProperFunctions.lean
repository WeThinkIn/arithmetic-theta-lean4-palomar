module

public import ProperFunctionsDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace ArithmeticThetaProperFunctions

theorem constant_map_integral (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [UniversallyClosed f] :
    (constantMap K X f).IsIntegral := by
  unfold constantMap
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

theorem proper_global_sections_field (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] :
    IsField (X.presheaf.obj (Opposite.op ⊤)) :=
  isField_of_universallyClosed K f

theorem proper_global_sections_finite (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] :
    f.appTop.hom.Finite :=
  finite_appTop_of_universallyClosed K f

theorem proper_constant_map_bijective (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] [IsAlgClosed K] :
    Function.Bijective (constantMap K X f) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral _ (constant_map_integral K X f)

theorem proper_unique_constant (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] [IsAlgClosed K] :
    ∀ s : (X.presheaf.obj (Opposite.op ⊤)), ∃! c : K, constantMap K X f c = s := by
  intro s
  obtain ⟨c, hc⟩ := (proper_constant_map_bijective K X f).surjective s
  exact ⟨c, hc, fun d hd ↦ (proper_constant_map_bijective K X f).injective (hd.trans hc.symm)⟩

end ArithmeticThetaProperFunctions
