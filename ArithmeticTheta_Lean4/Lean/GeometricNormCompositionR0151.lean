import FiniteEtaleLocalNormR0150
import Mathlib.RingTheory.Norm.Transitivity

/-! Composition of geometric field maps and their determinant norms. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaKatoExistenceR0151
open CategoryTheory AlgebraicGeometry ArithmeticThetaGeometricNormR0150

/-- The generic-point maps of finite étale surjections compose, and so do
 their determinant norms, with all scalar structures induced by those maps. -/
theorem geometric_norm_composition
    (X Y Z : Scheme.{u}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Etale f] [Surjective f]
    [IsFinite g] [Etale g] [Surjective g]
    (φ : Y.functionField →+* X.functionField)
    (ψ : Z.functionField →+* Y.functionField)
    (hφ : IsFieldMap f φ) (hψ : IsFieldMap g ψ) :
    IsFieldMap (f ≫ g) (φ.comp ψ) ∧ FiniteFieldMap (φ.comp ψ) ∧
      (∀ z : X.functionField,
        fieldNorm ψ (fieldNorm φ z) = fieldNorm (φ.comp ψ) z) := by
  have hcomp : IsFieldMap (f ≫ g) (φ.comp ψ) := by
    unfold IsFieldMap at *
    calc
      X.fromSpecStalk (genericPoint X) ≫ (f ≫ g) =
          (X.fromSpecStalk (genericPoint X) ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom φ) ≫
          Y.fromSpecStalk (genericPoint Y)) ≫ g := by rw [hφ]
      _ = Spec.map (CommRingCat.ofHom φ) ≫
          (Spec.map (CommRingCat.ofHom ψ) ≫ Z.fromSpecStalk (genericPoint Z)) := by
            rw [Category.assoc, hψ]
      _ = Spec.map (CommRingCat.ofHom (φ.comp ψ)) ≫
          Z.fromSpecStalk (genericPoint Z) := by
            rw [← Category.assoc, ← Spec.map_comp]
            rfl
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  letI : IsScalarTower Z.functionField Y.functionField X.functionField :=
    .of_algebraMap_eq' rfl
  letI : FiniteDimensional Y.functionField X.functionField :=
    (finite_etale_local_norm X Y f φ hφ).1
  letI : FiniteDimensional Z.functionField Y.functionField :=
    (finite_etale_local_norm Y Z g ψ hψ).1
  letI : FiniteDimensional Z.functionField X.functionField :=
    Module.Finite.trans Y.functionField X.functionField
  refine ⟨hcomp, (show FiniteDimensional Z.functionField X.functionField from inferInstance), ?_⟩
  intro z
  exact Algebra.norm_norm (R := Z.functionField) (S := Y.functionField) (a := z)

end ArithmeticThetaKatoExistenceR0151
