module
public import Mathlib
public import FiniteEtaleNormFamilyR0251

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaPalomarEtaleNorm259
open CategoryTheory AlgebraicGeometry

abbrev Sections (X : Scheme.{u}) (U : X.Opens) :=
  X.presheaf.obj (Opposite.op U)

def restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (a : Sections X U) : Sections X V :=
  X.presheaf.map (homOfLE h).op a

/-- Determinant with scalar algebra given by the actual morphism on sections. -/
def affineNorm {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) : Sections Y U :=
  letI := (f.app U).hom.toAlgebra
  Algebra.norm (Sections Y U) a

def AffineFree {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : Prop :=
  letI := (f.app U).hom.toAlgebra
  Module.Free (Sections Y U) (Sections X (f ⁻¹ᵁ U))

/-- The norm section agrees with the actual determinant on every free affine test. -/
def IsNormSection {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) : Prop :=
  ∀ (V : Y.affineOpens) (e : V.1 ≤ U), AffineFree f V.1 →
    affineNorm f V.1
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) = restrict U V.1 e b

abbrev NormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) →* Sections Y U

/-- All sections, including zero, with determinant normalization and restriction. -/
def IsNormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : Prop :=
  (∀ (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)), IsNormSection f U a (N U a)) ∧
  ∀ (U V : Y.Opens) (e : V ≤ U) (a : Sections X (f ⁻¹ᵁ U)),
    N V (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a) =
      restrict U V e (N U a)

/-- Exact accepted-098 scope: existence and uniqueness on arbitrary schemes. -/
theorem finite_etale_norm_family
    (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] [Etale f] :
    ∃! N : NormFamily f, IsNormFamily f N := by
  exact ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family X Y f

end ArithmeticThetaPalomarEtaleNorm259

open CategoryTheory AlgebraicGeometry

namespace ArithmeticThetaPalomarEtaleNorm259
 theorem sections_bridge (X : Scheme.{u}) (U : X.Opens) :
    Sections X U = ArithmeticThetaSchemeKatoNormR0251.Sections X U := rfl
 theorem restrict_bridge {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U) (a : Sections X U) :
    restrict U V h a = ArithmeticThetaSchemeKatoNormR0251.restrict U V h a := rfl
 theorem affineNorm_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) :
    affineNorm f U a = ArithmeticThetaGeometricNormR0150.affineNorm f U a := rfl
 theorem affineFree_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    AffineFree f U = ArithmeticThetaGeometricNormR0150.AffineFree f U := rfl
 theorem isNormSection_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) :
    IsNormSection f U a b = ArithmeticThetaSchemeKatoNormR0251.IsNormSection f U a b := rfl
 theorem normFamily_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NormFamily f = ArithmeticThetaSchemeKatoNormR0251.NormFamily f := rfl
 theorem isNormFamily_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) :
    IsNormFamily f N = ArithmeticThetaSchemeKatoNormR0251.IsNormFamily f N := rfl
end ArithmeticThetaPalomarEtaleNorm259

#print axioms ArithmeticThetaPalomarEtaleNorm259.finite_etale_norm_family
#print axioms ArithmeticThetaPalomarEtaleNorm259.sections_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.restrict_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.affineNorm_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.affineFree_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.isNormSection_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.normFamily_bridge
#print axioms ArithmeticThetaPalomarEtaleNorm259.isNormFamily_bridge
