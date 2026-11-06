module
public import Mathlib

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
  sorry

end ArithmeticThetaPalomarEtaleNorm259
