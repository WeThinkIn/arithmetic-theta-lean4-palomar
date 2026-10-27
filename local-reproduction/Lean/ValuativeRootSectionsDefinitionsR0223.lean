import SimultaneousDiskRootSectionsR0187

/-! Valuative, full-section formulations of prescribed simultaneous roots.
These definitions introduce no construction or target proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaValuativeRootsR0223
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaOpenHodgeR0180

abbrev FieldPoint (Ω : Type) [Field Ω] := Spec (CommRingCat.of Ω)
abbrev ValuationPoint (Ω : Type) [Field Ω] (A : ValuationSubring Ω) :=
  Spec (CommRingCat.of A)

def genericInclusion (Ω : Type) [Field Ω] (A : ValuationSubring Ω) :
    FieldPoint Ω ⟶ ValuationPoint Ω A :=
  Spec.map (CommRingCat.ofHom (algebraMap A Ω))

/-- The generic frame is the actual pullback of the given integral frame. -/
def genericFrame (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} (f : ValuationPoint Ω A ⟶ Z) (J : Z.Modules)
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J)) :
    Sections (FieldPoint Ω)
      ((Scheme.Modules.pullback (genericInclusion Ω A ≫ f)).obj J) :=
  ((Scheme.Modules.pullbackComp (genericInclusion Ω A) f).app J).hom.app ⊤
    (pullbackGlobalSection (genericInclusion Ω A) ((Scheme.Modules.pullback f).obj J) h)

/-- Prescribed roots are field elements; no integral lift is assumed. -/
def FieldEquation (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} (f : ValuationPoint Ω A ⟶ Z) (J : Z.Modules) (K : ℕ)
    (F : Sections Z (tensorPower Z J K))
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (r : Ω) : Prop :=
  pullbackPowerSection (genericInclusion Ω A ≫ f) J K F =
    scalar Ω (r ^ K) • tensorPowerSection (FieldPoint Ω)
      ((Scheme.Modules.pullback (genericInclusion Ω A ≫ f)).obj J) K ⊤
      (genericFrame Ω A f J h)

def IntegralEquation (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} (f : ValuationPoint Ω A ⟶ Z) (J : Z.Modules) (K : ℕ)
    (F : Sections Z (tensorPower Z J K))
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (a : A) : Prop :=
  pullbackPowerSection f J K F =
    scalar A (a ^ K) • tensorPowerSection (ValuationPoint Ω A)
      ((Scheme.Modules.pullback f).obj J) K ⊤ h

/-- The same valuative map and frame realize every complete section, with a
single dominating branch through one integral cover. -/
def Realizes (k : Type) [Field k] {Z : Scheme.{0}}
    {b : Z ⟶ Spec (CommRingCat.of k)} {bound : ℕ}
    (R : RootCover k Z b bound) (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (J : Z.Modules) (K s : ℕ) (F : Fin s → Sections Z (tensorPower Z J K))
    (f : ValuationPoint Ω A ⟶ Z)
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (a : Fin s → A) : Prop :=
  ∃ (g : ValuationPoint Ω A ⟶ R.space) (hg : g ≫ R.map = f),
    IsDominant (genericInclusion Ω A ≫ g) ∧
    ∃ t : Fin s → Sections R.space ((Scheme.Modules.pullback R.map).obj J),
      ∀ j, t j ≠ 0 ∧
        tensorPowerSection R.space ((Scheme.Modules.pullback R.map).obj J) K ⊤ (t j) =
          pullbackPowerSection R.map J K (F j) ∧
        (ArithmeticThetaCommonHalfHodgeR0185.along g R.map f hg J).hom.app ⊤
          (pullbackGlobalSection g ((Scheme.Modules.pullback R.map).obj J) (t j)) =
            scalar A (a j) • h

/-- A source-facing field prescription, including integral lifts as outputs. -/
def PrescribedFieldRoots (k : Type) [Field k] {Z : Scheme.{0}}
    {b : Z ⟶ Spec (CommRingCat.of k)} {bound : ℕ}
    (R : RootCover k Z b bound) (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (J : Z.Modules) (K s : ℕ) (F : Fin s → Sections Z (tensorPower Z J K))
    (f : ValuationPoint Ω A ⟶ Z)
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (r : Fin s → Ω) : Prop :=
  ∃ a : Fin s → A, (∀ j, algebraMap A Ω (a j) = r j) ∧
    Realizes k R Ω A J K s F f h a

/-- Extend the original formal disk through the specified ring map. -/
def extendedDisk (k : Type) [Field k] (Ω : Type) [Field Ω]
    (A : ValuationSubring Ω) (ρ : PowerSeries k →+* A)
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) :
    ValuationPoint Ω A ⟶ Z :=
  Spec.map (CommRingCat.ofHom ρ) ≫ f

/-- The chosen frame stays the pullback of the original disk frame. -/
def extendedFrame (k : Type) [Field k] (Ω : Type) [Field Ω]
    (A : ValuationSubring Ω) (ρ : PowerSeries k →+* A)
    {Z : Scheme.{0}} (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (J : Z.Modules)
    (h : Sections (ArithmeticThetaTateCuspsR0181.Disk k)
      ((Scheme.Modules.pullback f).obj J)) :
    Sections (ValuationPoint Ω A)
      ((Scheme.Modules.pullback (extendedDisk k Ω A ρ f)).obj J) :=
  ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom ρ)) f).app J).hom.app ⊤
    (pullbackGlobalSection (Spec.map (CommRingCat.ofHom ρ))
      ((Scheme.Modules.pullback f).obj J) h)

end ArithmeticThetaValuativeRootsR0223
