import ComponentHodgePowerDegreeR0184
import EffectiveDivisorLine
import EqualDivisorLineIso
import SignedDivisorTensor
import GlobalRootTorsor
import FiniteEtaleSelectedComponent
import FiniteEtaleFormalDiskLift

/-! Actual divisor lines, twisted discriminant, and the common half-Hodge
cover. All existence assertions are future obligations, not fields supplied
as source hypotheses. Tensor products and pullbacks are the accepted maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaCommonHalfHodgeR0185
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaSectionOrder ArithmeticThetaCurveDegree
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184

structure DivisorLine (Z : Scheme) where
  line : Z.Modules
  section_ : Γ(line, ⊤)

def Represents (Z : Scheme) [IsIntegral Z] [IsLocallyNoetherian Z]
    (A : DivisorLine Z) (E : Z →₀ ℤ) : Prop :=
  Scheme.Modules.IsInvertible A.line ∧ A.section_ ≠ 0 ∧
  (∃ ι : Type, Nonempty (NormalFrameCover Z A.line ι)) ∧
  ∀ (ι : Type) (C : NormalFrameCover Z A.line ι),
    MatchesSectionOrder Z A.line C A.section_ E

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- O((L/24) C) with its canonical effective-divisor section, identified by
its actual orders at every point, including the generic point. -/
def IsCuspHalfLine (A : DivisorLine (Component k L D X x)) : Prop :=
  ∃ E : Component k L D X x →₀ ℤ,
    Represents (Component k L D X x) A E ∧
    ∀ y, (y ∈ cuspSet k L D X x → E y = (L / 24 : ℕ)) ∧
      (y ∉ cuspSet k L D X x → E y = 0)

/-- Literal Euler product at q=t^L, using the accepted complete product. -/
def euler : PowerSeries k :=
  PowerSeries.subst (PowerSeries.X ^ L)
    (PowerSeries.map (algebraMap ℚ k) ArithmeticThetaDiscriminant.P)

def diskHodgeIso (H : Extension k L D X) (V : DiskTest k L D X)
    (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk) :
    (Scheme.Modules.pullback f).obj (hodge k L D X x H) ≅
      (Scheme.Modules.pullback V.disk).obj H.line :=
  (Scheme.Modules.pullbackComp f (inclusion k L D X x)).app H.line ≪≫
    (Scheme.Modules.pullbackCongr hf).app H.line

structure Twist (A : DivisorLine (Component k L D X x)) (H : Extension k L D X) where
  line : (Component k L D X x).Modules
  multiply : sheafTensor (Component k L D X x) line
      (tensorPower (Component k L D X x) A.line 2) ≅ hodge k L D X x H
  section_ : Γ(tensorPower (Component k L D X x) line 24, ⊤)

/-- The normalized D2 is a unit section of M^24 for M=omega(-D).
The equality is tested in actual local frames and the given multiplication
isomorphism; it is not an assumed expansion or degree formula. -/
def IsTwist {A : DivisorLine (Component k L D X x)} {H : Extension k L D X}
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (W : Twist k L D X x A H) : Prop :=
  Scheme.Modules.IsInvertible W.line ∧
  ArithmeticThetaRootTorsor.IsGeneratingSection (Component k L D X x)
    (tensorPower (Component k L D X x) W.line 24) W.section_ ∧
  ∀ (U : (Component k L D X x).Opens) (μ : LocalFrame (Component k L D X x) W.line U),
    (power k L D X x H 24).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (restrict k L D X x H 24 s) =
    sectionCoordinate (Component k L D X x) (tensorPower (Component k L D X x) W.line 24)
      U (tensorPowerFrame (Component k L D X x) W.line U μ 24) W.section_ •
      tensorPowerSection (Component k L D X x) (hodge k L D X x H) 24 U
        (W.multiply.hom.app U (tensorSection (Component k L D X x) W.line
          (tensorPower (Component k L D X x) A.line 2) U (μ.equiv U le_rfl 1)
          (tensorPowerSection (Component k L D X x) A.line 2 U
            (A.line.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op A.section_))))

/-- Pullback of the same multiplication, with both tensor comparisons. -/
def pullMultiply {A : DivisorLine (Component k L D X x)} {H : Extension k L D X}
    (W : Twist k L D X x A H) {Z : Scheme} (f : Z ⟶ Component k L D X x) :
    sheafTensor Z ((Scheme.Modules.pullback f).obj W.line)
      (tensorPower Z ((Scheme.Modules.pullback f).obj A.line) 2) ≅
        (Scheme.Modules.pullback f).obj (hodge k L D X x H) :=
  sheafTensorCongr Z (Iso.refl _) (pullback_tensorPower_iso Z _ f A.line 2).symm ≪≫
    (pullback_sheafTensor_iso Z _ f W.line (tensorPower _ A.line 2)).symm ≪≫
    (Scheme.Modules.pullback f).mapIso W.multiply

/-- The explicit root E(t)^2 e_M, expressed without dividing by a vanishing
section: its product with the square of 1_H is E(t)^2 t^(L/12) delta. -/
def IsTateRoot {A : DivisorLine (Component k L D X x)} {H : Extension k L D X}
    (W : Twist k L D X x A H) (V : DiskTest k L D X)
    (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk)
    (v : Γ((Scheme.Modules.pullback f).obj W.line, ⊤)) : Prop :=
  ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((Scheme.Modules.pullback f).obj W.line) ⊤ v ∧
  tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj W.line) 24 ⊤ v =
    pullbackPowerSection f W.line 24 W.section_ ∧
  ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤), ExtendsGenerator k L H V η →
    (diskHodgeIso k L D X x H V f hf).hom.app ⊤
      ((pullMultiply k L D X x W f).hom.app ⊤
        (tensorSection (Disk k) ((Scheme.Modules.pullback f).obj W.line)
          (tensorPower (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2) ⊤ v
          (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤
            (pullbackGlobalSection f A.line A.section_)))) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) • η

/-- Canonical comparison over a specified commuting triangle. -/
def along {Z Y B : Scheme} (g : Z ⟶ Y) (p : Y ⟶ B) (f : Z ⟶ B)
    (h : g ≫ p = f) (M : B.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback f).obj M :=
  (Scheme.Modules.pullbackComp g p).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

def pullSquare {Z Y B : Scheme} (g : Z ⟶ Y) (p : Y ⟶ B) (f : Z ⟶ B)
    (h : g ≫ p = f) (A J : B.Modules)
    (β : tensorPower Y ((Scheme.Modules.pullback p).obj A) 2 ≅
      (Scheme.Modules.pullback p).obj J) :
    tensorPower Z ((Scheme.Modules.pullback f).obj A) 2 ≅ (Scheme.Modules.pullback f).obj J :=
  (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison
    g ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback f).obj A)
    (along g p f h A) 2).symm ≪≫
    (Scheme.Modules.pullback g).mapIso β ≪≫ along g p f h J

/-- A finite etale common square-root Hodge line on one genuine component.
All geometric predicates are on the displayed maps and are construction outputs. -/
structure HalfCover (A : DivisorLine (Component k L D X x)) (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) where
  space : Scheme
  map : space ⟶ Component k L D X x
  integral : IsIntegral space
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  proper : IsProper (map ≫ projection k L D X x)
  smooth : SmoothOfRelativeDimension 1 (map ≫ projection k L D X x)
  rank : ∀ y, 0 < map.finrank y ∧ map.finrank y ≤ 24
  square : tensorPower space ((Scheme.Modules.pullback map).obj A.line) 2 ≅
    (Scheme.Modules.pullback map).obj (hodge k L D X x H)
  discriminant : tensorPowerSection space ((Scheme.Modules.pullback map).obj (hodge k L D X x H))
      24 ⊤ (square.hom.app ⊤ (tensorPowerSection space ((Scheme.Modules.pullback map).obj A.line)
        2 ⊤ (pullbackGlobalSection map A.line A.section_))) =
    pullbackPowerSection map (hodge k L D X x H) 24 (restrict k L D X x H 24 s)

/-- Specified complete Tate branch and regular square frame h_T.
The coefficient E(t)t^(L/24) determines h_T from the same canonical section. -/
def HasBranch {A : DivisorLine (Component k L D X x)} {H : Extension k L D X}
    {s : Γ(tensorPower X.space H.line 24, ⊤)}
    (C : HalfCover k L D X x A H s) (V : DiskTest k L D X)
    (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk) : Prop :=
  ∃ (g : Disk k ⟶ C.space) (hg : g ≫ C.map = f),
    ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤), ExtendsGenerator k L H V η →
      ∃ h : Γ((Scheme.Modules.pullback f).obj A.line, ⊤),
        ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ h ∧
        pullbackGlobalSection f A.line A.section_ =
          ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
            (euler k L * PowerSeries.X ^ (L / 24)) • h ∧
        (diskHodgeIso k L D X x H V f hf).hom.app ⊤
          ((pullSquare g C.map f hg A.line (hodge k L D X x H) C.square).hom.app ⊤
            (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ h)) = η

/-- End-to-end source consumer. The cusp component and its disk factor are
constructed, and the full common frame is part of the output. -/
def CommonHalfHodge (H : Extension k L D X)
    (s : Γ(tensorPower X.space H.line 24, ⊤)) (V : DiskTest k L D X) : Prop :=
  let x := V.disk (closedPoint k)
  ∃ (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk)
    (A : DivisorLine (Component k L D X x)),
    IsCuspHalfLine k L D X x A ∧
    ∃ C : HalfCover k L D X x A H s, HasBranch k L D X x C V f hf

end ArithmeticThetaCommonHalfHodgeR0185
