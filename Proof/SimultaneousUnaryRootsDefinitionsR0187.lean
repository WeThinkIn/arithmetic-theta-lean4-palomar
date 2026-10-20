module

public import CommonHalfHodgeCoverR0185
public import SmoothRootSections
public import NormalizationPrescribedBranch
public import RootCoverGeometricDegree
public import RootCoverGeometricDegreePositive

@[expose] public section

/-! Definitions for the missing simultaneous completed-branch consumer.
The records below occur as existential construction outputs. Their geometric
predicates concern their actual maps. No target theorem is supplied here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaSimultaneousUnaryR0187
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections
open ArithmeticThetaPullback ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaCompactUnaryR0183

abbrev Sections (B : Scheme) (J : B.Modules) := J.presheaf.obj (Opposite.op ⊤)

/-- The actual integral unary series, before the accepted Laurent inclusion. -/
def unarySeries (k : Type) [Field k] (N m : ℕ) (ν : ℤ) : PowerSeries k :=
  PowerSeries.map (Int.castRingHom k)
    (PowerSeries.subst (PowerSeries.X ^ (N^2/m))
      (ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν))

/-- All degrees refer to this finite map; dimension and properness refer to
its composite with the displayed structure morphism. -/
structure RootCover (k : Type) [Field k] (B : Scheme)
    (b : B ⟶ Spec (CommRingCat.of k)) (bound : ℕ) where
  space : Scheme
  map : space ⟶ B
  integral : IsIntegral space
  finite : IsFinite map
  flat : Flat map
  surjective : Surjective map
  proper : IsProper (map ≫ b)
  smooth : SmoothOfRelativeDimension 1 (map ≫ b)
  degree : ∀ x : B, 0 < map.finrank x ∧ map.finrank x ≤ bound

/-- The root sections and their full disk values use the same pullback maps,
not arbitrary expansion functionals. The puncture dominates the chosen curve. -/
def RealizesRoots (k : Type) [Field k] [CharZero k]
    {B : Scheme} {b : B ⟶ Spec (CommRingCat.of k)} {bound : ℕ}
    (R : RootCover k B b bound) (J : B.Modules) (K s : ℕ)
    (F : Fin s → Sections B (tensorPower B J K))
    (f : Disk k ⟶ B) (h : Sections (Disk k) ((Scheme.Modules.pullback f).obj J))
    (a : Fin s → PowerSeries k) : Prop :=
  ∃ (g : Disk k ⟶ R.space) (hg : g ≫ R.map = f),
    IsDominant (genericInclusion k ≫ g) ∧
    ∃ t : Fin s → Sections R.space ((Scheme.Modules.pullback R.map).obj J),
      ∀ j, t j ≠ 0 ∧
        tensorPowerSection R.space ((Scheme.Modules.pullback R.map).obj J) K ⊤ (t j) =
          pullbackPowerSection R.map J K (F j) ∧
        (along g R.map f hg J).hom.app ⊤
          (pullbackGlobalSection g ((Scheme.Modules.pullback R.map).obj J) (t j)) =
            ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (a j) • h

/-- Pull back the specific square map and the same commuting triangle. -/
def squareOnDisk (k : Type) [Field k] {B X : Scheme}
    (p : B ⟶ X) (J : B.Modules) (H : X.Modules)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H)
    (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) :
    tensorPower (Disk k) ((Scheme.Modules.pullback f).obj J) 2 ≅
      (Scheme.Modules.pullback d).obj H :=
  (pullback_tensorPower_iso (Disk k) B f J 2).symm ≪≫
    (Scheme.Modules.pullback f).mapIso β ≪≫ along f p d hf H

/-- An iterated power comparison is required to preserve pure tensor sections
on every open; an arbitrary isomorphism of the underlying sheaves is insufficient. -/
def IsSquarePower {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (N : ℕ)
    (e : tensorPower B J (exponent N) ≅
      tensorPower B ((Scheme.Modules.pullback p).obj H) (weight N)) : Prop :=
  ∀ (U : B.Opens) (v : J.presheaf.obj (Opposite.op U)),
    e.hom.app U (tensorPowerSection B J (exponent N) U v) =
      tensorPowerSection B ((Scheme.Modules.pullback p).obj H) (weight N) U
        (β.hom.app U (tensorPowerSection B J 2 U v))

/-- Source-specific powered sections, identified with the SAME accepted
compact normalized Kato/Hodge sections via an actual tensor comparison. -/
def UnaryPowers (k : Type) [Field k] [CharZero k] (N s : ℕ)
    (m : Fin s → ℕ) (ν : Fin s → ℤ) {D : LevelData k (level N)}
    {X : Compactification k (level N) D} (H : Extension k (level N) D X)
    {B : Scheme} (p : B ⟶ X.space) (J : B.Modules)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H.line)
    (F : Fin s → Sections B (tensorPower B J (exponent N))) : Prop :=
  ∃ e : tensorPower B J (exponent N) ≅
      tensorPower B ((Scheme.Modules.pullback p).obj H.line) (weight N),
    IsSquarePower p J H.line β N e ∧ ∀ j,
      F j ≠ 0 ∧ ∃ (a b : Fin N),
        a.val = unaryResidue (m j) N (ν j) ∧ b.val = N/2 ∧
        ∃ (A : OpenPower k (m j) N D a b)
          (t : Sections X.space (tensorPower X.space H.line (weight N))),
          RealizesUnary k (m j) N H (ν j) A t ∧
          e.hom.app ⊤ (F j) = pullbackPowerSection p H.line (weight N) t

/-- The actual square map on the accepted half-Hodge cover, now compared
with the original compact curve by the canonical pullback composition. -/
def halfSquare (k : Type) [Field k] [CharZero k] (L : ℕ)
    {D : LevelData k L} {X : Compactification k L D} {x : X.space}
    {A : DivisorLine (Component k L D X x)} {H : Extension k L D X}
    {s : Sections X.space (tensorPower X.space H.line 24)}
    (C : HalfCover k L D X x A H s) :
    tensorPower C.space ((Scheme.Modules.pullback C.map).obj A.line) 2 ≅
      (Scheme.Modules.pullback (C.map ≫ inclusion k L D X x)).obj H.line :=
  C.square ≪≫ (Scheme.Modules.pullbackComp C.map (inclusion k L D X x)).app H.line

/-- Complete simultaneous source construction for any finite unary family.
The half-cover, roots, branch, common frame and positive bounded degrees are
all outputs; the hypotheses will be only the accepted modular input data. -/
def SimultaneousUnary (k : Type) [Field k] [CharZero k] (N s : ℕ)
    (m : Fin s → ℕ) (ν : Fin s → ℤ) {D : LevelData k (level N)}
    {X : Compactification k (level N) D} (H : Extension k (level N) D X)
    (d2 : Sections X.space (tensorPower X.space H.line 24))
    (V : DiskTest k (level N) D X) : Prop :=
  let x := V.disk (closedPoint k)
  ∃ (f : Disk k ⟶ Component k (level N) D X x)
    (hf : f ≫ inclusion k (level N) D X x = V.disk)
    (A : DivisorLine (Component k (level N) D X x)),
    IsCuspHalfLine k (level N) D X x A ∧
    ∃ C : HalfCover k (level N) D X x A H d2,
      HasBranch k (level N) D X x C V f hf ∧
      ∃ (g : Disk k ⟶ C.space) (hg : g ≫ C.map = f)
        (hgp : g ≫ (C.map ≫ inclusion k (level N) D X x) = V.disk)
        (η : Sections (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line)),
        ExtendsGenerator k (level N) H V η ∧
        ∃ h : Sections (Disk k) ((Scheme.Modules.pullback g).obj
            ((Scheme.Modules.pullback C.map).obj A.line)),
          ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ h ∧
          pullbackGlobalSection f A.line A.section_ =
            ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
              (euler k (level N) * PowerSeries.X ^ (level N / 24)) •
                ((along g C.map f hg A.line).hom.app ⊤ h) ∧
          (squareOnDisk k (C.map ≫ inclusion k (level N) D X x)
            ((Scheme.Modules.pullback C.map).obj A.line) H.line (halfSquare k (level N) C)
            g V.disk hgp).hom.app ⊤
              (tensorPowerSection (Disk k)
                ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback C.map).obj A.line))
                2 ⊤ h) = η ∧
          ∃ F : Fin s → Sections C.space
              (tensorPower C.space ((Scheme.Modules.pullback C.map).obj A.line) (exponent N)),
            UnaryPowers k N s m ν H (C.map ≫ inclusion k (level N) D X x)
              ((Scheme.Modules.pullback C.map).obj A.line) (halfSquare k (level N) C) F ∧
            ∃ R : RootCover k C.space (C.map ≫ projection k (level N) D X x) ((exponent N)^s),
              RealizesRoots k R ((Scheme.Modules.pullback C.map).obj A.line)
                (exponent N) s F g h (fun j => unarySeries k N (m j) (ν j)) ∧
              ∀ z : Component k (level N) D X x,
                0 < (R.map ≫ C.map).finrank z ∧
                (R.map ≫ C.map).finrank z ≤ 24 * (exponent N)^s

end ArithmeticThetaSimultaneousUnaryR0187
