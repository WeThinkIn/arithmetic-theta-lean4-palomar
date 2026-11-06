import CompactFullLevelAlphaR0190
import SquareIsomorphismTorsor
import SimultaneousSquareLineComparison
import FiniteEtaleSelectedComponent
import FiniteEtaleFormalDiskLift

/-! Actual half divisors and square-compatible isomorphisms of invertible sheaves.
These definitions assert no existence of the new covers or half lines. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaSquareLinesR0192
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaGlobalFourTorsionR0190

/-- A genuine invertible sheaf with its specified square isomorphism. -/
structure SquareLine (Z : Scheme) (W : Z.Modules) where
  line : Z.Modules
  invertible : Scheme.Modules.IsInvertible line
  square : tensorPower Z line 2 ≅ W

/-- Pullback retains the supplied square map and the canonical tensor comparison. -/
def squarePull {Z Y : Scheme} {W : Z.Modules} (f : Y ⟶ Z) (A : SquareLine Z W) :
    tensorPower Y ((Scheme.Modules.pullback f).obj A.line) 2 ≅
      (Scheme.Modules.pullback f).obj W :=
  (pullback_tensorPower_iso Y Z f A.line 2).symm ≪≫
    (Scheme.Modules.pullback f).mapIso A.square

/-- Equality of the two actual square maps on pure tensors on every open. -/
def IsSquareIsometry {Z Y : Scheme} {W : Z.Modules} (f : Y ⟶ Z)
    (A B : SquareLine Z W)
    (e : (Scheme.Modules.pullback f).obj A.line ≅ (Scheme.Modules.pullback f).obj B.line) : Prop :=
  ∀ (U : Y.Opens) (v : Γ((Scheme.Modules.pullback f).obj A.line, U)),
    (squarePull f A).hom.app U
      (tensorPowerSection Y ((Scheme.Modules.pullback f).obj A.line) 2 U v) =
    (squarePull f B).hom.app U
      (tensorPowerSection Y ((Scheme.Modules.pullback f).obj B.line) 2 U (e.hom.app U v))

/-- The actual isomorphism transported through a specified commuting triangle. -/
def transportIsometry {Z Y S : Scheme} {W : Z.Modules} (p : Y ⟶ Z)
    (A B : SquareLine Z W)
    (e : (Scheme.Modules.pullback p).obj A.line ≅ (Scheme.Modules.pullback p).obj B.line)
    (f : S ⟶ Z) (g : S ⟶ Y) (hg : g ≫ p = f) :
    (Scheme.Modules.pullback f).obj A.line ≅ (Scheme.Modules.pullback f).obj B.line :=
  (along g p f hg A.line).symm ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
    along g p f hg B.line

/-- Common normalized disk frames; all square equations use the same W and eta. -/
def DiskFrames (k : Type) [Field k] {Z : Scheme} {W : Z.Modules}
    (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (s : ℕ)
    (A : Fin (s+1) → SquareLine Z W)
    (η : Γ((Scheme.Modules.pullback f).obj W, ⊤))
    (h : ∀ i, Γ((Scheme.Modules.pullback f).obj (A i).line, ⊤)) : Prop :=
  ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((Scheme.Modules.pullback f).obj W) ⊤ η ∧
  ∀ i, ArithmeticThetaRelativeDiscriminantR0171.IsFrame
      ((Scheme.Modules.pullback f).obj (A i).line) ⊤ (h i) ∧
    (squarePull f (A i)).hom.app ⊤
      (tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k)
        ((Scheme.Modules.pullback f).obj (A i).line) 2 ⊤ (h i)) = η

/-- One integral component of the product of square-isometry torsors,
with the prescribed unramified disk branch and simultaneous identifications. -/
def CommonComparison (k : Type) [Field k] [CharZero k]
    (Z : Scheme) (b : Z ⟶ Spec (CommRingCat.of k)) (W : Z.Modules) (s : ℕ)
    (A : Fin (s+1) → SquareLine Z W)
    (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z)
    (h : ∀ i, Γ((Scheme.Modules.pullback f).obj (A i).line, ⊤)) : Prop :=
  ∃ C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k Z b (2^s),
    Etale C.map ∧
    ∃ (g : ArithmeticThetaTateCuspsR0181.Disk k ⟶ C.space) (hg : g ≫ C.map = f),
      IsDominant (ArithmeticThetaTateCuspsR0181.genericInclusion k ≫ g) ∧
      ∃ e : ∀ i, (Scheme.Modules.pullback C.map).obj (A i).line ≅
          (Scheme.Modules.pullback C.map).obj (A 0).line,
        e 0 = Iso.refl _ ∧
        ∀ i, IsSquareIsometry C.map (A i) (A 0) (e i) ∧
          (transportIsometry C.map (A i) (A 0) (e i) f g hg).hom.app ⊤ (h i) = h 0

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)

def IsCompactAlpha (a : Γ(H.line, ⊤)) : Prop :=
  IsOpenAlpha L k D (restrictAlpha L k D X H a) ∧
    CuspOrders L k D X H a ∧ ExactTateAlpha L k D X H a

def componentAlpha (x : X.space) (a : Γ(H.line, ⊤)) :
    Γ(hodge k L D X x H, ⊤) :=
  pullbackGlobalSection (inclusion k L D X x) H.line a

/-- Half the divisor of this particular alpha, including zero off the cusp locus. -/
def HalfAlphaDivisor (x : X.space) (a : Γ(H.line, ⊤))
    (E : Component k L D X x →₀ ℤ) : Prop :=
  (∀ y, 0 ≤ E y) ∧
  (∀ y, E y = 0 ∨ E y = ((L/8 : ℕ) : ℤ)) ∧
  (∀ y, y ∉ cuspSet k L D X x → E y = 0) ∧
  componentAlpha k L D X H x a ≠ 0 ∧
  (∃ ι : Type, Nonempty (NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι)) ∧
  ∀ (ι : Type) (C : NormalFrameCover (Component k L D X x) (hodge k L D X x H) ι),
    MatchesSectionOrder (Component k L D X x) (hodge k L D X x H) C
      (componentAlpha k L D X H x a) (2 • E)

/-- The genuine bounded-pole sheaf O(E) and its canonical section 1_E. -/
def canonicalDivisorData (x : X.space) (E : Component k L D X x →₀ ℤ)
    (hE : ∀ y, 0 ≤ E y) (hN : NormalAffine (Component k L D X x)) :
    DivisorLine (Component k L D X x) :=
  ⟨ArithmeticThetaGeometricPrerequisites.divisorSheaf _ hN E,
   ArithmeticThetaGeometricPrerequisites.divisorCanonicalSection _ hN E hE⟩

/-- The prescribed theta frame is on the original disk, without another cover. -/
def AlphaHalfBranch (x : X.space) (A : DivisorLine (Component k L D X x))
    (β : tensorPower (Component k L D X x) A.line 2 ≅ hodge k L D X x H) : Prop :=
  ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ V.level →
    ∀ (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Component k L D X x)
      (hf : f ≫ inclusion k L D X x = V.disk)
      (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤)),
    ExtendsGenerator k L H V η →
    ∃ h : Γ((Scheme.Modules.pullback f).obj A.line, ⊤),
      ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((Scheme.Modules.pullback f).obj A.line) ⊤ h ∧
      pullbackGlobalSection f A.line A.section_ =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k L) • h ∧
      (diskHodgeIso k L D X x H V f hf).hom.app ⊤
        (((pullback_tensorPower_iso _ _ f A.line 2).symm ≪≫
          (Scheme.Modules.pullback f).mapIso β).hom.app ⊤
          (tensorPowerSection _ ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ h)) = η

end ArithmeticThetaSquareLinesR0192
