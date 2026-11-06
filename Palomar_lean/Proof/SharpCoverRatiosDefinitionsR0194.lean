module

public import IsogenyCanonicalHalfLineR0193
public import CompactIsogenyAlphaR0193
public import CuspHalfLineCoverDegreeR0188
public import AlignedMarkingProjectiveValuesR0142
public import Mathlib.AlgebraicGeometry.FunctionField
public import IsogenyHalfLinesDefinitionsR0193

@[expose] public section

/-! Actual square-cover consumers and rational unary expansions. Only definitions;
all new existence assertions belong to future proof-worker obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaSharpCoverR0194
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaIsogenyHalfLinesR0193

/-- A canonical isogeny half-line, retained as construction OUTPUT, not an
assumption of the common-cover existence obligation. -/
structure CanonicalHalf (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (x : X.space) where
  openData : OpenAlpha k L m D
  alpha : Γ(H.line, ⊤)
  realizes : CompactRealizes k L m D X H openData alpha
  divisor : Component k L D X x →₀ ℤ
  effective : ∀ y, 0 ≤ divisor y
  normal : NormalAffine (Component k L D X x)
  half : HalfDivisor k L D X H x alpha divisor
  invertible : Scheme.Modules.IsInvertible
    (canonicalDivisorData k L D X x divisor effective normal).line
  square : tensorPower (Component k L D X x)
    (canonicalDivisorData k L D X x divisor effective normal).line 2 ≅ hodge k L D X x H
  square_section : square.hom.app ⊤ (tensorPowerSection _
    (canonicalDivisorData k L D X x divisor effective normal).line 2 ⊤
    (canonicalDivisorData k L D X x divisor effective normal).section_) =
      componentAlpha k L D X H x alpha
  branch : HalfBranch k L m D X H x
    (canonicalDivisorData k L D X x divisor effective normal) square

variable {k : Type} [Field k] [CharZero k] {L m : ℕ} {D : LevelData k L}
    {X : Compactification k L D} {H : Extension k L D X} {x : X.space}

def CanonicalHalf.data (A : CanonicalHalf k L m D X H x) : DivisorLine (Component k L D X x) :=
  canonicalDivisorData k L D X x A.divisor A.effective A.normal

def CanonicalHalf.squareLine (A : CanonicalHalf k L m D X H x) :
    SquareLine (Component k L D X x) (hodge k L D X x H) :=
  ⟨A.data.line, A.invertible, A.square⟩

/-- The actual common basic unary sections on the compact square-comparison
cover, including its original unramified disk and the exact Hodge square. -/
def CommonBasic (k : Type) [Field k] [CharZero k] (L s : ℕ) (m : Fin (s+1) → ℕ)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (V : DiskTest k L D X) : Prop :=
  let x := V.disk (closedPoint k)
  ∃ A : ∀ i, CanonicalHalf k L (m i) D X H x,
    ∃ C : RootCover k (Component k L D X x) (projection k L D X x) (2^s),
      Etale C.map ∧ (s = 0 → IsIso C.map) ∧
      ∃ (g : Disk k ⟶ C.space)
        (hg : g ≫ (C.map ≫ inclusion k L D X x) = V.disk),
        IsDominant (genericInclusion k ≫ g) ∧
        ∃ (e : ∀ i, (Scheme.Modules.pullback C.map).obj (A i).data.line ≅
            (Scheme.Modules.pullback C.map).obj (A 0).data.line),
          e 0 = Iso.refl _ ∧
          (∀ i, IsSquareIsometry C.map (A i).squareLine (A 0).squareLine (e i)) ∧
          ∃ (h : Γ((Scheme.Modules.pullback g).obj
              ((Scheme.Modules.pullback C.map).obj (A 0).data.line), ⊤))
            (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤))
            (t : Fin (s+1) → Γ((Scheme.Modules.pullback C.map).obj (A 0).data.line, ⊤)),
            ArithmeticThetaRelativeDiscriminantR0171.IsFrame _ ⊤ h ∧
            ExtendsGenerator k L H V η ∧
            (squareOnDisk k (C.map ≫ inclusion k L D X x)
              ((Scheme.Modules.pullback C.map).obj (A 0).data.line) H.line
              (squarePull C.map (A 0).squareLine ≪≫
                (Scheme.Modules.pullbackComp C.map (inclusion k L D X x)).app H.line)
              g V.disk hg).hom.app ⊤ (tensorPowerSection _ _ 2 ⊤ h) = η ∧
            ∀ i, t i = (e i).hom.app ⊤
                (pullbackGlobalSection C.map (A i).data.line (A i).data.section_) ∧
              t i ≠ 0 ∧
              pullbackGlobalSection g ((Scheme.Modules.pullback C.map).obj (A 0).data.line) (t i) =
                ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
                  (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L * m i)) • h

/-- Half-Hodge degree on any actual finite cover. Unlike CoverDegree R0188,
no uniform cusp divisor or nonzero section of the base half-line is assumed. -/
def SquareCoverDegree (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (x : X.space) (J : SquareLine (Component k L D X x) (hodge k L D X x H))
    (b n : ℕ) (C : RootCover k (Component k L D X x) (projection k L D X x) b) : Prop :=
  letI := C.integral
  ∃ hY : IsLocallyNoetherian C.space, letI := hY
    ArithmeticThetaCurveDegree.OneDimensionalCharts C.space ∧ NormalAffine C.space ∧
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback C.map).obj J.line) ∧
    (∃ ι : Type, Nonempty (NormalFrameCover C.space
      (tensorPower C.space ((Scheme.Modules.pullback C.map).obj J.line) n) ι)) ∧
    ∀ (ι : Type) (F : NormalFrameCover C.space
      (tensorPower C.space ((Scheme.Modules.pullback C.map).obj J.line) n) ι)
      (t : Γ(tensorPower C.space ((Scheme.Modules.pullback C.map).obj J.line) n, ⊤))
      (E : C.space →₀ ℤ), t ≠ 0 →
      MatchesSectionOrder C.space
        (tensorPower C.space ((Scheme.Modules.pullback C.map).obj J.line) n) F t E →
      24 * ArithmeticThetaCurveDegree.weightedDegree k (C.map ≫ projection k L D X x) E =
        (n : ℤ) * (C.map.finrank (genericPoint (Component k L D X x)) : ℤ) *
          (L : ℤ) * (Nat.card (Cusps k L D X x) : ℤ) ∧
      48 * ArithmeticThetaCurveDegree.weightedDegree k (C.map ≫ projection k L D X x) E ≤
        (n : ℤ) * (b : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ)

/-- Full q=t^L unary expansion for a residue; L is divisible by 2m. -/
def levelUnary (k : Type) [Field k] (L m : ℕ) (ν : Fin m) : PowerSeries k :=
  PowerSeries.subst (PowerSeries.X ^ (L/(2*m))) (ArithmeticThetaSchrodingerR0119.unary k m ν)

/-- A rational function is represented on a genuine nonempty open and pulled
back through the actual punctured disk. No arbitrary series-valued map is used. -/
def RationalExpansion (k : Type) [Field k] (Z : Scheme) [IsIntegral Z]
    (f : Puncture k ⟶ Z) (r : Z.functionField) (a : LaurentSeries k) : Prop :=
  ∃ (U : Z.Opens) (hU : Nonempty U), letI := hU
    ∃ v : Z.presheaf.obj (Opposite.op U),
      (Z.germToFunctionField U) v = r ∧
      f ⁻¹ᵁ U = ⊤ ∧
      f.app U v = (Puncture k).presheaf.map
        (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) a)

/-- Actual rational functions on the selected full-level component. This is
the algebraicity/complete-expansion consumer, not a packaged theta marking. -/
def ProjectiveRatios (k : Type) [Field k] [CharZero k] (L m : ℕ) (hm : 0 < m)
    (D : LevelData k L) (X : Compactification k L D) (V : DiskTest k L D X) : Prop :=
  let x := V.disk (closedPoint k)
  ∃ (f : Disk k ⟶ Component k L D X x),
    f ≫ inclusion k L D X x = V.disk ∧ IsDominant (genericInclusion k ≫ f) ∧
    ∃ r : Fin m → (Component k L D X x).functionField,
      r ⟨0, hm⟩ = 1 ∧ ∀ ν,
        RationalExpansion k (Component k L D X x) (genericInclusion k ≫ f) (r ν)
          (algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ν) /
            algebraMap (PowerSeries k) (LaurentSeries k) (levelUnary k L m ⟨0, hm⟩))

end ArithmeticThetaSharpCoverR0194
