module

public import PhaseFreeKeyNaturalityR0219
public import MultiplierFourthTrivializationR0219
public import FourTorsionTateBehaviorR0190
public import TateFullLevelMarkingR0181

@[expose] public section

/-! Actual Tate tests of the phase-free key formula. These definitions specify
maps and complete sections; they assume no expansion or key normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaKeyTateR0220
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaPullback ArithmeticThetaSheafTensor

/-- The actual level-four reduction fixes both quarter-level sections. -/
def ReducesFour (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : ArithmeticThetaRelativeKatoR0169.Law R W) (N : ℕ)
    (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G N (𝟙 (Base R)))
    (M4 : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (Base R))) : Prop :=
  M4.x = G.nsmul (𝟙 (Base R)) (N/4) M.x ∧
  M4.y = G.nsmul (𝟙 (Base R)) (N/4) M.y

/-- A Cartesian Tate presentation of an actual marked scheme family. The
level-four marking is explicitly the reduction of the supplied full N-marking. -/
structure TateTest (k : Type) [Field k] [CharZero k] (N : ℕ)
    (T : ArithmeticThetaTateCuspsR0181.TateLevel k N)
    {S : Scheme} (E : Family S) (M : FullLevel E 4) where
  marking : ArithmeticThetaFullLevelCoverR0175.FullLevel (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k N) T.law 4
    (𝟙 (Base (LaurentSeries k)))
  reduces : ReducesFour (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k N) T.law N T.marking marking
  base : Base (LaurentSeries k) ⟶ S
  comparison : ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k N) ⟶ E.curve
  cartesian : IsPullback comparison
    (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k N)) E.p base
  zero_eq : ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k N) ≫ comparison = base ≫ E.zero
  mul_eq : ∀ (U : Scheme) (t : U ⟶ Base (LaurentSeries k))
    (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap
      (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k N)))
    (x' y' : SchemeHomOver (t ≫ base) E.p),
    x'.val = x.val ≫ comparison → y'.val = y.val ≫ comparison →
    (E.law.mul _ x' y').val = (T.law.mul t x y).val ≫ comparison
  x_eq : marking.x.val ≫ comparison = base ≫ M.x.val
  y_eq : marking.y.val ≫ comparison = base ≫ M.y.val

variable (k : Type) [Field k] [CharZero k] (N : ℕ)
  (T : ArithmeticThetaTateCuspsR0181.TateLevel k N)

/-- Retain every map of the Tate test in the accepted all-affine-test interface. -/
def TateTest.affine {S : Scheme} {E : Family S} {M : FullLevel E 4}
    (A : TateTest k N T E M) : AffineTest E M where
  ring := LaurentSeries k
  equation := ArithmeticThetaTateCuspsR0181.TateCurve k N
  elliptic := T.elliptic
  law := T.law
  originLaw := T.originLaw
  base := A.base
  comparison := A.comparison
  cartesian := A.cartesian
  zero_eq := A.zero_eq
  mul_eq := A.mul_eq
  level := A.marking
  x_eq := A.x_eq
  y_eq := A.y_eq

/-- The conormal-to-Hodge derivative is fixed by the actual affine test. -/
def alphaAt {S : Scheme} (E : Family S) (M : FullLevel E 4)
    (A : TateTest k N T E M) (a : Γ(Cotangent E, ⊤)) :
    Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k N), ⊤) :=
  (SchemeAlphaSection.hodgeIso E M (A.affine k N T)).hom.app ⊤
    (pullbackGlobalSection A.base (Cotangent E) a)

variable {S : Scheme} (E : Family S) (P : EvenPoint E) (L : S.Modules)
  (m : Frames E P L) (A : MarkedTest E P)
  (B : TateTest k N T A.family A.marking)

/-- After the marked Cartesian test and then its Tate test, keep the actual
multiplier pullback; no scalar-valued substitute for this sheaf is introduced. -/
abbrev tateMultiplier :=
  (Scheme.Modules.pullback B.base).obj ((Scheme.Modules.pullback A.map).obj L)

def tateMultiplierFrame : Γ(tateMultiplier k N T E P L A B, ⊤) :=
  pullbackGlobalSection B.base ((Scheme.Modules.pullback A.map).obj L) (m A)

abbrev tateProduct := sheafTensor (Base (LaurentSeries k))
  (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k N)) (tateMultiplier k N T E P L A B)

/-- Pull an entire product section through the specified cotangent comparison,
then through the canonical conormal derivative on the actual Tate curve. -/
def productAt
    (c : (Scheme.Modules.pullback A.map).obj (Cotangent E) ≅ Cotangent A.family)
    (s : Γ(productLine E L, ⊤)) : Γ(tateProduct k N T E P L A B, ⊤) :=
  let first := ((pullback_sheafTensor_iso A.base S A.map (Cotangent E) L) ≪≫
    sheafTensorCongr A.base c (Iso.refl _)).hom.app ⊤
      (pullbackGlobalSection A.map (productLine E L) s)
  ((pullback_sheafTensor_iso (Base (LaurentSeries k)) A.base B.base
    (Cotangent A.family) ((Scheme.Modules.pullback A.map).obj L)) ≪≫
    sheafTensorCongr (Base (LaurentSeries k))
      (SchemeAlphaSection.hodgeIso A.family A.marking (B.affine k N T))
      (Iso.refl _)).hom.app ⊤
        (pullbackGlobalSection B.base _ first)

/-- The target frame uses precisely dz/z and the prescribed level frame. -/
def productFrame (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k N) :
    Γ(tateProduct k N T E P L A B, ⊤) :=
  tensorSection (Base (LaurentSeries k))
    (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k N))
    (tateMultiplier k N T E P L A B) ⊤
    (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k N δ)
    (tateMultiplierFrame k N T E P L m A B)

/-- Complete Laurent equality, including the specified canonical sign. The
coefficient is integral of order zero or N/4 for every actual marking. -/
def Expansion (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k N)
    (s : Γ(tateProduct k N T E P L A B, ⊤)) : Prop :=
  (∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = N/4) ∧
    s = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
      (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
        productFrame k N T E P L m A B δ) ∧
  (∀ ζ : k, IsPrimitiveRoot ζ N → ArithmeticThetaTateCuspsR0181.CanonicalMarking k N ζ T →
    s = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k N ^ 2)) •
          productFrame k N T E P L m A B δ)

end ArithmeticThetaKeyTateR0220
