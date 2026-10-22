module

public import AlgebraizedPositiveFormalSectionsR0136
public import AlgebraizedEffectiveCartierR0136
public import AlgebraizedMarkedIdealSpecializationR0136
public import UniformThetaChartRealizationR0128
public import CompletedChartThetaIndependenceR0128
public import CorrectedGammaDataExistsR0061
public import CorrectedGammaDataUniqueR0061
public import CorrectedGammaInteriorOverlapR0061
public import CorrectedGammaPeriodBoundaryR0061
public import CorrectedGammaTailExistsR0061
public import AnnularThetaGluingDefinitionsR0128
public import AlgebraizedMarkedLineDefinitionsR0136
public import FiniteStageCompletionComparisonR0129

@[expose] public section

/-! The single marked divisor and literal theta numerators on the same model.
The module is the dual of the actual power of the identity section's kernel.
All coefficient and completion maps below are fixed by the accepted geometry. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
variable (k : Type u) [Field k] [CharZero k]

def zeroIndex (r : ℕ) (hr : 0 < r) : Fin r := ⟨0, hr⟩

def equation (r n : ℕ) (i : Fin r) : A k n :=
  (if i.val = 0 then 1 - ArithmeticThetaInfinitesimalPolygonR0129.coordX k n else 1) *
  (if i.val + 1 = r then 1 - ArithmeticThetaInfinitesimalPolygonR0129.coordY k n else 1)

def stageIdeal {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) : D.X.IdealSheafData :=
  (ArithmeticThetaPolygonCohomologyR0131.markedSection k r n hr D (zeroIndex r hr) 1).ker

def chartIdeal {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (i : Fin r) : Ideal (A k n) :=
  letI : IsAffine (specA k n) := by
    change IsAffine (Spec (CommRingCat.of (A k n)))
    infer_instance
  Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom
    (((stageIdeal k D).comap (D.chart i)).ideal ⟨⊤, isAffineOpen_top (specA k n)⟩)

def Compatible (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    (d : ℕ) (v : Fin r → A k n) : Prop :=
  ∀ i : Fin r,
    E (restriction k n false (v i)) * restriction k n true (equation k r n (next r hr i))^d =
    restriction k n true (v (next r hr i)) * E (restriction k n false (equation k r n i))^d

def Sections (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true) (d : ℕ) :=
  {v : Fin r → A k n // Compatible k r n hr E d v}

def IsBasis {r n : ℕ} {hr : 0 < r} (E : B k n false ≃+* B k n true) (d : ℕ)
    (b : Fin d → Sections k r n hr E d) : Prop :=
  ∀ v : Sections k r n hr E d, ∃! c : Fin d → R k n,
    ∀ i : Fin r, v.val i = ∑ j : Fin d, base k n (c j) * (b j).val i

def stageModule {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (d : ℕ) : D.X.Modules :=
  GlobalCartierIdealLineR0133.idealModule ((stageIdeal k D)^d)

def StageDual {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (d : ℕ) :=
  stageModule k D d ⟶ (SheafOfModules.unit D.X.ringCatSheaf : D.X.Modules)

def StageRealizes {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (d : ℕ) (v : Fin r → A k n) (φ : StageDual k D d) : Prop :=
  ∀ i : Fin r,
    let f := D.chart i
    let P := (Scheme.Modules.pullback f).obj (stageModule k D d)
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion ((stageIdeal k D)^d)) ≫ unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k r n i)^d) ∧
      q.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (v i)

def completedReduction (n : ℕ) : Hat k →+* A k n :=
  (Classical.choose (finite_stage_completion_comparison k n)).toRingHom.comp
    (trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n)

def gammaTail (r : ℕ) (hr : 0 < r) (i : Fin r) : (Hat k)ˣ :=
  (Classical.choose_spec (ArithmeticThetaCorrectedGammaR0061.gamma_tail_exists
    k r i.val hr i.isLt)).1.unit

/-- Numerator of t^C z^(m/2) theta / gamma^m relative to the equation of m[0].
Only the proved unit tail is inverted; the horizontal zero is retained. -/
def thetaNumerator (m : ℕ) (hm : 0 < m) (he : Even m)
    (w : Fin m → PowerSeries k) (i : Fin (2*m)) : Hat k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (i.val * (m/2)) *
    ArithmeticThetaAnnularTorsionPrereqR0053.cx k ^ (m/2) *
    ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he w i *
    (↑((gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i)⁻¹) : Hat k)^m

def finiteNumerator (m : ℕ) (hm : 0 < m) (he : Even m)
    (w : Fin m → PowerSeries k) (n : ℕ) (i : Fin (2*m)) : A k n :=
  completedReduction k n (thetaNumerator k m hm he w i)

def powerModule {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ) : M.X.Modules :=
  GlobalCartierIdealLineR0133.idealModule (s.ker^d)

def Dual {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ) :=
  powerModule k M s d ⟶ (SheafOfModules.unit M.X.ringCatSheaf : M.X.Modules)

/-- Values of the actual pulled-back map on the actual local ideal generator.
b records one uniform vertical clearing power. It does not select an expansion. -/
def Realizes {m : ℕ} {hm : 0 < m} (he : Even m)
    {T : Tower k (2*m) (Nat.mul_pos (by decide) hm)} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (b : ℕ) (w : Fin m → PowerSeries k)
    (φ : Dual k M s m) : Prop :=
  ∀ n (i : Fin (2*m)),
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj (powerModule k M s m)
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker^m)) ≫ unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((equation k (2*m) n i)^m) ∧
      base k n (ArithmeticThetaInfinitesimalPolygonR0129.parameter k n ^ b) *
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom (q.app ⊤ z) =
      finiteNumerator k m hm he w n i

end ArithmeticThetaIdentitySectionsR0138
