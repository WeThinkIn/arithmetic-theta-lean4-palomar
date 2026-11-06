import AlgebraizedGeometricConnectednessR0135
import SplitFiniteMarkedDivisorR0133
import GlobalPositiveSectionRealizationR0134

/-! Actual sections, their divisor, and complete positive-line expansions on
an algebraization of the accepted polygon tower. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCartierR0133
variable (k : Type u) [Field k] [CharZero k]

def baseScheme : Scheme.{u} := Spec (CommRingCat.of (PowerSeries k))

def MarkedLift {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (i : Fin r) (a : kˣ) (s : baseScheme k ⟶ M.X) : Prop :=
  s ≫ M.p = 𝟙 (baseScheme k) ∧ ∀ n : ℕ,
    baseInclusion k n ≫ s = markedSection k r n hr (T.atlas n) i a ≫ M.inclusion n

def LiftFamily {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X)) : Prop :=
  ∀ i, MarkedLift k M i (a i) (s i)

def markedIdeal {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : Fin r → (baseScheme k ⟶ M.X)) : M.X.IdealSheafData :=
  ⨅ i : Fin r, (s i).ker

def splitStructure (r : ℕ) : Spec (CommRingCat.of (Fin r → PowerSeries k)) ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom (RingHom.pi (fun _ : Fin r => RingHom.id (PowerSeries k))))

def componentMap (r : ℕ) (i : Fin r) :
    baseScheme k ⟶ Spec (CommRingCat.of (Fin r → PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin r => PowerSeries k) i))

def SplitDivisor {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : Fin r → (baseScheme k ⟶ M.X)) : Prop :=
  let I := markedIdeal k M s
  IsClosedImmersion I.subschemeι ∧ IsFinite (I.subschemeι ≫ M.p) ∧
    Etale (I.subschemeι ≫ M.p) ∧
    ∃ e : I.subscheme ≅ Spec (CommRingCat.of (Fin r → PowerSeries k)),
      e.hom ≫ splitStructure k r = I.subschemeι ≫ M.p ∧
      ∀ i, componentMap k r i ≫ e.inv ≫ I.subschemeι = s i

def powerIdealModule {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : Fin r → (baseScheme k ⟶ M.X)) (d : ℕ) : M.X.Modules :=
  GlobalCartierIdealLineR0133.idealModule ((markedIdeal k M s)^d)

def DualSections {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : Fin r → (baseScheme k ⟶ M.X)) (d : ℕ) : Type u :=
  powerIdealModule k M s d ⟶ (SheafOfModules.unit M.X.ringCatSheaf : M.X.Modules)

/-- The actual pullback to each chart of each infinitesimal stage, tested on
the prescribed local equation of dD. No arbitrary expansion map is supplied. -/
def Realizes {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X)) (d : ℕ)
    (v : FormalSection k r hr T a d) (φ : DualSections k M s d) : Prop :=
  ∀ n i,
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj (powerIdealModule k M s d)
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion ((markedIdeal k M s)^d)) ≫ unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    ∃ t : Γ(P, ⊤),
      j.app ⊤ t = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        ((ArithmeticThetaPositiveLineR0134.equation k r n hr a i)^d) ∧
      q.app ⊤ t = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv ((v.val n).val i)

end ArithmeticThetaAlgebraizedMarkedLineR0136
