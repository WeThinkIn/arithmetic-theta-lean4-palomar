import MarkedSectionAlgebraizationR0136
import AlgebraizedPositiveFormalSectionsR0136
import ProjectiveTowerEffectivityR0135

/-! Actual chart, tower and algebraic-model automorphisms.
All actions are specified by their ring maps and geometric restriction equations.
No existence, group law or theta-line identification is built into the data. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
variable (k : Type u) [Field k] [CharZero k]

def chartX (n : ℕ) : A k n :=
  trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
    (ArithmeticThetaNodeCharts.x k)
def chartY (n : ℕ) : A k n :=
  trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
    (ArithmeticThetaNodeCharts.y k)
def scalar (n : ℕ) (a : k) : A k n :=
  base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C a))

def CoordinateMap (n : ℕ) (a : kˣ) (flip : Bool) (f : A k n →+* A k n) : Prop :=
  (∀ b : R k n, f (base k n b) = base k n b) ∧
  f (chartX k n) = scalar k n (a : k) * (if flip then chartY k n else chartX k n) ∧
  f (chartY k n) = scalar k n ((a⁻¹ : kˣ) : k) * (if flip then chartX k n else chartY k n)

def StageAction {r n : ℕ} {hr : 0 < r}
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (perm : Fin r → Fin r) (a : kˣ) (flip : Bool) (g : D.X ≅ D.X) : Prop :=
  g.hom ≫ D.p = D.p ∧ ∃ f : A k n →+* A k n,
    CoordinateMap k n a flip f ∧ ∀ i : Fin r,
      D.chart i ≫ g.hom = Spec.map (CommRingCat.ofHom f) ≫ D.chart (perm i)

def CompatibleAutos {r : ℕ} {hr : 0 < r} (T : Tower k r hr)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) : Prop :=
  (∀ n, (g n).hom ≫ (T.atlas n).p = (T.atlas n).p) ∧
  ∀ n N (h : n ≤ N), T.transition n N h ≫ (g N).hom = (g n).hom ≫ T.transition n N h

def TowerAction {r : ℕ} {hr : 0 < r} (T : Tower k r hr)
    (perm : Fin r → Fin r) (a : kˣ) (flip : Bool)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) : Prop :=
  CompatibleAutos k T g ∧ ∀ n, StageAction k (T.atlas n) perm a flip (g n)

def Algebraizes {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) (f : M.X ≅ M.X) : Prop :=
  f.hom ≫ M.p = M.p ∧ ∀ n, M.inclusion n ≫ f.hom = (g n).hom ≫ M.inclusion n

def ModelAction {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (perm : Fin r → Fin r) (a : kˣ) (flip : Bool) (f : M.X ≅ M.X) : Prop :=
  ∃ g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X,
    TowerAction k T perm a flip g ∧ Algebraizes k M g f

def Actions {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X) : Prop :=
  ModelAction k M (next r hr) 1 false rot ∧
  (∀ a, ModelAction k M id a false (scal a)) ∧
  ModelAction k M Fin.rev 1 true inv

def iterateHom {X : Scheme.{u}} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n+1 => iterateHom f n ≫ f

def ActionLaws {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X) : Prop :=
  iterateHom rot.hom r = 𝟙 M.X ∧
  (scal 1).hom = 𝟙 M.X ∧
  (∀ a b : kˣ, (scal (a*b)).hom = (scal a).hom ≫ (scal b).hom) ∧
  inv.hom ≫ inv.hom = 𝟙 M.X ∧
  (∀ a : kˣ, rot.hom ≫ (scal a).hom = (scal a).hom ≫ rot.hom) ∧
  inv.hom ≫ rot.hom ≫ inv.hom = rot.inv ∧
  (∀ a : kˣ, inv.hom ≫ (scal a).hom ≫ inv.hom = (scal a⁻¹).hom) ∧
  (∀ (c : ℕ) (a : kˣ), a^c = 1 → iterateHom (scal a).hom c = 𝟙 M.X)

def negIndex (r : ℕ) (hr : 0 < r) (i : Fin r) : Fin r :=
  ⟨(r-i.val)%r, Nat.mod_lt _ hr⟩

def MarkedTransport {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X) : Prop :=
  ∀ (i : Fin r) (b : kˣ) (s : baseScheme k ⟶ M.X), MarkedLift k M i b s →
    MarkedLift k M (next r hr i) b (s ≫ rot.hom) ∧
    (∀ a : kˣ, MarkedLift k M i (a*b) (s ≫ (scal a).hom)) ∧
    MarkedLift k M (negIndex r hr i) b⁻¹ (s ≫ inv.hom)
end ArithmeticThetaModelSymmetriesR0137
