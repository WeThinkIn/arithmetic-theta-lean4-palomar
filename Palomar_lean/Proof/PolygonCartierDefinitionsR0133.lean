module

public import PolygonCompatibleMarkingsR0131
public import PolygonGlobalFunctionsR0131
public import PolygonCechObstructionR0131
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import PolygonCohomologyDefinitionsR0131

@[expose] public section

/-! Actual ideal sheaves and module sheaves on the accepted infinitesimal
polygon. The predicates below specify conclusions to be proved, not additional
geometric hypotheses on the atlas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131

variable (k : Type u) [Field k] [CharZero k]

def leftMarkedPoint (n : ℕ) (b : kˣ) : A k n →+* R k n :=
  mkPoint (RingHom.id (R k n))
    (parameter k n * (markedUnit k n b : R k n))
    (↑((markedUnit k n b)⁻¹)) (by simp [mul_assoc])

def pairEvaluation (n : ℕ) (a b : kˣ) : A k n →+* R k n × R k n :=
  (markedPoint k n a).prod (leftMarkedPoint k n b)

def pairEquation (n : ℕ) (a b : kˣ) : A k n :=
  markedEquation k n a *
    (coordY k n - base k n (↑((markedUnit k n b)⁻¹)))

def markedIdeal (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) : D.X.IdealSheafData :=
  ⨅ i : Fin r, (markedSection k r n hr D i (a i)).ker

def chartIdeal (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) (i : Fin r) : Ideal (A k n) :=
  letI : IsAffine (specA k n) := by
    change IsAffine (Spec (CommRingCat.of (A k n)))
    infer_instance
  Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom
    (((markedIdeal k r n hr D a).comap (D.chart i)).ideal
      ⟨⊤, isAffineOpen_top (specA k n)⟩)

def splitBase (r n : ℕ) : R k n →+* (Fin r → R k n) :=
  RingHom.pi (fun _ => RingHom.id (R k n))

def splitStructure (r n : ℕ) :
    Spec (CommRingCat.of (Fin r → R k n)) ⟶ specR k n :=
  Spec.map (CommRingCat.ofHom (splitBase k r n))

def componentMap (r n : ℕ) (i : Fin r) :
    specR k n ⟶ Spec (CommRingCat.of (Fin r → R k n)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin r => R k n) i))

def SplitMarkedDivisor (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) : Prop :=
  let I := markedIdeal k r n hr D a
  IsClosedImmersion I.subschemeι ∧
    IsFinite (I.subschemeι ≫ D.p) ∧ Etale (I.subschemeι ≫ D.p) ∧
    (∃ e : I.subscheme ≅ Spec (CommRingCat.of (Fin r → R k n)),
      e.hom ≫ splitStructure k r n = I.subschemeι ≫ D.p ∧
      ∀ i : Fin r, componentMap k r n i ≫ e.inv ≫ I.subschemeι =
        markedSection k r n hr D i (a i))

def IsEffectiveCartierIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∃ f : X.presheaf.obj (Opposite.op U.1),
      IsRegular f ∧ I.ideal U = Ideal.span ({f} : Set _)

def IdealRealization {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) (j : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) : Prop :=
  Mono j ∧ ∀ U : X.affineOpens,
    Set.range (fun s => (Scheme.Modules.Hom.app j U.1 s :
      X.presheaf.obj (Opposite.op U.1))) = (I.ideal U).carrier

def CartierLineFacts (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) : Prop :=
  IsEffectiveCartierIdeal (markedIdeal k r n hr D a) ∧
    ∃ (M : D.X.Modules)
      (j : M ⟶ (SheafOfModules.unit D.X.ringCatSheaf : D.X.Modules)),
      IdealRealization (markedIdeal k r n hr D a) M j ∧
      ∀ i : Fin r, Nonempty
        ((Scheme.Modules.pullback (D.chart i)).obj M ≅
          (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules))

def divisorComplement (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (a : Fin r → kˣ) : D.X.Opens :=
  (markedIdeal k r n hr D a).support.compl

def unitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

def LineReductionFacts (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (a : Fin r → kˣ) (n N : ℕ) (h : n ≤ N) : Prop :=
  ∀ (M : (T.atlas N).X.Modules) (L : (T.atlas n).X.Modules)
    (j : M ⟶ (SheafOfModules.unit (T.atlas N).X.ringCatSheaf : (T.atlas N).X.Modules))
    (l : L ⟶ (SheafOfModules.unit (T.atlas n).X.ringCatSheaf : (T.atlas n).X.Modules)),
    IdealRealization (markedIdeal k r N hr (T.atlas N) a) M j →
    IdealRealization (markedIdeal k r n hr (T.atlas n) a) L l →
    ∃! e : (Scheme.Modules.pullback (T.transition n N h)).obj M ≅ L,
      e.hom ≫ l = (Scheme.Modules.pullback (T.transition n N h)).map j ≫
        unitPullback (T.transition n N h)

end ArithmeticThetaPolygonCartierR0133
