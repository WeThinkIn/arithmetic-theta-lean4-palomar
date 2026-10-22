module

public import SharpFamilyRootLevelR0196
public import RootTestPullbackCoherenceR0196
public import SquareIsometryMuTwoActionR0196
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective
public import MetaplecticTestDefinitionsR0196
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

@[expose] public section

/-! Concrete descent data for the existing square-root moduli problem.
The predicates below specify output properties, without asserting effectivity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe v
namespace ArithmeticThetaRootDescentR0197
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections
open ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196

abbrev moduleFunctor := (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁

/-- The canonical descent functor for the actual specified family of maps. -/
abbrev descent {B : Scheme.{0}} {ι : Type v} {V : ι → Scheme.{0}}
    (f : ∀ i, V i ⟶ B) := moduleFunctor.toDescentData f

/-- Genuine invertible module descent data with specified local square maps.
The module datum already contains all pullback, identity and cocycle equations.
The square-map compatibility is imposed by CompatibleSquares. -/
structure RootDatum {B : Scheme.{0}} (W : B.Modules) {ι : Type v}
    {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ B) where
  data : moduleFunctor.DescentData f
  invertible : ∀ i, Scheme.Modules.IsInvertible (data.obj i)
  square : ∀ i, tensorPower (V i) (data.obj i) 2 ≅ (Scheme.Modules.pullback (f i)).obj W

def localRoot {B : Scheme.{0}} {W : B.Modules} {ι : Type v}
    {V : ι → Scheme.{0}} {f : ∀ i, V i ⟶ B} (D : RootDatum W f) (i : ι) :
    SquareLine (V i) ((Scheme.Modules.pullback (f i)).obj W) :=
  ⟨D.data.obj i, D.invertible i, D.square i⟩

/-- The two square maps agree on every common test scheme, after transport
to the same pullback of W. These are sheaf morphisms, not pointwise tests. -/
def CompatibleSquares {B : Scheme.{0}} {W : B.Modules} {ι : Type v}
    {V : ι → Scheme.{0}} {f : ∀ i, V i ⟶ B} (D : RootDatum W f) : Prop :=
  ∀ (S : Scheme.{0}) (p : S ⟶ B) (i j : ι)
    (a : S ⟶ V i) (b : S ⟶ V j) (ha : a ≫ f i = p) (hb : b ≫ f j = p),
    tensorPowerMap (D.data.hom p a b ha hb) 2 ≫ (squarePull b (localRoot D j)).hom ≫
      ((Scheme.Modules.pullbackComp b (f j)).app W).hom ≫
      ((Scheme.Modules.pullbackCongr hb).app W).hom =
    (squarePull a (localRoot D i)).hom ≫
      ((Scheme.Modules.pullbackComp a (f i)).app W).hom ≫
      ((Scheme.Modules.pullbackCongr ha).app W).hom

/-- An effective root must realize both the module cocycle and every specified
square map, with the same descent isomorphism. -/
def Realizes {B : Scheme.{0}} {W : B.Modules} {ι : Type v}
    {V : ι → Scheme.{0}} {f : ∀ i, V i ⟶ B} (D : RootDatum W f)
    (J : SquareLine B W) (e : (descent f).obj J.line ≅ D.data) : Prop :=
  ∀ i, tensorPowerMap (e.hom.hom i) 2 ≫ (D.square i).hom = (squarePull (f i) J).hom

def Effective {B : Scheme.{0}} {W : B.Modules} {ι : Type v}
    {V : ι → Scheme.{0}} {f : ∀ i, V i ⟶ B} (D : RootDatum W f) : Prop :=
  ∃ (J : SquareLine B W) (e : (descent f).obj J.line ≅ D.data), Realizes D J e

/-- Compatibility of a descent isomorphism with the original global squares. -/
def IsoCompatible {B : Scheme.{0}} {W : B.Modules} {ι : Type v}
    {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ B) (J K : SquareLine B W)
    (e : (descent f).obj J.line ≅ (descent f).obj K.line) : Prop :=
  ∀ i, tensorPowerMap (e.hom.hom i) 2 ≫ (squarePull (f i) K).hom =
    (squarePull (f i) J).hom

/-- Full faithfulness retains the entire descended sheaf isomorphism.
Uniqueness is equality of actual square-compatible isomorphisms. -/
def RootIsoDescent {B : Scheme.{0}} (W : B.Modules) {ι : Type v}
    {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ B) : Prop :=
  ∀ (J K : SquareLine B W)
    (e : (descent f).obj J.line ≅ (descent f).obj K.line),
    IsoCompatible f J K e →
    ∃! z : SquareIso J K, (descent f).mapIso z.val = e

/-- Weight-n regular sections are morphisms O -> J^n. The module descent datum
contains their equality on every overlap and pullback, including n = 0. -/
def WeightSectionDescent {B : Scheme.{0}} (W : B.Modules) {ι : Type v}
    {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ B) : Prop :=
  ∀ (J : SquareLine B W) (n : ℕ)
    (t : (descent f).obj (SheafOfModules.unit B.ringCatSheaf) ⟶
      (descent f).obj (tensorPower B J.line n)),
    ∃! s : SheafOfModules.unit B.ringCatSheaf ⟶ tensorPower B J.line n,
      (descent f).map s = t

/-- Effective objects, fully faithful square isomorphisms, and their actual
weight sections for the specified cover. This is a theorem target. -/
def RootDescent {B : Scheme.{0}} (W : B.Modules) {ι : Type v}
    {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ B) : Prop :=
  (∀ D : RootDatum W f, CompatibleSquares D → Effective D) ∧
    RootIsoDescent W f ∧ WeightSectionDescent W f

end ArithmeticThetaRootDescentR0197
