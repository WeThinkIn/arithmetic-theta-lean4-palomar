module

public import TautologicalSquarePullbackR0199

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaStackLevelR0199
namespace CategoricalRootFiberR0199
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRootStackR0198 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaMetaplecticTestsR0196 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198
open ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196
open ArithmeticThetaMetaplecticTestsR0196.RelativeRootTestFiberR0196 (sameLift_iff_eq)
attribute [local instance] CategoryTheory.uliftCategory

variable {B : Scheme.{0}} {W : B.Modules} {P : Presentation B W}
  {Y T : Over B} {H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W)}
  {R : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W)}

structure Geo (H : SquareLine Y.left ((Scheme.Modules.pullback Y.hom).obj W))
    (R : SquareLine T.left ((Scheme.Modules.pullback T.hom).obj W)) (S : Over B) where
  l : S ⟶ Y
  t : S ⟶ T
  e : SquareIso (pullObj t R) (pullObj l H)

def Geo.lift {S : Over B} (d : Geo H R S) :
    Lift Y.hom H (⟨T.hom, R⟩ : RootObject B W T.left) S.left where
  toLevel := d.l.left
  toTest := d.t.left
  triangle := (Over.w d.l).trans (Over.w d.t).symm
  iso := d.e.val

lemma compatible_iff {S : Over B} (l : S ⟶ Y) (t : S ⟶ T)
    (e : (pullObj t R).line ≅ (pullObj l H).line) :
    (tensorPowerMap e.hom 2 ≫ (pullObj l H).square.hom = (pullObj t R).square.hom) ↔
    Compatible (⟨l.left, t.left, (Over.w l).trans (Over.w t).symm, e⟩ :
      Lift Y.hom H (⟨T.hom, R⟩ : RootObject B W T.left) S.left) := by
  unfold Compatible
  dsimp only [pullObj, Iso.trans_hom]
  rw [← cancel_mono ((Scheme.Modules.pullbackCongr (Over.w t)).app W).hom]
  simp only [Category.assoc]
  have h : (Scheme.Modules.pullbackCongr ((Over.w l).trans (Over.w t).symm)).hom.app W ≫
      (Scheme.Modules.pullbackCongr (Over.w t)).hom.app W =
      (Scheme.Modules.pullbackCongr (Over.w l)).hom.app W := by
    simp [Scheme.Modules.pullbackCongr]
  erw [h]
  rfl

lemma Geo.compatible {S : Over B} (d : Geo H R S) : Compatible d.lift :=
  (compatible_iff d.l d.t d.e.val).mp d.e.property

lemma Geo.lift_injective {S : Over B} : Function.Injective (Geo.lift (H := H) (R := R) (S := S)) := by
  intro d e h
  obtain ⟨l,t,i⟩ := d
  obtain ⟨l',t',i'⟩ := e
  have hl : l = l' := Over.OverMorphism.ext (congrArg Lift.toLevel h)
  have ht : t = t' := Over.OverMorphism.ext (congrArg Lift.toTest h)
  subst l'; subst t'
  have hi : i = i' := Subtype.ext (by
    obtain ⟨_,_,hi⟩ := (sameLift_iff_eq H (⟨T.hom,R⟩ : RootObject B W T.left) _ _).mpr h
    change i.val ≪≫ Iso.refl _ = Iso.refl _ ≪≫ i'.val at hi
    simpa using hi)
  subst i'; rfl

def toGeo (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    {S : Over B} (x : TestFiber j.map r.map S) : Geo H R S where
  l := x.left.down.as
  t := x.right.down.as
  e := trans (symm (cr.component S x.right.down.as))
    (trans (symm (P.homEquiv S _ _ x.hom)) (cj.component S x.left.down.as))

def fromGeo (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    {S : Over B} (d : Geo H R S) : TestFiber j.map r.map S where
  left := point d.l
  right := point d.t
  hom := (P.homEquiv S _ _).symm
    (trans (cj.component S d.l) (trans (symm d.e) (symm (cr.component S d.t))))

lemma from_to (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    {S : Over B} (x : TestFiber j.map r.map S) :
    fromGeo j r cj cr (toGeo j r cj cr x) = x := by
  obtain ⟨⟨⟨l⟩⟩, ⟨⟨t⟩⟩, h⟩ := x
  dsimp only [fromGeo, toGeo]
  congr 1
  apply (P.homEquiv S _ _).injective
  simp only [Equiv.apply_symm_apply]
  apply Subtype.ext; apply Iso.ext
  simp [point, RootModuliPseudofunctorR0198.trans, RootModuliPseudofunctorR0198.symm]

lemma to_from (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    {S : Over B} (d : Geo H R S) :
    toGeo j r cj cr (fromGeo j r cj cr d) = d := by
  obtain ⟨l,t,e⟩ := d
  dsimp only [fromGeo, toGeo]
  congr 1
  apply Subtype.ext; apply Iso.ext
  simp [point, RootModuliPseudofunctorR0198.trans, RootModuliPseudofunctorR0198.symm]


variable (F : ArithmeticThetaMetaplecticTestsR0196.Fiber Y.hom H
  (⟨T.hom, R⟩ : RootObject B W T.left))

def space : Over B := Over.mk (F.universal.toTest ≫ T.hom)
def toLevel : space F ⟶ Y := Over.homMk F.universal.toLevel F.universal.triangle
def toTest : space F ⟶ T := Over.homMk F.universal.toTest rfl

def geoPoint (hF : Represents F) {S : Over B} (f : S ⟶ space F) : Geo H R S where
  l := f ≫ toLevel F
  t := f ≫ toTest F
  e := ⟨(reindex F.universal f.left).iso,
    (compatible_iff (f ≫ toLevel F) (f ≫ toTest F) _).mpr
      (compatible_reindex F.universal f.left hF.1)⟩

lemma geoPoint_lift (hF : Represents F) {S : Over B} (f : S ⟶ space F) :
    (geoPoint F hF f).lift = reindex F.universal f.left := rfl

lemma geoPoint_bijective (hF : Represents F) (S : Over B) :
    Function.Bijective (geoPoint F hF (S := S)) := by
  constructor
  · intro f g h
    apply Over.OverMorphism.ext
    have hf := (hF.2 S.left (geoPoint F hF f).lift (geoPoint F hF f).compatible)
    obtain ⟨k, hk, hu⟩ := hf
    have hf' : SameLift (reindex F.universal f.left) (geoPoint F hF f).lift :=
      (sameLift_iff_eq H (⟨T.hom,R⟩ : RootObject B W T.left) _ _).mpr rfl
    have hg' : SameLift (reindex F.universal g.left) (geoPoint F hF f).lift :=
      (sameLift_iff_eq H (⟨T.hom,R⟩ : RootObject B W T.left) _ _).mpr
        (congrArg Geo.lift h).symm
    exact (hu _ hf').trans (hu _ hg').symm
  · intro d
    obtain ⟨f, hf, _⟩ := hF.2 S.left d.lift d.compatible
    have he := (sameLift_iff_eq H (⟨T.hom,R⟩ : RootObject B W T.left) _ _).mp hf
    have ht : f ≫ F.universal.toTest = d.t.left := congrArg Lift.toTest he
    let g : S ⟶ space F := Over.homMk f (by
      change f ≫ (F.universal.toTest ≫ T.hom) = S.hom
      rw [← Category.assoc, ht]
      exact Over.w d.t)
    refine ⟨g, Geo.lift_injective ?_⟩
    exact he

instance pointsDiscrete (S Z : Over B) : IsDiscrete (Points S Z) where
  subsingleton _ _ := ⟨fun f g => by exact congrArg Discrete.Hom.mk rfl⟩
  eq_of_hom f := by apply ULift.ext; exact Discrete.ext (Discrete.eq_of_hom f)

instance fiberDiscrete (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (S : Over B) : IsDiscrete (TestFiber j.map r.map S) where
  subsingleton x y := ⟨fun f g => by
    apply CommaMorphism.ext <;> exact congrArg Discrete.Hom.mk rfl⟩
  eq_of_hom := by
    intro x y f
    have hl : x.left = y.left := by apply ULift.ext; exact Discrete.ext (Discrete.eq_of_hom f.left)
    have ht : x.right = y.right := by apply ULift.ext; exact Discrete.ext (Discrete.eq_of_hom f.right)
    obtain ⟨l,t,h⟩ := x
    obtain ⟨l',t',h'⟩ := y
    dsimp at hl ht
    subst l'; subst t'
    have hfl : f.left = 𝟙 l := by exact congrArg Discrete.Hom.mk rfl
    have hft : f.right = 𝟙 t := by exact congrArg Discrete.Hom.mk rfl
    have hh := f.w
    rw [hfl, hft, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hh
    cases hh
    rfl

/-- Object equivalences between discrete categories retain all their arrows. -/
def discreteEquivalence {C D : Type*} [Category C] [Category D]
    [IsDiscrete C] [IsDiscrete D] (e : C ≃ D) : C ≌ D where
  functor := { obj := e, map := fun f => eqToHom (congrArg e (obj_ext_of_isDiscrete f)) }
  inverse := { obj := e.symm, map := fun f => eqToHom (congrArg e.symm (obj_ext_of_isDiscrete f)) }
  unitIso := NatIso.ofComponents (fun x => eqToIso (e.symm_apply_apply x).symm)
  counitIso := NatIso.ofComponents (fun x => eqToIso (e.apply_symm_apply x))


lemma component_iso_natural (j : ClassifiedMap P Y H) (cj : TautologicalComparison j)
    {S S' : Over B} (a : S' ⟶ S) (f : S ⟶ Y) :
    (cj.component S' (a ≫ f)).val =
      (P.forget.app (.mk (.op S'))).toFunctor.mapIso
        ((Cat.Hom.toNatIso (j.map.naturality a.op.toLoc)).app (point f)) ≪≫
      (Cat.Hom.toNatIso (P.forget.naturality a.op.toLoc)).app
        ((j.map.app (.mk (.op S))).toFunctor.obj (point f)) ≪≫
      (Scheme.Modules.pullback a.left).mapIso (cj.component S f).val ≪≫
      (Scheme.Modules.pullbackComp a.left f.left).app H.line := by
  apply Iso.ext
  exact cj.natural S S' a f

lemma toGeo_inv (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    {S : Over B} (x : TestFiber j.map r.map S) :
    (toGeo j r cj cr x).e.val.inv =
      (cj.component S x.left.down.as).val.inv ≫
      (P.forget.app (.mk (.op S))).toFunctor.map x.hom ≫
      (cr.component S x.right.down.as).val.hom := by
  dsimp only [toGeo, RootModuliPseudofunctorR0198.trans,
    RootModuliPseudofunctorR0198.symm, Iso.trans_inv, Iso.symm_inv]
  rw [P.hom_eq]
  simp only [Category.assoc]

lemma toGeo_pull (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    {S S' : Over B} (a : S' ⟶ S) (x : TestFiber j.map r.map S) :
    (toGeo j r cj cr ((fiberPull j.map r.map a).obj x)).lift =
      reindex (toGeo j r cj cr x).lift a.left := by
  apply (sameLift_iff_eq H (⟨T.hom,R⟩ : RootObject B W T.left) _ _).mp
  refine ⟨rfl, rfl, ?_⟩
  change (toGeo j r cj cr ((fiberPull j.map r.map a).obj x)).e.val ≪≫ Iso.refl _ =
    Iso.refl _ ≪≫ (reindex (toGeo j r cj cr x).lift a.left).iso
  simp only [Iso.trans_refl, Iso.refl_trans]
  apply Iso.ext_inv
  rw [toGeo_inv]
  change (cj.component S' (a ≫ x.left.down.as)).val.inv ≫
    (P.forget.app (.mk (.op S'))).toFunctor.map
      ((j.map.naturality a.op.toLoc).hom.toNatTrans.app x.left ≫
        (P.functor.map a.op.toLoc).toFunctor.map x.hom ≫
        (r.map.naturality a.op.toLoc).inv.toNatTrans.app x.right) ≫
    (cr.component S' (a ≫ x.right.down.as)).val.hom =
      (Scheme.Modules.pullbackComp a.left x.left.down.as.left).inv.app H.line ≫
        (Scheme.Modules.pullback a.left).map (toGeo j r cj cr x).e.val.inv ≫
        (Scheme.Modules.pullbackComp a.left x.right.down.as.left).hom.app R.line
  rw [toGeo_inv, component_iso_natural j cj, component_iso_natural r cr]
  dsimp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Iso.app]
  simp only [Functor.map_comp, Category.assoc]
  have hj : (P.forget.app (.mk (.op S'))).toFunctor.map
      ((j.map.naturality a.op.toLoc).inv.toNatTrans.app x.left) ≫
    (P.forget.app (.mk (.op S'))).toFunctor.map
      ((j.map.naturality a.op.toLoc).hom.toNatTrans.app x.left) = 𝟙 _ := by
    rw [← Functor.map_comp]
    change _ = _
    simp
  have hr : (P.forget.app (.mk (.op S'))).toFunctor.map
      ((r.map.naturality a.op.toLoc).inv.toNatTrans.app x.right) ≫
    (P.forget.app (.mk (.op S'))).toFunctor.map
      ((r.map.naturality a.op.toLoc).hom.toNatTrans.app x.right) = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  have hn := (P.forget.naturality a.op.toLoc).hom.toNatTrans.naturality x.hom
  erw [reassoc_of% hj, reassoc_of% hr]
  erw [reassoc_of% hn]
  change _ ≫ _ ≫ (P.forget.naturality a.op.toLoc).inv.toNatTrans.app
    ((j.map.app (.mk (.op S))).toFunctor.obj x.left) ≫
    (P.forget.naturality a.op.toLoc).hom.toNatTrans.app
    ((j.map.app (.mk (.op S))).toFunctor.obj x.left) ≫ _ = _
  have hf := Cat.Hom.inv_hom_id_toNatTrans_app (P.forget.naturality a.op.toLoc)
    ((j.map.app (.mk (.op S))).toFunctor.obj x.left)
  erw [reassoc_of% hf]
  rfl


def pointEquiv (S Z : Over B) : Points S Z ≃ (S ⟶ Z) where
  toFun x := x.down.as
  invFun := point
  left_inv x := by cases x; rfl
  right_inv _ := rfl

def objectEquiv (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    (hF : Represents F) (S : Over B) : Points S (space F) ≃ TestFiber j.map r.map S :=
  (pointEquiv S (space F)).trans
    ((Equiv.ofBijective (geoPoint F hF) (geoPoint_bijective F hF S)).trans
      { toFun := fromGeo j r cj cr
        invFun := toGeo j r cj cr
        left_inv := to_from j r cj cr
        right_inv := from_to j r cj cr })

def equivalence (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    (hF : Represents F) (S : Over B) : Points S (space F) ≌ TestFiber j.map r.map S :=
  discreteEquivalence (objectEquiv F j r cj cr hF S)

lemma equivalence_obj (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    (hF : Represents F) (S : Over B) (f : S ⟶ space F) :
    (equivalence F j r cj cr hF S).functor.obj (point f) =
      fromGeo j r cj cr (geoPoint F hF f) := rfl

lemma equivalence_natural_obj (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    (hF : Represents F) {S S' : Over B} (a : S' ⟶ S) (f : S ⟶ space F) :
    (equivalence F j r cj cr hF S').functor.obj (point (a ≫ f)) =
      (fiberPull j.map r.map a).obj ((equivalence F j r cj cr hF S).functor.obj (point f)) := by
  apply (Function.LeftInverse.injective (from_to j r cj cr))
  apply Geo.lift_injective
  rw [toGeo_pull, equivalence_obj, equivalence_obj, to_from, to_from]
  exact ((sameLift_iff_eq H (⟨T.hom,R⟩ : RootObject B W T.left) _ _).mp
    (reindex_comp F.universal f.left a.left)).symm

def presentation (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    (hF : Represents F) : FiberPresentation j.map r.map where
  space := space F
  toLevel := toLevel F
  toTest := toTest F
  equiv := equivalence F j r cj cr hF
  left_eq _ _ := rfl
  right_eq _ _ := rfl
  natural S S' a := ⟨NatIso.ofComponents (fun x => eqToIso (by
      obtain ⟨⟨f⟩⟩ := x
      exact equivalence_natural_obj F j r cj cr hF a f))
    (by intro x y f; apply CommaMorphism.ext <;> exact congrArg Discrete.Hom.mk rfl)⟩

lemma usesFiber (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (cj : TautologicalComparison j) (cr : TautologicalComparison r)
    (hF : Represents F) : UsesFiber j r F (presentation F j r cj cr hF) := by
  exact ⟨Iso.refl _, Category.id_comp _, Category.id_comp _⟩

end CategoricalRootFiberR0199

/-- Every categorical two-fiber of the specified strong classifying maps is
represented by the accepted geometric square-isometry fiber, naturally on all tests. -/
theorem categorical_root_fiber
    (B : AlgebraicGeometry.Scheme.{0}) (W : B.Modules)
    (P : ArithmeticThetaRootStackR0198.Presentation B W)
    (Y : CategoryTheory.Over B)
    (H : ArithmeticThetaSquareLinesR0192.SquareLine Y.left
      ((AlgebraicGeometry.Scheme.Modules.pullback Y.hom).obj W))
    (T : CategoryTheory.Over B)
    (R : ArithmeticThetaSquareLinesR0192.SquareLine T.left
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj W))
    (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (F : ArithmeticThetaMetaplecticTestsR0196.Fiber Y.hom H
      (⟨T.hom, R⟩ : ArithmeticThetaMetaplecticTestsR0196.RootObject B W T.left))
    (hF : ArithmeticThetaMetaplecticTestsR0196.Represents F) :
    ∃ G : FiberPresentation j.map r.map, UsesFiber j r F G := by
  obtain ⟨cj⟩ := tautological_square_pullback B W P Y H j
  obtain ⟨cr⟩ := tautological_square_pullback B W P T R r
  exact ⟨CategoricalRootFiberR0199.presentation F j r cj cr hF,
    CategoricalRootFiberR0199.usesFiber F j r cj cr hF⟩

end ArithmeticThetaStackLevelR0199

#print axioms ArithmeticThetaStackLevelR0199.categorical_root_fiber
