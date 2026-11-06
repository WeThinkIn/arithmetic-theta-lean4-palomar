module

public import ActualAnchoredPullbackR0208
public import CategoricalRootFiberR0199

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaActualLevelR0208
namespace ActualCategoricalRootFiberProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaMetaplecticComparisonR0206 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
open ArithmeticThetaStackLevelR0199
open ActualFamilyFPQCDescentProof
attribute [local instance] CategoryTheory.uliftCategory

variable {k : Type} [Field k] [CharZero k] {L : ℕ} (P : Provider k L)
  {C : Coherence L (Base k)} {Y T : Over (Base k)}
  {p : Y ⟶ base P} {b : T ⟶ base P}
  {H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P))}
  {R : SquareLine T.left ((Scheme.Modules.pullback b.left).obj (hodge P))}

lemma object_classifier :
    (classifier P.universal (S := Y) (object P p H)).val = p.left := by
  let m := model P p
  let X := object P p H
  have hc := P.universal.1.2.2 Y.left Y.left Y.hom Y.hom m.family m.family
    m.marking m.marking (𝟙 Y.left) (𝟙 m.family.curve) (Category.id_comp _)
    (ActualGroupoidProof.marked_id X)
    p.left (classifier P.universal (S := Y) X).val m.curve
    (classifierCurve P.universal (S := Y) X) m.classifies (classifier_spec P.universal X)
  simpa only [Category.id_comp] using hc.1

lemma evaluation_classifier (j : AnchoredMap C Y (object P p H))
    (S : Over (Base k)) (f : S ⟶ Y) :
    (classifier P.universal (S := S)
      ((j.map.app (.mk (.op S))).toFunctor.obj (point f))).val = f.left ≫ p.left := by
  have ha := classifier_arrow P.universal ((group L S.left).arrow _ _
    (ActualAnchoredPullbackProof.component j S f).hom)
  rw [classifier_pull] at ha
  have hv := congrArg Subtype.val ha
  change _ = f.left ≫ (classifier P.universal (S := Y) (object P p H)).val at hv
  rw [object_classifier] at hv
  exact hv

/-- An actual arrow forces equality of the classifiers on every field-base test. -/
lemma fiber_triangle (j : AnchoredMap C Y (object P p H))
    (r : AnchoredMap C T (object P b R)) {S : Over (Base k)}
    (x : TestFiber j.map r.map S) :
    x.left.down.as.left ≫ p.left = x.right.down.as.left ≫ b.left := by
  obtain ⟨⟨⟨f⟩⟩, ⟨⟨g⟩⟩, u⟩ := x
  have h := congrArg Subtype.val
    (classifier_arrow P.universal ((group L S.left).arrow _ _ u))
  exact (evaluation_classifier P j S f).symm.trans
    (h.trans (evaluation_classifier P r S g))

abbrev roots (S : Over (Base k)) :=
  RootFiber k L P.atlas P.two P.cover P.quotient S

abbrev rootPull {S S' : Over (Base k)} (a : S' ⟶ S) :=
  rootReindex k L P.atlas P.two P.cover P.quotient a

abbrev comparison (hL : 3 ≤ L) (heven : Even L) (S : Over (Base k)) :=
  FiberEquivalenceProof.comparison hL heven P.universal (group L S.left)

def rootPoint : roots P Y := ⟨⟨p.left, Over.w p⟩, H⟩

/-- The normalized accepted comparison relates the actual pullback to the
canonical model of the pulled root, without discarding any curve arrow. -/
def pullComparison (hL : 3 ≤ L) (heven : Even L)
    {S : Over (Base k)} (f : S ⟶ Y) :
    rootPull P f ⋙ (comparison P hL heven S).equiv.functor ≅
      (comparison P hL heven Y).equiv.functor ⋙ (pull L f.left).functor :=
  (NaturalComparisonProof.normalized_exists_unique
    (comparison P hL heven Y) (comparison P hL heven S) f (pull L f.left)
    hL heven P.universal).choose

def evaluationIso (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (S : Over (Base k)) (f : S ⟶ Y) :
    (j.map.app (.mk (.op S))).toFunctor.obj (point f) ≅
      (comparison P hL heven S).equiv.functor.obj
        ((rootPull P f).obj (rootPoint P (p := p) (H := H))) :=
  ActualAnchoredPullbackProof.component j S f ≪≫
    ((pullComparison P hL heven f).app (rootPoint P (p := p) (H := H))).symm

/-- Transport all arrows, using full faithfulness of the accepted family model. -/
def evaluationHomEquiv (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (f : S ⟶ Y) (g : S ⟶ T) :
    (((j.map.app (.mk (.op S))).toFunctor.obj (point f)) ⟶
      ((r.map.app (.mk (.op S))).toFunctor.obj (point g))) ≃
    ((rootPull P f).obj (rootPoint P (p := p) (H := H)) ⟶
      (rootPull P g).obj (rootPoint P (p := b) (H := R))) where
  toFun u := (comparison P hL heven S).equiv.functor.preimage
    ((evaluationIso P hL heven j S f).inv ≫ u ≫ (evaluationIso P hL heven r S g).hom)
  invFun v := (evaluationIso P hL heven j S f).hom ≫
    (comparison P hL heven S).equiv.functor.map v ≫ (evaluationIso P hL heven r S g).inv
  left_inv u := by simp
  right_inv v := by
    apply (comparison P hL heven S).equiv.functor.map_injective
    simp

open ArithmeticThetaTensorPower ArithmeticThetaCoverComparison

/-- The complete square map for a root arrow, including equality of its classifiers. -/
structure RootArrow {S : Over (Base k)} (X Z : roots P S) where
  base_eq : X.1.val = Z.1.val
  line : X.2.line ≅ Z.2.line
  square : tensorPowerMap line.hom 2 ≫ Z.2.square.hom =
    X.2.square.hom ≫ ((Scheme.Modules.pullbackCongr base_eq).app (hodge P)).hom

def rootArrow {S : Over (Base k)} {X Z : roots P S} (u : X ⟶ Z) : RootArrow P X Z := by
  obtain ⟨c, J⟩ := X
  obtain ⟨d, K⟩ := Z
  rcases u with ⟨u⟩
  exact ⟨rfl, u.val, by simpa [Scheme.Modules.pullbackCongr] using u.property⟩

def rootArrowInv {S : Over (Base k)} {X Z : roots P S} (u : RootArrow P X Z) : X ⟶ Z := by
  obtain ⟨c, J⟩ := X
  obtain ⟨d, K⟩ := Z
  obtain ⟨hc, e, he⟩ := u
  have hcd : c = d := Subtype.ext hc
  subst d
  exact CategoryTheory.Sigma.SigmaHom.mk ⟨e, by simpa [Scheme.Modules.pullbackCongr] using he⟩

lemma rootArrow_left_inv {S : Over (Base k)} {X Z : roots P S} (u : X ⟶ Z) :
    rootArrowInv P (rootArrow P u) = u := by
  obtain ⟨c, J⟩ := X
  obtain ⟨d, K⟩ := Z
  rcases u with ⟨u⟩
  rfl

lemma rootArrow_right_inv {S : Over (Base k)} {X Z : roots P S} (u : RootArrow P X Z) :
    rootArrow P (rootArrowInv P u) = u := by
  obtain ⟨c, J⟩ := X
  obtain ⟨d, K⟩ := Z
  obtain ⟨hc, e, he⟩ := u
  have hcd : c = d := Subtype.ext hc
  subst d
  rfl

def rootArrowEquiv {S : Over (Base k)} (X Z : roots P S) :
    (X ⟶ Z) ≃ RootArrow P X Z :=
  ⟨rootArrow P, rootArrowInv P, rootArrow_left_inv P, rootArrow_right_inv P⟩

lemma rootArrow_line {S : Over (Base k)} {X Z : roots P S} (u : X ⟶ Z) :
    (rootArrow P u).line.hom =
      (rootForget k L P.atlas P.two P.cover P.quotient S).map u := by
  obtain ⟨c, J⟩ := X
  obtain ⟨d, K⟩ := Z
  rcases u with ⟨u⟩
  rfl

structure Geo (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
    (b : T ⟶ base P)
    (R : SquareLine T.left ((Scheme.Modules.pullback b.left).obj (hodge P)))
    (S : Over (Base k)) where
  l : S ⟶ Y
  t : S ⟶ T
  arrow : RootArrow P ((rootPull P t).obj (rootPoint P (p := b) (H := R)))
    ((rootPull P l).obj (rootPoint P (p := p) (H := H)))

def Geo.lift {S : Over (Base k)} (d : Geo P p H b R S) :
    Lift p.left H (⟨b.left, R⟩ : RootObject (base P).left (hodge P) T.left) S.left where
  toLevel := d.l.left
  toTest := d.t.left
  triangle := d.arrow.base_eq.symm
  iso := d.arrow.line

lemma Geo.compatible {S : Over (Base k)} (d : Geo P p H b R S) :
    Compatible d.lift := by
  have h := d.arrow.square
  change tensorPowerMap d.arrow.line.hom 2 ≫
    (((squarePull d.l.left H).hom ≫ (Scheme.Modules.pullbackComp d.l.left p.left).hom.app _) ≫
      (Scheme.Modules.pullbackCongr rfl).hom.app _) =
    (((squarePull d.t.left R).hom ≫ (Scheme.Modules.pullbackComp d.t.left b.left).hom.app _) ≫
      (Scheme.Modules.pullbackCongr rfl).hom.app _) ≫
      (Scheme.Modules.pullbackCongr d.arrow.base_eq).hom.app _ at h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] at h
  change tensorPowerMap d.arrow.line.hom 2 ≫ (squarePull d.l.left H).hom ≫
    (Scheme.Modules.pullbackComp d.l.left p.left).hom.app _ ≫
    (Scheme.Modules.pullbackCongr d.arrow.base_eq.symm).hom.app _ = _
  have hh := congrArg (fun q => q ≫
    (Scheme.Modules.pullbackCongr d.arrow.base_eq.symm).hom.app (hodge P)) h
  simpa [Geo.lift, Scheme.Modules.pullbackCongr, Category.assoc] using hh

lemma Geo.lift_injective {S : Over (Base k)} :
    Function.Injective (Geo.lift (P := P) (p := p) (H := H) (b := b) (R := R) (S := S)) := by
  intro d e h
  obtain ⟨l,t,i⟩ := d
  obtain ⟨l',t',i'⟩ := e
  have hl : l = l' := Over.OverMorphism.ext (congrArg Lift.toLevel h)
  have ht : t = t' := Over.OverMorphism.ext (congrArg Lift.toTest h)
  subst l'; subst t'
  have hi : i.line = i'.line := by
    obtain ⟨_,_,hi⟩ := (RelativeRootTestFiberR0196.sameLift_iff_eq H
      (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) _ _).mpr h
    change i.line ≪≫ Iso.refl _ = Iso.refl _ ≪≫ i'.line at hi
    simpa using hi
  obtain ⟨hc,i,hs⟩ := i
  obtain ⟨hc',i',hs'⟩ := i'
  dsimp at hi
  subst i'
  rfl

/-- Recover the root arrow from the entire compatible geometric lift. -/
def geoOfLift {S : Over (Base k)} (l : S ⟶ Y) (t : S ⟶ T)
    (ht : l.left ≫ p.left = t.left ≫ b.left)
    (e : (Scheme.Modules.pullback t.left).obj R.line ≅
      (Scheme.Modules.pullback l.left).obj H.line)
    (he : Compatible (⟨l.left,t.left,ht,e⟩ :
      Lift p.left H (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) S.left)) :
    Geo P p H b R S where
  l := l
  t := t
  arrow := ⟨ht.symm, e, by
    change tensorPowerMap e.hom 2 ≫
      (((squarePull l.left H).hom ≫ (Scheme.Modules.pullbackComp l.left p.left).hom.app _) ≫
        (Scheme.Modules.pullbackCongr rfl).hom.app _) =
      (((squarePull t.left R).hom ≫ (Scheme.Modules.pullbackComp t.left b.left).hom.app _) ≫
        (Scheme.Modules.pullbackCongr rfl).hom.app _) ≫
        (Scheme.Modules.pullbackCongr ht.symm).hom.app _
    simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id]
    change tensorPowerMap e.hom 2 ≫ (squarePull l.left H).hom ≫
      (Scheme.Modules.pullbackComp l.left p.left).hom.app _ ≫
      (Scheme.Modules.pullbackCongr ht).hom.app _ = _ at he
    have hh := congrArg (fun q => q ≫ (Scheme.Modules.pullbackCongr ht.symm).hom.app (hodge P)) he
    simpa [Scheme.Modules.pullbackCongr, Category.assoc] using hh⟩

def toGeo (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (x : TestFiber j.map r.map S) : Geo P p H b R S where
  l := x.left.down.as
  t := x.right.down.as
  arrow := rootArrow P (evaluationHomEquiv P hL heven r j
    x.right.down.as x.left.down.as (inv (C := (group L S.left).Objects) x.hom))

def fromGeo (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (d : Geo P p H b R S) : TestFiber j.map r.map S where
  left := point d.l
  right := point d.t
  hom := inv (C := (group L S.left).Objects) ((evaluationHomEquiv P hL heven r j d.t d.l).symm (rootArrowInv P d.arrow))

lemma from_to (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (x : TestFiber j.map r.map S) :
    fromGeo P hL heven j r (toGeo P hL heven j r x) = x := by
  obtain ⟨⟨⟨l⟩⟩, ⟨⟨t⟩⟩, h⟩ := x
  dsimp only [fromGeo, toGeo]
  congr 1
  simp only [rootArrow_left_inv, Equiv.symm_apply_apply, IsIso.inv_inv]

lemma to_from (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (d : Geo P p H b R S) :
    toGeo P hL heven j r (fromGeo P hL heven j r d) = d := by
  obtain ⟨l,t,e⟩ := d
  dsimp only [fromGeo, toGeo, point]
  congr 1
  simp only [IsIso.inv_inv, Equiv.apply_symm_apply, rootArrow_right_inv]

variable (F : Fiber p.left H (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left))

def space : Over (Base k) := Over.mk (F.universal.toTest ≫ T.hom)
def toLevel : space P F ⟶ Y := Over.homMk F.universal.toLevel (by
  change F.universal.toLevel ≫ Y.hom = F.universal.toTest ≫ T.hom
  calc
    _ = (F.universal.toLevel ≫ p.left) ≫ (base P).hom := by rw [Category.assoc, Over.w p]
    _ = (F.universal.toTest ≫ b.left) ≫ (base P).hom :=
      congrArg (fun q => q ≫ (base P).hom) F.universal.triangle
    _ = _ := by rw [Category.assoc, Over.w b])
def toTest : space P F ⟶ T := Over.homMk F.universal.toTest rfl

def geoPoint (hF : Represents F) {S : Over (Base k)} (f : S ⟶ space P F) : Geo P p H b R S :=
  geoOfLift P (f ≫ toLevel P F) (f ≫ toTest P F)
    (reindex F.universal f.left).triangle (reindex F.universal f.left).iso
    (RootTestPullbackCoherenceR0196.compatible_reindex F.universal f.left hF.1)

lemma geoPoint_lift (hF : Represents F) {S : Over (Base k)} (f : S ⟶ space P F) :
    (geoPoint P F hF f).lift = reindex F.universal f.left := rfl

lemma geoPoint_bijective (hF : Represents F) (S : Over (Base k)) :
    Function.Bijective (geoPoint P F hF (S := S)) := by
  constructor
  · intro f g h
    apply Over.OverMorphism.ext
    obtain ⟨v, hv, hu⟩ := hF.2 S.left (geoPoint P F hF f).lift (geoPoint P F hF f).compatible
    have hf' : SameLift (reindex F.universal f.left) (geoPoint P F hF f).lift :=
      (RelativeRootTestFiberR0196.sameLift_iff_eq H
        (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) _ _).mpr rfl
    have hg' : SameLift (reindex F.universal g.left) (geoPoint P F hF f).lift :=
      (RelativeRootTestFiberR0196.sameLift_iff_eq H
        (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) _ _).mpr
        (congrArg (Geo.lift P) h).symm
    exact (hu _ hf').trans (hu _ hg').symm
  · intro d
    obtain ⟨f, hf, _⟩ := hF.2 S.left d.lift d.compatible
    have he := (RelativeRootTestFiberR0196.sameLift_iff_eq H
      (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) _ _).mp hf
    have ht : f ≫ F.universal.toTest = d.t.left := congrArg Lift.toTest he
    let g : S ⟶ space P F := Over.homMk f (by
      change f ≫ (F.universal.toTest ≫ T.hom) = S.hom
      rw [← Category.assoc, ht]
      exact Over.w d.t)
    exact ⟨g, Geo.lift_injective P he⟩

instance fiberDiscrete (j : AnchoredMap C Y (object P p H))
    (r : AnchoredMap C T (object P b R)) (S : Over (Base k)) :
    IsDiscrete (TestFiber j.map r.map S) where
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

def objectEquiv (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) (S : Over (Base k)) : Points S (space P F) ≃ TestFiber j.map r.map S :=
  (CategoricalRootFiberR0199.pointEquiv S (space P F)).trans
    ((Equiv.ofBijective (geoPoint P F hF) (geoPoint_bijective P F hF S)).trans
      ⟨fromGeo P hL heven j r, toGeo P hL heven j r,
        to_from P hL heven j r, from_to P hL heven j r⟩)

def equivalence (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) (S : Over (Base k)) : Points S (space P F) ≌ TestFiber j.map r.map S :=
  CategoricalRootFiberR0199.discreteEquivalence (objectEquiv P F hL heven j r hF S)

/-- The actual line comparison extracted from anchored pullback. -/
def lineComponent (j : AnchoredMap C Y (object P p H)) (S : Over (Base k)) (f : S ⟶ Y) :
    ((j.map.app (.mk (.op S))).toFunctor.obj (point f)).root.line ≅
      (Scheme.Modules.pullback f.left).obj H.line :=
  (lineForget (group L S.left)).mapIso (ActualAnchoredPullbackProof.component j S f) ≪≫
    (pull L f.left).line (object P p H)

lemma evaluationIso_line (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (S : Over (Base k)) (f : S ⟶ Y) :
    (lineForget (group L S.left)).map (evaluationIso P hL heven j S f).hom =
      (lineComponent P j S f).hom := by
  have hn := (NaturalComparisonProof.normalized_exists_unique
    (comparison P hL heven Y) (comparison P hL heven S) f (pull L f.left)
    hL heven P.universal).choose_spec.1 (rootPoint P (p := p) (H := H))
  change (lineForget (group L S.left)).map
    ((pullComparison P hL heven f).hom.app (rootPoint P (p := p) (H := H))) =
    𝟙 _ ≫ (Scheme.Modules.pullback f.left).map (𝟙 H.line) ≫
      ((pull L f.left).line (object P p H)).inv at hn
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  change (lineForget (group L S.left)).map
    ((ActualAnchoredPullbackProof.component j S f).hom ≫
      ((pullComparison P hL heven f).app (rootPoint P (p := p) (H := H))).inv) = _
  rw [CategoryTheory.Functor.map_comp]
  have hi : (lineForget (group L S.left)).map
      (((pullComparison P hL heven f).app (rootPoint P (p := p) (H := H))).inv) =
      ((pull L f.left).line (object P p H)).hom := by
    apply (cancel_mono ((pull L f.left).line (object P p H)).inv).1
    rw [← hn, ← CategoryTheory.Functor.map_comp]
    simp [hn]
  rw [hi]
  rfl

lemma evaluationHomEquiv_line (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (f : S ⟶ Y) (g : S ⟶ T)
    (u : ((j.map.app (.mk (.op S))).toFunctor.obj (point f)) ⟶
      ((r.map.app (.mk (.op S))).toFunctor.obj (point g))) :
    (rootArrow P (evaluationHomEquiv P hL heven j r f g u)).line.hom =
      (lineComponent P j S f).inv ≫ (lineForget (group L S.left)).map u ≫
        (lineComponent P r S g).hom := by
  rw [rootArrow_line]
  let v := evaluationHomEquiv P hL heven j r f g u
  have hn := (comparison P hL heven S).line.hom.naturality v
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ (lineForget (group L S.left)).map
    ((comparison P hL heven S).equiv.functor.map v) at hn
  simp only [Category.comp_id, Category.id_comp] at hn
  rw [hn]
  dsimp only [v, evaluationHomEquiv, Equiv.coe_fn_mk]
  rw [CategoryTheory.Functor.map_preimage]
  simp only [CategoryTheory.Functor.map_comp, evaluationIso_line]
  have hi : (lineForget (group L S.left)).map (evaluationIso P hL heven j S f).inv =
      (lineComponent P j S f).inv := by
    apply (cancel_mono (lineComponent P j S f).hom).1
    rw [← evaluationIso_line P hL heven j S f, ← CategoryTheory.Functor.map_comp]
    simp [evaluationIso_line]
  rw [hi]

def underlying (j : AnchoredMap C Y (object P p H)) := j.map.vcomp (lineTransformation C)

lemma underlying_naturality (j : AnchoredMap C Y (object P p H))
    {S S' : Over (Base k)} (a : S' ⟶ S) (x : Points S Y) :
    ((underlying P j).naturality a.op.toLoc).hom.toNatTrans.app x =
      (lineForget (group L S'.left)).map
        ((j.map.naturality a.op.toLoc).hom.toNatTrans.app x) ≫
      ((pull L a.left).line ((j.map.app (.mk (.op S))).toFunctor.obj x)).hom := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

lemma lineComponent_hom (j : AnchoredMap C Y (object P p H))
    (S : Over (Base k)) (f : S ⟶ Y) :
    (lineComponent P j S f).hom =
      TautologicalSquarePullbackR0199.yonedaHom (underlying P j) f ≫
        (Scheme.Modules.pullback f.left).map ((lineForget (group L Y.left)).map j.anchor.hom) := by
  simp only [lineComponent, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    ActualAnchoredPullbackProof.component_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (pull L f.left).line_natural _ _ j.anchor.hom
  change (lineForget (group L S.left)).map _ ≫ _ = _ at hn
  rw [hn]
  dsimp only [TautologicalSquarePullbackR0199.yonedaHom]
  rw [underlying_naturality]
  simp only [ActualAnchoredPullbackProof.yonedaHom, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

lemma lineComponent_natural (j : AnchoredMap C Y (object P p H))
    {S S' : Over (Base k)} (a : S' ⟶ S) (f : S ⟶ Y) :
    (lineComponent P j S' (a ≫ f)).hom =
      (lineForget (group L S'.left)).map
        ((j.map.naturality a.op.toLoc).hom.toNatTrans.app (point f)) ≫
      ((pull L a.left).line ((j.map.app (.mk (.op S))).toFunctor.obj (point f))).hom ≫
      (Scheme.Modules.pullback a.left).map (lineComponent P j S f).hom ≫
      (Scheme.Modules.pullbackComp a.left f.left).hom.app H.line := by
  rw [lineComponent_hom, lineComponent_hom,
    TautologicalSquarePullbackR0199.yonedaHom_natural, underlying_naturality]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (Scheme.Modules.pullbackComp a.left f.left).hom.naturality
    ((lineForget (group L Y.left)).map j.anchor.hom)
  erw [← hn]
  rfl

lemma lineComponent_iso_natural (j : AnchoredMap C Y (object P p H))
    {S S' : Over (Base k)} (a : S' ⟶ S) (f : S ⟶ Y) :
    lineComponent P j S' (a ≫ f) =
      (lineForget (group L S'.left)).mapIso
        ((Cat.Hom.toNatIso (j.map.naturality a.op.toLoc)).app (point f)) ≪≫
      (pull L a.left).line ((j.map.app (.mk (.op S))).toFunctor.obj (point f)) ≪≫
      (Scheme.Modules.pullback a.left).mapIso (lineComponent P j S f) ≪≫
      (Scheme.Modules.pullbackComp a.left f.left).app H.line := by
  apply Iso.ext
  exact lineComponent_natural P j a f

lemma toGeo_line (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (x : TestFiber j.map r.map S) :
    (toGeo P hL heven j r x).arrow.line =
      (lineComponent P r S x.right.down.as).symm ≪≫
      ((lineForget (group L S.left)).mapIso (asIso x.hom)).symm ≪≫
      lineComponent P j S x.left.down.as := by
  apply Iso.ext
  exact evaluationHomEquiv_line P hL heven r j x.right.down.as x.left.down.as (inv (C := (group L S.left).Objects) x.hom)

lemma toGeo_inv (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S : Over (Base k)} (x : TestFiber j.map r.map S) :
    (toGeo P hL heven j r x).lift.iso.inv =
      (lineComponent P j S x.left.down.as).inv ≫
      (lineForget (group L S.left)).map x.hom ≫
      (lineComponent P r S x.right.down.as).hom := by
  change (toGeo P hL heven j r x).arrow.line.inv = _
  rw [toGeo_line]
  simp only [Iso.trans_inv, Iso.symm_inv, CategoryTheory.Functor.mapIso_hom, asIso_hom, Category.assoc]

lemma toGeo_pull (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    {S S' : Over (Base k)} (a : S' ⟶ S) (x : TestFiber j.map r.map S) :
    (toGeo P hL heven j r ((fiberPull j.map r.map a).obj x)).lift =
      reindex (toGeo P hL heven j r x).lift a.left := by
  apply (RelativeRootTestFiberR0196.sameLift_iff_eq H
    (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) _ _).mp
  refine ⟨rfl, rfl, ?_⟩
  change (toGeo P hL heven j r ((fiberPull j.map r.map a).obj x)).lift.iso ≪≫ Iso.refl _ =
    Iso.refl _ ≪≫ (reindex (toGeo P hL heven j r x).lift a.left).iso
  simp only [Iso.trans_refl, Iso.refl_trans]
  apply Iso.ext_inv
  rw [toGeo_inv]
  change (lineComponent P j S' (a ≫ x.left.down.as)).inv ≫
    (lineForget (group L S'.left)).map
      ((j.map.naturality a.op.toLoc).hom.toNatTrans.app x.left ≫
        (pull L a.left).functor.map x.hom ≫
        (r.map.naturality a.op.toLoc).inv.toNatTrans.app x.right) ≫
    (lineComponent P r S' (a ≫ x.right.down.as)).hom =
      (Scheme.Modules.pullbackComp a.left x.left.down.as.left).inv.app H.line ≫
        (Scheme.Modules.pullback a.left).map (toGeo P hL heven j r x).lift.iso.inv ≫
        (Scheme.Modules.pullbackComp a.left x.right.down.as.left).hom.app R.line
  rw [toGeo_inv, lineComponent_iso_natural P j, lineComponent_iso_natural P r]
  dsimp only [Iso.trans_inv, Iso.trans_hom, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.mapIso_hom, Iso.app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hj : (lineForget (group L S'.left)).map
      ((j.map.naturality a.op.toLoc).inv.toNatTrans.app x.left) ≫
    (lineForget (group L S'.left)).map
      ((j.map.naturality a.op.toLoc).hom.toNatTrans.app x.left) = 𝟙 _ := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      congrArg (lineForget (group L S'.left)).map
        (Cat.Hom.inv_hom_id_toNatTrans_app (j.map.naturality a.op.toLoc) x.left)
  have hr : (lineForget (group L S'.left)).map
      ((r.map.naturality a.op.toLoc).inv.toNatTrans.app x.right) ≫
    (lineForget (group L S'.left)).map
      ((r.map.naturality a.op.toLoc).hom.toNatTrans.app x.right) = 𝟙 _ := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      congrArg (lineForget (group L S'.left)).map
        (Cat.Hom.inv_hom_id_toNatTrans_app (r.map.naturality a.op.toLoc) x.right)
  erw [reassoc_of% hj, reassoc_of% hr]
  have hn := (pull L a.left).line_natural _ _ x.hom
  change (lineForget (group L S'.left)).map ((pull L a.left).functor.map x.hom) ≫
    ((pull L a.left).line ((r.map.app (.mk (.op S))).toFunctor.obj x.right)).hom =
      ((pull L a.left).line ((j.map.app (.mk (.op S))).toFunctor.obj x.left)).hom ≫
      (Scheme.Modules.pullback a.left).map ((lineForget (group L S.left)).map x.hom) at hn
  erw [reassoc_of% hn]
  exact congrArg
    (fun q => (Scheme.Modules.pullbackComp a.left x.left.down.as.left).inv.app H.line ≫
      (Scheme.Modules.pullback a.left).map (lineComponent P j S x.left.down.as).inv ≫ q)
    (((pull L a.left).line ((j.map.app (.mk (.op S))).toFunctor.obj x.left)).inv_hom_id_assoc
      ((Scheme.Modules.pullback a.left).map ((lineForget (group L S.left)).map x.hom) ≫
        (Scheme.Modules.pullback a.left).map (lineComponent P r S x.right.down.as).hom ≫
        (Scheme.Modules.pullbackComp a.left x.right.down.as.left).hom.app R.line))

lemma equivalence_obj (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) (S : Over (Base k)) (f : S ⟶ space P F) :
    (equivalence P F hL heven j r hF S).functor.obj (point f) =
      fromGeo P hL heven j r (geoPoint P F hF f) := rfl

lemma equivalence_natural_obj (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) {S S' : Over (Base k)} (a : S' ⟶ S) (f : S ⟶ space P F) :
    (equivalence P F hL heven j r hF S').functor.obj (point (a ≫ f)) =
      (fiberPull j.map r.map a).obj ((equivalence P F hL heven j r hF S).functor.obj (point f)) := by
  apply (Function.LeftInverse.injective (from_to P hL heven j r))
  apply Geo.lift_injective P
  rw [toGeo_pull, equivalence_obj, equivalence_obj, to_from, to_from]
  exact ((RelativeRootTestFiberR0196.sameLift_iff_eq H
    (⟨b.left,R⟩ : RootObject (base P).left (hodge P) T.left) _ _).mp
    (RootTestPullbackCoherenceR0196.reindex_comp F.universal f.left a.left)).symm

/-- Isolate categorical packaging from the concrete geometric presentations. -/
def discreteNatIso {D E : Type*} [Category D] [Category E] [IsDiscrete E]
    (f g : D ⥤ E) (h : ∀ x, f.obj x = g.obj x) : f ≅ g :=
  NatIso.ofComponents (fun x => eqToIso (h x)) (by
    intro x y u
    exact Subsingleton.elim _ _)

lemma equivalence_natural (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) (S S' : Over (Base k)) (a : S' ⟶ S) :
    Nonempty (precompose (space P F) a ⋙ (equivalence P F hL heven j r hF S').functor ≅
      (equivalence P F hL heven j r hF S).functor ⋙ fiberPull j.map r.map a) := by
  refine ⟨discreteNatIso _ _ ?_⟩
  rintro ⟨⟨f⟩⟩
  exact equivalence_natural_obj P F hL heven j r hF a f

def presentation (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) : FiberPresentation j.map r.map where
  space := space P F
  toLevel := toLevel P F
  toTest := toTest P F
  equiv := equivalence P F hL heven j r hF
  left_eq _ _ := rfl
  right_eq _ _ := rfl
  natural := equivalence_natural P F hL heven j r hF

lemma usesFiber (hL : 3 ≤ L) (heven : Even L)
    (j : AnchoredMap C Y (object P p H)) (r : AnchoredMap C T (object P b R))
    (hF : Represents F) : UsesFiber F (presentation P F hL heven j r hF) :=
  ⟨Iso.refl _, Category.id_comp _, Category.id_comp _⟩

end ActualCategoricalRootFiberProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196

/-- The all-test categorical fiber retains the actual marked family arrows and
is represented by the given geometric square-isometry fiber, with both projections. -/
theorem actual_categorical_root_fiber
    (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (P : Provider k L) (C : Coherence L (Base k))
    (Y : Over (Base k)) (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
    (j : AnchoredMap C Y (object P p H))
    (Z : Over (Base k)) (b : Z ⟶ base P)
    (R : SquareLine Z.left ((Scheme.Modules.pullback b.left).obj (hodge P)))
    (r : AnchoredMap C Z (object P b R))
    (F : Fiber p.left H (⟨b.left,R⟩ : RootObject (base P).left (hodge P) Z.left))
    (hF : Represents F) : ∃ G : FiberPresentation j.map r.map, UsesFiber F G :=
  ⟨ActualCategoricalRootFiberProof.presentation P F hL heven j r hF,
    ActualCategoricalRootFiberProof.usesFiber P F hL heven j r hF⟩

end ArithmeticThetaActualLevelR0208
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.fiber_triangle
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.evaluationHomEquiv

#print axioms ArithmeticThetaActualLevelR0208.actual_categorical_root_fiber
