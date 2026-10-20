module

public import CoherentMetaplecticPullbackR0207
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaMetaplecticStackR0207
namespace ActualFamilyFPQCDescentProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205

variable {k : Type} [Field k] [CharZero k] {L : ℕ}
  {A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L}
  {B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A}
  {V : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B}
  {Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B V}
  (H : HodgeUniversal k L A B V Q)

/-- Classification is chosen from the accepted actual-family universal property. -/
def classifier {S : Over (Base k)} (X : Object L S.left) : BaseMap k L A B V Q S :=
  ⟨(H.1.1 S.left S.hom X.family X.marking).choose,
    (H.1.1 S.left S.hom X.family X.marking).choose_spec.1.choose_spec.1.1⟩

def classifierCurve {S : Over (Base k)} (X : Object L S.left) :
    X.family.curve ⟶ A.descent.family.curve :=
  (H.1.1 S.left S.hom X.family X.marking).choose_spec.1.choose

lemma classifier_spec {S : Over (Base k)} (X : Object L S.left) :
    Classifies k L A B V Q S.hom X.family X.marking
      (classifier H X).val (classifierCurve H X) :=
  (H.1.1 S.left S.hom X.family X.marking).choose_spec.1.choose_spec.1

lemma classifier_arrow {S : Over (Base k)} {X Y : Object L S.left}
    (f : Arrow X Y) : classifier H X = classifier H Y := by
  apply Subtype.ext
  have h := H.1.2.2 S.left S.left S.hom S.hom Y.family X.family
    Y.marking X.marking (𝟙 S.left) f.curve.hom (Category.id_comp _) f.marked
    (classifier H Y).val (classifier H X).val
    (classifierCurve H Y) (classifierCurve H X) (classifier_spec H Y) (classifier_spec H X)
  simpa only [Category.id_comp] using h.1

lemma classifier_pull {S T : Over (Base k)} (a : T ⟶ S)
    (X : (group L S.left).Objects) :
    classifier H ((pull L a.left).functor.obj X) = mapBase k L A B V Q a (classifier H X) := by
  apply Subtype.ext
  exact (H.1.2.2 S.left T.left S.hom T.hom X.family
    ((pull L a.left).functor.obj X).family X.marking
    ((pull L a.left).functor.obj X).marking a.left ((pull L a.left).curve X)
    (Over.w a) ((pull L a.left).marked X)
    (classifier H X).val (classifier H ((pull L a.left).functor.obj X)).val
    (classifierCurve H X) (classifierCurve H ((pull L a.left).functor.obj X))
    (classifier_spec H X) (classifier_spec H ((pull L a.left).functor.obj X))).1

/-- Every transition of actual families identifies the pulled-back classifiers. -/
lemma classifier_transition (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (D : C.functor.DescentData (fun _ : Unit => q))
    {S : Over (Base k)} (p : S ⟶ T) (a b : S ⟶ U)
    (ha : a ≫ q = p) (hb : b ≫ q = p) :
    a.left ≫ (classifier H (D.obj ())).val =
      b.left ≫ (classifier H (D.obj ())).val := by
  have h := classifier_arrow H ((group L S.left).arrow _ _ (D.hom p (i₁ := ()) (i₂ := ()) a b ha hb))
  change classifier H ((pull L a.left).functor.obj (D.obj ())) =
    classifier H ((pull L b.left).functor.obj (D.obj ())) at h
  rw [classifier_pull, classifier_pull] at h
  exact congrArg Subtype.val h

/-- The varying classifying map itself descends along the fpqc cover.
No classifier on the target is supplied as a hypothesis. -/
lemma classifier_descends (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left)
    (D : C.functor.DescentData (fun _ : Unit => q)) :
    ∃! b : BaseMap k L A B V Q T,
      q.left ≫ b.val = (classifier H (D.obj ())).val := by
  letI := hq
  letI := hf
  letI := hs
  let c := classifier H (D.obj ())
  have hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ U.left),
      a ≫ q.left = b ≫ q.left → a ≫ c.val = b ≫ c.val := by
    intro Z a b hab
    let S : Over (Base k) := Over.mk (a ≫ U.hom)
    let a' : S ⟶ U := Over.homMk a rfl
    let b' : S ⟶ U := Over.homMk b (by
      dsimp [S]
      rw [← Over.w q, ← Category.assoc, ← Category.assoc, hab])
    exact classifier_transition H C q D (a' ≫ q) a' b' rfl (by
      apply Over.OverMorphism.ext
      exact hab.symm)
  let b := EffectiveEpi.desc q.left c.val hc
  have hb : q.left ≫ b = c.val := EffectiveEpi.fac q.left c.val hc
  have hk : b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = T.hom := by
    apply (cancel_epi q.left).1
    rw [← Category.assoc, hb, c.property, Over.w q]
  refine ⟨⟨b, hk⟩, hb, ?_⟩
  intro b' hb'
  apply Subtype.ext
  exact (cancel_epi q.left).1 (hb'.trans hb.symm)

include H in
/-- Fpqc pullback detects actual family arrows: line descent is combined with
full-level rigidity, so no curve component is discarded. -/
lemma pull_faithful {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    (pull L q.left).functor.Faithful := by
  letI := hq
  letI := hf
  letI := hs
  constructor
  intro X Y f g hfg
  apply NaturalComparisonProof.line_faithful H (group L T.left) f g
  apply ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.pullback_map_injective
    q.left X.root.line Y.root.line X.root.invertible Y.root.invertible
  apply (cancel_epi ((pull L q.left).line X).hom).1
  rw [← (pull L q.left).line_natural X Y f,
    ← (pull L q.left).line_natural X Y g, hfg]

include H in
lemma descent_faithful (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    (C.functor.toDescentData (fun _ : Unit => q)).Faithful := by
  letI := pull_faithful H q hq hf hs
  constructor
  intro X Y f g hfg
  apply (pull L q.left).functor.map_injective
  exact congrArg (fun t => t.hom ()) hfg

/-- The chosen classifier carries the uniquely normalized Hodge comparison. -/
def classifiedModel {S : Over (Base k)} (X : Object L S.left) :
    FiberEquivalenceProof.Model (classifier H X) where
  family := X.family
  marking := X.marking
  curve := classifierCurve H X
  classifies := classifier_spec H X
  hodge := (H.2.1 S.left S.hom X.family X.marking _ _ (classifier_spec H X)).choose
  canonical := (H.2.1 S.left S.hom X.family X.marking _ _ (classifier_spec H X)).choose_spec.1

/-- The actual specified root expressed over its own descended-classifier target. -/
def classifiedRoot {S : Over (Base k)} (X : Object L S.left) :
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber
      (ModularHodge k L A B V Q) (Over.mk (classifier H X).val) :=
  ⟨X.root.line, X.root.invertible, X.root.square ≪≫ (classifiedModel H X).hodge.symm⟩

/-- The specified line maps transport a family descent datum to module descent. -/
def lineTransformation (C : Coherence L (Base k)) :
    Pseudofunctor.StrongTrans C.functor
      (ArithmeticThetaRootStackR0198.modulesOver (Base k)) where
  app S := (lineForget (group L S.as.unop.left)).toCatHom
  naturality a := Cat.Hom.isoMk (linePull L (Base k) a.as.unop)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id S := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (𝟙 S.as.unop.left)).line X).hom ≫
      (Scheme.Modules.pullbackId S.as.unop.left).hom.app X.root.line =
      ((group L S.as.unop.left).arrow _ _
        ((C.unit S.as).hom.toNatTrans.app X)).line.hom ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact ((C.unit_normalized S.as.unop X).2).symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (g.as.unop.left ≫ f.as.unop.left)).line X).hom ≫
      (Scheme.Modules.pullbackComp g.as.unop.left f.as.unop.left).inv.app X.root.line =
      ((group L _).arrow _ _ ((C.comp f.as g.as).hom.toNatTrans.app X)).line.hom ≫
      𝟙 _ ≫ ((pull L g.as.unop.left).line ((pull L f.as.unop.left).functor.obj X)).hom ≫
      𝟙 _ ≫ (Scheme.Modules.pullback g.as.unop.left).map
        ((pull L f.as.unop.left).line X).hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact ((C.comp_normalized _ _ _ f.as.unop g.as.unop X).2).symm

/-- The full all-test module datum, retaining every root-line transition. -/
def lineDatum (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (D : C.functor.DescentData (fun _ : Unit => q)) :=
  ArithmeticThetaRootStackR0198.CategoricalRootDescentR0198.unsliceData
    (fun _ : Unit => q)
    ((ArithmeticThetaRootStackR0198.CategoricalRootDescentR0198.strongData
      (lineTransformation C) (fun _ : Unit => q)).obj D)

open ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower
open ArithmeticThetaCoverComparison ArithmeticThetaMetaplecticTestsR0196

/-- Express a specified cotangent root on a classified family as a Hodge root. -/
def modelRoot {S : Over (Base k)} {b : BaseMap k L A B V Q S}
    (m : FiberEquivalenceProof.Model b) (J : SquareLine S.left (Cotangent m.family)) :
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber
      (ModularHodge k L A B V Q) (Over.mk b.val) :=
  ⟨J.line, J.invertible, J.square ≪≫ m.hodge.symm⟩

include H in
/-- The actual arrow's canonical cotangent map identifies the two normalized
Hodge maps. In particular, every sign in its line map remains visible. -/
lemma model_arrow_square {S : Over (Base k)} {b : BaseMap k L A B V Q S}
    (m n : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family))
    (K : SquareLine S.left (Cotangent n.family))
    (f : Arrow ⟨m.family, m.marking, J⟩ ⟨n.family, n.marking, K⟩) :
    tensorPowerMap f.line.hom 2 ≫ (modelRoot n K).square.hom =
      (modelRoot m J).square.hom := by
  have hc := H.1.2.2 S.left S.left S.hom S.hom n.family m.family
    n.marking m.marking (𝟙 S.left) f.curve.hom (Category.id_comp _) f.marked
    b.val b.val n.curve m.curve n.classifies m.classifies
  have hd := FiberEquivalenceProof.hodge_backward H n m f.curve.hom f.marked hc.2.symm
  rw [← ActualGroupoidProof.arrow_backward f] at hd
  have hi : f.cotangent.hom ≫ n.hodge.inv = m.hodge.inv := by
    apply (cancel_epi m.hodge.hom).1
    calc
      m.hodge.hom ≫ (f.cotangent.hom ≫ n.hodge.inv) =
          (n.hodge.hom ≫ f.cotangent.inv) ≫ (f.cotangent.hom ≫ n.hodge.inv) :=
        congrArg (fun t => t ≫ (f.cotangent.hom ≫ n.hodge.inv)) hd.symm
      _ = m.hodge.hom ≫ m.hodge.inv := by simp
  change tensorPowerMap f.line.hom 2 ≫ (K.square.hom ≫ n.hodge.inv) =
    J.square.hom ≫ m.hodge.inv
  calc
    _ = (tensorPowerMap f.line.hom 2 ≫ K.square.hom) ≫ n.hodge.inv :=
      (Category.assoc _ _ _).symm
    _ = (J.square.hom ≫ f.cotangent.hom) ≫ n.hodge.inv :=
      congrArg (fun t => t ≫ n.hodge.inv) f.square
    _ = _ := by simp only [Category.assoc, hi]

/-- Full and faithful root-arrow transport over a common classifier. -/
def modelHomEquiv (hL : 3 ≤ L) (heven : Even L)
    {S : Over (Base k)} (G : GroupoidData L S.left)
    {b : BaseMap k L A B V Q S} (m n : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family))
    (K : SquareLine S.left (Cotangent n.family)) :
    (@Quiver.Hom G.Objects _ ⟨m.family, m.marking, J⟩ ⟨n.family, n.marking, K⟩) ≃
      SquareIso (modelRoot m J) (modelRoot n K) :=
  Equiv.ofBijective
    (fun f => ⟨(G.arrow _ _ f).line, model_arrow_square H m n J K (G.arrow _ _ f)⟩)
    (by
      constructor
      · intro f g hfg
        apply NaturalComparisonProof.line_faithful H G f g
        exact congrArg (fun e => e.val.hom) hfg
      · intro e
        obtain ⟨f, hf⟩ := NaturalComparisonProof.arrow_of_square hL heven H m n J K
          e.val e.property
        refine ⟨(G.arrow _ _).symm f, ?_⟩
        apply Subtype.ext
        apply Iso.ext
        simpa only [Equiv.apply_symm_apply] using hf)

/-- Base change of a classified actual object, with its canonical Hodge map. -/
def pulledModel {S T : Over (Base k)} (a : T ⟶ S)
    {b : BaseMap k L A B V Q S} (m : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family)) :
    FiberEquivalenceProof.Model (mapBase k L A B V Q a b) := by
  let X : (group L S.left).Objects := ⟨m.family, m.marking, J⟩
  let Z := (pull L a.left).functor.obj X
  have hc : Classifies k L A B V Q T.hom Z.family Z.marking
      (a.left ≫ b.val) ((pull L a.left).curve X ≫ m.curve) :=
    SchemeFullLevelUniversal.classifies_comp A (Over.w a) ((pull L a.left).marked X)
      m.classifies
  exact ⟨Z.family, Z.marking, (pull L a.left).curve X ≫ m.curve, hc,
    (H.2.1 T.left T.hom Z.family Z.marking _ _ hc).choose,
    (H.2.1 T.left T.hom Z.family Z.marking _ _ hc).choose_spec.1⟩

lemma pulledModel_natural {S T : Over (Base k)} (a : T ⟶ S)
    {b : BaseMap k L A B V Q S} (m : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family)) :
    (Scheme.Modules.pullback a.left).map m.hodge.hom ≫
        ((pull L a.left).cotangent ⟨m.family, m.marking, J⟩).hom =
      (Scheme.Modules.pullbackComp a.left b.val).hom.app (ModularHodge k L A B V Q) ≫
        (pulledModel H a m J).hodge.hom :=
  H.2.2 S.left T.left m.family ((pulledModel H a m J).family) a.left
    ((pull L a.left).curve ⟨m.family, m.marking, J⟩)
    ((pull L a.left).marked ⟨m.family, m.marking, J⟩).2.1 b.val m.curve
    m.hodge (pulledModel H a m J).hodge
    ((pull L a.left).cotangent ⟨m.family, m.marking, J⟩)
    m.canonical (pulledModel H a m J).canonical
    ((pull L a.left).canonical ⟨m.family, m.marking, J⟩)

/-- The root-side base-change leg retains the original geometric map. -/
def rootLeg {S T : Over (Base k)} (a : T ⟶ S) (b : BaseMap k L A B V Q S) :
    Over.mk (mapBase k L A B V Q a b).val ⟶ Over.mk b.val :=
  Over.homMk a.left rfl

/-- Comparison of classified roots under base change, with the exact line map
from the actual family pullback. -/
def modelPullIso {S T : Over (Base k)} (a : T ⟶ S)
    {b : BaseMap k L A B V Q S} (m : FiberEquivalenceProof.Model b)
    (J : SquareLine S.left (Cotangent m.family)) :
    SquareIso
      (modelRoot (pulledModel H a m J)
        ((pull L a.left).functor.obj ⟨m.family, m.marking, J⟩).root)
      (ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.pullObj
        (rootLeg a b) (modelRoot m J)) := by
  let X : (group L S.left).Objects := ⟨m.family, m.marking, J⟩
  let P := pull L a.left
  let n := pulledModel H a m J
  refine ⟨P.line X, ?_⟩
  have hn := pulledModel_natural H a m J
  have hi : (Scheme.Modules.pullback a.left).map m.hodge.inv ≫
        (Scheme.Modules.pullbackComp a.left b.val).hom.app (ModularHodge k L A B V Q) =
      (P.cotangent X).hom ≫ n.hodge.inv := by
    apply (cancel_epi ((Scheme.Modules.pullback a.left).map m.hodge.hom)).1
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id, Category.id_comp]
    rw [hn]
    dsimp only [n]
    erw [(Scheme.Modules.pullback a.left).map_id]
    simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change tensorPowerMap (P.line X).hom 2 ≫
    (((squarePull a.left (modelRoot m J)).hom ≫
      (Scheme.Modules.pullbackComp a.left b.val).hom.app _) ≫
      (Scheme.Modules.pullbackCongr (show a.left ≫ b.val = a.left ≫ b.val from rfl)).hom.app _) =
    ((P.functor.obj X).root.square.hom ≫ n.hodge.inv)
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]
  have hp : (squarePull a.left (modelRoot m J)).hom =
      (squarePull a.left J).hom ≫ (Scheme.Modules.pullback a.left).map m.hodge.inv := by
    simp only [squarePull, modelRoot, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
  rw [hp]
  simp only [Category.assoc]
  rw [hi]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ n.hodge.inv) (P.square X)

/-- The specific structural map of the compatible quotient to the field base. -/
abbrev quotientStructure : Base Q.quotient.ring ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring))

abbrev quotientToBase : Over (Base Q.quotient.ring) ⥤ Over (Base k) :=
  Over.map (quotientStructure (Q := Q))

/-- Restrict the given coherent actual pullback along the specific quotient map. -/
def quotientCoherence (C : Coherence L (Base k)) : Coherence L (Base Q.quotient.ring) where
  unit S := C.unit ((quotientToBase (Q := Q)).op.obj S)
  comp f g := C.comp ((quotientToBase (Q := Q)).op.map f) ((quotientToBase (Q := Q)).op.map g)
  unit_normalized S := C.unit_normalized ((quotientToBase (Q := Q)).obj S)
  comp_normalized S T U a b := C.comp_normalized _ _ _
    ((quotientToBase (Q := Q)).map a) ((quotientToBase (Q := Q)).map b)
  associativity f g h := C.associativity ((quotientToBase (Q := Q)).op.map f)
    ((quotientToBase (Q := Q)).op.map g) ((quotientToBase (Q := Q)).op.map h)
  left_unit f := C.left_unit ((quotientToBase (Q := Q)).op.map f)
  right_unit f := C.right_unit ((quotientToBase (Q := Q)).op.map f)

/-- Actual families on the quotient slice; their curve and root data are unchanged. -/
abbrev quotientFamilies (C : Coherence L (Base k)) := (quotientCoherence (Q := Q) C).functor

/-- This is the actual classifier equality, not an unspecified property field. -/
def fixedClassifier (C : Coherence L (Base k)) :
    (quotientFamilies (Q := Q) C).ObjectProperty where
  prop S X := (classifier H (S := (quotientToBase (Q := Q)).obj S.as.unop) X).val =
    S.as.unop.hom

instance fixedClassifier_closed (C : Coherence L (Base k)) :
    (fixedClassifier H C).IsClosedUnderMapObj where
  map_obj {X Y} {M} hM f := by
    change (classifier H (S := (quotientToBase (Q := Q)).obj Y.as.unop)
      ((pull L f.as.unop.left).functor.obj M)).val = Y.as.unop.hom
    have hn := congrArg Subtype.val
      (classifier_pull H ((quotientToBase (Q := Q)).map f.as.unop) M)
    change (classifier H (S := (quotientToBase (Q := Q)).obj Y.as.unop)
      ((pull L f.as.unop.left).functor.obj M)).val =
      f.as.unop.left ≫ (classifier H (S := (quotientToBase (Q := Q)).obj X.as.unop) M).val at hn
    exact hn.trans ((congrArg (fun t => f.as.unop.left ≫ t) hM).trans (Over.w f.as.unop))

abbrev fixedFamilies (C : Coherence L (Base k)) := (fixedClassifier H C).fullsubcategory

/-- Normalize the actual Hodge comparison at the specified classifier. -/
def fixedModel (C : Coherence L (Base k)) (S : Over (Base Q.quotient.ring))
    (X : (fixedFamilies H C).obj (.mk (.op S))) :
    FiberEquivalenceProof.Model
      (⟨S.hom, rfl⟩ : BaseMap k L A B V Q ((quotientToBase (Q := Q)).obj S)) := by
  have hc : Classifies k L A B V Q ((quotientToBase (Q := Q)).obj S).hom
      X.obj.family X.obj.marking S.hom (classifierCurve H (S := (quotientToBase (Q := Q)).obj S) X.obj) := by
    have hh := classifier_spec H (S := (quotientToBase (Q := Q)).obj S) X.obj
    have hx : (classifier H (S := (quotientToBase (Q := Q)).obj S) X.obj).val = S.hom := X.property
    exact hx ▸ hh
  exact ⟨X.obj.family, X.obj.marking, classifierCurve H (S := (quotientToBase (Q := Q)).obj S) X.obj, hc,
    (H.2.1 S.left ((quotientToBase (Q := Q)).obj S).hom X.obj.family X.obj.marking _ _ hc).choose,
    (H.2.1 S.left ((quotientToBase (Q := Q)).obj S).hom X.obj.family X.obj.marking _ _ hc).choose_spec.1⟩

/-- Forget only the classifier proof and then the actual curve data. -/
def fixedLine (C : Coherence L (Base k)) (S : Over (Base Q.quotient.ring)) :
    (fixedFamilies H C).obj (.mk (.op S)) ⥤ S.left.Modules :=
  ((fixedClassifier H C).prop (.mk (.op S))).ι ⋙ lineForget (group L S.left)

def fixedLinePull (C : Coherence L (Base k))
    {S T : Over (Base Q.quotient.ring)} (a : T ⟶ S) :
    ((fixedFamilies H C).map a.op.toLoc).toFunctor ⋙ fixedLine H C T ≅
      fixedLine H C S ⋙ Scheme.Modules.pullback a.left :=
  NatIso.ofComponents (fun X => (pull L a.left).line X.obj)
    (fun f => (pull L a.left).line_natural _ _ f.hom)

/-- The canonical line comparison on actual families with fixed classifier. -/
def fixedLineTransformation (C : Coherence L (Base k)) :
    Pseudofunctor.StrongTrans (fixedFamilies H C)
      (ArithmeticThetaRootStackR0198.modulesOver (Base Q.quotient.ring)) where
  app S := (fixedLine H C S.as.unop).toCatHom
  naturality a := Cat.Hom.isoMk (fixedLinePull H C a.as.unop)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id S := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (𝟙 S.as.unop.left)).line X.obj).hom ≫
      (Scheme.Modules.pullbackId S.as.unop.left).hom.app X.obj.root.line =
      ((group L S.as.unop.left).arrow _ _
        ((C.unit (.op ((quotientToBase (Q := Q)).obj S.as.unop))).hom.toNatTrans.app X.obj)).line.hom ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact ((C.unit_normalized ((quotientToBase (Q := Q)).obj S.as.unop) X.obj).2).symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (g.as.unop.left ≫ f.as.unop.left)).line X.obj).hom ≫
      (Scheme.Modules.pullbackComp g.as.unop.left f.as.unop.left).inv.app X.obj.root.line =
      ((group L _).arrow _ _
        ((C.comp ((quotientToBase (Q := Q)).map f.as.unop).op
          ((quotientToBase (Q := Q)).map g.as.unop).op).hom.toNatTrans.app X.obj)).line.hom ≫
      𝟙 _ ≫ ((pull L g.as.unop.left).line ((pull L f.as.unop.left).functor.obj X.obj)).hom ≫
      𝟙 _ ≫ (Scheme.Modules.pullback g.as.unop.left).map
        ((pull L f.as.unop.left).line X.obj).hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact ((C.comp_normalized _ _ _ ((quotientToBase (Q := Q)).map f.as.unop)
      ((quotientToBase (Q := Q)).map g.as.unop) X.obj).2).symm

/-- Actual families with fixed classifier and their normalized square maps. -/
def fixedDiagram (C : Coherence L (Base k)) :
    ArithmeticThetaRootStackR0198.RootDiagram (Base Q.quotient.ring) (ModularHodge k L A B V Q) where
  functor := fixedFamilies H C
  forget := fixedLineTransformation H C
  invertible _ X := X.obj.root.invertible
  square S X := X.obj.root.square ≪≫ (fixedModel H C S X).hodge.symm

include H in
/-- Hodge naturality with the actual target classifier equality retained. -/
lemma hodge_natural_general {S T : Scheme.{0}} (E : Family S) (F : Family T)
    (a : T ⟶ S) (g : F.curve ⟶ E.curve) (hg : F.zero ≫ g = a ≫ E.zero)
    (b : S ⟶ Base Q.quotient.ring) (c : T ⟶ Base Q.quotient.ring) (hc : a ≫ b = c)
    (f : E.curve ⟶ A.descent.family.curve) (t : F.curve ⟶ A.descent.family.curve)
    (ht : g ≫ f = t)
    (eE : (Scheme.Modules.pullback b).obj (ModularHodge k L A B V Q) ≅ Cotangent E)
    (eF : (Scheme.Modules.pullback c).obj (ModularHodge k L A B V Q) ≅ Cotangent F)
    (eG : (Scheme.Modules.pullback a).obj (Cotangent E) ≅ Cotangent F)
    (hE : ClassifierHodge k L A B V Q E b f eE)
    (hF : ClassifierHodge k L A B V Q F c t eF)
    (hG : CotangentCompatible E F a g hg eG) :
    (Scheme.Modules.pullback a).map eE.hom ≫ eG.hom =
      (Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr hc).hom.app
        (ModularHodge k L A B V Q) ≫ eF.hom := by
  subst c
  subst t
  simpa [Scheme.Modules.pullbackCongr] using
    H.2.2 S T E F a g hg b f eE eF eG hE hF hG

lemma fixed_square_natural (C : Coherence L (Base k)) :
    ArithmeticThetaRootStackR0198.SquareNatural (fixedDiagram H C) := by
  intro S T f X
  let Y := ((fixedFamilies H C).map f.op.toLoc).toFunctor.obj X
  let m := fixedModel H C T X
  let n := fixedModel H C S Y
  let P := pull L f.left
  have hc := H.1.2.2 T.left S.left ((quotientToBase (Q := Q)).obj T).hom
    ((quotientToBase (Q := Q)).obj S).hom X.obj.family Y.obj.family
    X.obj.marking Y.obj.marking f.left (P.curve X.obj)
    (Over.w ((quotientToBase (Q := Q)).map f)) (P.marked X.obj)
    T.hom S.hom m.curve n.curve m.classifies n.classifies
  have hn := hodge_natural_general H X.obj.family Y.obj.family f.left (P.curve X.obj)
    (P.marked X.obj).2.1 T.hom S.hom (Over.w f) m.curve n.curve hc.2.symm
    m.hodge n.hodge (P.cotangent X.obj) m.canonical n.canonical (P.canonical X.obj)
  have hi : (Scheme.Modules.pullback f.left).map m.hodge.inv ≫
      (Scheme.Modules.pullbackComp f.left T.hom).hom.app (ModularHodge k L A B V Q) ≫
      (Scheme.Modules.pullbackCongr (Over.w f)).hom.app (ModularHodge k L A B V Q) =
      (P.cotangent X.obj).hom ≫ n.hodge.inv := by
    apply (cancel_epi ((Scheme.Modules.pullback f.left).map m.hodge.hom)).1
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    erw [(Scheme.Modules.pullback f.left).map_id]
    simp only [Category.id_comp]
    rw [hn]
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  change tensorPowerMap (P.line X.obj).hom 2 ≫
      (squarePull f.left (modelRoot m X.obj.root)).hom ≫
      (Scheme.Modules.pullbackComp f.left T.hom).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (Over.w f)).hom.app _ =
      Y.obj.root.square.hom ≫ n.hodge.inv
  have hp : (squarePull f.left (modelRoot m X.obj.root)).hom =
      (squarePull f.left X.obj.root).hom ≫
        (Scheme.Modules.pullback f.left).map m.hodge.inv := by
    simp only [squarePull, modelRoot, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
  rw [hp]
  simp only [Category.assoc]
  rw [hi]
  change _ = (P.functor.obj X.obj).root.square.hom ≫ n.hodge.inv
  simpa only [Category.assoc] using congrArg (fun t => t ≫ n.hodge.inv) (P.square X.obj)

/-- No arrows are discarded by fixing the classifier. -/
def fixedHomEquiv (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k))
    (S : Over (Base Q.quotient.ring)) (X Y : (fixedFamilies H C).obj (.mk (.op S))) :
    (X ⟶ Y) ≃ ArithmeticThetaMetaplecticTestsR0196.SquareIso
      (ArithmeticThetaRootStackR0198.root (fixedDiagram H C) S X)
      (ArithmeticThetaRootStackR0198.root (fixedDiagram H C) S Y) :=
  (((fixedClassifier H C).prop (.mk (.op S))).fullyFaithfulι.homEquiv).trans
    (modelHomEquiv H hL heven (group L S.left) (fixedModel H C S X) (fixedModel H C S Y)
      X.obj.root Y.obj.root)

/-- Invertibility is inherited from the actual universal elliptic-family Hodge sheaf. -/
lemma modularHodge_invertible : Scheme.Modules.IsInvertible (ModularHodge k L A B V Q) := by
  exact (ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180.hodge_invertible
    A.descent.family).pullback Q.inclusion

/-- Every specified Hodge root is realized by an actual classified family. -/
lemma fixed_essentially_surjective (C : Coherence L (Base k))
    (S : Over (Base Q.quotient.ring))
    (J : SquareLine S.left ((Scheme.Modules.pullback S.hom).obj (ModularHodge k L A B V Q))) :
    ∃ X : (fixedFamilies H C).obj (.mk (.op S)),
      Nonempty (SquareIso (ArithmeticThetaRootStackR0198.root (fixedDiagram H C) S X) J) := by
  let Sbase := (quotientToBase (Q := Q)).obj S
  let b : BaseMap k L A B V Q Sbase := ⟨S.hom, rfl⟩
  let m := FiberEquivalenceProof.model H b
  let X₀ : (group L S.left).Objects := FiberEquivalenceProof.obj m J
  have hc := H.1.2.2 S.left S.left Sbase.hom Sbase.hom m.family m.family
    m.marking m.marking (𝟙 S.left) (𝟙 m.family.curve) (Category.id_comp _)
    (ActualGroupoidProof.marked_id X₀)
    b.val (classifier H (S := Sbase) X₀).val m.curve (classifierCurve H (S := Sbase) X₀)
    m.classifies (classifier_spec H (S := Sbase) X₀)
  have hx : (classifier H (S := Sbase) X₀).val = S.hom := by
    simpa only [Category.id_comp] using hc.1
  let X : (fixedFamilies H C).obj (.mk (.op S)) := ⟨X₀, hx⟩
  let n := fixedModel H C S X
  have hh := model_arrow_square H n m X₀.root X₀.root (ActualGroupoidProof.identity X₀)
  have hm : (modelRoot m X₀.root).square.hom = J.square.hom := by
    change (J.square.hom ≫ m.hodge.hom) ≫ m.hodge.inv = J.square.hom
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨X, ⟨⟨Iso.refl _, ?_⟩⟩⟩
  change tensorPowerMap (𝟙 J.line) 2 ≫ J.square.hom = (modelRoot n X₀.root).square.hom
  change tensorPowerMap (𝟙 J.line) 2 ≫ (modelRoot m X₀.root).square.hom =
    (modelRoot n X₀.root).square.hom at hh
  simpa only [hm] using hh

/-- A faithful presentation by actual families with the specified classifier. -/
def fixedPresentation (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k)) :
    ArithmeticThetaRootStackR0198.Presentation (Base Q.quotient.ring) (ModularHodge k L A B V Q) where
  toRootDiagram := fixedDiagram H C
  groupoid S := by
    let P := (fixedClassifier H C).prop (.mk (.op S))
    letI := P.fullyFaithfulι.reflectsIsomorphisms
    letI : IsGroupoid ((quotientFamilies (Q := Q) C).obj (.mk (.op S))) :=
      inferInstanceAs (IsGroupoid (group L S.left).Objects)
    exact isGroupoid_of_reflects_iso P.ι
  square_natural := fixed_square_natural H C
  homEquiv := fixedHomEquiv H hL heven C
  hom_eq _ _ _ _ := rfl
  essentially_surjective := fixed_essentially_surjective H C

/-- Reuse categorical fpqc root descent for the actual classified-family presentation. -/
lemma fixed_singleton_descent (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k)) :
    ArithmeticThetaRootStackR0198.SingletonDescent (fixedFamilies H C) :=
  ArithmeticThetaRootStackR0198.categorical_fpqc_root_descent _ _
    (modularHodge_invertible (A := A) (B := B) (V := V) (Q := Q))
    (fixedPresentation H hL heven C)

/-- Restrict an actual-family datum to tests over its descended classifier. -/
def fixedLiftData (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    (D : C.functor.DescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q))
    (hD : (classifier H (S := (quotientToBase (Q := Q)).obj U) (D.obj ())).val = U.hom) :
    (fixedFamilies H C).DescentData (fun _ : Unit => q) where
  obj i := ⟨D.obj i, by cases i; exact hD⟩
  hom S p i j a b ha hb := ObjectProperty.homMk
    (D.hom ((quotientToBase (Q := Q)).map p) (i₁ := i) (i₂ := j)
      ((quotientToBase (Q := Q)).map a) ((quotientToBase (Q := Q)).map b)
      (by rw [← Functor.map_comp, ha]) (by rw [← Functor.map_comp, hb]))
  hom_self S p i a ha := by
    apply ObjectProperty.hom_ext
    exact D.hom_self ((quotientToBase (Q := Q)).map p) (i := i)
      ((quotientToBase (Q := Q)).map a) (by rw [← Functor.map_comp, ha])
  hom_comp S p i j l a b c ha hb hc := by
    apply ObjectProperty.hom_ext
    exact D.hom_comp ((quotientToBase (Q := Q)).map p) (i₁ := i) (i₂ := j) (i₃ := l)
      ((quotientToBase (Q := Q)).map a) ((quotientToBase (Q := Q)).map b)
      ((quotientToBase (Q := Q)).map c)
      (by rw [← Functor.map_comp, ha]) (by rw [← Functor.map_comp, hb])
      (by rw [← Functor.map_comp, hc])
  pullHom_hom S' S g p p' hp i j a b ha hb ga gb hga hgb := by
    apply ObjectProperty.hom_ext
    exact D.pullHom_hom ((quotientToBase (Q := Q)).map g)
      ((quotientToBase (Q := Q)).map p) ((quotientToBase (Q := Q)).map p')
      (by rw [← Functor.map_comp, hp]) (i₁ := i) (i₂ := j)
      ((quotientToBase (Q := Q)).map a) ((quotientToBase (Q := Q)).map b)
      (by rw [← Functor.map_comp, ha]) (by rw [← Functor.map_comp, hb])
      ((quotientToBase (Q := Q)).map ga) ((quotientToBase (Q := Q)).map gb)
      (by rw [← Functor.map_comp, hga]) (by rw [← Functor.map_comp, hgb])

/-- Restrict all component arrows, without changing their actual curve or line maps. -/
def fixedLiftHom (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    {D E : C.functor.DescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)}
    (hD : (classifier H (S := (quotientToBase (Q := Q)).obj U) (D.obj ())).val = U.hom)
    (hE : (classifier H (S := (quotientToBase (Q := Q)).obj U) (E.obj ())).val = U.hom)
    (φ : D ⟶ E) : fixedLiftData H C q D hD ⟶ fixedLiftData H C q E hE where
  hom i := ObjectProperty.homMk (φ.hom i)
  comm S p i j a b ha hb := by
    apply ObjectProperty.hom_ext
    exact φ.comm ((quotientToBase (Q := Q)).map p) (i₁ := i) (i₂ := j)
      ((quotientToBase (Q := Q)).map a) ((quotientToBase (Q := Q)).map b)
      (by rw [← Functor.map_comp, ha]) (by rw [← Functor.map_comp, hb])

lemma fixed_canonical_property (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    (X : (fixedFamilies H C).obj (.mk (.op T))) :
    (classifier H (S := (quotientToBase (Q := Q)).obj U)
      (((C.functor.toDescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)).obj X.obj).obj ())).val = U.hom :=
  (((fixedFamilies H C).map q.op.toLoc).toFunctor.obj X).property

/-- The restricted canonical datum is the canonical restricted-family datum. -/
def fixedCanonicalIso (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    (X : (fixedFamilies H C).obj (.mk (.op T))) :
    ((fixedFamilies H C).toDescentData (fun _ : Unit => q)).obj X ≅
      fixedLiftData H C q
        ((C.functor.toDescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)).obj X.obj)
        (fixed_canonical_property H C q X) :=
  Pseudofunctor.DescentData.isoMk (fun _ => Iso.refl _) (by
    intro S p i j a b ha hb
    apply ObjectProperty.hom_ext
    change (pull L a.left).functor.map (𝟙 ((pull L q.left).functor.obj X.obj)) ≫ _ =
      _ ≫ (pull L b.left).functor.map (𝟙 ((pull L q.left).functor.obj X.obj))
    erw [(pull L a.left).functor.map_id, (pull L b.left).functor.map_id]
    simp only [Category.id_comp, Category.comp_id]
    rfl)

/-- A morphism seen on quotient tests already commutes on every field-base test:
the map of such a test to the quotient is forced by its map to the target. -/
def reflectFixedHom (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    {D E : C.functor.DescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)}
    (hD : (classifier H (S := (quotientToBase (Q := Q)).obj U) (D.obj ())).val = U.hom)
    (hE : (classifier H (S := (quotientToBase (Q := Q)).obj U) (E.obj ())).val = U.hom)
    (φ : fixedLiftData H C q D hD ⟶ fixedLiftData H C q E hE) : D ⟶ E where
  hom i := (φ.hom i).hom
  comm S p i j a b ha hb := by
    rcases S with ⟨S, ⟨⟨⟩⟩, s⟩
    rcases p with ⟨p, pr, hp⟩
    change S ⟶ Base k at s
    change S ⟶ T.left at p
    have hp' := Over.w
      (show Over.mk s ⟶ (quotientToBase (Q := Q)).obj T from ⟨p, pr, hp⟩)
    change p ≫ (T.hom ≫ quotientStructure (Q := Q)) = s at hp'
    rw [← Category.assoc] at hp'
    subst s
    let Z : Over (Base Q.quotient.ring) := Over.mk (p ≫ T.hom)
    let p' : Z ⟶ T := Over.homMk p rfl
    have ha' : a.left ≫ q.left = p := congrArg Over.Hom.left ha
    have hb' : b.left ≫ q.left = p := congrArg Over.Hom.left hb
    let a' : Z ⟶ U := Over.homMk a.left (by
      dsimp [Z]
      exact (congrArg (fun t => a.left ≫ t) (Over.w q).symm).trans
        ((Category.assoc a.left q.left T.hom).symm.trans
          (congrArg (fun t => t ≫ T.hom) ha')))
    let b' : Z ⟶ U := Over.homMk b.left (by
      dsimp [Z]
      exact (congrArg (fun t => b.left ≫ t) (Over.w q).symm).trans
        ((Category.assoc b.left q.left T.hom).symm.trans
          (congrArg (fun t => t ≫ T.hom) hb')))
    have h := congrArg InducedCategory.Hom.hom
      (φ.comm p' (i₁ := i) (i₂ := j) a' b'
        (by apply Over.OverMorphism.ext; exact ha')
        (by apply Over.OverMorphism.ext; exact hb'))
    exact h

/-- Effective actual-family descent after the classifier has descended. -/
lemma classified_effective (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left)
    (D : C.functor.DescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q))
    (hD : (classifier H (S := (quotientToBase (Q := Q)).obj U) (D.obj ())).val = U.hom) :
    ∃ X : C.functor.obj (.mk (.op ((quotientToBase (Q := Q)).obj T))),
      Nonempty (((C.functor.toDescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)).obj X) ≅ D) := by
  let F := (fixedFamilies H C).toDescentData (fun _ : Unit => q)
  letI : F.IsEquivalence := fixed_singleton_descent H hL heven C T U q hq hf hs
  obtain ⟨X, ⟨e⟩⟩ := CategoryTheory.Functor.EssSurj.mem_essImage F (fixedLiftData H C q D hD)
  let ψ := reflectFixedHom H C q (fixed_canonical_property H C q X) hD
    ((fixedCanonicalIso H C q X).inv ≫ e.hom)
  letI : IsGroupoid (C.functor.obj (.mk (.op ((quotientToBase (Q := Q)).obj U)))) :=
    inferInstanceAs (IsGroupoid (group L U.left).Objects)
  refine ⟨X.obj, ⟨Pseudofunctor.DescentData.isoMk (fun i => asIso (ψ.hom i)) ?_⟩⟩
  intro S p i j a b ha hb
  exact ψ.comm p a b ha hb

/-- Every descent arrow between globally classified families descends. -/
lemma classified_full (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k))
    {T U : Over (Base Q.quotient.ring)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left)
    (X Y : (fixedFamilies H C).obj (.mk (.op T)))
    (t : (C.functor.toDescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)).obj X.obj ⟶
      (C.functor.toDescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)).obj Y.obj) :
    ∃ f : X.obj ⟶ Y.obj,
      (C.functor.toDescentData (fun _ : Unit => (quotientToBase (Q := Q)).map q)).map f = t := by
  let F := (fixedFamilies H C).toDescentData (fun _ : Unit => q)
  letI : F.IsEquivalence := fixed_singleton_descent H hL heven C T U q hq hf hs
  let η := (fixedCanonicalIso H C q X).hom ≫
    fixedLiftHom H C q (fixed_canonical_property H C q X) (fixed_canonical_property H C q Y) t ≫
      (fixedCanonicalIso H C q Y).inv
  let f := F.preimage η
  refine ⟨f.hom, ?_⟩
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  have hh := congrArg (fun r => (r.hom i).hom) (F.map_preimage η)
  change (pull L q.left).functor.map f.hom = _
  change (pull L q.left).functor.map f.hom = 𝟙 _ ≫ t.hom i ≫ 𝟙 _ at hh
  simpa only [Category.id_comp, Category.comp_id] using hh

lemma over_hom_heq {S T S' T' : Over (Base k)} (hS : S = S') (hT : T = T')
    (f : S ⟶ T) (g : S' ⟶ T') (h : HEq f.left g.left) : HEq f g := by
  subst S'
  subst T'
  exact heq_of_eq (Over.OverMorphism.ext (eq_of_heq h))

/-- Present the same original cover over its descended classifier. The displayed
heterogeneous equalities retain the original schemes and morphism. -/
lemma normalizeCover {T U : Over (Base k)} (q : U ⟶ T)
    (b : BaseMap k L A B V Q T) (c : BaseMap k L A B V Q U)
    (hc : q.left ≫ b.val = c.val) :
    ∃ (T' U' : Over (Base Q.quotient.ring)) (q' : U' ⟶ T')
      (hT : (quotientToBase (Q := Q)).obj T' = T)
      (hU : (quotientToBase (Q := Q)).obj U' = U),
      HEq ((quotientToBase (Q := Q)).map q') q ∧
        HEq T'.hom b.val ∧ HEq U'.hom c.val := by
  let T' : Over (Base Q.quotient.ring) := Over.mk b.val
  let U' : Over (Base Q.quotient.ring) := Over.mk c.val
  let q' : U' ⟶ T' := Over.homMk q.left hc
  have hT : (quotientToBase (Q := Q)).obj T' = T := by
    refine CostructuredArrow.obj_ext ((quotientToBase (Q := Q)).obj T') T rfl ?_
    change 𝟙 T.left ≫ T.hom = b.val ≫ quotientStructure (Q := Q)
    exact (Category.id_comp _).trans b.property.symm
  have hU : (quotientToBase (Q := Q)).obj U' = U := by
    refine CostructuredArrow.obj_ext ((quotientToBase (Q := Q)).obj U') U rfl ?_
    change 𝟙 U.left ≫ U.hom = c.val ≫ quotientStructure (Q := Q)
    exact (Category.id_comp _).trans c.property.symm
  exact ⟨T', U', q', hT, hU, over_hom_heq hU hT _ _ HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- A locally existing actual arrow forces equality of the global classifiers. -/
lemma classifier_of_pull_arrow {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left)
    (X Y : (group L T.left).Objects)
    (f : (pull L q.left).functor.obj X ⟶ (pull L q.left).functor.obj Y) :
    classifier H (S := T) X = classifier H (S := T) Y := by
  letI := hq
  letI := hf
  letI := hs
  apply Subtype.ext
  apply (cancel_epi q.left).1
  have h := classifier_arrow H (S := U) ((group L U.left).arrow _ _ f)
  rw [classifier_pull H q X, classifier_pull H q Y] at h
  exact congrArg Subtype.val h

include H in
/-- Descend every actual object, including its varying classifier. -/
lemma actual_essSurj (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    (C.functor.toDescentData (fun _ : Unit => q)).EssSurj := by
  constructor
  intro D
  obtain ⟨b, hb, _⟩ := classifier_descends H C q hq hf hs D
  obtain ⟨T', U', q', hT, hU, hq', _, hclass⟩ :=
    normalizeCover q b (classifier H (S := U) (D.obj ())) hb
  subst T
  subst U
  have hqq := eq_of_heq hq'
  subst q
  exact classified_effective H hL heven C q' hq hf hs D (eq_of_heq hclass).symm

include H in
/-- Descend every actual arrow; local existence forces a common global classifier. -/
lemma actual_full (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    (C.functor.toDescentData (fun _ : Unit => q)).Full := by
  constructor
  intro X Y t
  have hXY := classifier_of_pull_arrow H q hq hf hs X Y (t.hom ())
  let b := classifier H (S := T) X
  obtain ⟨T', U', q', hT, hU, hq', hbase, _⟩ :=
    normalizeCover q b (mapBase k L A B V Q q b) rfl
  subst T
  subst U
  have hqq := eq_of_heq hq'
  subst q
  have hx : (classifier H (S := (quotientToBase (Q := Q)).obj T') X).val = T'.hom :=
    (eq_of_heq hbase).symm
  have hy : (classifier H (S := (quotientToBase (Q := Q)).obj T') Y).val = T'.hom :=
    (congrArg Subtype.val hXY.symm).trans hx
  let X' : (fixedFamilies H C).obj (.mk (.op T')) := ⟨X, hx⟩
  let Y' : (fixedFamilies H C).obj (.mk (.op T')) := ⟨Y, hy⟩
  exact classified_full H hL heven C q' hq hf hs X' Y' t

/-- One actual Legendre atlas and one compatible quotient supply all classifiers. -/
structure Provider (k : Type) [Field k] [CharZero k] (L : ℕ) where
  atlas : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L
  two : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L atlas
  canonicalTwo : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L atlas two
  cover : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L atlas two
  quotient : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L atlas two cover
  universal : HodgeUniversal k L atlas two cover quotient

lemma provider_exists (k : Type) [Field k] [CharZero k] (L : ℕ)
    (hL : 3 ≤ L) (heven : Even L) : Nonempty (Provider k L) := by
  obtain ⟨A⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction k L hL
  obtain ⟨B, hB, V, Q, H⟩ := scheme_hodge_universal k L hL heven A
  exact ⟨⟨A, B, hB, V, Q, H⟩⟩

/-- Faithfulness with the providers constructed, rather than hypothesized. -/
lemma actual_descent_faithful (k : Type) [Field k] [CharZero k] (L : ℕ)
    (hL : 3 ≤ L) (heven : Even L) (C : Coherence L (Base k))
    {T U : Over (Base k)} (q : U ⟶ T)
    (hq : QuasiCompact q.left) (hf : Flat q.left) (hs : Surjective q.left) :
    (C.functor.toDescentData (fun _ : Unit => q)).Faithful := by
  obtain ⟨P⟩ := provider_exists k L hL heven
  exact descent_faithful P.universal C q hq hf hs

end ActualFamilyFPQCDescentProof

/-- Actual level-marked elliptic families with specified cotangent roots satisfy
categorical descent along every quasicompact faithfully flat surjection. -/
theorem actual_family_fpqc_descent
    (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (C : Coherence L (ArithmeticThetaLocalWeierstrassR0203.Base k)) :
    ArithmeticThetaRootStackR0198.SingletonDescent C.functor := by
  obtain ⟨P⟩ := ActualFamilyFPQCDescentProof.provider_exists k L hL heven
  intro T U q hq hf hs
  exact {
    faithful := ActualFamilyFPQCDescentProof.descent_faithful P.universal C q hq hf hs
    full := ActualFamilyFPQCDescentProof.actual_full P.universal hL heven C q hq hf hs
    essSurj := ActualFamilyFPQCDescentProof.actual_essSurj P.universal hL heven C q hq hf hs }

end ArithmeticThetaMetaplecticStackR0207

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.classifier_descends

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.descent_faithful

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.lineTransformation

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.modelHomEquiv

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.actual_descent_faithful

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.modelPullIso

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.fixed_square_natural

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.fixed_singleton_descent

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.reflectFixedHom

#print axioms ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.classified_effective

#print axioms ArithmeticThetaMetaplecticStackR0207.actual_family_fpqc_descent
