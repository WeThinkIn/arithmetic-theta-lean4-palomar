import CoherentMetaplecticPullbackR0207

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaMetaplecticStackR0207
namespace ActualFamilyOpenDescentProof
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205

variable {k : Type} [Field k] [CharZero k] {L : ℕ}
  {A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L}
  {B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A}
  {K : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B}
  {Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B K}
  (H : HodgeUniversal k L A B K Q)

/-- The classifier is chosen from the accepted universal property of the
actual marked family, without imposing a frame on its square root. -/
def classifier {S : Over (Base k)} (X : Object L S.left) : S.left ⟶ Base Q.quotient.ring :=
  Classical.choose (H.1.1 S.left S.hom X.family X.marking)

def classifierCurve {S : Over (Base k)} (X : Object L S.left) :
    X.family.curve ⟶ A.descent.family.curve :=
  Classical.choose (Classical.choose_spec (H.1.1 S.left S.hom X.family X.marking)).1

lemma classifier_spec {S : Over (Base k)} (X : Object L S.left) :
    Classifies k L A B K Q S.hom X.family X.marking
      (classifier H X) (classifierCurve H X) :=
  (Classical.choose_spec
    (Classical.choose_spec (H.1.1 S.left S.hom X.family X.marking)).1).1

/-- Every actual arrow preserves the classifying map. -/
lemma classifier_arrow {S : Over (Base k)} {G : GroupoidData L S.left}
    {X Y : G.Objects} (f : X ⟶ Y) : classifier H X = classifier H Y := by
  have h := H.1.2.2 S.left S.left S.hom S.hom Y.family X.family
    Y.marking X.marking (𝟙 S.left) (G.arrow _ _ f).curve.hom
    (Category.id_comp _) (G.arrow _ _ f).marked
    (classifier H Y) (classifier H X) (classifierCurve H Y) (classifierCurve H X)
    (classifier_spec H Y) (classifier_spec H X)
  simpa only [Category.id_comp] using h.1

/-- The same chosen classifier commutes with every accepted geometric pullback. -/
lemma classifier_pull {S T : Over (Base k)} (a : T ⟶ S)
    {GS : GroupoidData L S.left} {GT : GroupoidData L T.left}
    (P : PullbackData GS GT a.left) (X : GS.Objects) :
    classifier H (P.functor.obj X) = a.left ≫ classifier H X :=
  (H.1.2.2 S.left T.left S.hom T.hom X.family (P.functor.obj X).family
    X.marking (P.functor.obj X).marking a.left (P.curve X) (Over.w a) (P.marked X)
    (classifier H X) (classifier H (P.functor.obj X))
    (classifierCurve H X) (classifierCurve H (P.functor.obj X))
    (classifier_spec H X) (classifier_spec H (P.functor.obj X))).1

variable (C : Coherence L (Base k))

/-- The classifying maps of a categorical datum agree on every test overlap. -/
lemma classifier_agreement {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    (D : C.functor.DescentData f) {S : Over (Base k)} (p : S ⟶ T)
    {i j : ι} (a : S ⟶ V i) (b : S ⟶ V j)
    (ha : a ≫ f i = p) (hb : b ≫ f j = p) :
    a.left ≫ classifier H (D.obj i) = b.left ≫ classifier H (D.obj j) := by
  have h := classifier_arrow H (G := group L S.left) (D.hom p a b ha hb)
  change classifier H ((pull L a.left).functor.obj (D.obj i)) =
    classifier H ((pull L b.left).functor.obj (D.obj j)) at h
  rw [classifier_pull H a, classifier_pull H b] at h
  exact h

/-- Classifying maps glue over arbitrary open covers, including the empty
cover of the empty test scheme. This does not assume root effectivity. -/
lemma classifier_glue {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    (ho : ∀ i, IsOpenImmersion (f i).left)
    (hc : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base)
    (D : C.functor.DescentData f) :
    ∃! b : BaseMap k L A B K Q T, ∀ i, (f i).left ≫ b.val = classifier H (D.obj i) := by
  letI : ∀ i, IsOpenImmersion (f i).left := ho
  let U : T.left.OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => (V i).left) (fun i => (f i).left) hc ho
  have compat (i j : ι) :
      pullback.fst ((f i).left) ((f j).left) ≫ classifier H (D.obj i) =
        pullback.snd ((f i).left) ((f j).left) ≫ classifier H (D.obj j) := by
    let p := pullback.fst ((f i).left) ((f j).left) ≫ (f i).left
    let S : Over (Base k) := Over.mk (p ≫ T.hom)
    let a : S ⟶ V i := Over.homMk (pullback.fst ((f i).left) ((f j).left)) (by
      dsimp [S, p]; rw [Category.assoc, Over.w])
    let b : S ⟶ V j := Over.homMk (pullback.snd ((f i).left) ((f j).left)) (by
      dsimp [S, p]; rw [pullback.condition, Category.assoc, Over.w])
    exact classifier_agreement H C f D (Over.homMk p rfl) a b
      (by ext; rfl) (by ext; exact pullback.condition.symm)
  let b := U.glueMorphisms (fun i => classifier H (D.obj i)) compat
  have hb (i : ι) : (f i).left ≫ b = classifier H (D.obj i) :=
    U.ι_glueMorphisms _ _ i
  have hk : b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = T.hom := by
    apply U.hom_ext
    intro i
    change (f i).left ≫ (b ≫ _) = (f i).left ≫ T.hom
    rw [← Category.assoc, hb, (classifier_spec H (D.obj i)).1, Over.w]
  refine ⟨⟨b, hk⟩, hb, ?_⟩
  intro b' hb'
  apply Subtype.ext
  exact U.hom_ext _ _ (fun i => (hb' i).trans (hb i).symm)

/-- The underlying lines form a strong transformation with the original
geometric line comparisons. -/
def lineStrong : Pseudofunctor.StrongTrans C.functor
    (ArithmeticThetaRootStackR0198.modulesOver (Base k)) where
  app S := (lineForget (group L S.as.unop.left)).toCatHom
  naturality f := Cat.Hom.isoMk (linePull L (Base k) f.as.unop)
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
      (𝟙 _ ≫ (Scheme.Modules.pullbackId S.as.unop.left).hom.app X.root.line ≫ 𝟙 _) =
      ((group L S.as.unop.left).arrow _ _ ((C.unit S.as).hom.toNatTrans.app X)).line.hom ≫
        𝟙 _ ≫ 𝟙 _
    simpa [reindex, lineForget] using
      (C.unit_normalized S.as.unop X).2.symm

  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (g.as.unop.left ≫ f.as.unop.left)).line X).hom ≫
      (𝟙 _ ≫ (Scheme.Modules.pullbackComp g.as.unop.left f.as.unop.left).inv.app X.root.line ≫ 𝟙 _) =
      (lineForget (group L _)).map ((C.comp f.as g.as).hom.toNatTrans.app X) ≫
        𝟙 _ ≫ ((pull L g.as.unop.left).line ((pull L f.as.unop.left).functor.obj X)).hom ≫
        𝟙 _ ≫ (Scheme.Modules.pullback g.as.unop.left).map ((pull L f.as.unop.left).line X).hom ≫ 𝟙 _
    simpa [reindex, lineForget, Category.assoc] using
      (C.comp_normalized _ _ _ f.as.unop g.as.unop X).2.symm

open ArithmeticThetaRootDescentR0197
open ArithmeticThetaRootStackR0198.CategoricalRootDescentR0198

/-- Descent data in actual families retain their complete line-module datum. -/
def concreteFunctor {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) :=
  strongData (lineStrong C) f ⋙ unsliceFunctor f

/-- The concrete functor uses the original pullback line comparison. -/
def concreteCanonicalIso {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    (X : (group L T.left).Objects) :
    (concreteFunctor C f).obj ((C.functor.toDescentData f).obj X) ≅
      (descent (fun i => (f i).left)).obj X.root.line :=
  (unsliceFunctor f).mapIso (strongCanonicalIso (lineStrong C) f X) ≪≫
    unsliceCanonical f X.root.line

include H in
/-- Equality of arrows is local for every jointly covering open family. -/
lemma categorical_faithful {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    (ho : ∀ i, IsOpenImmersion (f i).left)
    (hc : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base) :
    (C.functor.toDescentData f).Faithful where
  map_injective {X Y} a b hab := by
    letI : ∀ i, IsOpenImmersion (f i).left := ho
    apply NaturalComparisonProof.line_faithful H (group L T.left)
    apply (Scheme.Modules.toDescentData_map_bijective_of_openCover
      (fun i => (f i).left) hc X.root.line Y.root.line).1
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    have hi := congrArg (fun t => t.hom i) hab
    change (pull L (f i).left).functor.map a = (pull L (f i).left).functor.map b at hi
    have ha := (pull L (f i).left).line_natural X Y a
    have hb := (pull L (f i).left).line_natural X Y b
    rw [hi] at ha
    exact (cancel_epi ((pull L (f i).left).line X).hom).1 (ha.symm.trans hb)

open ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower
open ArithmeticThetaCoverComparison
open ArithmeticThetaMetaplecticTestsR0196

/-- A classifier with its normalized Hodge map for a specified actual object. -/
structure Classified {S : Over (Base k)} (X : Object L S.left)
    (b : BaseMap k L A B K Q S) where
  curve : X.family.curve ⟶ A.descent.family.curve
  classifies : Classifies k L A B K Q S.hom X.family X.marking b.val curve
  hodge : (Scheme.Modules.pullback b.val).obj (ModularHodge k L A B K Q) ≅ Cotangent X.family
  canonical : ClassifierHodge k L A B K Q X.family b.val curve hodge

def Classified.model {S : Over (Base k)} {X : Object L S.left}
    {b : BaseMap k L A B K Q S} (m : Classified X b) : FiberEquivalenceProof.Model b :=
  ⟨X.family, X.marking, m.curve, m.classifies, m.hodge, m.canonical⟩

def Classified.root {S : Over (Base k)} {X : Object L S.left}
    {b : BaseMap k L A B K Q S} (m : Classified X b) :
    SquareLine S.left ((Scheme.Modules.pullback b.val).obj (ModularHodge k L A B K Q)) :=
  ⟨X.root.line, X.root.invertible, X.root.square ≪≫ m.hodge.symm⟩

include H in
/-- All arrows preserve the normalized root square over a common classifier. -/
lemma arrow_root_square {S : Over (Base k)} {X Y : Object L S.left}
    {b : BaseMap k L A B K Q S} (m : Classified X b) (n : Classified Y b)
    (f : Arrow X Y) :
    tensorPowerMap f.line.hom 2 ≫ n.root.square.hom = m.root.square.hom := by
  have ht := (H.1.2.2 S.left S.left S.hom S.hom Y.family X.family
    Y.marking X.marking (𝟙 S.left) f.curve.hom (Category.id_comp _) f.marked
    b.val b.val n.curve m.curve n.classifies m.classifies).2.symm
  have hd := FiberEquivalenceProof.hodge_backward H n.model m.model
    f.curve.hom f.marked ht
  have he := ActualGroupoidProof.backward_unique f.curve.hom f.marked.1 f.marked.2.1
    f.cotangent.symm f.canonical
  change n.hodge.hom ≫ (ActualGroupoidProof.backward f.curve.hom
    f.marked.1 f.marked.2.1).hom = m.hodge.hom at hd
  rw [← he] at hd
  change n.hodge.hom ≫ f.cotangent.inv = m.hodge.hom at hd
  change tensorPowerMap f.line.hom 2 ≫ (Y.root.square.hom ≫ n.hodge.inv) =
    X.root.square.hom ≫ m.hodge.inv
  apply (cancel_mono n.hodge.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [f.square]
  congr 1
  apply (cancel_epi m.hodge.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← hd]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

lemma classified_exists {S : Over (Base k)} (X : Object L S.left)
    (b : BaseMap k L A B K Q S) (hb : classifier H X = b.val) :
    Nonempty (Classified X b) := by
  have hc := classifier_spec H X
  rw [hb] at hc
  obtain ⟨e, he, _⟩ := H.2.1 S.left S.hom X.family X.marking b.val (classifierCurve H X) hc
  exact ⟨⟨classifierCurve H X, hc, e, he⟩⟩

def classified {S : Over (Base k)} (X : Object L S.left)
    (b : BaseMap k L A B K Q S) (hb : classifier H X = b.val) : Classified X b :=
  Classical.choice (classified_exists H X b hb)

include H in
/-- Hodge naturality with an arbitrary, explicitly equal, classifying map. -/
lemma classified_natural {S T : Over (Base k)} (a : T ⟶ S)
    {GS : GroupoidData L S.left} {GT : GroupoidData L T.left}
    (P : PullbackData GS GT a.left) (X : GS.Objects)
    {b : BaseMap k L A B K Q S} {c : BaseMap k L A B K Q T}
    (m : Classified X b) (n : Classified (P.functor.obj X) c)
    (hc : a.left ≫ b.val = c.val) :
    (Scheme.Modules.pullback a.left).map m.hodge.hom ≫ (P.cotangent X).hom =
      (OpenSquareRootEffectivityR0197.compare a.left b.val c.val hc
        (ModularHodge k L A B K Q)).hom ≫ n.hodge.hom := by
  have ht := (H.1.2.2 S.left T.left S.hom T.hom X.family (P.functor.obj X).family
    X.marking (P.functor.obj X).marking a.left (P.curve X) (Over.w a) (P.marked X)
    b.val c.val m.curve n.curve m.classifies n.classifies).2
  rcases b with ⟨b, hb⟩
  rcases c with ⟨c, hc'⟩
  dsimp only at hc
  subst c
  have hn : ClassifierHodge k L A B K Q (P.functor.obj X).family
      (a.left ≫ b) (P.curve X ≫ m.curve) n.hodge := by
    rw [← ht]
    exact n.canonical
  simpa [OpenSquareRootEffectivityR0197.compare, Scheme.Modules.pullbackCongr] using
    H.2.2 S.left T.left X.family (P.functor.obj X).family a.left (P.curve X)
      (P.marked X).2.1 b m.curve m.hodge n.hodge (P.cotangent X)
      m.canonical hn (P.canonical X)

include H in
/-- The prescribed pullback line map respects the roots after their Hodge
normalizations, with the actual classifier equality retained. -/
lemma classified_pull_square {S T : Over (Base k)} (a : T ⟶ S)
    {GS : GroupoidData L S.left} {GT : GroupoidData L T.left}
    (P : PullbackData GS GT a.left) (X : GS.Objects)
    {b : BaseMap k L A B K Q S} {c : BaseMap k L A B K Q T}
    (m : Classified X b) (n : Classified (P.functor.obj X) c)
    (hc : a.left ≫ b.val = c.val) :
    tensorPowerMap (P.line X).hom 2 ≫ (squarePull a.left m.root).hom ≫
      (OpenSquareRootEffectivityR0197.compare a.left b.val c.val hc
        (ModularHodge k L A B K Q)).hom = n.root.square.hom := by
  let d := OpenSquareRootEffectivityR0197.compare a.left b.val c.val hc
    (ModularHodge k L A B K Q)
  have hn := classified_natural H a P X m n hc
  change (Scheme.Modules.pullback a.left).map m.hodge.hom ≫ (P.cotangent X).hom =
    d.hom ≫ n.hodge.hom at hn
  apply (cancel_mono n.hodge.hom).1
  change (tensorPowerMap (P.line X).hom 2 ≫ (squarePull a.left m.root).hom ≫ d.hom) ≫
    n.hodge.hom = ((P.functor.obj X).root.square.hom ≫ n.hodge.inv) ≫ n.hodge.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hn]
  have hs : (squarePull a.left m.root).hom ≫ (Scheme.Modules.pullback a.left).map m.hodge.hom =
      (squarePull a.left X.root).hom := by
    dsimp [squarePull, Classified.root]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, Functor.map_id, Category.comp_id]
  rw [← Category.assoc (squarePull a.left m.root).hom, hs]
  exact P.square X

lemma classifier_eq {S : Over (Base k)} {X : Object L S.left}
    {b : BaseMap k L A B K Q S} (m : Classified X b) : classifier H X = b.val := by
  have h := H.1.2.2 S.left S.left S.hom S.hom X.family X.family X.marking X.marking
    (𝟙 S.left) (𝟙 X.family.curve) (Category.id_comp _) (ActualGroupoidProof.marked_id X)
    b.val (classifier H X) m.curve (classifierCurve H X) m.classifies (classifier_spec H X)
  simpa only [Category.id_comp] using h.1

def classifiedPull {S T : Over (Base k)} (a : T ⟶ S)
    {GS : GroupoidData L S.left} {GT : GroupoidData L T.left}
    (P : PullbackData GS GT a.left) (X : GS.Objects)
    {b : BaseMap k L A B K Q S} (m : Classified X b)
    (c : BaseMap k L A B K Q T) (hc : a.left ≫ b.val = c.val) :
    Classified (P.functor.obj X) c :=
  classified H (P.functor.obj X) c (by rw [classifier_pull H a, classifier_eq H m]; exact hc)

open OpenSquareRootEffectivityR0197

/-- The underlying line datum, with squares in the Hodge line of the glued
classifier. The chosen local classified models retain the original families. -/
def rootDatum {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) (D : C.functor.DescentData f)
    (b : BaseMap k L A B K Q T)
    (m : ∀ i, Classified (D.obj i) (mapBase k L A B K Q (f i) b)) :
    RootDatum ((Scheme.Modules.pullback b.val).obj (ModularHodge k L A B K Q))
      (fun i => (f i).left) where
  data := (concreteFunctor C f).obj D
  invertible i := (D.obj i).root.invertible
  square i := (m i).root.square ≪≫
    (compare (f i).left b.val ((f i).left ≫ b.val) rfl (ModularHodge k L A B K Q)).symm

lemma rootDatum_square_test {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) (D : C.functor.DescentData f)
    (b : BaseMap k L A B K Q T)
    (m : ∀ i, Classified (D.obj i) (mapBase k L A B K Q (f i) b))
    {S : Scheme.{0}} (p : S ⟶ T.left) (i : ι) (a : S ⟶ (V i).left)
    (ha : a ≫ (f i).left = p) :
    (squarePull a (localRoot (rootDatum C f D b m) i)).hom ≫
      (compare a (f i).left p ha ((Scheme.Modules.pullback b.val).obj
        (ModularHodge k L A B K Q))).hom ≫
      (compare p b.val (p ≫ b.val) rfl (ModularHodge k L A B K Q)).hom =
    (squarePull a (m i).root).hom ≫
      (compare a ((f i).left ≫ b.val) (p ≫ b.val)
        (by exact (Category.assoc a (f i).left b.val).symm.trans (congrArg (fun q => q ≫ b.val) ha)) (ModularHodge k L A B K Q)).hom := by
  rw [compare_comp a (f i).left b.val p ((f i).left ≫ b.val) (p ≫ b.val)
    ha rfl rfl ((Category.assoc a (f i).left b.val).symm.trans (congrArg (fun q => q ≫ b.val) ha))]
  dsimp [squarePull, localRoot, rootDatum, Classified.root]
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rfl

include H in
/-- All test-overlap square equations survive the passage to the glued
classifier and the concrete line datum. -/
lemma rootDatum_compatible {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) (D : C.functor.DescentData f)
    (b : BaseMap k L A B K Q T)
    (m : ∀ i, Classified (D.obj i) (mapBase k L A B K Q (f i) b)) :
    CompatibleSquares (rootDatum C f D b m) := by
  intro S p i j a a' ha ha'
  let pa : testOver p ⟶ T := Over.homMk p rfl
  let c := mapBase k L A B K Q pa b
  let ai := testLeg (f i) p a ha
  let aj := testLeg (f j) p a' ha'
  have hi : ai.left ≫ (mapBase k L A B K Q (f i) b).val = c.val := by
    change a ≫ ((f i).left ≫ b.val) = p ≫ b.val
    exact (Category.assoc a (f i).left b.val).symm.trans (congrArg (fun q => q ≫ b.val) ha)
  have hj : aj.left ≫ (mapBase k L A B K Q (f j) b).val = c.val := by
    change a' ≫ ((f j).left ≫ b.val) = p ≫ b.val
    exact (Category.assoc a' (f j).left b.val).symm.trans (congrArg (fun q => q ≫ b.val) ha')
  let ni := classifiedPull H ai (pull L a) (D.obj i) (m i) c hi
  let nj := classifiedPull H aj (pull L a') (D.obj j) (m j) c hj
  have hni := classified_pull_square H ai (pull L a) (D.obj i) (m i) ni hi
  have hnj := classified_pull_square H aj (pull L a') (D.obj j) (m j) nj hj
  have ht := arrow_root_square H ni nj
    ((group L S).arrow _ _ (D.hom pa ai aj (testLeg_comp (f i) p a ha)
      (testLeg_comp (f j) p a' ha')))
  change tensorPowerMap (transition (lineStrong C) ai aj
      (D.hom pa ai aj (testLeg_comp (f i) p a ha) (testLeg_comp (f j) p a' ha'))) 2 ≫
      (squarePull a' (localRoot (rootDatum C f D b m) j)).hom ≫
      (compare a' (f j).left p ha' ((Scheme.Modules.pullback b.val).obj
        (ModularHodge k L A B K Q))).hom =
    (squarePull a (localRoot (rootDatum C f D b m) i)).hom ≫
      (compare a (f i).left p ha ((Scheme.Modules.pullback b.val).obj
        (ModularHodge k L A B K Q))).hom
  apply (cancel_mono (compare p b.val (p ≫ b.val) rfl (ModularHodge k L A B K Q)).hom).1
  simp only [Category.assoc]
  rw [rootDatum_square_test C f D b m p j a' ha', rootDatum_square_test C f D b m p i a ha]
  exact square_conjugate ((pull L a).line (D.obj i)) ((pull L a').line (D.obj j))
    ((group L S).arrow _ _ (D.hom pa ai aj (testLeg_comp (f i) p a ha)
      (testLeg_comp (f j) p a' ha'))).line.hom
    _ _ _ _ hni hnj ht

/-- Reflect compatible concrete module maps through the faithful actual
family comparison, including their equations on every test overlap. -/
def liftConcreteHom {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    {f : ∀ i, V i ⟶ T} {D E : C.functor.DescentData f}
    (φ : ∀ i, D.obj i ⟶ E.obj i)
    (ψ : (concreteFunctor C f).obj D ⟶ (concreteFunctor C f).obj E)
    (hφ : ∀ i, ((group L (V i).left).arrow _ _ (φ i)).line.hom = ψ.hom i) : D ⟶ E :=
  liftStrongHom (lineStrong C)
    (fun S => ⟨by
      intro X Y a b h
      exact NaturalComparisonProof.line_faithful H (group L S.left) a b h⟩)
    φ (liftUnsliceHom ψ) hφ

@[simp] lemma concreteCanonicalIso_hom {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    (X : (group L T.left).Objects) (i : ι) :
    (concreteCanonicalIso C f X).hom.hom i = ((pull L (f i).left).line X).hom := by
  change ((pull L (f i).left).line X).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

include H in
/-- Reconstruct the actual local family arrow from a realized root datum,
retaining its specified full line map. -/
lemma effectiveLocalArrow_exists (hL : 3 ≤ L) (heven : Even L)
    {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) (D : C.functor.DescentData f)
    (b : BaseMap k L A B K Q T)
    (m : ∀ i, Classified (D.obj i) (mapBase k L A B K Q (f i) b))
    (J : SquareLine T.left ((Scheme.Modules.pullback b.val).obj (ModularHodge k L A B K Q)))
    (e : (descent (fun i => (f i).left)).obj J.line ≅ (rootDatum C f D b m).data)
    (he : Realizes (rootDatum C f D b m) J e)
    (X : (group L T.left).Objects) (mx : Classified X b) (r : SquareIso mx.root J)
    (i : ι) :
    ∃ g : (pull L (f i).left).functor.obj X ⟶ D.obj i,
      ((group L (V i).left).arrow _ _ g).line.hom =
        ((pull L (f i).left).line X).hom ≫
          (Scheme.Modules.pullback (f i).left).map r.val.hom ≫ e.hom.hom i := by
  let P := pull L (f i).left
  let n := classifiedPull H (f i) P X mx (mapBase k L A B K Q (f i) b) rfl
  let z := P.line X ≪≫ (Scheme.Modules.pullback (f i).left).mapIso r.val ≪≫
    componentIso (rootDatum C f D b m) e i
  let d := compare (f i).left b.val ((f i).left ≫ b.val) rfl (ModularHodge k L A B K Q)
  have hs : ((rootDatum C f D b m).square i).hom ≫ d.hom = (m i).root.square.hom := by
    change ((m i).root.square.hom ≫ d.inv) ≫ d.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hz : tensorPowerMap z.hom 2 ≫ (m i).root.square.hom = n.root.square.hom := by
    rw [← hs]
    exact square_chain_transport (P.line X)
      ((Scheme.Modules.pullback (f i).left).mapIso r.val)
      (componentIso (rootDatum C f D b m) e i) d
      _ _ _ _ (classified_pull_square H (f i) P X mx n rfl)
      (pull_square_iso (f i).left mx.root J r) (he i)
  obtain ⟨g, hg⟩ := NaturalComparisonProof.arrow_of_square hL heven H n.model (m i).model
    (P.functor.obj X).root (D.obj i).root z hz
  refine ⟨((group L (V i).left).arrow _ _).symm g, ?_⟩
  simpa only [Equiv.apply_symm_apply, z, Iso.trans_hom, Functor.mapIso_hom,
    componentIso, Category.assoc] using hg

include H in
/-- Once the compatible root datum is effective, the actual marked family
datum is effective through the accepted Cartesian reconstruction. -/
lemma effective_actual (hL : 3 ≤ L) (heven : Even L)
    {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) (D : C.functor.DescentData f)
    (b : BaseMap k L A B K Q T)
    (m : ∀ i, Classified (D.obj i) (mapBase k L A B K Q (f i) b))
    (heff : Effective (rootDatum C f D b m)) :
    ∃ X : (group L T.left).Objects, Nonempty ((C.functor.toDescentData f).obj X ≅ D) := by
  obtain ⟨J, e, he⟩ := heff
  let n := FiberEquivalenceProof.model H b
  let X : (group L T.left).Objects := FiberEquivalenceProof.obj n J
  let mx : Classified X b := ⟨n.curve, n.classifies, n.hodge, n.canonical⟩
  have hr : tensorPowerMap (𝟙 J.line) 2 ≫ J.square.hom = mx.root.square.hom := by
    change tensorPowerMap (𝟙 J.line) 2 ≫ J.square.hom =
      (J.square.hom ≫ n.hodge.hom) ≫ n.hodge.inv
    simp only [tensorPowerMap_id, Category.id_comp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let r : SquareIso mx.root J := ⟨Iso.refl _, hr⟩
  choose g hg using effectiveLocalArrow_exists H C hL heven f D b m J e he X mx r
  let ψ : (concreteFunctor C f).obj ((C.functor.toDescentData f).obj X) ⟶
      (concreteFunctor C f).obj D := (concreteCanonicalIso C f X).hom ≫ e.hom
  have hg' (i : ι) : ((group L (V i).left).arrow _ _ (g i)).line.hom = ψ.hom i := by
    dsimp only [ψ, Pseudofunctor.DescentData.comp_hom]
    rw [concreteCanonicalIso_hom]
    have hi := hg i
    have hid : (Scheme.Modules.pullback (f i).left).map r.val.hom = 𝟙 _ :=
      (Scheme.Modules.pullback (f i).left).map_id _
    rw [hid] at hi
    exact hi.trans (congrArg (fun q => ((pull L (f i).left).line X).hom ≫ q)
      (Category.id_comp (e.hom.hom i)))
  let u := liftConcreteHom H C g ψ hg'
  refine ⟨X, ⟨Pseudofunctor.DescentData.isoMk (fun i => asIso (g i)) ?_⟩⟩
  intro S p i j a a' ha ha'
  exact u.comm p a a' ha ha'

namespace RootBridge
open ArithmeticThetaRootStackR0198
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {Z : Scheme.{0}} {W : Z.Modules} {ι : Type 1}
  {U : ι → Scheme.{0}} (f : ∀ i, U i ⟶ Z)

abbrev coverLeg (i : ι) : Over.mk (f i) ⟶ Over.mk (𝟙 Z) :=
  Over.homMk (f i) (Category.comp_id _)

lemma forget_transition {S T V : Over Z} (a : S ⟶ T) (b : S ⟶ V)
    {x : RootModuliPseudofunctorR0198.Fiber W T} {y : RootModuliPseudofunctorR0198.Fiber W V}
    (t : (RootModuliPseudofunctorR0198.pull a).obj x ⟶ (RootModuliPseudofunctorR0198.pull b).obj y) :
    transition (RootModuliPseudofunctorR0198.forgetStrong (W := W)) a b t = t.val.hom := by
  change 𝟙 _ ≫ t.val.hom ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

lemma forget_pullHom {S S' T V : Over Z} (a : S ⟶ T) (b : S ⟶ V)
    (g : S' ⟶ S) {x : RootModuliPseudofunctorR0198.Fiber W T} {y : RootModuliPseudofunctorR0198.Fiber W V}
    (t : (RootModuliPseudofunctorR0198.pull a).obj x ⟶ (RootModuliPseudofunctorR0198.pull b).obj y)
    (ga : S' ⟶ T) (gb : S' ⟶ V) (ha : g ≫ a = ga) (hb : g ≫ b = gb) :
    (pullHom (F := RootModuliPseudofunctorR0198.rootFunctor (W := W)) t g ga gb ha hb).val.hom =
      pullHom (F := modulesOver Z) t.val.hom g ga gb ha hb := by
  simpa only [forget_transition] using
    (transition_pull (RootModuliPseudofunctorR0198.forgetStrong (W := W)) a b g t ga gb ha hb).symm

/-- A concrete compatible root datum is a categorical root datum on the slice. -/
def categoricalDatum (D : RootDatum W f) (hD : CompatibleSquares D) :
    (RootModuliPseudofunctorR0198.rootFunctor (W := W)).DescentData (coverLeg f) where
  obj i := localRoot D i
  hom S p i j a b ha hb :=
    ⟨D.data.iso S.hom a.left b.left (Over.w a) (Over.w b), by
      change tensorPowerMap (D.data.hom S.hom a.left b.left (Over.w a) (Over.w b)) 2 ≫
        ((squarePull b.left (localRoot D j)).hom ≫
          (compare b.left (f j) S.hom (Over.w b) W).hom) =
        (squarePull a.left (localRoot D i)).hom ≫
          (compare a.left (f i) S.hom (Over.w a) W).hom
      exact hD S.left S.hom i j a.left b.left (Over.w a) (Over.w b)⟩
  hom_self S p i a ha := by
    apply RootModuliPseudofunctorR0198.hom_ext
    exact D.data.hom_self S.hom a.left (Over.w a)
  hom_comp S p i j l a b c ha hb hc := by
    apply RootModuliPseudofunctorR0198.hom_ext
    exact D.data.hom_comp S.hom a.left b.left c.left (Over.w a) (Over.w b) (Over.w c)
  pullHom_hom S' S g p p' hp i j a b ha hb ga gb hga hgb := by
    apply RootModuliPseudofunctorR0198.hom_ext
    rw [forget_pullHom a b g]
    dsimp only [pullHom]
    rw [precompose_comp_hom (Over.forget Z) moduleFunctor a g ga hga,
      precompose_comp_inv (Over.forget Z) moduleFunctor b g gb hgb]
    exact D.data.pullHom_hom g.left S.hom S'.hom (Over.w g)
      a.left b.left (Over.w a) (Over.w b) ga.left gb.left
      (congrArg Over.Hom.left hga) (congrArg Over.Hom.left hgb)

/-- Forgetting this categorical datum recovers precisely the original all-test
module datum, including its transition maps. -/
def categoricalUnderlyingIso (D : RootDatum W f) (hD : CompatibleSquares D) :
    (ArithmeticThetaRootStackR0198.CategoricalRootDescentR0198.concreteFunctor
      (RootModuliPseudofunctorR0198.presentation (W := W)) (coverLeg f)).obj (categoricalDatum f D hD) ≅ D.data :=
  Pseudofunctor.DescentData.isoMk (fun i => Iso.refl _) (by
    intro S p i j a b ha hb
    simp only [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]
    change (Scheme.Modules.pullback a).map (𝟙 _) ≫ D.data.hom p a b ha hb =
      (𝟙 _ ≫ D.data.hom (p ≫ 𝟙 Z) a b _ _ ≫ 𝟙 _) ≫
        (Scheme.Modules.pullback b).map (𝟙 _)
    erw [(Scheme.Modules.pullback a).map_id, (Scheme.Modules.pullback b).map_id]
    simp only [Category.id_comp, Category.comp_id]
    erw [Category.comp_id (D.data.hom (p ≫ 𝟙 Z) a b _ _)]
    congr 1)

/-- The accepted categorical theorem supplies effectivity of the original
concrete root datum, including its exact local squares. -/
lemma effective (ho : ∀ i, IsOpenImmersion (f i))
    (hc : ∀ z : Z, ∃ i, z ∈ Set.range (f i).base)
    (hW : Scheme.Modules.IsInvertible W)
    (D : RootDatum W f) (hD : CompatibleSquares D) : Effective D := by
  let P := RootModuliPseudofunctorR0198.presentation (W := W)
  let F := P.functor.toDescentData (coverLeg f)
  letI : F.IsEquivalence := categorical_open_root_descent Z W hW P
    (Over.mk (𝟙 Z)) ι (fun i => Over.mk (f i)) (coverLeg f) ho hc
  let D' := categoricalDatum f D hD
  let J₀ := F.objPreimage D'
  let e₀ : F.obj J₀ ≅ D' := F.objObjPreimageIso D'
  let J : SquareLine Z W :=
    ⟨J₀.line, J₀.invertible, J₀.square ≪≫ (Scheme.Modules.pullbackId Z).app W⟩
  let e : (descent f).obj J.line ≅ D.data :=
    (ArithmeticThetaRootStackR0198.CategoricalRootDescentR0198.concreteCanonicalIso
      P (coverLeg f) J₀).symm ≪≫
    (ArithmeticThetaRootStackR0198.CategoricalRootDescentR0198.concreteFunctor
      P (coverLeg f)).mapIso e₀ ≪≫ categoricalUnderlyingIso f D hD
  refine ⟨J, e, ?_⟩
  intro i
  have hi := (e₀.hom.hom i).property
  have hei : e.hom.hom i = (e₀.hom.hom i).val.hom := by
    change (𝟙 _ ≫ 𝟙 _) ≫ (e₀.hom.hom i).val.hom ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  rw [hei]
  change tensorPowerMap (e₀.hom.hom i).val.hom 2 ≫ (D.square i).hom = _ at hi
  rw [hi]
  change (squarePull (f i) J₀).hom ≫ (compare (f i) (𝟙 Z) (f i)
    (Category.comp_id _) W).hom = (squarePull (f i) J).hom
  have hcomp := congrArg (fun t => t.app W) (Scheme.Modules.pseudofunctor_left_unitality (f i))
  have hcomp' : (compare (f i) (𝟙 Z) (f i) (Category.comp_id _) W).hom =
      (Scheme.Modules.pullback (f i)).map ((Scheme.Modules.pullbackId Z).hom.app W) := by
    have hh : (Scheme.Modules.pullbackComp (f i) (𝟙 Z)).inv.app W ≫
        (Scheme.Modules.pullback (f i)).map ((Scheme.Modules.pullbackId Z).hom.app W) =
        (Scheme.Modules.pullbackCongr (Category.comp_id (f i))).hom.app W := by
      simpa [Scheme.Modules.pullbackCongr] using hcomp
    change (Scheme.Modules.pullbackComp (f i) (𝟙 Z)).hom.app W ≫ _ = _
    exact (congrArg (fun q => (Scheme.Modules.pullbackComp (f i) (𝟙 Z)).hom.app W ≫ q)
      hh.symm).trans (Iso.hom_inv_id_app_assoc _ _ _)
  rw [hcomp']
  simp only [J, squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

end RootBridge


/-- Every actual descent arrow is invertible, with its original components. -/
def descentArrowIso {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    {f : ∀ i, V i ⟶ T} {D E : C.functor.DescentData f} (t : D ⟶ E) : D ≅ E :=
  Pseudofunctor.DescentData.isoMk (fun i => asIso (t.hom i))
    (fun {_} p {_ _} a b ha hb => t.comm p a b ha hb)

def underlyingArrowIso {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T) {X Y : (group L T.left).Objects}
    (t : (C.functor.toDescentData f).obj X ⟶ (C.functor.toDescentData f).obj Y) :
    (descent (fun i => (f i).left)).obj X.root.line ≅
      (descent (fun i => (f i).left)).obj Y.root.line :=
  (concreteCanonicalIso C f X).symm ≪≫
    (concreteFunctor C f).mapIso (descentArrowIso C t) ≪≫ concreteCanonicalIso C f Y

lemma underlyingArrowIso_hom {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    {X Y : (group L T.left).Objects}
    (t : (C.functor.toDescentData f).obj X ⟶ (C.functor.toDescentData f).obj Y) (i : ι) :
    (underlyingArrowIso C f t).hom.hom i =
      ((pull L (f i).left).line X).inv ≫
        ((group L (V i).left).arrow _ _ (t.hom i)).line.hom ≫
        ((pull L (f i).left).line Y).hom := by
  change (𝟙 _ ≫ ((pull L (f i).left).line X).inv) ≫
    ((group L (V i).left).arrow _ _ (t.hom i)).line.hom ≫
      (((pull L (f i).left).line Y).hom ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

include H in
lemma underlyingArrowIso_compatible {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    {X Y : (group L T.left).Objects} {b : BaseMap k L A B K Q T}
    (mx : Classified X b) (my : Classified Y b)
    (t : (C.functor.toDescentData f).obj X ⟶ (C.functor.toDescentData f).obj Y) :
    IsoCompatible (fun i => (f i).left) mx.root my.root (underlyingArrowIso C f t) := by
  intro i
  rw [underlyingArrowIso_hom]
  let P := pull L (f i).left
  let nx := classifiedPull H (f i) P X mx (mapBase k L A B K Q (f i) b) rfl
  let ny := classifiedPull H (f i) P Y my (mapBase k L A B K Q (f i) b) rfl
  let d := compare (f i).left b.val ((f i).left ≫ b.val) rfl (ModularHodge k L A B K Q)
  apply (cancel_mono d.hom).1
  simp only [Category.assoc]
  exact square_conjugate (P.line X) (P.line Y)
    ((group L (V i).left).arrow _ _ (t.hom i)).line.hom
    _ _ _ _ (classified_pull_square H (f i) P X mx nx rfl)
    (classified_pull_square H (f i) P Y my ny rfl)
    (arrow_root_square H nx ny ((group L (V i).left).arrow _ _ (t.hom i)))

include H in
/-- A compatible local actual arrow identifies the global classifiers. -/
lemma classifier_of_descentArrow {T : Over (Base k)} {ι : Type 1}
    {V : ι → Over (Base k)} (f : ∀ i, V i ⟶ T)
    (ho : ∀ i, IsOpenImmersion (f i).left)
    (hc : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base)
    {X Y : (group L T.left).Objects}
    (t : (C.functor.toDescentData f).obj X ⟶ (C.functor.toDescentData f).obj Y) :
    classifier H X = classifier H Y := by
  let U : T.left.OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => (V i).left) (fun i => (f i).left) hc ho
  apply U.hom_ext
  intro i
  have hi := classifier_arrow H (G := group L (V i).left) (t.hom i)
  change classifier H ((pull L (f i).left).functor.obj X) =
    classifier H ((pull L (f i).left).functor.obj Y) at hi
  rw [classifier_pull H (f i), classifier_pull H (f i)] at hi
  exact hi

include H in
lemma categorical_full (hL : 3 ≤ L) (heven : Even L)
    {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T)
    (ho : ∀ i, IsOpenImmersion (f i).left)
    (hc : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base) :
    (C.functor.toDescentData f).Full := by
  letI : ∀ i, IsOpenImmersion (f i).left := ho
  constructor
  intro X Y t
  let b : BaseMap k L A B K Q T := ⟨classifier H X, (classifier_spec H X).1⟩
  let mx := classified H X b rfl
  let my := classified H Y b (classifier_of_descentArrow H C f ho hc t).symm
  have hW : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback b.val).obj
      (ModularHodge k L A B K Q)) :=
    invertible_of_iso mx.root.square.symm
      (ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorPower_invertible
        mx.root.line mx.root.invertible 2)
  obtain ⟨z, hz, _⟩ := root_iso_descent_family (fun i => (f i).left)
    (fun M N _ _ => Scheme.Modules.toDescentData_map_bijective_of_openCover
      (fun i => (f i).left) hc M N) _ hW mx.root my.root (underlyingArrowIso C f t)
    (underlyingArrowIso_compatible H C f mx my t)
  obtain ⟨a, ha⟩ := NaturalComparisonProof.arrow_of_square hL heven H mx.model my.model
    X.root Y.root z.val z.property
  let g : X ⟶ Y := ((group L T.left).arrow X Y).symm a
  have hg : ((group L T.left).arrow _ _ g).line.hom = z.val.hom := by
    simpa only [g, Equiv.apply_symm_apply] using ha
  refine ⟨g, ?_⟩
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  apply NaturalComparisonProof.line_faithful H (group L (V i).left)
  have hi := congrArg (fun e => e.hom.hom i) hz
  change (Scheme.Modules.pullback (f i).left).map z.val.hom =
    (underlyingArrowIso C f t).hom.hom i at hi
  rw [underlyingArrowIso_hom] at hi
  apply (cancel_mono ((pull L (f i).left).line Y).hom).1
  change ((group L (V i).left).arrow _ _ ((pull L (f i).left).functor.map g)).line.hom ≫ _ = _
  exact ((pull L (f i).left).line_natural X Y g).trans
    ((congrArg (fun q => ((pull L (f i).left).line X).hom ≫ q)
      ((congrArg (Scheme.Modules.pullback (f i).left).map hg).trans hi)).trans
        (Iso.hom_inv_id_assoc _ _))



include H in
/-- Effectivity for every actual family datum over an arbitrary open cover. -/
lemma categorical_essSurj (hL : 3 ≤ L) (heven : Even L)
    {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T)
    (ho : ∀ i, IsOpenImmersion (f i).left)
    (hc : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base) :
    (C.functor.toDescentData f).EssSurj := by
  letI : ∀ i, IsOpenImmersion (f i).left := ho
  constructor
  intro D
  obtain ⟨b, hb, _⟩ := classifier_glue H C f ho hc D
  let m (i : ι) : Classified (D.obj i) (mapBase k L A B K Q (f i) b) :=
    classified H (D.obj i) (mapBase k L A B K Q (f i) b) (hb i).symm
  let RD := rootDatum C f D b m
  have hW : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback b.val).obj
      (ModularHodge k L A B K Q)) := by
    apply invertible_of_open_cover (fun i => (f i).left) hc
    intro i
    exact invertible_of_iso (RD.square i).symm
      (ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorPower_invertible
        (RD.data.obj i) (RD.invertible i) 2)
  exact effective_actual H C hL heven f D b m
    (RootBridge.effective (fun i => (f i).left) ho hc hW RD (rootDatum_compatible H C f D b m))

include H in
lemma categorical_equivalence (hL : 3 ≤ L) (heven : Even L)
    {T : Over (Base k)} {ι : Type 1} {V : ι → Over (Base k)}
    (f : ∀ i, V i ⟶ T)
    (ho : ∀ i, IsOpenImmersion (f i).left)
    (hc : ∀ t : T.left, ∃ i, t ∈ Set.range (f i).left.base) :
    (C.functor.toDescentData f).IsEquivalence where
  faithful := categorical_faithful H C f ho hc
  full := categorical_full H C hL heven f ho hc
  essSurj := categorical_essSurj H C hL heven f ho hc

end ActualFamilyOpenDescentProof

open CategoryTheory AlgebraicGeometry
/-- Actual root-bearing marked elliptic families satisfy categorical descent
along every jointly covering open family, including infinite and empty covers. -/
theorem actual_family_open_descent :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (C : ArithmeticThetaMetaplecticStackR0207.Coherence L
        (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ArithmeticThetaRootStackR0198.OpenDescent C.functor := by
  intro k _ _ L hL heven C
  obtain ⟨A⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction k L hL
  obtain ⟨B, hB, K, Q, H⟩ := ArithmeticThetaSchemeHodgeR0205.scheme_hodge_universal k L hL heven A
  intro T ι V f ho hc
  exact ActualFamilyOpenDescentProof.categorical_equivalence H C hL heven f ho hc

#print axioms actual_family_open_descent

end ArithmeticThetaMetaplecticStackR0207
