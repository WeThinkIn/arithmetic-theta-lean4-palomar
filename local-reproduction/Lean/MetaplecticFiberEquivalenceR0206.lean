import ActualMetaplecticGroupoidR0206
import MarkedCartesianReconstructionR0206

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticComparisonR0206
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaCoverComparison

namespace FiberEquivalenceProof

variable {k : Type} [Field k] [CharZero k] {L : ℕ}
  {A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L}
  {B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A}
  {C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B}
  {Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C}
  {S : Over (Base k)}

/-- Chosen converse data depend only on the base map, not on the root. -/
structure Model (b : BaseMap k L A B C Q S) where
  family : Family S.left
  marking : FullLevel family L
  curve : family.curve ⟶ A.descent.family.curve
  classifies : Classifies k L A B C Q S.hom family marking b.val curve
  hodge : (Scheme.Modules.pullback b.val).obj (ModularHodge k L A B C Q) ≅ Cotangent family
  canonical : ClassifierHodge k L A B C Q family b.val curve hodge

lemma model_exists (H : HodgeUniversal k L A B C Q) (b : BaseMap k L A B C Q S) :
    Nonempty (Model b) := by
  obtain ⟨E, M, f, hf⟩ := H.1.2.1 S.left S.hom b.val b.property
  obtain ⟨e, he, _⟩ := H.2.1 S.left S.hom E M b.val f hf
  exact ⟨⟨E, M, f, hf, e, he⟩⟩

def model (H : HodgeUniversal k L A B C Q) (b : BaseMap k L A B C Q S) : Model b :=
  Classical.choice (model_exists H b)

def obj {b : BaseMap k L A B C Q S} (m : Model b)
    (r : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk b.val)) : Object L S.left :=
  ⟨m.family, m.marking, ⟨r.line, r.invertible, r.square ≪≫ m.hodge⟩⟩

lemma hom_ext (G : GroupoidData L S.left) {X Y : G.Objects} (f g : X ⟶ Y)
    (hc : (G.arrow _ _ f).curve.hom = (G.arrow _ _ g).curve.hom)
    (hl : (G.arrow _ _ f).line.hom = (G.arrow _ _ g).line.hom) : f = g :=
  (G.arrow _ _).injective (ActualGroupoidProof.arrow_ext _ _ hc hl)

def mapArrow {b : BaseMap k L A B C Q S} (m : Model b)
    {r t : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk b.val)} (f : r ⟶ t) :
    Arrow (obj m r) (obj m t) where
  curve := Iso.refl _
  marked := ActualGroupoidProof.marked_id (obj m r)
  cotangent := Iso.refl _
  canonical := (ActualGroupoidProof.identity (obj m r)).canonical
  line := f.val
  square := by
    change tensorPowerMap f.val.hom 2 ≫ (t.square.hom ≫ m.hodge.hom) =
      (r.square.hom ≫ m.hodge.hom) ≫ 𝟙 _
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun q => q ≫ m.hodge.hom) f.property

def component (G : GroupoidData L S.left) {b : BaseMap k L A B C Q S} (m : Model b) :
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk b.val) ⥤ G.Objects where
  obj := obj m
  map f := (G.arrow _ _).symm (mapArrow m f)
  map_id r := by
    apply hom_ext G
    · simp only [Equiv.apply_symm_apply, mapArrow, Iso.refl_hom, G.curve_id]
    · simp only [Equiv.apply_symm_apply, mapArrow, G.line_id]; rfl
  map_comp f g := by
    apply hom_ext G
    · simp only [Equiv.apply_symm_apply, mapArrow, Iso.refl_hom, G.curve_comp,
        Category.id_comp, obj]
    · simp only [Equiv.apply_symm_apply, mapArrow, G.line_comp]; rfl

def forward (G : GroupoidData L S.left) (m : ∀ b : BaseMap k L A B C Q S, Model b) :
    RootFiber k L A B C Q S ⥤ G.Objects := CategoryTheory.Sigma.desc (fun b => component G (m b))

lemma classifier_arrow (H : HodgeUniversal k L A B C Q)
    {b c : BaseMap k L A B C Q S} (m : Model b) (n : Model c)
    {r : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk b.val)}
    {t : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk c.val)}
    (f : Arrow (obj m r) (obj n t)) :
    b = c ∧ f.curve.hom ≫ n.curve = m.curve := by
  have h := H.1.2.2 S.left S.left S.hom S.hom n.family m.family n.marking m.marking
    (𝟙 S.left) f.curve.hom (Category.id_comp _) f.marked c.val b.val n.curve m.curve
    n.classifies m.classifies
  exact ⟨Subtype.ext (by simpa using h.1), h.2.symm⟩

lemma self_curve (H : HodgeUniversal k L A B C Q)
    {b : BaseMap k L A B C Q S} (m : Model b)
    {r t : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk b.val)}
    (f : Arrow (obj m r) (obj m t)) : f.curve.hom = 𝟙 m.family.curve := by
  apply m.classifies.2.1.hom_ext
  · change f.curve.hom ≫ m.curve = 𝟙 m.family.curve ≫ m.curve
    exact (classifier_arrow H m m f).2.trans (Category.id_comp _).symm
  · change f.curve.hom ≫ m.family.p = 𝟙 m.family.curve ≫ m.family.p
    have hh : f.curve.hom ≫ m.family.p = m.family.p ≫ 𝟙 S.left := f.marked.1.w
    exact hh.trans ((Category.comp_id _).trans (Category.id_comp _).symm)

lemma self_cotangent (H : HodgeUniversal k L A B C Q)
    {b : BaseMap k L A B C Q S} (m : Model b)
    {r t : ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber (ModularHodge k L A B C Q) (Over.mk b.val)}
    (f : Arrow (obj m r) (obj m t)) : f.cotangent.hom = 𝟙 (Cotangent m.family) := by
  have h := ActualGroupoidProof.arrow_backward f
  have hc := self_curve H m f
  change f.cotangent.symm = @ActualGroupoidProof.backward S.left m.family m.family
    f.curve.hom _ _ at h
  generalize_proofs at h
  simp only [hc] at h
  rw [ActualGroupoidProof.backward_id m.family] at h
  have hi := congrArg Iso.inv h
  simpa using hi

lemma natural_general (H : HodgeUniversal k L A B C Q)
    (E F : Family S.left) (a : S.left ⟶ S.left)
    (g : F.curve ⟶ E.curve) (hg : F.zero ≫ g = a ≫ E.zero)
    (b c : S.left ⟶ Base Q.quotient.ring) (hc : a ≫ b = c)
    (f : E.curve ⟶ A.descent.family.curve) (t : F.curve ⟶ A.descent.family.curve)
    (ht : g ≫ f = t)
    (eE : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E)
    (eF : (Scheme.Modules.pullback c).obj (ModularHodge k L A B C Q) ≅ Cotangent F)
    (eG : (Scheme.Modules.pullback a).obj (Cotangent E) ≅ Cotangent F)
    (hE : ClassifierHodge k L A B C Q E b f eE)
    (hF : ClassifierHodge k L A B C Q F c t eF)
    (hG : CotangentCompatible E F a g hg eG) :
    (Scheme.Modules.pullback a).map eE.hom ≫ eG.hom =
      (Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr hc).hom.app
        (ModularHodge k L A B C Q) ≫ eF.hom := by
  subst c; subst t
  simpa [Scheme.Modules.pullbackCongr] using
    H.2.2 S.left S.left E F a g hg b f eE eF eG hE hF hG

lemma hodge_backward (H : HodgeUniversal k L A B C Q)
    {b : BaseMap k L A B C Q S} (m n : Model b)
    (g : n.family.curve ⟶ m.family.curve)
    (hg : MarkedCartesian m.family n.family m.marking n.marking (𝟙 S.left) g)
    (ht : g ≫ m.curve = n.curve) :
    m.hodge.hom ≫ (ActualGroupoidProof.backward g hg.1 hg.2.1).hom = n.hodge.hom := by
  have h := natural_general H m.family n.family (𝟙 S.left) g hg.2.1 b.val b.val
    (Category.id_comp _) m.curve n.curve ht m.hodge n.hodge
    ((Scheme.Modules.pullbackId S.left).app _ ≪≫ ActualGroupoidProof.backward g hg.1 hg.2.1)
    m.canonical n.canonical (ActualGroupoidProof.backward_canonical g hg.1 hg.2.1)
  change (Scheme.Modules.pullback (𝟙 S.left)).map m.hodge.hom ≫
    ((Scheme.Modules.pullbackId S.left).hom.app _ ≫ _) =
    ((Scheme.Modules.pullbackComp (𝟙 S.left) b.val).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp b.val)).hom.app _) ≫ n.hodge.hom at h
  rw [ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.comp_id] at h
  rw [← Category.assoc ((Scheme.Modules.pullback (𝟙 S.left)).map m.hodge.hom)
    ((Scheme.Modules.pullbackId S.left).hom.app (Cotangent m.family))
    (ActualGroupoidProof.backward g hg.1 hg.2.1).hom,
    (Scheme.Modules.pullbackId S.left).hom.naturality m.hodge.hom] at h
  simp only [Functor.id_map, Category.assoc] at h
  exact (cancel_epi ((Scheme.Modules.pullbackId S.left).hom.app _)).mp h

lemma forward_faithful (G : GroupoidData L S.left)
    (m : ∀ b : BaseMap k L A B C Q S, Model b) : (forward G m).Faithful where
  map_injective := by
    rintro ⟨b, r⟩ ⟨_, t⟩ ⟨f⟩ ⟨g⟩ h
    congr 1
    apply ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.hom_ext
    have hh := congrArg (fun q => (G.arrow _ _ q).line.hom) h
    change (G.arrow _ _ ((G.arrow _ _).symm (mapArrow (m b) f))).line.hom =
      (G.arrow _ _ ((G.arrow _ _).symm (mapArrow (m b) g))).line.hom at hh
    simpa only [Equiv.apply_symm_apply, mapArrow] using hh

lemma forward_full (H : HodgeUniversal k L A B C Q) (G : GroupoidData L S.left)
    (m : ∀ b : BaseMap k L A B C Q S, Model b) : (forward G m).Full where
  map_surjective := by
    rintro ⟨b, r⟩ ⟨c, t⟩ f
    have hc := (classifier_arrow H (m b) (m c) (G.arrow _ _ f)).1
    subst c
    let d : Arrow (obj (m b) r) (obj (m b) t) := G.arrow _ _ f
    have hs : tensorPowerMap d.line.hom 2 ≫ t.square.hom = r.square.hom := by
      apply (cancel_mono (m b).hodge.hom).mp
      have h := d.square
      rw [self_cotangent H (m b) d] at h
      change tensorPowerMap d.line.hom 2 ≫ (t.square.hom ≫ (m b).hodge.hom) =
        (r.square.hom ≫ (m b).hodge.hom) ≫ 𝟙 _ at h
      simpa only [Category.assoc, Category.comp_id] using h
    let e : r ⟶ t := ⟨d.line, hs⟩
    refine ⟨CategoryTheory.Sigma.SigmaHom.mk e, ?_⟩
    apply hom_ext G
    · change (G.arrow _ _ ((G.arrow _ _).symm (mapArrow (m b) e))).curve.hom = d.curve.hom
      simp only [Equiv.apply_symm_apply, mapArrow, Iso.refl_hom]
      exact (self_curve H (m b) d).symm
    · change (G.arrow _ _ ((G.arrow _ _).symm (mapArrow (m b) e))).line.hom = d.line.hom
      simp only [Equiv.apply_symm_apply, mapArrow]
      rfl

/-- The root pulled back from an actual object uses its entire specified square. -/
def originalRoot {b : BaseMap k L A B C Q S} (n : Model b)
    (r : SquareLine S.left (Cotangent n.family)) :
    ArithmeticThetaRootStackR0198.RootModuliPseudofunctorR0198.Fiber
      (ModularHodge k L A B C Q) (Over.mk b.val) :=
  ⟨r.line, r.invertible, r.square ≪≫ n.hodge.symm⟩

lemma essential_arrow (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q)
    {b : BaseMap k L A B C Q S} (m n : Model b)
    (r : SquareLine S.left (Cotangent n.family)) :
    Nonempty (Arrow (obj m (originalRoot n r)) ⟨n.family, n.marking, r⟩) := by
  obtain ⟨g, ⟨hg, ht⟩, _⟩ := marked_cartesian_reconstruction k L hL heven A B C Q
    S.left S.left S.hom S.hom n.family m.family n.marking m.marking (𝟙 S.left)
    b.val b.val n.curve m.curve (Category.id_comp _) n.classifies m.classifies
    (Category.id_comp _).symm
  letI : IsIso g := hg.1.isIso_fst_of_isIso
  let d := ActualGroupoidProof.backward g hg.1 hg.2.1
  have hd : n.hodge.hom ≫ d.hom = m.hodge.hom := hodge_backward H n m g hg ht
  refine ⟨{
    curve := asIso g
    marked := hg
    cotangent := d.symm
    canonical := ActualGroupoidProof.backward_canonical g hg.1 hg.2.1
    line := Iso.refl _
    square := ?_
  }⟩
  change tensorPowerMap (𝟙 r.line) 2 ≫ r.square.hom =
    ((r.square.hom ≫ n.hodge.inv) ≫ m.hodge.hom) ≫ d.inv
  rw [tensorPowerMap_id, Category.id_comp]
  rw [← hd]
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]

lemma forward_essSurj (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q) (G : GroupoidData L S.left)
    (m : ∀ b : BaseMap k L A B C Q S, Model b) : (forward G m).EssSurj where
  mem_essImage X := by
    obtain ⟨b, ⟨f, hf, _⟩, _⟩ := H.1.1 S.left S.hom X.family X.marking
    obtain ⟨e, he, _⟩ := H.2.1 S.left S.hom X.family X.marking b f hf
    let bb : BaseMap k L A B C Q S := ⟨b, hf.1⟩
    let n : Model bb := ⟨X.family, X.marking, f, hf, e, he⟩
    let r := originalRoot n X.root
    obtain ⟨d⟩ := essential_arrow hL heven H (m bb) n X.root
    refine ⟨⟨bb, r⟩, ?_⟩
    exact ⟨asIso ((G.arrow _ _).symm d)⟩

def lineIso (G : GroupoidData L S.left)
    (m : ∀ b : BaseMap k L A B C Q S, Model b) :
    rootForget k L A B C Q S ≅ forward G m ⋙ lineForget G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro ⟨b, r⟩ ⟨_, t⟩ ⟨f⟩
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change f.val.hom = (G.arrow _ _ ((G.arrow _ _).symm (mapArrow (m b) f))).line.hom
    simp only [Equiv.apply_symm_apply, mapArrow])

/-- All constructions use the given groupoid presentation and fixed quotient. -/
def comparison (hL : 3 ≤ L) (heven : Even L)
    (H : HodgeUniversal k L A B C Q) (G : GroupoidData L S.left) :
    FiberComparison k L A B C Q S G := by
  let m : ∀ b : BaseMap k L A B C Q S, Model b := model H
  let F := forward G m
  letI : F.Faithful := forward_faithful G m
  letI : F.Full := forward_full H G m
  letI : F.EssSurj := forward_essSurj hL heven H G m
  letI : F.IsEquivalence := {}
  exact {
    equiv := F.asEquivalence
    line := lineIso G m
    curve := fun r => (m r.1).curve
    classifies := fun r => (m r.1).classifies
    cotangent := fun r => (m r.1).hodge
    canonical := fun r => (m r.1).canonical
    square := fun r => by
      change tensorPowerMap (𝟙 r.2.line) 2 ≫ (r.2.square ≪≫ (m r.1).hodge).hom = _
      simp only [tensorPowerMap_id, Category.id_comp, Iso.trans_hom]
  }

end FiberEquivalenceProof

/-- The actual marked families with their specified cotangent roots are equivalent
    to the accepted root categories over all maps to the same fixed quotient. -/
theorem metaplectic_fiber_equivalence :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C), ArithmeticThetaSchemeHodgeR0205.HodgeUniversal k L A B C Q → ∀ (S : CategoryTheory.Over (ArithmeticThetaLocalWeierstrassR0203.Base k)) (G : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L S.left), Nonempty (ArithmeticThetaMetaplecticComparisonR0206.FiberComparison k L A B C Q S G) := by
  intro k _ _ L hL heven A B C Q H S G
  exact ⟨FiberEquivalenceProof.comparison hL heven H G⟩

#print axioms metaplectic_fiber_equivalence
end ArithmeticThetaMetaplecticComparisonR0206
