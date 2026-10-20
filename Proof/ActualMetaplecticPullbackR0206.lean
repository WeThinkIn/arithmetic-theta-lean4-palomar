module

public import ActualMetaplecticGroupoidR0206

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticComparisonR0206
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaCoverComparison

namespace ActualPullbackProof
variable {L : ℕ} {S T : Scheme.{0}} (a : T ⟶ S)

/-- A chosen Cartesian family, retaining the actual pullback line. -/
structure Lift (X : Object L S) where
  obj : Object L T
  curve : obj.family.curve ⟶ X.family.curve
  marked : MarkedCartesian X.family obj.family X.marking obj.marking a curve
  cotangent : (Scheme.Modules.pullback a).obj (Cotangent X.family) ≅ Cotangent obj.family
  canonical : CotangentCompatible X.family obj.family a curve marked.2.1 cotangent
  line_eq : obj.root.line = (Scheme.Modules.pullback a).obj X.root.line
  square : tensorPowerMap (eqToHom line_eq) 2 ≫ (squarePull a X.root).hom ≫
    cotangent.hom = obj.root.square.hom

def lift (X : Object L S) : Lift a X := Classical.choice (by
  obtain ⟨F, f, hc, hz, hm⟩ := scheme_family_base_change S T X.family a
  obtain ⟨M, hM, _⟩ := cartesian_full_marking S T X.family F a f hc hz hm L X.marking
  obtain ⟨i, hi, _⟩ := cartesian_identity_ideal S T X.family F a f hc hz
  let e := cotangentComparison X.family F a f hz i
  exact ⟨{
    obj := ⟨F, M, ⟨(Scheme.Modules.pullback a).obj X.root.line,
      X.root.invertible.pullback a, squarePull a X.root ≪≫ e⟩⟩
    curve := f
    marked := ⟨hc, hz, hm, hM⟩
    cotangent := e
    canonical := ⟨i, hi, rfl⟩
    line_eq := rfl
    square := by simp
  }⟩)

variable {a} {X Y Z : Object L S}

/-- Universal-property lift of a curve arrow. -/
def curveMap (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    P.obj.family.curve ⟶ Q.obj.family.curve :=
  Q.marked.1.lift (P.curve ≫ f.curve.hom) P.obj.family.p (by
    rw [Category.assoc, show f.curve.hom ≫ Y.family.p = X.family.p from by simpa using f.marked.1.w]
    exact P.marked.1.w)

@[simp] lemma curveMap_fst (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    curveMap P Q f ≫ Q.curve = P.curve ≫ f.curve.hom := Q.marked.1.lift_fst _ _ _
@[simp] lemma curveMap_snd (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    curveMap P Q f ≫ Q.obj.family.p = P.obj.family.p := Q.marked.1.lift_snd _ _ _

lemma curveMap_identity (P : Lift a X) (f : Arrow X X) (hf : f.curve.hom = 𝟙 _) :
    curveMap P P f = 𝟙 _ := by
  apply P.marked.1.hom_ext <;> simp [hf]

lemma curveMap_comp (P : Lift a X) (Q : Lift a Y) (R : Lift a Z)
    (f : Arrow X Y) (g : Arrow Y Z) (h : Arrow X Z)
    (hh : h.curve.hom = f.curve.hom ≫ g.curve.hom) :
    curveMap P R h = curveMap P Q f ≫ curveMap Q R g := by
  apply R.marked.1.hom_ext <;> simp [Category.assoc, reassoc_of% (curveMap_fst P Q f), hh]

def curveIso (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    P.obj.family.curve ≅ Q.obj.family.curve where
  hom := curveMap P Q f
  inv := curveMap Q P (ActualGroupoidProof.inverse f)
  hom_inv_id := by
    rw [← curveMap_comp P Q P f (ActualGroupoidProof.inverse f)
      (ActualGroupoidProof.identity X) (by simp [ActualGroupoidProof.identity, ActualGroupoidProof.inverse])]
    exact curveMap_identity P _ rfl
  inv_hom_id := by
    rw [← curveMap_comp Q P Q (ActualGroupoidProof.inverse f) f
      (ActualGroupoidProof.identity Y) (by simp [ActualGroupoidProof.identity, ActualGroupoidProof.inverse])]
    exact curveMap_identity Q _ rfl

lemma curveMap_zero (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    P.obj.family.zero ≫ curveMap P Q f = 𝟙 T ≫ Q.obj.family.zero := by
  apply Q.marked.1.hom_ext
  · rw [Category.assoc, curveMap_fst, ← Category.assoc, P.marked.2.1, Category.assoc,
      f.marked.2.1, Category.id_comp, Category.id_comp, Q.marked.2.1]
  · simp only [Category.assoc, curveMap_snd, Category.id_comp]
    exact (P.obj.family.law.one (𝟙 T)).property.trans (Q.obj.family.law.one (𝟙 T)).property.symm

lemma curveMap_mult (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    Multiplicative Q.obj.family P.obj.family (𝟙 T) (curveMap P Q f) := by
  intro U t x y x' y' hx hy
  apply Q.marked.1.hom_ext
  · let xx : SchemeHomOver (t ≫ a) X.family.p :=
      ⟨x.val ≫ P.curve, by rw [Category.assoc, P.marked.1.w, ← Category.assoc, x.property]⟩
    let yy : SchemeHomOver (t ≫ a) X.family.p :=
      ⟨y.val ≫ P.curve, by rw [Category.assoc, P.marked.1.w, ← Category.assoc, y.property]⟩
    let xx' : SchemeHomOver ((t ≫ 𝟙 T) ≫ a) Y.family.p :=
      ⟨x'.val ≫ Q.curve, by rw [Category.assoc, Q.marked.1.w, ← Category.assoc, x'.property]⟩
    let yy' : SchemeHomOver ((t ≫ 𝟙 T) ≫ a) Y.family.p :=
      ⟨y'.val ≫ Q.curve, by rw [Category.assoc, Q.marked.1.w, ← Category.assoc, y'.property]⟩
    have hq := Q.marked.2.2.1 U (t ≫ 𝟙 T) x' y' xx' yy' rfl rfl
    have hp := P.marked.2.2.1 U t x y xx yy rfl rfl
    have hf := f.marked.2.2.1 U (t ≫ a) xx yy
      ⟨xx'.val, by simpa using xx'.property⟩ ⟨yy'.val, by simpa using yy'.property⟩
      (by dsimp [xx', xx]; rw [hx, Category.assoc, curveMap_fst, Category.assoc])
      (by dsimp [yy', yy]; rw [hy, Category.assoc, curveMap_fst, Category.assoc])
    simpa only [Category.comp_id] using hq.symm.trans (hf.trans (by rw [hp]; simp))
  · simp only [Category.assoc, curveMap_snd]
    exact (Q.obj.family.law.mul _ x' y').property.trans
      (by simpa using (P.obj.family.law.mul t x y).property.symm)

lemma curveMap_marked (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    MarkedCartesian Q.obj.family P.obj.family Q.obj.marking P.obj.marking
      (𝟙 T) (curveIso P Q f).hom := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp [curveIso]⟩,
    curveMap_zero P Q f, curveMap_mult P Q f, ?_, ?_⟩
  · apply Q.marked.1.hom_ext
    · simp only [curveIso, Category.assoc, curveMap_fst, Category.id_comp]
      rw [← Category.assoc, P.marked.2.2.2.1, Category.assoc, f.marked.2.2.2.1,
        Category.id_comp, Q.marked.2.2.2.1]
    · simp only [curveIso, Category.assoc, curveMap_snd, Category.id_comp]
      exact P.obj.marking.x.property.trans Q.obj.marking.x.property.symm
  · apply Q.marked.1.hom_ext
    · simp only [curveIso, Category.assoc, curveMap_fst, Category.id_comp]
      rw [← Category.assoc, P.marked.2.2.2.2, Category.assoc, f.marked.2.2.2.2,
        Category.id_comp, Q.marked.2.2.2.2]
    · simp only [curveIso, Category.assoc, curveMap_snd, Category.id_comp]
      exact P.obj.marking.y.property.trans Q.obj.marking.y.property.symm

/-- Coherence with an explicitly identified composite base map. -/
lemma coherence {A B C : Scheme.{0}} (E : Family A) (F : Family B) (G : Family C)
    (b : B ⟶ A) (a : C ⟶ B) (c : C ⟶ A) (hab : a ≫ b = c)
    (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve)
    (k : G.curve ⟶ E.curve) (hgk : g ≫ f = k)
    (zf : F.zero ≫ f = b ≫ E.zero) (zg : G.zero ≫ g = a ≫ F.zero)
    (zk : G.zero ≫ k = c ≫ E.zero)
    (ef : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (eg : (Scheme.Modules.pullback a).obj (Cotangent F) ≅ Cotangent G)
    (ek : (Scheme.Modules.pullback c).obj (Cotangent E) ≅ Cotangent G)
    (hf : CotangentCompatible E F b f zf ef)
    (hg : CotangentCompatible F G a g zg eg)
    (hk : CotangentCompatible E G c k zk ek) :
    (Scheme.Modules.pullback a).map ef.hom ≫ eg.hom =
      (Scheme.Modules.pullbackComp a b).hom.app (Cotangent E) ≫
        (Scheme.Modules.pullbackCongr hab).hom.app (Cotangent E) ≫ ek.hom := by
  subst c; subst k
  simpa [Scheme.Modules.pullbackCongr] using
    scheme_cotangent_coherence.2 A B C E F G b a f g zf zg zk ef eg ek hf hg hk

lemma pull_comp_id (a : T ⟶ S) (M : S.Modules) :
    (Scheme.Modules.pullbackComp a (𝟙 S)).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.comp_id a)).hom.app M =
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackId S).hom.app M) := by
  have h := congrArg (fun q ↦ q.app M) (Scheme.Modules.pseudofunctor_left_unitality a)
  apply (cancel_epi ((Scheme.Modules.pullbackComp a (𝟙 S)).inv.app M)).mp
  simpa [Scheme.Modules.pullbackCongr] using h.symm

lemma cotangent_natural (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    (Scheme.Modules.pullback a).map f.cotangent.inv ≫ P.cotangent.hom =
      Q.cotangent.hom ≫
        (ActualGroupoidProof.backward (curveIso P Q f).hom
          (curveMap_marked P Q f).1 (curveMap_marked P Q f).2.1).hom := by
  let b := ActualGroupoidProof.backward (curveIso P Q f).hom
    (curveMap_marked P Q f).1 (curveMap_marked P Q f).2.1
  have hc : IsPullback (P.curve ≫ f.curve.hom) P.obj.family.p Y.family.p a := by
    simpa using P.marked.1.paste_horiz f.marked.1
  have hz : P.obj.family.zero ≫ (P.curve ≫ f.curve.hom) = a ≫ Y.family.zero := by
    rw [← Category.assoc, P.marked.2.1, Category.assoc, f.marked.2.1, Category.id_comp]
  obtain ⟨i, hi, _⟩ := cartesian_identity_ideal S T Y.family P.obj.family a
    (P.curve ≫ f.curve.hom) hc hz
  let e := cotangentComparison Y.family P.obj.family a (P.curve ≫ f.curve.hom) hz i
  have he : CotangentCompatible Y.family P.obj.family a (P.curve ≫ f.curve.hom) hz e := ⟨i, hi, rfl⟩
  have h₁ := coherence Y.family X.family P.obj.family (𝟙 S) a a (Category.comp_id a)
    f.curve.hom P.curve (P.curve ≫ f.curve.hom) rfl f.marked.2.1 P.marked.2.1 hz
    ((Scheme.Modules.pullbackId S).app (Cotangent Y.family) ≪≫ f.cotangent.symm)
    P.cotangent e f.canonical P.canonical he
  have h₂ := coherence Y.family Q.obj.family P.obj.family a (𝟙 T) a (Category.id_comp a)
    Q.curve (curveIso P Q f).hom (P.curve ≫ f.curve.hom) (curveMap_fst P Q f)
    Q.marked.2.1 (curveMap_marked P Q f).2.1 hz Q.cotangent
    ((Scheme.Modules.pullbackId T).app (Cotangent Q.obj.family) ≪≫ b) e
    Q.canonical (ActualGroupoidProof.backward_canonical _ _ _) he
  rw [← Category.assoc, pull_comp_id] at h₁
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] at h₁
  have h₁' := (cancel_epi ((Scheme.Modules.pullback a).map
    ((Scheme.Modules.pullbackId S).hom.app (Cotangent Y.family)))).mp h₁
  rw [← Category.assoc,
    ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.comp_id] at h₂
  simp only [Iso.trans_hom, Iso.app_hom] at h₂
  rw [← Category.assoc, (Scheme.Modules.pullbackId T).hom.naturality] at h₂
  simp only [Functor.id_map, Category.assoc] at h₂
  have h₂' := (cancel_epi ((Scheme.Modules.pullbackId T).hom.app
    ((Scheme.Modules.pullback a).obj (Cotangent Y.family)))).mp h₂
  exact h₁'.trans h₂'.symm

def lineIso (P : Lift a X) : P.obj.root.line ≅ (Scheme.Modules.pullback a).obj X.root.line :=
  eqToIso P.line_eq

def lineMap (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    P.obj.root.line ≅ Q.obj.root.line :=
  lineIso P ≪≫ (Scheme.Modules.pullback a).mapIso f.line ≪≫ (lineIso Q).symm

lemma lineMap_natural (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    (lineMap P Q f).hom ≫ (lineIso Q).hom =
      (lineIso P).hom ≫ (Scheme.Modules.pullback a).map f.line.hom := by
  simp [lineMap]

lemma squarePull_natural (f : Arrow X Y) :
    tensorPowerMap ((Scheme.Modules.pullback a).map f.line.hom) 2 ≫ (squarePull a Y.root).hom =
      (squarePull a X.root).hom ≫ (Scheme.Modules.pullback a).map f.cotangent.hom := by
  simp only [squarePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc,
    ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.power_natural_inv
      a X.root.invertible f.line.hom 2]
  simp only [Category.assoc]
  rw [← Functor.map_comp, f.square, Functor.map_comp]

lemma cotangent_forward (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
    P.cotangent.hom ≫
        (ActualGroupoidProof.backward (curveIso P Q f).hom
          (curveMap_marked P Q f).1 (curveMap_marked P Q f).2.1).inv =
      (Scheme.Modules.pullback a).map f.cotangent.hom ≫ Q.cotangent.hom := by
  apply (cancel_mono (ActualGroupoidProof.backward (curveIso P Q f).hom
    (curveMap_marked P Q f).1 (curveMap_marked P Q f).2.1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← cotangent_natural, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The line arrow is the actual sheaf pullback and obeys the exact square. -/
def arrow (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) : Arrow P.obj Q.obj where
  curve := curveIso P Q f
  marked := curveMap_marked P Q f
  cotangent := (ActualGroupoidProof.backward (curveIso P Q f).hom
    (curveMap_marked P Q f).1 (curveMap_marked P Q f).2.1).symm
  canonical := ActualGroupoidProof.backward_canonical (curveIso P Q f).hom
    (curveMap_marked P Q f).1 (curveMap_marked P Q f).2.1
  line := lineMap P Q f
  square := by
    change tensorPowerMap (lineMap P Q f).hom 2 ≫ Q.obj.root.square.hom = _
    rw [← Q.square, ← P.square]
    change tensorPowerMap (lineMap P Q f).hom 2 ≫
      (tensorPowerMap (lineIso Q).hom 2 ≫ (squarePull a Y.root).hom ≫ Q.cotangent.hom) =
      (tensorPowerMap (lineIso P).hom 2 ≫ (squarePull a X.root).hom ≫ P.cotangent.hom) ≫ _
    rw [← Category.assoc (tensorPowerMap _ 2), ← tensorPowerMap_comp, lineMap_natural,
      tensorPowerMap_comp]
    simp only [Category.assoc, Iso.symm_hom]
    rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullback a).map f.line.hom) 2),
      squarePull_natural, Category.assoc, cotangent_forward]

lemma lineMap_identity (P : Lift a X) (f : Arrow X X) (hf : f.line.hom = 𝟙 _) :
    (lineMap P P f).hom = 𝟙 _ := by
  simp [lineMap, hf]

lemma lineMap_comp (P : Lift a X) (Q : Lift a Y) (R : Lift a Z)
    (f : Arrow X Y) (g : Arrow Y Z) (h : Arrow X Z)
    (hh : h.line.hom = f.line.hom ≫ g.line.hom) :
    (lineMap P R h).hom = (lineMap P Q f).hom ≫ (lineMap Q R g).hom := by
  simp [lineMap, hh]

variable (GS : GroupoidData L S) (GT : GroupoidData L T) (a : T ⟶ S)

def pullFunctor : GS.Objects ⥤ GT.Objects where
  obj X := (lift a X).obj
  map {X Y} f := (GT.arrow _ _).symm (arrow (lift a X) (lift a Y) (GS.arrow _ _ f))
  map_id X := by
    apply (GT.arrow _ _).injective
    rw [Equiv.apply_symm_apply]
    apply ActualGroupoidProof.arrow_ext
    · change curveMap (lift a X) (lift a X) (GS.arrow _ _ (𝟙 X)) = _
      rw [GT.curve_id]
      exact curveMap_identity _ _ (GS.curve_id X)
    · change (lineMap (lift a X) (lift a X) (GS.arrow _ _ (𝟙 X))).hom = _
      rw [GT.line_id]
      exact lineMap_identity _ _ (GS.line_id X)
  map_comp {X Y Z} f g := by
    apply (GT.arrow _ _).injective
    rw [Equiv.apply_symm_apply]
    apply ActualGroupoidProof.arrow_ext
    · rw [GT.curve_comp]
      simp only [Equiv.apply_symm_apply]
      exact curveMap_comp _ _ _ _ _ _ (GS.curve_comp X Y Z f g)
    · rw [GT.line_comp]
      simp only [Equiv.apply_symm_apply]
      exact lineMap_comp _ _ _ _ _ _ (GS.line_comp X Y Z f g)

/-- The simultaneous curve, canonical cotangent, and line comparisons. -/
def pullData : PullbackData GS GT a where
  functor := pullFunctor GS GT a
  curve X := (lift a X).curve
  marked X := (lift a X).marked
  cotangent X := (lift a X).cotangent
  canonical X := (lift a X).canonical
  line X := lineIso (lift a X)
  square X := (lift a X).square
  curve_natural X Y f := by
    change (GT.arrow _ _ ((GT.arrow _ _).symm _)).curve.hom ≫ _ = _
    rw [Equiv.apply_symm_apply]
    exact curveMap_fst _ _ _
  line_natural X Y f := by
    change (GT.arrow _ _ ((GT.arrow _ _).symm _)).line.hom ≫ _ = _
    rw [Equiv.apply_symm_apply]
    exact lineMap_natural _ _ _

end ActualPullbackProof

/-- Actual marked elliptic families with specified cotangent square roots admit
functorial pullback along every morphism of test schemes. -/
theorem actual_metaplectic_pullback :
    ∀ (L : ℕ) (S T : AlgebraicGeometry.Scheme.{0})
      (GS : GroupoidData L S) (GT : GroupoidData L T) (a : Quiver.Hom T S),
      Nonempty (PullbackData GS GT a) := by
  intro L S T GS GT a
  exact ⟨ActualPullbackProof.pullData GS GT a⟩

#print axioms actual_metaplectic_pullback
end ArithmeticThetaMetaplecticComparisonR0206
