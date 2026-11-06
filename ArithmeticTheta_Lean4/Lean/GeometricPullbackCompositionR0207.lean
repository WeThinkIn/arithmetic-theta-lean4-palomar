import MetaplecticStackDefinitionsR0207

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticStackR0207
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaCoverComparison
namespace GeometricCompositionProof

variable {L : ℕ} {S T U : Scheme.{0}}

structure Model (a : T ⟶ S) (X : Object L S) where
  obj : Object L T
  curve : obj.family.curve ⟶ X.family.curve
  marked : MarkedCartesian X.family obj.family X.marking obj.marking a curve
  cotangent : (Scheme.Modules.pullback a).obj (Cotangent X.family) ≅ Cotangent obj.family
  canonical : CotangentCompatible X.family obj.family a curve marked.2.1 cotangent
  line : obj.root.line ≅ (Scheme.Modules.pullback a).obj X.root.line
  square : tensorPowerMap line.hom 2 ≫ (squarePull a X.root).hom ≫ cotangent.hom =
    obj.root.square.hom

/-- Auxiliary literal pullback root, used only to invoke the accepted Cartesian
curve comparison. Its family, marking, projection and cotangent are unchanged. -/
def Model.geometry {a : T ⟶ S} {X : Object L S} (M : Model a X) :
    ActualPullbackProof.Lift a X where
  obj := ⟨M.obj.family, M.obj.marking, ⟨_, X.root.invertible.pullback a,
    squarePull a X.root ≪≫ M.cotangent⟩⟩
  curve := M.curve
  marked := M.marked
  cotangent := M.cotangent
  canonical := M.canonical
  line_eq := rfl
  square := by simp

variable {a : T ⟶ S} {X : Object L S}

def comparisonCurve (M N : Model a X) : M.obj.family.curve ≅ N.obj.family.curve :=
  ActualPullbackProof.curveIso M.geometry N.geometry (ActualGroupoidProof.identity X)

lemma comparisonCurve_fst (M N : Model a X) :
    (comparisonCurve M N).hom ≫ N.curve = M.curve := by
  simpa only [comparisonCurve, ActualPullbackProof.curveIso, Model.geometry,
    ActualGroupoidProof.identity, Iso.refl_hom, Category.comp_id] using
    ActualPullbackProof.curveMap_fst M.geometry N.geometry (ActualGroupoidProof.identity X)

lemma comparisonCurve_marked (M N : Model a X) :
    MarkedCartesian N.obj.family M.obj.family N.obj.marking M.obj.marking
      (𝟙 T) (comparisonCurve M N).hom :=
  ActualPullbackProof.curveMap_marked M.geometry N.geometry (ActualGroupoidProof.identity X)

def comparisonBackward (M N : Model a X) : Cotangent N.obj.family ≅ Cotangent M.obj.family :=
  ActualGroupoidProof.backward _ (comparisonCurve_marked M N).1
    (comparisonCurve_marked M N).2.1

lemma comparison_cotangent (M N : Model a X) :
    N.cotangent.hom ≫ (comparisonBackward M N).hom = M.cotangent.hom := by
  have h := ActualPullbackProof.cotangent_natural M.geometry N.geometry
    (ActualGroupoidProof.identity X)
  simpa only [comparisonBackward, comparisonCurve, Model.geometry,
    ActualGroupoidProof.identity, Iso.refl_inv, CategoryTheory.Functor.map_id, Category.id_comp] using h.symm

def comparison (M N : Model a X) : Arrow M.obj N.obj where
  curve := comparisonCurve M N
  marked := comparisonCurve_marked M N
  cotangent := (comparisonBackward M N).symm
  canonical := ActualGroupoidProof.backward_canonical _
    (comparisonCurve_marked M N).1 (comparisonCurve_marked M N).2.1
  line := M.line ≪≫ N.line.symm
  square := by
    apply (cancel_mono (comparisonBackward M N).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← N.square, ← M.square]
    simp only [Iso.trans_hom, Iso.symm_hom, tensorPowerMap_comp, Category.assoc]
    rw [← Category.assoc (tensorPowerMap N.line.inv 2), ← tensorPowerMap_comp,
      Iso.inv_hom_id, tensorPowerMap_id, Category.id_comp, comparison_cotangent]

lemma comparison_line (M N : Model a X) :
    (comparison M N).line.hom ≫ N.line.hom = M.line.hom := by
  simp [comparison]

def ofPull {GS : GroupoidData L S} {GT : GroupoidData L T}
    (P : PullbackData GS GT a) (X : GS.Objects) : Model a X :=
  ⟨P.functor.obj X, P.curve X, P.marked X, P.cotangent X, P.canonical X,
    P.line X, P.square X⟩

lemma marked_comp {a : T ⟶ S} {b : U ⟶ T}
    {X : Object L S} {Y : Object L T} {Z : Object L U}
    {f : Y.family.curve ⟶ X.family.curve} {g : Z.family.curve ⟶ Y.family.curve}
    (hf : MarkedCartesian X.family Y.family X.marking Y.marking a f)
    (hg : MarkedCartesian Y.family Z.family Y.marking Z.marking b g) :
    MarkedCartesian X.family Z.family X.marking Z.marking (b ≫ a) (g ≫ f) := by
  refine ⟨hg.1.paste_horiz hf.1, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hg.2.1, Category.assoc, hf.2.1, Category.assoc]
  · intro V t x y x' y' hx hy
    let xx : SchemeHomOver (t ≫ b) Y.family.p :=
      ⟨x.val ≫ g, by rw [Category.assoc, hg.1.w, ← Category.assoc, x.property]⟩
    let yy : SchemeHomOver (t ≫ b) Y.family.p :=
      ⟨y.val ≫ g, by rw [Category.assoc, hg.1.w, ← Category.assoc, y.property]⟩
    have hh := hf.2.2.1 V (t ≫ b) xx yy
      ⟨x'.val, by simpa only [Category.assoc] using x'.property⟩
      ⟨y'.val, by simpa only [Category.assoc] using y'.property⟩
      (by simpa only [xx, Category.assoc] using hx)
      (by simpa only [yy, Category.assoc] using hy)
    have h := hg.2.2.1 V t x y xx yy rfl rfl
    exact hh.trans ((congrArg (fun q => q ≫ f) h).trans (Category.assoc _ _ _))
  · rw [← Category.assoc, hg.2.2.2.1, Category.assoc, hf.2.2.2.1, Category.assoc]
  · rw [← Category.assoc, hg.2.2.2.2, Category.assoc, hf.2.2.2.2, Category.assoc]

variable {GS : GroupoidData L S} {GT : GroupoidData L T} {GU : GroupoidData L U}
  {a : T ⟶ S} {b : U ⟶ T}
  (P : PullbackData GS GT a) (Q : PullbackData GT GU b)

def composite (X : GS.Objects) : Model (b ≫ a) X := by
  let Y := P.functor.obj X
  let Z := Q.functor.obj Y
  have hm := marked_comp (P.marked X) (Q.marked Y)
  let i := Classical.choose (cartesian_identity_ideal S U X.family Z.family (b ≫ a)
    (Q.curve Y ≫ P.curve X) hm.1 hm.2.1)
  have hi := (Classical.choose_spec (cartesian_identity_ideal S U X.family Z.family (b ≫ a)
    (Q.curve Y ≫ P.curve X) hm.1 hm.2.1)).1
  let e := cotangentComparison X.family Z.family (b ≫ a) _ hm.2.1 i
  have he : CotangentCompatible X.family Z.family (b ≫ a) _ hm.2.1 e := ⟨i, hi, rfl⟩
  have hc := scheme_cotangent_coherence.2 S T U X.family Y.family Z.family a b
    (P.curve X) (Q.curve Y) (P.marked X).2.1 (Q.marked Y).2.1 hm.2.1
    (P.cotangent X) (Q.cotangent Y) e (P.canonical X) (Q.canonical Y) he
  let l := Q.line Y ≪≫ (Scheme.Modules.pullback b).mapIso (P.line X) ≪≫
    (Scheme.Modules.pullbackComp b a).app X.root.line
  have hs : tensorPowerMap l.hom 2 ≫ (squarePull (b ≫ a) X.root).hom ≫ e.hom =
      Z.root.square.hom := by
    simp only [l, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      tensorPowerMap_comp, Category.assoc]
    rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullbackComp b a).hom.app _) 2),
      ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.square_comp]
    simp only [Category.assoc]
    simp only [Iso.app_hom] at hc
    erw [← hc]
    rw [← Category.assoc (tensorPowerMap ((Scheme.Modules.pullback b).map (P.line X).hom) 2),
      ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196.power_natural_inv
        b Y.root.invertible (P.line X).hom 2]
    simp only [Category.assoc]
    have hs := congrArg ((Scheme.Modules.pullback b).map) (P.square X)
    simp only [Functor.map_comp] at hs
    rw [reassoc_of% hs]
    exact Q.square Y
  exact ⟨Z, _, hm, e, he, l, hs⟩

variable (R : PullbackData GS GU (b ≫ a))

def component (X : GS.Objects) : R.functor.obj X ⟶ (P.functor ⋙ Q.functor).obj X :=
  (GU.arrow _ _).symm (comparison (ofPull R X) (composite P Q X))

lemma component_curve (X : GS.Objects) :
    (GU.arrow _ _ (component P Q R X)).curve.hom ≫
      Q.curve (P.functor.obj X) ≫ P.curve X = R.curve X := by
  change (GU.arrow _ _ ((GU.arrow _ _).symm _)).curve.hom ≫ _ = _
  rw [Equiv.apply_symm_apply]
  exact comparisonCurve_fst (ofPull R X) (composite P Q X)

lemma component_line (X : GS.Objects) :
    (GU.arrow _ _ (component P Q R X)).line.hom ≫
      (Q.line (P.functor.obj X)).hom ≫ (Scheme.Modules.pullback b).map (P.line X).hom =
    (R.line X).hom ≫ (Scheme.Modules.pullbackComp b a).inv.app X.root.line := by
  apply (cancel_mono ((Scheme.Modules.pullbackComp b a).hom.app X.root.line)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change (GU.arrow _ _ ((GU.arrow _ _).symm _)).line.hom ≫ _ = _
  rw [Equiv.apply_symm_apply]
  exact comparison_line (ofPull R X) (composite P Q X)

lemma normalized_ext {X Y : GS.Objects}
    (f g : R.functor.obj X ⟶ (P.functor ⋙ Q.functor).obj Y)
    (hc : (GU.arrow _ _ f).curve.hom ≫ Q.curve (P.functor.obj Y) ≫ P.curve Y =
      (GU.arrow _ _ g).curve.hom ≫ Q.curve (P.functor.obj Y) ≫ P.curve Y)
    (hl : (GU.arrow _ _ f).line.hom ≫ (Q.line (P.functor.obj Y)).hom ≫
        (Scheme.Modules.pullback b).map (P.line Y).hom =
      (GU.arrow _ _ g).line.hom ≫ (Q.line (P.functor.obj Y)).hom ≫
        (Scheme.Modules.pullback b).map (P.line Y).hom) : f = g := by
  apply (GU.arrow _ _).injective
  apply ActualGroupoidProof.arrow_ext
  · apply ((composite P Q Y).marked.1).hom_ext
    · exact hc
    · exact (GU.arrow _ _ f).marked.1.w.trans (GU.arrow _ _ g).marked.1.w.symm
  · exact (cancel_mono ((Q.line (P.functor.obj Y)).hom ≫
      (Scheme.Modules.pullback b).map (P.line Y).hom)).mp hl

lemma component_natural {X Y : GS.Objects} (f : X ⟶ Y) :
    R.functor.map f ≫ component P Q R Y =
      component P Q R X ≫ (P.functor ⋙ Q.functor).map f := by
  apply normalized_ext P Q R
  · simp only [GU.curve_comp, Functor.comp_map, Category.assoc]
    rw [component_curve, R.curve_natural]
    erw [reassoc_of% (Q.curve_natural _ _ (P.functor.map f)), P.curve_natural]
    erw [reassoc_of% (component_curve P Q R X)]
  · simp only [GU.line_comp, Functor.comp_map, Category.assoc]
    rw [component_line, ← Category.assoc, R.line_natural]
    erw [reassoc_of% (Q.line_natural _ _ (P.functor.map f))]
    rw [← Functor.map_comp, P.line_natural, Functor.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% (component_line P Q R X)]
    exact congrArg (fun q => (R.line X).hom ≫ q)
      ((Scheme.Modules.pullbackComp b a).inv.naturality (GS.arrow _ _ f).line.hom)

lemma exists_unique : ∃! e : R.functor ≅ P.functor ⋙ Q.functor,
    CompNormalized P Q R e := by
  let e := NatIso.ofComponents (fun X => asIso (component P Q R X))
    (fun f => component_natural P Q R f)
  have he : CompNormalized P Q R e := fun X =>
    ⟨component_curve P Q R X, component_line P Q R X⟩
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact normalized_ext P Q R _ _ ((hd X).1.trans (he X).1.symm)
    ((hd X).2.trans (he X).2.symm)

end GeometricCompositionProof

/-- The uniquely normalized geometric comparison between direct and successive
pullback, retaining both actual Cartesian projections and the specified line maps. -/
theorem geometric_pullback_composition :
    ∀ (L : ℕ) (S T U : AlgebraicGeometry.Scheme.{0})
      (GS : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L S)
      (GT : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L T)
      (GU : ArithmeticThetaMetaplecticComparisonR0206.GroupoidData L U)
      (a : Quiver.Hom T S) (b : Quiver.Hom U T)
      (P : ArithmeticThetaMetaplecticComparisonR0206.PullbackData GS GT a)
      (Q : ArithmeticThetaMetaplecticComparisonR0206.PullbackData GT GU b)
      (R : ArithmeticThetaMetaplecticComparisonR0206.PullbackData GS GU
        (CategoryTheory.CategoryStruct.comp b a)),
      ∃! e : CategoryTheory.Iso R.functor (CategoryTheory.Functor.comp P.functor Q.functor),
        ArithmeticThetaMetaplecticStackR0207.CompNormalized P Q R e := by
  intro L S T U GS GT GU a b P Q R
  exact GeometricCompositionProof.exists_unique P Q R

#print axioms geometric_pullback_composition
end ArithmeticThetaMetaplecticStackR0207
