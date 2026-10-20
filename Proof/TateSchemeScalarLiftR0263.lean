module

public import TateSchemeMarkingDefinitionsR0263

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaTateSchemeMarkingR0263
namespace ScalarLift
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

def pullbackEquivalence {X Y : Scheme} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId Y).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
      Scheme.Modules.pullbackId X)

lemma changeLine_bijective {X : Scheme} (f : X ⟶ X) {M N : X.Modules} (c : M ≅ N) :
    Function.Bijective (SectionAction.changeLine f c) := by
  have hinv (a : (Scheme.Modules.pullback f).obj M ≅ M) :
      SectionAction.changeLine f c.symm (SectionAction.changeLine f c a) = a := by
    ext
    simp [SectionAction.changeLine]
  have hinv' (a : (Scheme.Modules.pullback f).obj N ≅ N) :
      SectionAction.changeLine f c (SectionAction.changeLine f c.symm a) = a := by
    ext
    simp [SectionAction.changeLine]
  exact ⟨Function.LeftInverse.injective hinv, Function.RightInverse.surjective hinv'⟩

lemma baseChangedLift_bijective {X Y : Scheme} (e : X ≅ Y)
    (f : Y ⟶ Y) (g : X ⟶ X) (h : e.hom ≫ f = g ≫ e.hom) (M : Y.Modules) :
    Function.Bijective (SectionAction.baseChangedLift e.hom f g h (M := M)) := by
  letI : (Scheme.Modules.pullback e.hom).IsEquivalence :=
    (pullbackEquivalence e).isEquivalence_functor
  constructor
  · intro a b hab
    apply (Scheme.Modules.pullback e.hom).mapIso_injective
    apply Iso.ext
    have hh := congrArg Iso.hom hab
    exact (cancel_epi _).mp hh
  · intro b
    let s := ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.squareIso
      f e.hom e.hom g h M
    refine ⟨(Scheme.Modules.pullback e.hom).preimageIso (s.symm ≪≫ b), ?_⟩
    apply Iso.ext
    simp [SectionAction.baseChangedLift, s]

lemma globalAct_comp {X : Scheme} (f g : X ⟶ X) {N : X.Modules}
    (a : (Scheme.Modules.pullback f).obj N ≅ N)
    (b : (Scheme.Modules.pullback g).obj N ≅ N) (v : Γ(N, ⊤)) :
    SectionAction.globalAct (f ≫ g) (Midpoint.composeLift f g N a b) v =
      SectionAction.globalAct f a (SectionAction.globalAct g b v) := by
  apply (SectionAction.globalSectionsEquiv N).injective
  change ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection N _ = ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection N _
  rw [← SectionAction.act_fromSection, ← SectionAction.act_fromSection,
    ← SectionAction.act_fromSection, SectionAction.act_comp]

lemma globalAct_identity {X : Scheme} {N : X.Modules} (v : Γ(N, ⊤)) :
    SectionAction.globalAct (𝟙 X) ((Scheme.Modules.pullbackId X).app N) v = v := by
  apply (SectionAction.globalSectionsEquiv N).injective
  change ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection N _ = ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection N _
  rw [← SectionAction.act_fromSection]
  exact SectionAction.pull_id _

lemma globalAct_changeMap {X : Scheme} {f g : X ⟶ X} (h : f = g) {N : X.Modules}
    (a : (Scheme.Modules.pullback g).obj N ≅ N) (v : Γ(N, ⊤)) :
    SectionAction.globalAct f ((Scheme.Modules.pullbackCongr h).app N ≪≫ a) v =
      SectionAction.globalAct g a v := by
  subst g
  rfl

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140

/-- Faithfulness is proved from the accepted complete basis and geometric cancellation. -/
lemma model_lift_ext (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d n : ℕ)
    (b : Fin n → GenericDual k M s d) (hb : ArithmeticThetaGeometricLiftsR0141.HasBasis k M s d n b)
    (hL : Scheme.Modules.IsInvertible (genericPower k M s d))
    {Y : Scheme} (E : genericScheme k M ≅ Y) (N : Y.Modules)
    (c : (Scheme.Modules.pullback E.hom).obj N ≅ Scheme.Modules.dual (genericPower k M s d))
    (f : genericScheme k M ⟶ genericScheme k M) [IsIso f] (g : Y ⟶ Y)
    (h : E.hom ≫ g = f ≫ E.hom) (e : ArithmeticThetaGeometricLiftsR0141.Lift k M s d f)
    (a a' : (Scheme.Modules.pullback g).obj N ≅ N)
    (haa : ∀ v, SectionAction.globalAct g a v = SectionAction.globalAct g a' v) : a = a' := by
  have he : LocalTheta.inducedIdealLift k M s d hL E N c f g h e a =
      LocalTheta.inducedIdealLift k M s d hL E N c f g h e a' := by
    apply ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141.lift_ext_of_basis
      k M s d n b hb
    intro i
    obtain ⟨v, hv⟩ := (LocalTheta.modelFunctionalEquiv k M s d E N c).surjective (b i)
    change LocalTheta.modelFunctional k M s d E N c v = b i at hv
    rw [← hv, LocalTheta.modelFunctional_act, LocalTheta.modelFunctional_act, haa]
  apply (baseChangedLift_bijective E g f h N).injective
  apply (changeLine_bijective f c).injective
  rw [← LocalTheta.inducedIdealLift_dual k M s d hL E N c f g h e a,
    ← LocalTheta.inducedIdealLift_dual k M s d hL E N c f g h e a', he]

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (V : TateLevel k (2*m)) {ζ : kˣ} (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)

lemma scalar_square : Q.cubic.hom ≫ translation (family k V) (pointX k V) =
    Q.mapA ≫ Q.cubic.hom := by
  letI := V.elliptic
  have hn := ArithmeticThetaSchemeKatoUnitR0250.SchemeMultiplicationDegree.weierstrass_multiple
    (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw (𝟙 _) V.marking.x 2
  change Q.cubic.hom ≫ ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.shift V.law
    (ArithmeticThetaSchemeLevelR0204.multiple (family k V) (𝟙 _) 2 V.marking.x) = _
  rw [hn]
  exact Q.scalar_commutes.symm

lemma existsUnique_matches (g : (family k V).curve ⟶ (family k V).curve)
    (f : ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model ⟶
      ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model)
    (h : Q.cubic.hom ≫ g = f ≫ Q.cubic.hom)
    (e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m f) :
    ∃! a : Lift (family k V) m g, Matches k V Q he g f a e := by
  have hb := (changeLine_bijective f (modelComparison k V Q he)).comp
    (baseChangedLift_bijective Q.cubic g f h (thetaLine (family k V) m))
  obtain ⟨a, ha⟩ := hb.surjective (LocalTheta.dualLift f _ (Q.ideal_invertible he) e.symm)
  refine ⟨a, ⟨h, ha⟩, ?_⟩
  intro b hb'
  obtain ⟨h', hb'⟩ := hb'
  exact hb.injective (hb'.trans ha.symm)

lemma inversion_square : Q.cubic.hom ≫ inverse (family k V) = Q.mapS ≫ Q.cubic.hom :=
  Q.inversion_commutes.symm

lemma matches_act (g : (family k V).curve ⟶ (family k V).curve)
    (f : genericScheme k Q.model ⟶ genericScheme k Q.model)
    (a : Lift (family k V) m g)
    (e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m f)
    (ha : Matches k V Q he g f a e) (v : Γ(thetaLine (family k V) m, ⊤)) :
    sectionEquiv k V Q he (SectionAction.globalAct g a v) =
      ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m f e
        (sectionEquiv k V Q he v) := by
  obtain ⟨h, ha⟩ := ha
  change LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ _ _ =
    ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m f e
      (LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ _ v)
  unfold LocalTheta.modelFunctional
  rw [← LocalTheta.genericDual_globalAct k Q.model Q.origin m (Q.ideal_invertible he) f e,
    ← ha, SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]
  rfl

lemma matched_scalar_alternating (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointX k V)))
    (ha : Matches k V Q he _ Q.mapA a (Q.canonicalA he hζ))
    (ι : Lift (family k V) m (inverse (family k V)))
    (hι : NormalizedInversion (family k V) m ι)
    (v : Γ(thetaLine (family k V) m, ⊤)) :
    SectionAction.globalAct _ ι (SectionAction.globalAct _ a
      (SectionAction.globalAct _ ι (SectionAction.globalAct _ a v))) = v := by
  let eS := LocalTheta.inducedIdealLift k Q.model Q.origin m (Q.ideal_invertible he)
    Q.cubic _ (modelComparison k V Q he) Q.mapS (inverse (family k V))
    (inversion_square k V Q) (Q.canonicalS he) ι
  have hιact : ∀ w, SectionAction.globalAct _ ι (SectionAction.globalAct _ ι w) = w :=
    SectionAction.globalAct_square _ hι.2.choose ι hι.2.choose_spec
  have heS : ∀ φ, ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m Q.mapS eS
      (ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m Q.mapS eS φ) = φ :=
    LocalTheta.inducedIdealLift_square k Q.model Q.origin m (Q.ideal_invertible he)
      Q.cubic _ (modelComparison k V Q he) Q.mapS _ (inversion_square k V Q)
      (Q.canonicalS he) ι hιact
  have hsym := (LocalTheta.symmetric_change_inversion k Q.model Q.origin m m
    (thetaChartBound m hm he) Q.isModel Q.markedOrigin hm _
    (generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin)
    Q.mapA Q.mapS
    (ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.scalarMap_over
      k Q.model Q.rotation Q.scaling Q.inversion Q.actions (ζ^2))
    (ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141.inversionMap_structure
      k Q.model Q.rotation Q.scaling Q.inversion Q.actions)
    (Q.canonicalA he hζ) (Q.canonicalS he) eS
    (Q.canonical_relations he hζ).2.2.2.1 heS).mpr
      (Q.canonical_relations he hζ).2.2.2.2.1
  have hiMatch : Matches k V Q he _ Q.mapS ι eS :=
    ⟨inversion_square k V Q, (LocalTheta.inducedIdealLift_dual k Q.model Q.origin m
      (Q.ideal_invertible he) Q.cubic _ (modelComparison k V Q he) Q.mapS _
      (inversion_square k V Q) (Q.canonicalS he) ι).symm⟩
  apply (sectionEquiv k V Q he).injective
  rw [matches_act k V Q he _ _ ι eS hiMatch,
    matches_act k V Q he _ _ a _ ha,
    matches_act k V Q he _ _ ι eS hiMatch,
    matches_act k V Q he _ _ a _ ha]
  exact hsym _

include Q he in
lemma symmetric_of_alternating
    (a : Lift (family k V) m (translation (family k V) (pointX k V)))
    (ι : Lift (family k V) m (inverse (family k V)))
    (hι : NormalizedInversion (family k V) m ι)
    (halt : ∀ v, SectionAction.globalAct _ ι (SectionAction.globalAct _ a
      (SectionAction.globalAct _ ι (SectionAction.globalAct _ a v))) = v) :
    Symmetric (family k V) m (pointX k V) ι a := by
  let E := family k V
  let r := reflection E (pointX k V)
  let φ := reflectionLift E m (pointX k V) ι a
  have hr : r ≫ r = 𝟙 E.curve :=
    SchemeMidpointThetaLift.reflection_square E (pointX k V)
  have hιact : ∀ w, SectionAction.globalAct _ ι (SectionAction.globalAct _ ι w) = w :=
    SectionAction.globalAct_square _ hι.2.choose ι hι.2.choose_spec
  have hφ : ∀ v, SectionAction.globalAct r φ (SectionAction.globalAct r φ v) = v := by
    intro v
    change SectionAction.globalAct _ (Midpoint.composeLift _ _ _ a ι)
      (SectionAction.globalAct _ (Midpoint.composeLift _ _ _ a ι) v) = v
    rw [globalAct_comp, globalAct_comp]
    have hh := congrArg (SectionAction.globalAct _ ι) (halt (SectionAction.globalAct _ ι v))
    simpa only [hιact] using hh
  have heq : compose E m r r φ φ = changeMap E m hr (identityLift E m) := by
    apply model_lift_ext k Q.model Q.origin m m _
      (generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin)
      (Q.ideal_invertible he) Q.cubic _ (modelComparison k V Q he) (𝟙 _) (r ≫ r)
      (by
        rw [hr]
        exact (Category.comp_id Q.cubic.hom).trans (Category.id_comp Q.cubic.hom).symm)
      ((Scheme.Modules.pullbackId _).app _).symm
    intro v
    change SectionAction.globalAct (r ≫ r) (Midpoint.composeLift r r _ φ φ) v =
      SectionAction.globalAct (r ≫ r)
        ((Scheme.Modules.pullbackCongr hr).app _ ≪≫ (Scheme.Modules.pullbackId _).app _) v
    rw [globalAct_comp, globalAct_changeMap, globalAct_identity, hφ]
  refine ⟨hr, ?_⟩
  change (Scheme.Modules.pullback r).mapIso φ ≪≫ φ = squareComparison E m r hr
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp r r).app (thetaLine E m)).inv).mp
  simpa only [compose, changeMap, identityLift, squareComparison, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using congrArg Iso.hom heq

#print axioms model_lift_ext
#print axioms matches_act
#print axioms matched_scalar_alternating
#print axioms symmetric_of_alternating

#print axioms existsUnique_matches
end ScalarLift

open ArithmeticThetaTateCuspsR0181 ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

theorem tate_scheme_scalar_lift :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
      (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
      ∀ Q : LocalTheta.MarkedModel k m hm V ζ,
      ∃! a : Lift (family k V) m (translation (family k V) (pointX k V)),
        scalarLiftFacts k V Q he hζ a := by
  intro k _ _ m hm he V ζ hζ Q
  obtain ⟨a, ha, hu⟩ := ScalarLift.existsUnique_matches k V Q he _ Q.mapA
    (ScalarLift.scalar_square k V Q) (Q.canonicalA he hζ)
  refine ⟨a, ⟨ha, ?_⟩, fun b hb => hu b hb.1⟩
  intro ι hι
  exact ScalarLift.symmetric_of_alternating k V Q he a ι hι
    (ScalarLift.matched_scalar_alternating k V Q he hζ a ha ι hι)

#print axioms tate_scheme_scalar_lift
end ArithmeticThetaTateSchemeMarkingR0263
