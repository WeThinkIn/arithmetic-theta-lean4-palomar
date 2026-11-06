module

public import TateSchemeMarkingDefinitionsR0263
public import SchemeMidpointThetaLiftR0259

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaTateSchemeMarkingR0263
namespace ShiftLiftProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- An equivariant scheme isomorphism and a fixed line comparison give a
bijection on actual sheaf lifts. -/
lemma existsUnique_transport {X Y : Scheme} (c : Y ≅ X)
    (g : X ⟶ X) (f : Y ⟶ Y) (h : c.hom ≫ g = f ≫ c.hom)
    (L : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.pullback c.hom).obj L ≅ N)
    (β : (Scheme.Modules.pullback f).obj N ≅ N) :
    ∃! α : (Scheme.Modules.pullback g).obj L ≅ L,
      SectionAction.changeLine f e
        (SectionAction.baseChangedLift c.hom g f h α) = β := by
  let E := CategoryTheory.Equivalence.mk (Scheme.Modules.pullback c.hom)
    (Scheme.Modules.pullback c.inv)
    ((Scheme.Modules.pullbackId X).symm ≪≫ Scheme.Modules.pullbackCongr c.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp c.inv c.hom).symm)
    (Scheme.Modules.pullbackComp c.hom c.inv ≪≫ Scheme.Modules.pullbackCongr c.hom_inv_id ≪≫
      Scheme.Modules.pullbackId Y)
  letI : (Scheme.Modules.pullback c.hom).IsEquivalence := E.isEquivalence_functor
  let t := ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.squareIso
    g c.hom c.hom f h L
  let δ := t.symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫ β ≪≫ e.symm
  let α := (Scheme.Modules.pullback c.hom).preimageIso δ
  have hα : (Scheme.Modules.pullback c.hom).mapIso α = δ := by
    apply Iso.ext
    exact Functor.map_preimage _ _
  refine ⟨α, ?_, ?_⟩
  · dsimp only [SectionAction.changeLine, SectionAction.baseChangedLift]
    rw [hα]
    simp [δ, t, Iso.trans_assoc]
  · intro α' hα'
    apply (Scheme.Modules.pullback c.hom).mapIso_injective
    rw [hα]
    apply Iso.ext
    have hh := congrArg Iso.hom hα'
    dsimp only [SectionAction.changeLine, SectionAction.baseChangedLift,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hh
    dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    apply (cancel_epi t.hom).mp
    apply (cancel_epi ((Scheme.Modules.pullback f).map e.inv)).mp
    apply (cancel_mono e.hom).mp
    simpa [t, Category.assoc, ← Functor.map_comp] using hh

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
    (V : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m))
    {ζ : kˣ} (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)

lemma shift_commutes : Q.cubic.hom ≫ translation (family k V) (pointY k V) =
    Q.mapB ≫ Q.cubic.hom := by
  exact Q.shift_commutes.symm

lemma existsUnique_matches :
    ∃! b : Lift (family k V) m (translation (family k V) (pointY k V)),
      Matches k V Q he _ Q.mapB b (Q.canonicalB he) := by
  obtain ⟨b, hb, hu⟩ := existsUnique_transport Q.cubic
    (translation (family k V) (pointY k V)) Q.mapB (shift_commutes k V Q)
    (thetaLine (family k V) m) _ (modelComparison k V Q he)
    (LocalTheta.dualLift Q.mapB _ (Q.ideal_invertible he) (Q.canonicalB he).symm)
  exact ⟨b, ⟨shift_commutes k V Q, hb⟩, fun b' hb' => hu b' hb'.choose_spec⟩

include he in
lemma action_ext
    (g : (family k V).curve ⟶ (family k V).curve)
    (f : ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model ⟶
      ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model) [IsIso f]
    (h : Q.cubic.hom ≫ g = f ≫ Q.cubic.hom)
    (e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m f)
    (a b : Lift (family k V) m g)
    (hab : ∀ v, SectionAction.globalAct g a v = SectionAction.globalAct g b v) : a = b := by
  let ea := LocalTheta.inducedIdealLift k Q.model Q.origin m (Q.ideal_invertible he)
    Q.cubic _ (modelComparison k V Q he) f g h e a
  let eb := LocalTheta.inducedIdealLift k Q.model Q.origin m (Q.ideal_invertible he)
    Q.cubic _ (modelComparison k V Q he) f g h e b
  have heq : ea = eb := by
    apply ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.lift_ext k Q.model
      (ArithmeticThetaGenericEvaluationR0140.thetaChartBound m hm he)
      Q.isModel Q.origin Q.markedOrigin m f
    intro φ
    obtain ⟨v, rfl⟩ := (sectionEquiv k V Q he).surjective φ
    change ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m f ea
      (LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ (modelComparison k V Q he) v) = _
    dsimp only [ea, eb]
    exact (LocalTheta.modelFunctional_act k Q.model Q.origin m (Q.ideal_invertible he)
      Q.cubic _ (modelComparison k V Q he) f g h e a v).trans
      ((congrArg (LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
        (modelComparison k V Q he)) (hab v)).trans
        (LocalTheta.modelFunctional_act k Q.model Q.origin m (Q.ideal_invertible he)
          Q.cubic _ (modelComparison k V Q he) f g h e b v).symm)
  have ht := congrArg (fun x => LocalTheta.dualLift f _ (Q.ideal_invertible he) x.symm) heq
  dsimp only [ea, eb] at ht
  rw [LocalTheta.inducedIdealLift_dual, LocalTheta.inducedIdealLift_dual] at ht
  obtain ⟨z, hz, hu⟩ := existsUnique_transport Q.cubic g f h _ _
    (modelComparison k V Q he)
    (SectionAction.changeLine f (modelComparison k V Q he)
      (SectionAction.baseChangedLift Q.cubic.hom g f h b))
  exact (hu a ht).trans (hu b rfl).symm

lemma matches_action
    (g : (family k V).curve ⟶ (family k V).curve)
    (f : ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model ⟶
      ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model)
    (a : Lift (family k V) m g)
    (e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m f)
    (ha : Matches k V Q he g f a e) (v : Γ(thetaLine (family k V) m, ⊤)) :
    sectionEquiv k V Q he (SectionAction.globalAct g a v) =
      ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m f e
        (sectionEquiv k V Q he v) := by
  obtain ⟨h, ha⟩ := ha
  change LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
    (modelComparison k V Q he) (SectionAction.globalAct g a v) = _
  unfold LocalTheta.modelFunctional
  rw [← SectionAction.globalAct_baseChanged Q.cubic.hom g f h a,
    ← SectionAction.globalAct_changeLine, ha]
  exact LocalTheta.genericDual_globalAct k Q.model Q.origin m (Q.ideal_invertible he) f e _

lemma inversion_commutes : Q.cubic.hom ≫ inverse (family k V) = Q.mapS ≫ Q.cubic.hom :=
  Q.inversion_commutes.symm

lemma alternating_of_matches (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointY k V)))
    (ha : Matches k V Q he _ Q.mapB a (Q.canonicalB he))
    (ι : Lift (family k V) m (inverse (family k V)))
    (hi : NormalizedInversion (family k V) m ι) :
    ∀ v : Γ(thetaLine (family k V) m, ⊤),
      SectionAction.globalAct _ ι (SectionAction.globalAct _ a
        (SectionAction.globalAct _ ι (SectionAction.globalAct _ a v))) = v := by
  let eS := LocalTheta.inducedIdealLift k Q.model Q.origin m (Q.ideal_invertible he)
    Q.cubic _ (modelComparison k V Q he) Q.mapS _ (inversion_commutes k V Q)
    (Q.canonicalS he) ι
  have hS : Matches k V Q he _ Q.mapS ι eS :=
    ⟨inversion_commutes k V Q,
      (LocalTheta.inducedIdealLift_dual k Q.model Q.origin m (Q.ideal_invertible he)
        Q.cubic _ (modelComparison k V Q he) Q.mapS _ (inversion_commutes k V Q)
        (Q.canonicalS he) ι).symm⟩
  have hisq : ∀ v : Γ(thetaLine (family k V) m, ⊤),
      SectionAction.globalAct _ ι (SectionAction.globalAct _ ι v) = v := by
    obtain ⟨h, hh⟩ := hi.2
    exact SectionAction.globalAct_square _ h ι hh
  have hesq := LocalTheta.inducedIdealLift_square k Q.model Q.origin m (Q.ideal_invertible he)
    Q.cubic _ (modelComparison k V Q he) Q.mapS _ (inversion_commutes k V Q)
    (Q.canonicalS he) ι hisq
  have hsym := (LocalTheta.symmetric_change_inversion k Q.model Q.origin m m
    (ArithmeticThetaGenericEvaluationR0140.thetaChartBound m hm he) Q.isModel Q.markedOrigin hm
    _ (ArithmeticThetaGenericEvaluationR0140.generic_theta_basis k m hm he Q.tower Q.model
      Q.isModel Q.origin Q.markedOrigin) Q.mapB Q.mapS
    (ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.shiftMap_structure k Q.model
      Q.rotation Q.scaling Q.inversion Q.actions)
    (ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141.inversionMap_structure k Q.model
      Q.rotation Q.scaling Q.inversion Q.actions)
    (Q.canonicalB he) (Q.canonicalS he) eS (Q.canonical_relations he hζ).2.2.2.1 hesq).mpr
      (Q.canonical_relations he hζ).2.2.2.2.2
  intro v
  apply (sectionEquiv k V Q he).injective
  rw [matches_action k V Q he _ _ ι eS hS,
    matches_action k V Q he _ _ a (Q.canonicalB he) ha,
    matches_action k V Q he _ _ ι eS hS,
    matches_action k V Q he _ _ a (Q.canonicalB he) ha]
  exact hsym _

open ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator

lemma globalAct_identity {X : Scheme} (L : X.Modules) (v : Γ(L, ⊤)) :
    SectionAction.globalAct (𝟙 X) ((Scheme.Modules.pullbackId X).app L) v = v := by
  apply (SectionAction.globalSectionsEquiv L).injective
  change ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection L (SectionAction.globalAct _ _ v) = _
  rw [← SectionAction.act_fromSection]
  exact SectionAction.pull_id _

include he Q in
lemma square_of_action (r : (family k V).curve ⟶ (family k V).curve)
    (hr : r ≫ r = 𝟙 _) (ρ : Lift (family k V) m r)
    (hs : ∀ v, SectionAction.globalAct r ρ (SectionAction.globalAct r ρ v) = v) :
    (Scheme.Modules.pullback r).mapIso ρ ≪≫ ρ = squareComparison (family k V) m r hr := by
  have hc : compose (family k V) m r r ρ ρ =
      changeMap (family k V) m hr (identityLift (family k V) m) := by
    apply action_ext k V Q he (r ≫ r) (𝟙 _) (by
      exact (congrArg (Q.cubic.hom ≫ ·) hr).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
      ((Scheme.Modules.pullbackId _).app
        (ArithmeticThetaGenericEvaluationR0140.genericPower k Q.model Q.origin m)).symm
    intro v
    exact (Sections.act_comp r r ρ ρ v).trans ((hs v).trans
      ((Sections.act_changeMap hr ((Scheme.Modules.pullbackId _).app _) v).trans
        (globalAct_identity _ v)).symm)
  apply Iso.ext
  have hh := congrArg Iso.hom hc
  apply (cancel_epi ((Scheme.Modules.pullbackComp r r).app
    (thetaLine (family k V) m)).inv).mp
  simpa [compose, changeMap, identityLift, squareComparison, Category.assoc] using hh

lemma symmetric_of_matches (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointY k V)))
    (ha : Matches k V Q he _ Q.mapB a (Q.canonicalB he))
    (ι : Lift (family k V) m (inverse (family k V)))
    (hi : NormalizedInversion (family k V) m ι) :
    Symmetric (family k V) m (pointY k V) ι a := by
  have halt := alternating_of_matches k V Q he hζ a ha ι hi
  have hisq : ∀ v : Γ(thetaLine (family k V) m, ⊤),
      SectionAction.globalAct _ ι (SectionAction.globalAct _ ι v) = v := by
    obtain ⟨h, hh⟩ := hi.2
    exact SectionAction.globalAct_square _ h ι hh
  let hr := SchemeMidpointThetaLift.reflection_square (family k V) (pointY k V)
  refine ⟨hr, square_of_action k V Q he _ hr _ ?_⟩
  intro v
  change Sections.act _ (compose (family k V) m _ _ a ι)
    (Sections.act _ (compose (family k V) m _ _ a ι) v) = v
  dsimp only [compose]
  rw [Sections.act_comp, Sections.act_comp]
  have hh := congrArg (SectionAction.globalAct _ ι)
    (halt (SectionAction.globalAct _ ι v))
  simp only [hisq] at hh
  simpa only [Sections.act, SectionAction.globalAct] using hh

#print axioms square_of_action
#print axioms symmetric_of_matches
#print axioms matches_action
#print axioms alternating_of_matches
#print axioms action_ext
#print axioms existsUnique_transport
#print axioms existsUnique_matches
end ShiftLiftProof

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- The literal shift on the actual conormal theta line, uniquely fixed by the
accepted canonical ideal lift, is symmetric for every normalized inversion. -/
theorem tate_scheme_shift_lift :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
      (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
    ∀ Q : LocalTheta.MarkedModel k m hm V ζ,
    ∃! b : Lift (family k V) m (translation (family k V) (pointY k V)),
      shiftLiftFacts k V Q he b := by
  intro k _ _ m hm he V ζ hζ Q
  obtain ⟨b, hb, hu⟩ := ShiftLiftProof.existsUnique_matches k V Q he
  exact ⟨b, ⟨hb, ShiftLiftProof.symmetric_of_matches k V Q he hζ b hb⟩,
    fun b' hb' => hu b' hb'.1⟩

#print axioms tate_scheme_shift_lift
end ArithmeticThetaTateSchemeMarkingR0263
