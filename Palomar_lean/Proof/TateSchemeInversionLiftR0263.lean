module

public import TateSchemeMarkingDefinitionsR0263
public import SchemeSymmetricSignsR0259
public import SchemeThetaInversionR0259

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaTateSchemeMarkingR0263
namespace TateSchemeInversionLift
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

private def pullbackEquivalence {X Y : Scheme} (e : Y ≅ X) :
    X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId X).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
      Scheme.Modules.pullbackId Y)

/-- Transport through the specified scheme and line isomorphisms is bijective
on actual sheaf lifts, independently of global-section faithfulness. -/
lemma lift_transport_bijective {X Y : Scheme} (e : Y ≅ X)
    (g : X ⟶ X) (f : Y ⟶ Y) (h : e.hom ≫ g = f ≫ e.hom)
    (M : X.Modules) (N : Y.Modules) (c : (Scheme.Modules.pullback e.hom).obj M ≅ N) :
    Function.Bijective (fun a : (Scheme.Modules.pullback g).obj M ≅ M =>
      SectionAction.changeLine f c (SectionAction.baseChangedLift e.hom g f h a)) := by
  let F := Scheme.Modules.pullback e.hom
  letI : F.IsEquivalence := (pullbackEquivalence e).isEquivalence_functor
  constructor
  · intro a b hab
    apply F.mapIso_injective
    apply Iso.ext
    have hh := congrArg Iso.hom hab
    simpa only [SectionAction.changeLine, SectionAction.baseChangedLift,
      Iso.trans_hom, Category.assoc, cancel_mono, cancel_epi] using hh
  · intro a
    let b := (ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.squareIso g e.hom e.hom f h M).symm ≪≫
      (Scheme.Modules.pullback f).mapIso c ≪≫ a ≪≫ c.symm
    refine ⟨F.preimageIso b, ?_⟩
    apply Iso.ext
    simp [SectionAction.changeLine, SectionAction.baseChangedLift, b, F,
      Functor.preimageIso, Category.assoc]

open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open Scheme.Modules
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

lemma normalized_evaluation {S : Scheme} (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (d : ℕ) (i : Lift E d (inverse E)) (hi : NormalizedInversion E d i)
    (v : Γ(thetaLine E d, ⊤)) :
    Scheme.Modules.pullbackLocalSection E.zero (SectionAction.globalAct _ i v) =
      Scheme.Modules.pullbackLocalSection E.zero v := by
  obtain ⟨h, hi⟩ := hi.1
  apply (SectionAction.globalSectionsEquiv _).injective
  change fromSection _ _ = fromSection _ _
  rw [← SectionAction.pull_fromSection, ← SectionAction.act_fromSection,
    SectionAction.act, SectionAction.pull_post]
  have hh := congrArg Iso.hom hi
  simp only [Functor.mapIso_hom] at hh
  rw [hh]
  simp only [fixedComparison, Iso.trans_hom, Iso.app_hom, ← Category.assoc]
  rw [SectionAction.pull_comp, SectionAction.pull_congr, SectionAction.pull_fromSection]

lemma scaled_action {S : Scheme} (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (d : ℕ) (g : E.curve ⟶ E.curve) (i : Lift E d g) (c : Γ(S, ⊤)ˣ)
    (v : Γ(thetaLine E d, ⊤)) :
    SectionAction.globalAct g (scaled E d c i) v =
      (scalar E c : Γ(E.curve, ⊤)) • SectionAction.globalAct g i v := by
  change (smulHom (scalar E c : Γ(E.curve, ⊤)) _).app ⊤ _ = _
  rw [smulHom_app_apply, resTop_top]
  rfl

/-- Over a field, a fixed section with nonzero identity value determines the
identity normalization of an inversion lift. -/
lemma normalized_of_fixed_section {F : Type} [Field F]
    (E : ArithmeticThetaLocalWeierstrassR0203.Family (Spec (CommRingCat.of F)))
    (d : ℕ) (i : Lift E d (inverse E)) (v : Γ(thetaLine E d, ⊤))
    (hv : SectionAction.globalAct _ i v = v)
    (hne : Scheme.Modules.pullbackLocalSection E.zero v ≠ 0) :
    NormalizedInversion E d i := by
  obtain ⟨j, hj, _⟩ := SchemeThetaInversion.normalized_exists_unique E d
  obtain ⟨c, hc⟩ := SchemeSymmetricSigns.exists_scaled E d j i
  have hscalar : E.zero.appTop (scalar E c : Γ(E.curve, ⊤)) = (c : Γ(Spec (CommRingCat.of F), ⊤)) := by
    have h := congrArg Scheme.Hom.appTop (SchemeThetaInversion.zero_over E)
    rw [Scheme.Hom.comp_appTop] at h
    exact ConcreteCategory.congr_hom h (c : Γ(Spec (CommRingCat.of F), ⊤))
  let w : Γ((Scheme.Modules.pullback E.zero).obj (thetaLine E d), ⊤) :=
    Scheme.Modules.pullbackLocalSection E.zero v
  let w' : Γ((Scheme.Modules.pullback E.zero).obj (thetaLine E d), ⊤) :=
    Scheme.Modules.pullbackLocalSection E.zero (SectionAction.globalAct _ j v)
  have hw' : w' = w := normalized_evaluation E d j hj v
  have hw := congrArg (Scheme.Modules.pullbackLocalSection E.zero) hv
  rw [hc, scaled_action, Scheme.Modules.pullbackLocalSection_smul] at hw
  change E.zero.appTop (scalar E c : Γ(E.curve, ⊤)) • w' = w at hw
  rw [hscalar, hw'] at hw
  have hc1 : (c : Γ(Spec (CommRingCat.of F), ⊤)) = 1 := by
    by_contra hn
    let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    have hunit : IsUnit ((c : Γ(Spec (CommRingCat.of F), ⊤)) - 1) := by
      apply (isUnit_map_iff e _).mp
      exact isUnit_iff_ne_zero.mpr (fun hz => hn (sub_eq_zero.mp (e.injective (by simpa using hz))))
    have hz : ((c : Γ(Spec (CommRingCat.of F), ⊤)) - 1) • w = 0 := by
      rw [sub_smul, one_smul, hw, sub_self]
    have hz' : w = 0 := hunit.smul_eq_zero.mp hz
    exact hne hz'
  have hcunit : c = 1 := Units.ext hc1
  have hij : i = j := by
    rw [hc, hcunit]
    apply Iso.ext
    simp [scaled, scalar, smulIso, smulHom_one]
  simpa only [hij] using hj

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (V : TateLevel k (2*m)) {ζ : kˣ} (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)

lemma inverse_map_comparison : Q.cubic.hom ≫ inverse (family k V) = Q.mapS ≫ Q.cubic.hom := by
  exact Q.inversion_commutes.symm

/-- The fixed literal matching equation has one and only one solution on the
actual conormal theta line. Identity normalization is a separate assertion. -/
lemma matching_inversion_exists_unique :
    ∃! i : Lift (family k V) m (inverse (family k V)),
      Matches k V Q he _ Q.mapS i (Q.canonicalS he) := by
  let h := inverse_map_comparison k V Q
  have hb := lift_transport_bijective Q.cubic (inverse (family k V)) Q.mapS h
    (thetaLine (family k V) m) _ (modelComparison k V Q he)
  obtain ⟨i, hi⟩ := hb.surjective (LocalTheta.dualLift Q.mapS _ (Q.ideal_invertible he)
    (Q.canonicalS he).symm)
  refine ⟨i, ⟨h, hi⟩, ?_⟩
  intro j hj
  obtain ⟨h', hj⟩ := hj
  exact hb.injective (hj.trans hi.symm)

/-- Uniqueness in the full frozen target follows already from its required
literal matching equation. -/
lemma inversion_facts_unique
    (i j : Lift (family k V) m (inverse (family k V)))
    (hi : inversionLiftFacts k V Q he i) (hj : inversionLiftFacts k V Q he j) : i = j :=
  (matching_inversion_exists_unique k V Q he).unique hi.1 hj.1

lemma matching_action
    (i : Lift (family k V) m (inverse (family k V)))
    (hi : Matches k V Q he _ Q.mapS i (Q.canonicalS he))
    (v : Γ(thetaLine (family k V) m, ⊤)) :
    sectionEquiv k V Q he (SectionAction.globalAct _ i v) =
      ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m Q.mapS
        (Q.canonicalS he) (sectionEquiv k V Q he v) := by
  obtain ⟨h, hi⟩ := hi
  change LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ _ _ =
    ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m Q.mapS
      (Q.canonicalS he) (LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ _ v)
  unfold LocalTheta.modelFunctional
  rw [← LocalTheta.genericDual_globalAct k Q.model Q.origin m (Q.ideal_invertible he)]
  rw [← hi, SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]
  rfl

lemma matching_fixes_zero_basis
    (i : Lift (family k V) m (inverse (family k V)))
    (hi : Matches k V Q he _ Q.mapS i (Q.canonicalS he)) :
    SectionAction.globalAct _ i (basisSection k V Q he ⟨0, hm⟩) =
      basisSection k V Q he ⟨0, hm⟩ := by
  apply (sectionEquiv k V Q he).injective
  rw [matching_action k V Q he i hi]
  simp only [basisSection, Equiv.apply_symm_apply]
  rw [Q.canonicalS_reverses he]
  congr 1
  apply Fin.ext
  simp [ArithmeticThetaModelSymmetriesR0137.negIndex]

lemma zero_basis_identity_nonzero :
    Scheme.Modules.pullbackLocalSection (family k V).zero
      (basisSection k V Q he ⟨0, hm⟩) ≠ 0 := by
  letI := V.elliptic
  obtain ⟨_, ⟨frame⟩, hframe⟩ := ArithmeticThetaGenericEvaluationR0140.generic_projective_evaluation
    k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
  intro hz
  have ho : ArithmeticThetaGenericEvaluationR0140.genericPoint k Q.model Q.origin
      Q.markedOrigin.1 ≫ Q.cubic.hom = (family k V).zero := by
    rw [Q.cubic_origin]
    exact (ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero
      (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw).symm
  have hzero := LocalTheta.genericValue_modelFunctional_zero k Q.model Q.origin
    Q.markedOrigin.1 m Q.cubic (thetaLine (family k V) m) (modelComparison k V Q he)
    frame (basisSection k V Q he ⟨0, hm⟩) (by rw [ho]; exact hz)
  change ArithmeticThetaGenericEvaluationR0140.genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
    (sectionEquiv k V Q he (basisSection k V Q he ⟨0, hm⟩)) = 0 at hzero
  simp only [basisSection, Equiv.apply_symm_apply] at hzero
  exact (hframe frame).1 hzero

end TateSchemeInversionLift

/-- The literal residue-reversal lift on the actual conormal theta line is
normalized at the actual identity and has the canonical square. -/
theorem tate_scheme_inversion_lift :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
      (V : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m)) (ζ : kˣ)
      (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
      ∀ Q : ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k m hm V ζ,
      ∃! i : ArithmeticThetaSchemeThetaMarkingR0259.Lift (family k V) m
        (ArithmeticThetaSchemeThetaMarkingR0259.inverse (family k V)),
        inversionLiftFacts k V Q he i := by
  intro k _ _ m hm he V ζ hζ Q
  obtain ⟨i, hi, hu⟩ := TateSchemeInversionLift.matching_inversion_exists_unique k V Q he
  refine ⟨i, ⟨hi, ?_⟩, fun j hj => hu j hj.1⟩
  exact TateSchemeInversionLift.normalized_of_fixed_section (family k V) m i
    (basisSection k V Q he ⟨0, hm⟩)
    (TateSchemeInversionLift.matching_fixes_zero_basis k V Q he i hi)
    (TateSchemeInversionLift.zero_basis_identity_nonzero k V Q he)

end ArithmeticThetaTateSchemeMarkingR0263

#print axioms ArithmeticThetaTateSchemeMarkingR0263.TateSchemeInversionLift.matching_inversion_exists_unique
#print axioms ArithmeticThetaTateSchemeMarkingR0263.TateSchemeInversionLift.inversion_facts_unique
#print axioms ArithmeticThetaTateSchemeMarkingR0263.tate_scheme_inversion_lift
