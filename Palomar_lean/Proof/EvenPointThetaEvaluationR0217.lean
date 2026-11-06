module

public import MultiplierKeyDefinitionsR0217
public import EvenMarkingSubcoverR0216
public import ArbitraryThetaGeneratorEvaluationR0213
public import SchemeThetaEvaluationR0213
public import ArbitraryThetaEvaluationBaseChangeR0213
public import ThetaIdentityEvaluationR0212
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaEvenMarkingTorsorR0216.EvenMarkingSubcover
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaUniversalEvaluationR0213
open Scheme.Modules

namespace EvenPointThetaEvaluation

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)

lemma thetaIdeal_invertible : (thetaIdeal E P).IsInvertible := by
  letI := E.proper
  letI := E.dimension
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id P.point.val P.point.property

lemma thetaMap_eq : thetaMap E P = (thetaIdeal E P).invModuleSection := rfl

lemma originGenerator_isIso : IsIso (originGenerator E P) := by
  letI := E.proper
  haveI : IsClosedImmersion (P.point.val ≫ E.p) := by
    rw [P.point.property]
    infer_instance
  haveI : IsClosedImmersion P.point.val := IsClosedImmersion.of_comp _ E.p
  have hI := thetaIdeal_invertible E P
  have hL := hI.isInvertible_invModule
  have hz : zeroSchemeIdeal (thetaMap E P) = thetaIdeal E P := by
    rw [thetaMap_eq]
    exact hI.zeroSchemeIdeal_invModuleSection
  have hd : Disjoint (Set.range E.zero) ((thetaIdeal E P).support : Set _) := by
    change Disjoint (Set.range E.zero) (P.point.val.ker.support : Set E.curve)
    rw [Scheme.Hom.support_ker, P.point.val.isClosedEmbedding.isClosed_range.closure_eq]
    exact P.avoids.symm
  have ht := ((thetaIdeal E P).comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
    E.zero hd).1
  have hp : zeroSchemeIdeal (originGenerator E P) = ⊤ := by
    change zeroSchemeIdeal (pullbackSection E.zero (thetaMap E P)) = ⊤
    rw [← hL.comap_zeroSchemeIdeal, hz, ht]
  apply ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames.isIso_of_frame_top
  apply (hL.pullback E.zero).isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
  rw [hp, Scheme.IdealSheafData.support_top]
  exact disjoint_bot_right

lemma rigidification_unique :
    ∃! e : (pullback E.zero).obj (thetaLine E P) ≅ 𝟙_ S.Modules,
      IsRigidification E P e := by
  haveI := originGenerator_isIso E P
  refine ⟨(asIso (originGenerator E P)).symm, IsIso.hom_inv_id _, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_epi (originGenerator E P)).mp
  exact he.trans (IsIso.hom_inv_id _).symm

lemma generator_evaluation
    (e : (pullback E.zero).obj (thetaLine E P) ≅ 𝟙_ S.Modules)
    (he : IsRigidification E P e) :
    generator E P ≫ evaluation E P e = 𝟙 _ := by
  have hn := ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.normalized_restriction
    E.zero (thetaLine E P) (thetaMap E P) e he
  unfold generator evaluation
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hn]
  exact ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.section_unit
    E.p E.zero (E.law.one (𝟙 S)).property

lemma thetaIdeal_comap {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (h : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val) :
    (thetaIdeal E P).comap f = thetaIdeal F Q := by
  letI := E.proper
  haveI : IsClosedImmersion (P.point.val ≫ E.p) := by
    rw [P.point.property]
    infer_instance
  haveI : IsClosedImmersion P.point.val := IsClosedImmersion.of_comp _ E.p
  exact ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator.section_ideal_comap
    F.p E.p f b h.1 Q.point.val P.point.val Q.point.property P.point.property hQ

lemma line_comparison {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (h : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f)
    (hQ : Q.point.val ≫ f = b ≫ P.point.val) :
    ∃ q : (pullback f).obj (thetaLine E P) ≅ thetaLine F Q,
      (pullbackUnitIso f).inv ≫ (pullback f).map (thetaMap E P) ≫ q.hom =
        thetaMap F Q := by
  have hI := thetaIdeal_comap E P F Q b f h hQ
  have hL := (thetaIdeal_invertible E P).isInvertible_invModule
  let s := pullbackSection f (thetaMap E P)
  have hz : zeroSchemeIdeal s = thetaIdeal F Q := by
    rw [← hL.comap_zeroSchemeIdeal, thetaMap_eq,
      (thetaIdeal_invertible E P).zeroSchemeIdeal_invModuleSection, hI]
  have hZ : (zeroSchemeIdeal s).IsInvertible := hz ▸ thetaIdeal_invertible F Q
  obtain ⟨q, hq⟩ := hL.pullback f |>.exists_iso_invModule_zeroSchemeIdeal s hZ
  have hq' : ∃ q : (pullback f).obj (thetaLine E P) ≅ thetaLine F Q,
      s ≫ q.hom = thetaMap F Q := by
    rw [thetaMap_eq]
    change ∃ q : (pullback f).obj (thetaLine E P) ≅ (thetaIdeal F Q).invModule,
      s ≫ q.hom = (thetaIdeal F Q).invModuleSection
    rw [← hz]
    exact ⟨q, hq⟩
  obtain ⟨q, hq⟩ := hq'
  refine ⟨q, ?_⟩
  exact hq

end EvenPointThetaEvaluation

open EvenPointThetaEvaluation

theorem even_point_theta_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : Family S) (P : EvenPoint E),
      (thetaIdeal E P).IsInvertible ∧
      Scheme.Modules.IsInvertible (thetaLine E P) ∧
      zeroSchemeIdeal (thetaMap E P) = thetaIdeal E P ∧
      (∃! e : Iso ((pullback E.zero).obj (thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf),
        IsRigidification E P e) ∧
      IsIso (generator E P) ∧
      (∀ e : Iso ((pullback E.zero).obj (thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf),
        IsRigidification E P e →
        IsIso (evaluation E P e) ∧
        generator E P ≫ evaluation E P e = 𝟙 _ ∧
        IsFrame (Scheme.Modules.dual (pushforwardLine E P)) ⊤ (evaluationSection E P e)) := by
  intro k _ _ S σ E P
  have hI := thetaIdeal_invertible E P
  have hz : zeroSchemeIdeal (thetaMap E P) = thetaIdeal E P := by
    rw [thetaMap_eq]
    exact hI.zeroSchemeIdeal_invModuleSection
  haveI := originGenerator_isIso E P
  haveI : IsIso (generator E P) := by
    apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
    intro x
    obtain ⟨L, hx⟩ := scheme_local_weierstrass k S σ E x
    letI := L.commRing
    letI := L.algebra
    letI : Algebra ℚ L.ring := Algebra.compHom L.ring (algebraMap ℚ k)
    letI : L.equation.IsElliptic := L.elliptic
    letI := L.openImmersion
    let F := ArithmeticThetaSchemeLevelR0204.SchemeLocalClassifier.family L
    have hz : F.zero ≫ L.comparison = L.base ≫ E.zero := by
      rw [ArithmeticThetaSchemeLevelR0204.SchemeLocalClassifier.family_zero]
      exact L.zero_eq
    have hF : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F L.base L.comparison :=
      ⟨L.cartesian, hz, L.mul_eq⟩
    let q : ArithmeticThetaRelativeDiscriminantR0171.Base L.ring ⟶ F.curve :=
      (pullSection E F L.base L.comparison hF P.point).val
    have hqE : q ≫ L.comparison = L.base ≫ P.point.val := by
      exact pullSection_comp E F L.base L.comparison hF P.point
    have hq0 : q ≫ F.p = 𝟙 _ := by
      exact (pullSection E F L.base L.comparison hF P.point).property
    let Q : EvenPoint F :=
      { point := ⟨q, hq0⟩
        killed := by
          exact pullSection_killed E F L.base L.comparison hF P.point 2 P.killed
        avoids := by
          apply Set.disjoint_left.mpr
          intro y hyq hy0
          obtain ⟨t, rfl⟩ := hyq
          obtain ⟨t', ht'⟩ := hy0
          apply Set.disjoint_left.mp P.avoids
          · exact ⟨L.base t, rfl⟩
          · refine ⟨L.base t', ?_⟩
            calc
              E.zero (L.base t') = (L.base ≫ E.zero) t' := rfl
              _ = (F.zero ≫ L.comparison) t' := by
                exact congrArg (fun z : ArithmeticThetaRelativeDiscriminantR0171.Base L.ring ⟶ E.curve => z t') hz.symm
              _ = (q ≫ L.comparison) t := by
                exact congrArg (fun z : F.curve => L.comparison z) ht'
              _ = P.point.val (L.base t) := by
                exact congrArg (fun z : ArithmeticThetaRelativeDiscriminantR0171.Base L.ring ⟶ E.curve => z t) hqE }
    haveI : IsIso (generator F Q) := by
      letI := F.proper
      letI : SmoothOfRelativeDimension 1 F.p := F.dimension
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom F.p (thetaLine F Q) ⊤
      have hε : Nonempty (Γ(thetaLine F Q, ⊤) ≃ₗ[L.ring] L.ring) :=
        ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator.point_sections_equiv
          L.ring L.equation L.law L.originLaw Q.point
      obtain ⟨ε⟩ := hε
      haveI := originGenerator_isIso F Q
      let e := (asIso (originGenerator F Q)).symm
      have he : IsRigidification F Q e := IsIso.hom_inv_id _
      have hgen := generator_evaluation F Q e he
      let v := ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator.pushforwardFunctional
        F.p (thetaLine F Q) (evaluation F Q e)
      let s : Γ(thetaLine F Q, ⊤) :=
        (Scheme.Modules.ihomGlobalSectionsEquiv (thetaIdeal F Q).module
          (𝟙_ F.curve.Modules)).symm (thetaIdeal F Q).moduleι
      have hscalar (r : L.ring) : (generator F Q).app ⊤
          ((Scheme.ΓSpecIso (.of L.ring)).inv r) = r • s := by
        change (thetaMap F Q).app ⊤
          (F.p.app ⊤ ((Scheme.ΓSpecIso (.of L.ring)).inv r)) = _
        have hmap : thetaMap F Q =
            ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection
              (thetaLine F Q) s :=
          (ArithmeticThetaThetaEvaluationR0212.EvenThetaRigidification.fromSection_ihom _ _ _).symm
        rw [hmap]
        erw [ArithmeticThetaThetaEvaluationR0212.PushforwardGenerator.fromSection_top_apply]
        change F.p.appTop ((Scheme.ΓSpecIso (.of L.ring)).inv r) • s =
          GradedOAlgebra.baseScalar F.p r • s
        rw [ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.GeometricCubic.baseScalar_eq_const]
        rfl
      have hvs : v s = 1 := by
        have h₁ := congrArg (fun f => f.app ⊤
          ((Scheme.ΓSpecIso (.of L.ring)).inv (1 : L.ring))) hgen
        change (evaluation F Q e).app ⊤
          ((generator F Q).app ⊤ ((Scheme.ΓSpecIso (.of L.ring)).inv 1)) =
          (Scheme.ΓSpecIso (.of L.ring)).inv 1 at h₁
        rw [hscalar, one_smul] at h₁
        change (Scheme.ΓSpecIso (.of L.ring)).hom ((evaluation F Q e).app ⊤ s) = 1
        rw [h₁]
        exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of L.ring)).inv_hom_id (1 : L.ring)
      have hb : Function.Bijective (fun r : L.ring => r • s) := by
        constructor
        · intro a b hab
          have hv := congrArg v hab
          simpa only [_root_.map_smul, hvs, smul_eq_mul, mul_one] using hv
        · intro x'
          refine ⟨v x', ?_⟩
          have hx' := ArithmeticThetaLocalWeierstrassR0203.NoetherianPoleFiltration.rank_one_interchange
            ε.symm v s x'
          simpa only [hvs, one_smul] using hx'.symm
      have hsg : Function.Bijective ((generator F Q).app ⊤) := by
        apply (Function.Bijective.of_comp_iff _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L.ring)).inv)).mp
        change Function.Bijective (fun r : L.ring =>
          (generator F Q).app ⊤ ((Scheme.ΓSpecIso (.of L.ring)).inv r))
        simpa only [hscalar] using hb
      haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of L.ring)
          (pushforwardLine F Q)) :=
        Scheme.Modules.isIso_fromTildeGamma_pushforward_of_locallyTrivial
          (A := L.ring) F.p
            (ArithmeticThetaThetaEvaluationR0212.PushforwardGenerator.weierstrassTwoAffineCover
              (R := L.ring) L.equation) (thetaLine F Q)
          (thetaIdeal_invertible F Q).isInvertible_invModule.1
      haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of L.ring)
          (𝟙_ (ArithmeticThetaRelativeDiscriminantR0171.Base L.ring).Modules)) :=
        Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial (R := CommRingCat.of L.ring) _
          (fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩)
      exact ArithmeticThetaThetaEvaluationR0212.PushforwardGenerator.isIso_of_bijective_global
        (A := CommRingCat.of L.ring) (generator F Q) hsg
    obtain ⟨qline, hqline⟩ := line_comparison E P F Q L.base L.comparison hF hqE
    let c := baseChangeHom L.cartesian.w (thetaLine E P) ≫
      (pushforward F.p).map qline.hom
    haveI : IsIso (baseChangeHom L.cartesian.w (thetaLine E P)) :=
      isIso_baseChangeHom_of_isOpenImmersion L.cartesian (thetaLine E P)
    haveI : IsIso c := by dsimp [c]; infer_instance
    have hc : (pullback L.base).map (generator E P) ≫ c =
        (pullbackUnitIso L.base).hom ≫ generator F Q :=
      ArithmeticThetaThetaEvaluationR0212.EvaluationBaseChange.base_change_generator
        L.cartesian.w (thetaMap E P) (thetaMap F Q) qline.hom hqline
    haveI : IsIso ((pullback L.base).map (generator E P) ≫ c) := by
      rw [hc]
      infer_instance
    haveI : IsIso ((pullback L.base).map (generator E P)) :=
      IsIso.of_isIso_comp_right _ c
    exact ⟨L.base.opensRange, hx, by
      let e := L.base.isoOpensRange
      haveI : IsIso (((pullback L.base) ⋙ pullback e.inv).map (generator E P)) := by
        change IsIso ((pullback e.inv).map ((pullback L.base).map (generator E P)))
        infer_instance
      haveI : IsIso ((pullback (e.inv ≫ L.base)).map (generator E P)) :=
        (NatIso.isIso_map_iff (pullbackComp e.inv L.base) (generator E P)).mp inferInstance
      rw [← L.base.isoOpensRange_inv_comp]
      infer_instance⟩
  refine ⟨thetaIdeal_invertible E P, (thetaIdeal_invertible E P).isInvertible_invModule,
    hz, rigidification_unique E P, inferInstance, ?_⟩
  intro e he
  have h := generator_evaluation E P e he
  have hv : evaluation E P e = inv (generator E P) := by
    apply (cancel_epi (generator E P)).mp
    exact h.trans (IsIso.hom_inv_id _).symm
  refine ⟨?_, h, ?_⟩
  · rw [hv]
    infer_instance
  · exact ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.dual_frame
      (pushforwardLine E P) (generator E P) (evaluation E P e) h

#print axioms even_point_theta_evaluation
end ArithmeticThetaMultiplierKeyR0217
