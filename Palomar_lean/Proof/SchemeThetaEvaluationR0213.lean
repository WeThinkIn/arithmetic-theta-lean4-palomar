module

public import UniversalThetaEvaluationDefinitionsR0213
public import ArbitraryEvenThetaRigidificationR0213
public import ArbitraryThetaGeneratorEvaluationR0213
public import ArbitraryThetaLineBaseChangeR0213
public import ArbitraryThetaEvaluationBaseChangeR0213

public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
public import ThetaEvaluationBaseChangeR0212
public import SchemeLocalClassifierR0204

@[expose] public section

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaUniversalEvaluationR0213
namespace SchemeThetaEvaluation
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open Scheme.Modules

variable {S : Scheme.{u}} (E : Family S)
  (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4)

lemma evenPoint_over : evenPoint E M ≫ E.p = 𝟙 S :=
  (E.law.mul (𝟙 S)
    (ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) 2 M.x)
    (ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) 2 M.y)).property

lemma thetaMap_eq : thetaMap E M = (thetaIdeal E M).invModuleSection :=
  ArithmeticThetaThetaEvaluationR0212.EvenThetaRigidification.fromSection_ihom _ _ _

lemma thetaIdeal_invertible : (thetaIdeal E M).IsInvertible := by
  letI := E.proper
  letI := E.dimension
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (evenPoint_over E M)

lemma originGenerator_isIso : IsIso (originGenerator E M) := by
  letI := E.proper
  haveI : IsClosedImmersion (evenPoint E M ≫ E.p) := by
    rw [evenPoint_over]; infer_instance
  haveI : IsClosedImmersion (evenPoint E M) := IsClosedImmersion.of_comp _ E.p
  have hI := thetaIdeal_invertible E M
  have hL := hI.isInvertible_invModule
  have hz : zeroSchemeIdeal (thetaMap E M) = thetaIdeal E M := by
    rw [thetaMap_eq]; exact hI.zeroSchemeIdeal_invModuleSection
  have hd : Disjoint (Set.range E.zero) ((thetaIdeal E M).support : Set _) := by
    change Disjoint (Set.range E.zero) ((evenPoint E M).ker.support : Set E.curve)
    rw [Scheme.Hom.support_ker, (evenPoint E M).isClosedEmbedding.isClosed_range.closure_eq]
    exact (M.avoids (2 : Fin 4) (2 : Fin 4) (Or.inl (by decide))).symm
  have ht := ((thetaIdeal E M).comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
    E.zero hd).1
  have hp : zeroSchemeIdeal (originGenerator E M) = ⊤ := by
    change zeroSchemeIdeal (pullbackSection E.zero (thetaMap E M)) = ⊤
    rw [← hL.comap_zeroSchemeIdeal, hz, ht]
  apply ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SectionFrames.isIso_of_frame_top
  apply (hL.pullback E.zero).isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
  rw [hp, Scheme.IdealSheafData.support_top]
  exact disjoint_bot_right

lemma rigidification_unique :
    ∃! e : (pullback E.zero).obj (thetaLine E M) ≅ 𝟙_ S.Modules,
      IsRigidification E M e := by
  haveI := originGenerator_isIso E M
  refine ⟨(asIso (originGenerator E M)).symm, IsIso.hom_inv_id _, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_epi (originGenerator E M)).mp
  exact he.trans (IsIso.hom_inv_id _).symm

lemma generator_evaluation
    (e : (pullback E.zero).obj (thetaLine E M) ≅ 𝟙_ S.Modules)
    (he : IsRigidification E M e) :
    generator E M ≫ evaluation E M e = 𝟙 _ := by
  have hn := ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.normalized_restriction
    E.zero (thetaLine E M) (thetaMap E M) e he
  unfold generator evaluation
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hn]
  exact ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.section_unit
    E.p E.zero (E.law.one (𝟙 S)).property

#print axioms thetaIdeal_invertible
#print axioms rigidification_unique
#print axioms generator_evaluation


variable {T : Scheme.{u}} (F : Family T)
  (N : ArithmeticThetaSchemeLevelR0204.FullLevel F 4) (b : T ⟶ S)
  (f : F.curve ⟶ E.curve)

lemma evenPoint_natural
    (h : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f) :
    evenPoint F N ≫ f = b ≫ evenPoint E M := by
  exact ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.mul_comp E F b f h.2.2.1
    _ _ _ _
    (ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.multiple_comp E F b f
      h.2.1 h.2.2.1 N.x M.x h.2.2.2.1 2)
    (ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.multiple_comp E F b f
      h.2.1 h.2.2.1 N.y M.y h.2.2.2.2 2)

lemma thetaIdeal_comap
    (h : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f) :
    (thetaIdeal E M).comap f = thetaIdeal F N := by
  letI := E.proper
  haveI : IsClosedImmersion (evenPoint E M ≫ E.p) := by
    rw [evenPoint_over]; infer_instance
  haveI : IsClosedImmersion (evenPoint E M) := IsClosedImmersion.of_comp _ E.p
  exact ArbitraryGenerator.section_ideal_comap F.p E.p f b h.1
    (evenPoint F N) (evenPoint E M) (evenPoint_over F N) (evenPoint_over E M)
    (evenPoint_natural E M F N b f h)

lemma line_comparison
    (h : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f) :
    ∃ q : (pullback f).obj (thetaLine E M) ≅ thetaLine F N,
      PreservesThetaSection E M F N f q := by
  have hI := thetaIdeal_comap E M F N b f h
  have hL := (thetaIdeal_invertible E M).isInvertible_invModule
  let s := pullbackSection f (thetaMap E M)
  have hz : zeroSchemeIdeal s = thetaIdeal F N := by
    rw [← hL.comap_zeroSchemeIdeal, thetaMap_eq,
      (thetaIdeal_invertible E M).zeroSchemeIdeal_invModuleSection, hI]
  have hZ : (zeroSchemeIdeal s).IsInvertible := hz ▸ thetaIdeal_invertible F N
  obtain ⟨q, hq⟩ := (hL.pullback f).exists_iso_invModule_zeroSchemeIdeal s hZ
  have hq' : ∃ q : (pullback f).obj (thetaLine E M) ≅ thetaLine F N,
      s ≫ q.hom = thetaMap F N := by
    rw [thetaMap_eq]
    change ∃ q : (pullback f).obj (thetaLine E M) ≅ (thetaIdeal F N).invModule,
      s ≫ q.hom = (thetaIdeal F N).invModuleSection
    rw [← hz]
    exact ⟨q, hq⟩
  exact hq'

lemma local_generator_isIso [IsOpenImmersion b]
    (h : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N b f)
    [IsIso (generator F N)] : IsIso ((pullback b).map (generator E M)) := by
  obtain ⟨q, hq⟩ := line_comparison E M F N b f h
  haveI := isIso_baseChangeHom_of_isOpenImmersion h.1 (thetaLine E M)
  let c := baseChangeHom h.1.w (thetaLine E M) ≫ (pushforward F.p).map q.hom
  haveI : IsIso c := by dsimp [c]; infer_instance
  have hc : (pullback b).map (generator E M) ≫ c =
      (pullbackUnitIso b).hom ≫ generator F N :=
    ArithmeticThetaThetaEvaluationR0212.EvaluationBaseChange.base_change_generator
      h.1.w (thetaMap E M) (thetaMap F N) q.hom hq
  haveI : IsIso ((pullback b).map (generator E M) ≫ c) := by rw [hc]; infer_instance
  exact IsIso.of_isIso_comp_right _ c

/-- An open chart can be replaced by its actual open image without changing
whether a pulled-back sheaf morphism is invertible. -/
lemma isIso_on_open_image {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {A B : X.Modules} (g : A ⟶ B) [IsIso ((pullback j).map g)] :
    IsIso ((pullback j.opensRange.ι).map g) := by
  let e := j.isoOpensRange
  haveI : IsIso (((pullback j) ⋙ pullback e.inv).map g) := by
    change IsIso ((pullback e.inv).map ((pullback j).map g))
    infer_instance
  haveI : IsIso ((pullback (e.inv ≫ j)).map g) :=
    (NatIso.isIso_map_iff (pullbackComp e.inv j) g).mp inferInstance
  have he : e.inv ≫ j = j.opensRange.ι := j.isoOpensRange_inv_comp
  rw [← he]
  infer_instance

#print axioms line_comparison
#print axioms local_generator_isIso
#print axioms isIso_on_open_image


/-- Local Weierstrass charts detect invertibility of the specified generator.
The comparison uses its actual canonical section and open base change. -/
lemma generator_isIso (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ Base k) : IsIso (generator E M) := by
  apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
  intro x
  obtain ⟨P, hx⟩ := scheme_local_weierstrass k S σ E x
  letI := P.commRing
  letI := P.algebra
  letI : Algebra ℚ P.ring := Algebra.compHom P.ring (algebraMap ℚ k)
  letI : P.equation.IsElliptic := P.elliptic
  letI := P.openImmersion
  let F := ArithmeticThetaSchemeLevelR0204.SchemeLocalClassifier.family P
  have hz : F.zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [ArithmeticThetaSchemeLevelR0204.SchemeLocalClassifier.family_zero]
    exact P.zero_eq
  obtain ⟨N, hN, -⟩ := ArithmeticThetaSchemeLevelR0204.cartesian_full_marking
    S (Base P.ring) E F P.base P.comparison P.cartesian hz P.mul_eq 4 M
  let A := ArithmeticThetaSchemeLevelR0204.SchemeLocalClassifier.affineLevel P N
  haveI : IsIso (generator F N) := by
    change IsIso (ArithmeticThetaThetaEvaluationR0212.generator P.ring P.equation P.law A)
    exact (arbitrary_theta_generator_evaluation P.ring P.equation P.law P.originLaw A).1
  have h : ArithmeticThetaSchemeLevelR0204.MarkedCartesian E F M N P.base P.comparison :=
    ⟨P.cartesian, hz, P.mul_eq, hN⟩
  haveI := local_generator_isIso E M F N P.base P.comparison h
  exact ⟨P.base.opensRange, hx, isIso_on_open_image P.base (generator E M)⟩

#print axioms generator_isIso
end SchemeThetaEvaluation
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203

/-- The actual even-theta identity evaluation for every characteristic-zero
scheme base, including empty, nonreduced and non-quasicompact bases. -/
theorem scheme_theta_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (ArithmeticThetaUniversalEvaluationR0213.thetaIdeal E M).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaUniversalEvaluationR0213.thetaLine E M) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaUniversalEvaluationR0213.thetaMap E M) = ArithmeticThetaUniversalEvaluationR0213.thetaIdeal E M ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaLocalWeierstrassR0203.Family.zero E)).obj (ArithmeticThetaUniversalEvaluationR0213.thetaLine E M)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaUniversalEvaluationR0213.IsRigidification E M e) ∧ CategoryTheory.IsIso (ArithmeticThetaUniversalEvaluationR0213.generator E M) ∧ (∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaLocalWeierstrassR0203.Family.zero E)).obj (ArithmeticThetaUniversalEvaluationR0213.thetaLine E M)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaUniversalEvaluationR0213.IsRigidification E M e → CategoryTheory.IsIso (ArithmeticThetaUniversalEvaluationR0213.evaluation E M e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaUniversalEvaluationR0213.generator E M) (ArithmeticThetaUniversalEvaluationR0213.evaluation E M e) = CategoryTheory.CategoryStruct.id (SheafOfModules.unit S.ringCatSheaf) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaUniversalEvaluationR0213.pushforwardLine E M)) ⊤ (ArithmeticThetaUniversalEvaluationR0213.evaluationSection E M e)) := by
  intro k _ _ S σ E M
  have hI := SchemeThetaEvaluation.thetaIdeal_invertible E M
  haveI := SchemeThetaEvaluation.generator_isIso E M k σ
  refine ⟨hI, hI.isInvertible_invModule, ?_,
    SchemeThetaEvaluation.rigidification_unique E M, inferInstance, ?_⟩
  · rw [SchemeThetaEvaluation.thetaMap_eq]
    exact hI.zeroSchemeIdeal_invModuleSection
  · intro e he
    have h := SchemeThetaEvaluation.generator_evaluation E M e he
    have hv : evaluation E M e = inv (generator E M) := by
      apply (cancel_epi (generator E M)).mp
      exact h.trans (IsIso.hom_inv_id _).symm
    refine ⟨?_, h, ?_⟩
    · rw [hv]; infer_instance
    · exact ArithmeticThetaThetaEvaluationR0212.IdentityEvaluation.dual_frame
        (pushforwardLine E M) (generator E M) (evaluation E M e) h

#print axioms scheme_theta_evaluation
end ArithmeticThetaUniversalEvaluationR0213
