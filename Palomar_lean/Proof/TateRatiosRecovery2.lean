module
import all GenericThetaBasisR0140
public import ProjectiveProviderBridge
import all ProjectiveProviderBridge
public import AlternationRecovery
import all AlternationRecovery
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 32768
set_option maxHeartbeats 64000000
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaTateSchemeMarkingR0263 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaInvariantRatiosR0265
open ArithmeticThetaInvariantRatiosR0265.TateInvariantComponentRatios
namespace PalomarRatios1408
def RatiosGenerator : Prop := ∀ {F : Type} [Field F] {M N : (Base F).Modules}
    {n : ℕ} (hn : 0 < n) (f : Fin n → (M ⟶ N)) (r : Fin n → F)
    (e : N ≅ (SheafOfModules.unit (Base F).ringCatSheaf : (Base F).Modules))
    (x₀ : Γ(M, ⊤))
    (hspan : ∀ x : Γ(M, ⊤), ∃ c : F,
      x = (Scheme.ΓSpecIso (CommRingCat.of F)).inv c • x₀)
    (hne : frameValue e ((f ⟨0,hn⟩).app ⊤ x₀) ≠ 0)
    (hr : ∀ i, frameValue e ((f i).app ⊤ x₀) =
      frameValue e ((f ⟨0,hn⟩).app ⊤ x₀) * r i),
    IsIso (f ⟨0,hn⟩) ∧ ∀ i, f i = f ⟨0,hn⟩ ≫ scalarEnd N (r i)
variable (hrg : RatiosGenerator) (hg : PalomarAlternation1305.GenericDualAction)
lemma action_top {S : Scheme} (E : Family S) (m : ℕ)
    (g : E.curve ⟶ E.curve) (a : Lift E m g) (A : End (V E m))
    (hA : IsAction E m g a A) (v : Γ(thetaLine E m, ⊤)) :
    A.app ⊤ v = SectionAction.globalAct g a v := by
  obtain ⟨h, hh⟩ := hA
  simpa [SectionAction.globalAct,
    ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.Sections.act]
    using (hh ⊤ v).symm

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (Vd : TateLevel k (2*m)) {ζ : kˣ}
  (Q : LocalTheta.MarkedModel k m hm Vd ζ) (he : Even m)

open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaGeometricLiftsR0141 (act)
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141 (sc sc_one)
open ArithmeticThetaGeometricLiftsR0141.GeometricIntertwinerRigidityR0141

open ArithmeticThetaTateSchemeMarkingR0263.SectionEvaluation
lemma model_fixed (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (v : GenericDual k Q.model Q.origin m)
    (hv : act k Q.model Q.origin m Q.mapA (Q.canonicalA he hζ) v = v) :
    ∃ c : LaurentSeries k, v = sc k Q.model Q.origin m c
      (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin ⟨0,hm⟩) := by
  classical
  letI : AddCommGroup (GenericDual k Q.model Q.origin m) :=
    inferInstanceAs (AddCommGroup (genericPower k Q.model Q.origin m ⟶
      (SheafOfModules.unit (genericScheme k Q.model).ringCatSheaf : (genericScheme k Q.model).Modules)))
  let b := genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin
  have hb := generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
  obtain ⟨c, hc, _⟩ := hb v
  have heq : v = combine k Q.model Q.origin m m b c :=
    (combines_iff k Q.model Q.origin m m b c v).mp hc
  have hact := eigen_combine k Q.model Q.origin m m b (ζ^2) Q.mapA
    (ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.scalarMap_over
      k Q.model Q.rotation Q.scaling Q.inversion Q.actions (ζ^2))
    (Q.canonicalA he hζ) (Q.canonicalA_eigen he hζ) c
  have hcoords : ArithmeticThetaSchrodingerR0119.standardA k m ((ζ^2 : kˣ) : k) c = c := by
    apply combine_injective k Q.model Q.origin m m b hb
    rw [← hact, ← heq, hv]
  have hvanish (i : Fin m) (hi : i ≠ ⟨0,hm⟩) : c i = 0 := by
    have hi0 : 0 < i.val := by
      by_contra hn
      apply hi
      apply Fin.ext
      change i.val = 0
      omega
    have hn := (LocalTheta.MarkedModel.root_half (hm := hm) hζ).pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hi0) i.isLt
    have hscalar : ArithmeticThetaSchrodingerR0119.scalar k (((ζ^2 : kˣ) : k)^i.val) ≠ 1 := by
      intro h
      apply hn
      exact HahnSeries.single_injective 0 (h.trans HahnSeries.single_zero_one.symm)
    have hiEq := congrFun hcoords i
    change ArithmeticThetaSchrodingerR0119.scalar k _ * c i = c i at hiEq
    exact (mul_eq_zero.mp (show
      (ArithmeticThetaSchrodingerR0119.scalar k (((ζ^2 : kˣ) : k)^i.val) - 1) * c i = 0 by
        rw [sub_mul, one_mul, hiEq, sub_self])).resolve_left (sub_ne_zero.mpr hscalar)
  refine ⟨c ⟨0,hm⟩, ?_⟩
  rw [heq]
  unfold combine
  rw [Finset.sum_eq_single ⟨0,hm⟩]
  · rfl
  · intro i _ hi
    rw [hvanish i hi]
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    simp [mulSection_app]
  · simp

include hg in
lemma operator_comparison : ArithmeticThetaTateSchemeMarkingR0263.OperatorComparison k Vd Q he := by
  intro g f a e h v
  obtain ⟨h, hc⟩ := h
  change LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
    (modelComparison k Vd Q he) (SectionAction.globalAct g a v) = _
  unfold LocalTheta.modelFunctional
  erw [← hg k Q.model Q.origin m (Q.ideal_invertible he) f e]
  rw [← hc, SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]
  rfl

lemma exact_values (hζ : IsPrimitiveRoot (ζ : k) (2*m)) : ArithmeticThetaTateSchemeMarkingR0263.ExactValues k Vd Q he := by
  obtain ⟨⟨frame⟩, hv⟩ := ArithmeticThetaGeometricLiftsR0141.geometric_basis_projective_values
    k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2)
    (LocalTheta.MarkedModel.root_half (hm := hm) hζ)
    (Q.canonicalA he hζ) (Q.canonicalB he) (Q.canonicalA_eigen he hζ) (Q.canonicalB_cyclic he)
    (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin)
    (generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin)
    (Q.canonicalA_eigen he hζ) (Q.canonicalB_cyclic he)
  refine ⟨⟨fiberFrame k Vd Q he frame⟩, ?_⟩
  intro e
  letI : Algebra (LaurentSeries k) Γ((family k Vd).curve, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k Vd).p.appTop).hom.toAlgebra
  letI : Module (LaurentSeries k) Γ(thetaLine (family k Vd) m, ⊤) :=
    Module.compHom _ (algebraMap (LaurentSeries k) Γ((family k Vd).curve, ⊤))
  let f := SectionAction.pointValueLinear (family k Vd).p (family k Vd).zero
    ((family k Vd).law.one (𝟙 _)).property (thetaLine (family k Vd) m) e
  let g := modelValueLinear k Vd Q he frame
  have hker : ∀ v, f v = 0 → g v = 0 := value_kernel k Vd Q he frame e
  have hg (ν : Fin m) : g (basisSection k Vd Q he ν) =
      genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
        (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin ν) := by
    change genericValue _ _ _ _ _ _ ((sectionEquiv k Vd Q he)
      ((sectionEquiv k Vd Q he).symm _)) = _
    rw [Equiv.apply_symm_apply]
  have hzero : g (basisSection k Vd Q he ⟨0,hm⟩) ≠ 0 := by
    rw [hg]
    exact (hv frame).1
  have hquot (ν : Fin m) :=
    ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation.quotient_of_kernel
      (RingHom.id (LaurentSeries k)) f g hker
      (basisSection k Vd Q he ⟨0,hm⟩) (basisSection k Vd Q he ν) hzero
  refine ⟨(hquot ⟨0,hm⟩).1, ?_⟩
  intro ν
  have h := (hquot ν).2
  rw [hg, hg] at h
  exact h.trans ((hv frame).2 ν)

include hrg hg in
lemma shift_basis
    (b : Lift (family k Vd) m (translation (family k Vd) (pointY k Vd)))
    (hb : shiftLiftFacts k Vd Q he b) (B : End (V (family k Vd) m))
    (hB : IsAction (family k Vd) m _ b B) (i : Fin m) :
    B.app ⊤ (basisSection k Vd Q he i) =
      basisSection k Vd Q he (ArithmeticThetaInfinitesimalPolygonR0129.next m hm i) := by
  rw [action_top _ _ _ _ _ hB]
  apply (sectionEquiv k Vd Q he).injective
  rw [operator_comparison hg k Vd Q he _ _ b _ hb.1]
  simp only [basisSection, Equiv.apply_symm_apply]
  exact Q.canonicalB_cyclic he i

include hrg hg in
lemma shift_pow_basis
    (b : Lift (family k Vd) m (translation (family k Vd) (pointY k Vd)))
    (hb : shiftLiftFacts k Vd Q he b) (B : End (V (family k Vd) m))
    (hB : IsAction (family k Vd) m _ b B) (n : ℕ) (hn : n < m) :
    (B ^ n).app ⊤ (basisSection k Vd Q he ⟨0,hm⟩) = basisSection k Vd Q he ⟨n,hn⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change B.app ⊤ ((B ^ n).app ⊤ (basisSection k Vd Q he ⟨0,hm⟩)) = _
    rw [ih (by omega), shift_basis hrg hg k Vd Q he b hb B hB]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt hn

include hrg hg in
lemma scalar_basis (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k Vd) m (translation (family k Vd) (pointX k Vd)))
    (ha : scalarLiftFacts k Vd Q he hζ a) (A : End (V (family k Vd) m))
    (hA : IsAction (family k Vd) m _ a A) :
    A.app ⊤ (basisSection k Vd Q he ⟨0,hm⟩) = basisSection k Vd Q he ⟨0,hm⟩ := by
  rw [action_top _ _ _ _ _ hA]
  apply (sectionEquiv k Vd Q he).injective
  rw [operator_comparison hg k Vd Q he _ _ a _ ha.1]
  simp only [basisSection, Equiv.apply_symm_apply]
  have h := (ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141.scaled_iff
    k Q.model Q.origin m _ _ _).mp (Q.canonicalA_eigen he hζ ⟨0,hm⟩)
  simpa [ArithmeticThetaGeometricLiftsR0141.phase, sc_one] using h

include hrg hg in
lemma fixed_top_span (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k Vd) m (translation (family k Vd) (pointX k Vd)))
    (ha : scalarLiftFacts k Vd Q he hζ a) (A : End (V (family k Vd) m))
    (hA : IsAction (family k Vd) m _ a A)
    (v : Γ(V (family k Vd) m, ⊤)) (hv : A.app ⊤ v = v) :
    ∃ c : LaurentSeries k, v =
      (((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k Vd).p.appTop) c) •
        basisSection k Vd Q he ⟨0,hm⟩ := by
  have hmodel : act k Q.model Q.origin m Q.mapA (Q.canonicalA he hζ)
      (sectionEquiv k Vd Q he v) = sectionEquiv k Vd Q he v := by
    rw [← operator_comparison hg k Vd Q he _ _ a _ ha.1,
      ← action_top _ _ _ _ _ hA, hv]
  obtain ⟨c, hc⟩ := model_fixed k Vd Q he hζ _ hmodel
  refine ⟨c, (sectionEquiv k Vd Q he).injective ?_⟩
  change _ = LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
    (modelComparison k Vd Q he)
    ((((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k Vd).p.appTop) c) • _)
  erw [LocalTheta.modelFunctional_smul k Q.model Q.origin m Q.cubic _
    (modelComparison k Vd Q he) (family k Vd).p Q.cubic_over]
  change (sectionEquiv k Vd Q he) v = sc k Q.model Q.origin m c
    ((sectionEquiv k Vd Q he) (basisSection k Vd Q he ⟨0,hm⟩))
  simpa only [basisSection, Equiv.apply_symm_apply] using hc

include hrg hg in
lemma value_evaluation (e : FiberFrame k Vd)
    (v : Γ(thetaLine (family k Vd) m, ⊤)) :
    value k Vd e v = (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
      (e.hom.app ⊤ ((evaluation (family k Vd) m).app ⊤ v)) := by
  rw [SchemeThetaIdentityEvaluation.evaluation_top]
  rfl

include hrg hg in
lemma component_ratios (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k Vd) m (translation (family k Vd) (pointX k Vd)))
    (b : Lift (family k Vd) m (translation (family k Vd) (pointY k Vd)))
    (ha : scalarLiftFacts k Vd Q he hζ a) (hb : shiftLiftFacts k Vd Q he b)
    (A B : End (V (family k Vd) m))
    (hA : IsAction (family k Vd) m _ a A) (hB : IsAction (family k Vd) m _ b B) :
    ComponentRatios (family k Vd) m hm A B (unaryRatio k m hm) := by
  obtain ⟨⟨e⟩, heval⟩ := exact_values k Vd Q he hζ
  obtain ⟨x₀, hx₀⟩ := (SchemeSchrodingerOrbit.fixedSections_bijective A ⊤).2
    ⟨basisSection k Vd Q he ⟨0,hm⟩, by
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact scalar_basis hrg hg k Vd Q he hζ a ha A hA⟩
  have hzero : (fixedι A).app ⊤ x₀ = basisSection k Vd Q he ⟨0,hm⟩ :=
    congrArg Subtype.val hx₀
  have hinj : Function.Injective ((fixedι A).app ⊤) :=
    (ModuleCat.mono_iff_injective ((SchemeSchrodingerOrbit.sections ⊤).map (fixedι A))).mp
      inferInstance
  have hspan (x : Γ(fixed A, ⊤)) : ∃ c : LaurentSeries k,
      x = (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c • x₀ := by
    obtain ⟨c, hc⟩ := fixed_top_span hrg hg k Vd Q he hζ a ha A hA
      ((fixedι A).app ⊤ x) (SchemeSchrodingerOrbit.fixed_mem A ⊤ x)
    refine ⟨c, hinj ?_⟩
    rw [Scheme.Modules.Hom.app_smul, hzero]
    exact hc
  have hcomp (i : Fin m) : frameValue e ((component (family k Vd) m A B i).app ⊤ x₀) =
      value k Vd e (basisSection k Vd Q he i) := by
    change frameValue e ((evaluation (family k Vd) m).app ⊤
      ((B ^ i.val).app ⊤ ((fixedι A).app ⊤ x₀))) = _
    rw [hzero, shift_pow_basis hrg hg k Vd Q he b hb B hB i.val i.isLt]
    exact (value_evaluation hrg hg k Vd e _).symm
  apply hrg hm (component (family k Vd) m A B) (unaryRatio k m hm) e x₀ hspan
  · rw [hcomp]
    exact (heval e).1
  · intro i
    rw [hcomp, hcomp]
    have h := (heval e).2 i
    change value k Vd e (basisSection k Vd Q he i) /
      value k Vd e (basisSection k Vd Q he ⟨0,hm⟩) = unaryRatio k m hm i at h
    exact (div_eq_iff (heval e).1).mp h |>.trans (mul_comm _ _)

theorem tateratios (hrg : RatiosGenerator) (hg : PalomarAlternation1305.GenericDualAction) : PalomarProjective969.TateRatios := by
  intro k _ _ m hm he Vd ζ hζ Q a b ha hb A B hA hB
  exact component_ratios hrg hg k Vd Q he hζ a b ha hb A B hA hB
end PalomarRatios1408
