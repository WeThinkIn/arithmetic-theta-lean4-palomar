import TateSchemeMarkingDefinitionsR0263

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaTateSchemeMarkingR0263
namespace SectionEvaluation
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaGenericEvaluationR0140

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (V : TateLevel k (2*m)) {ζ : kˣ}
  (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)

lemma operator_comparison : OperatorComparison k V Q he := by
  intro g f a e h v
  obtain ⟨h, hc⟩ := h
  change LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
    (modelComparison k V Q he) (SectionAction.globalAct g a v) = _
  unfold LocalTheta.modelFunctional
  erw [← LocalTheta.genericDual_globalAct k Q.model Q.origin m (Q.ideal_invertible he) f e]
  rw [← hc, SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]
  rfl

lemma pointed_comparison :
    genericPoint k Q.model Q.origin Q.markedOrigin.1 ≫ Q.cubic.hom = (family k V).zero := by
  let := V.elliptic
  exact Q.cubic_origin.trans
    (ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero
      (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw).symm

/-- Transport of the actual identity fiber along the fixed conormal comparison. -/
def fiberComparison :
    (pullback (family k V).zero).obj (thetaLine (family k V) m) ≅
    dual ((pullback (genericPoint k Q.model Q.origin Q.markedOrigin.1)).obj
      (genericPower k Q.model Q.origin m)) := by
  let p := genericPoint k Q.model Q.origin Q.markedOrigin.1
  let L := genericPower k Q.model Q.origin m
  letI := GenericDualLocalizationR0140.dualComparison_isIso p L (Q.ideal_invertible he)
  exact ((pullbackCongr (pointed_comparison k V Q)).app _).symm ≪≫
    ((pullbackComp p Q.cubic.hom).app _).symm ≪≫
    (pullback p).mapIso (modelComparison k V Q he) ≪≫
    asIso (GenericDualLocalizationR0140.dualComparison p L)

def fiberFrame (e : GenericFrame k Q.model Q.origin Q.markedOrigin.1 m) : FiberFrame k V :=
  fiberComparison k V Q he ≪≫
    ((MonoidalClosed.internalHom (C := (Puncture k).Modules)).mapIso e.symm.op).app
      (𝟙_ (Puncture k).Modules) ≪≫ MonoidalClosed.unitIsoSelf _

lemma value_kernel (frame : GenericFrame k Q.model Q.origin Q.markedOrigin.1 m)
    (e : FiberFrame k V) (v : Γ(thetaLine (family k V) m, ⊤))
    (hv : value k V e v = 0) :
    genericValue k Q.model Q.origin Q.markedOrigin.1 m frame (sectionEquiv k V Q he v) = 0 := by
  apply LocalTheta.genericValue_modelFunctional_zero
  rw [pointed_comparison k V Q]
  exact (SectionAction.pointValue_zero_iff _ _ _ v).mp hv

def modelValueLinear (frame : GenericFrame k Q.model Q.origin Q.markedOrigin.1 m) :
    letI : Algebra (LaurentSeries k) Γ((family k V).curve, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k V).p.appTop).hom.toAlgebra
    letI : Module (LaurentSeries k) Γ(thetaLine (family k V) m, ⊤) :=
      Module.compHom _ (algebraMap (LaurentSeries k) Γ((family k V).curve, ⊤))
    Γ(thetaLine (family k V) m, ⊤) →ₗ[LaurentSeries k] LaurentSeries k := by
  letI : Algebra (LaurentSeries k) Γ((family k V).curve, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k V).p.appTop).hom.toAlgebra
  letI : Module (LaurentSeries k) Γ(thetaLine (family k V) m, ⊤) :=
    Module.compHom _ (algebraMap (LaurentSeries k) Γ((family k V).curve, ⊤))
  refine { toFun := (fun v => genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
    (sectionEquiv k V Q he v)), map_add' := ?_, map_smul' := ?_ }
  · intro v w
    change genericValue _ _ _ _ _ _ (LocalTheta.modelFunctional _ _ _ _ _ _ _ (v+w)) = _
    rw [LocalTheta.modelFunctional_add, LocalTheta.genericValue_add]
    rfl
  · intro a v
    change genericValue _ _ _ _ _ _ (LocalTheta.modelFunctional _ _ _ _ _ _ _
      ((((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k V).p.appTop) a) • v)) = _
    erw [LocalTheta.modelFunctional_smul k Q.model Q.origin m Q.cubic _
      (modelComparison k V Q he) (family k V).p Q.cubic_over]
    exact ArithmeticThetaGeometricLiftsR0141.GeometricBasisProjectiveValuesR0141.value_scaled
      k Q.model Q.origin Q.markedOrigin.1 m frame a _ _
      ((ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141.scaled_iff
        k Q.model Q.origin m _ _ _).mpr rfl)

lemma exact_values (hζ : IsPrimitiveRoot (ζ : k) (2*m)) : ExactValues k V Q he := by
  obtain ⟨⟨frame⟩, hv⟩ := ArithmeticThetaGeometricLiftsR0141.geometric_basis_projective_values
    k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
    Q.rotation Q.scaling Q.inversion Q.actions (ζ^2)
    (LocalTheta.MarkedModel.root_half (hm := hm) hζ)
    (Q.canonicalA he hζ) (Q.canonicalB he) (Q.canonicalA_eigen he hζ) (Q.canonicalB_cyclic he)
    (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin)
    (generic_theta_basis k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin)
    (Q.canonicalA_eigen he hζ) (Q.canonicalB_cyclic he)
  refine ⟨⟨fiberFrame k V Q he frame⟩, ?_⟩
  intro e
  letI : Algebra (LaurentSeries k) Γ((family k V).curve, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k V).p.appTop).hom.toAlgebra
  letI : Module (LaurentSeries k) Γ(thetaLine (family k V) m, ⊤) :=
    Module.compHom _ (algebraMap (LaurentSeries k) Γ((family k V).curve, ⊤))
  let f := SectionAction.pointValueLinear (family k V).p (family k V).zero
    ((family k V).law.one (𝟙 _)).property (thetaLine (family k V) m) e
  let g := modelValueLinear k V Q he frame
  have hker : ∀ v, f v = 0 → g v = 0 := value_kernel k V Q he frame e
  have hg (ν : Fin m) : g (basisSection k V Q he ν) =
      genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
        (genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin ν) := by
    change genericValue _ _ _ _ _ _ ((sectionEquiv k V Q he)
      ((sectionEquiv k V Q he).symm _)) = _
    rw [Equiv.apply_symm_apply]
  have hzero : g (basisSection k V Q he ⟨0,hm⟩) ≠ 0 := by
    rw [hg]
    exact (hv frame).1
  have hquot (ν : Fin m) :=
    ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.Representation.quotient_of_kernel
      (RingHom.id (LaurentSeries k)) f g hker
      (basisSection k V Q he ⟨0,hm⟩) (basisSection k V Q he ν) hzero
  refine ⟨(hquot ⟨0,hm⟩).1, ?_⟩
  intro ν
  have h := (hquot ν).2
  rw [hg, hg] at h
  exact h.trans ((hv frame).2 ν)

end SectionEvaluation

open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- Actual section actions and complete identity values through the fixed
conormal theta comparison, in every identity-fiber frame. -/
theorem tate_scheme_section_evaluation :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
      (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
      ∀ Q : LocalTheta.MarkedModel k m hm V ζ,
        OperatorComparison k V Q he ∧ ExactValues k V Q he := by
  intro k _ _ m hm he V ζ hζ Q
  exact ⟨SectionEvaluation.operator_comparison k V Q he,
    SectionEvaluation.exact_values k V Q he hζ⟩

end ArithmeticThetaTateSchemeMarkingR0263

#print axioms ArithmeticThetaTateSchemeMarkingR0263.SectionEvaluation.operator_comparison
#print axioms ArithmeticThetaTateSchemeMarkingR0263.SectionEvaluation.fiberComparison
#print axioms ArithmeticThetaTateSchemeMarkingR0263.SectionEvaluation.value_kernel
#print axioms ArithmeticThetaTateSchemeMarkingR0263.tate_scheme_section_evaluation
