module

public import RationalTateDiscriminantDefinitionsR0247
public import RationalNormalizedFrameR0247

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaRationalTateR0247
namespace RationalCoordinateHodge
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential
open ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaPullback

variable (R S : Type) [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
  (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve S) [V.IsElliptic]
  (ι : R →ₐ[ℚ] S) (C : CoordinateComparison R S W V ι.toRingHom)

lemma normalized_on_open (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    relativeD (structureMap R W) (zOpen R W)
      (zSection R W (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective)) =
    zSection R W (zP R W) •
      res (structureMap R W).kaehler le_top (differentialSection R W δ) := by
  obtain ⟨ε,hεx,hεy⟩ := global_frame_on_open R W
  have he := normalized_of_open R W ε hεx
  have hEq := RationalNormalizedFrame.normalized_frames_equal R W ε δ he hδ
  subst δ
  rw [hεx]
  congr 1
  exact (frame_section_restrict (structureMap R W) ε ⊤ (zOpen R W) le_top).symm

def pullDifferential (s : Γ((structureMap R W).kaehler,⊤)) : Γ((structureMap S V).kaehler,⊤) := by
  letI : Algebra R S := ι.toRingHom.toAlgebra
  exact (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w).app ⊤
    (pullbackGlobalSection C.map (structureMap R W).kaehler s)

def pulledFrame (δ : CurveFrame R W) : CurveFrame S V := by
  letI : Algebra R S := ι.toRingHom.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI := differentialMap_isIso (structureMap R W) (structureMap S V) C.map C.cartesian.w C.cartesian
  exact (pullback_unit_iso (Curve S V) (Curve R W) C.map).symm ≪≫
    (Scheme.Modules.pullback C.map).mapIso δ ≪≫
      asIso (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w)

lemma pulledFrame_one (δ : CurveFrame R W) :
    differentialSection S V (pulledFrame R S W V ι C δ) =
      pullDifferential R S W V ι C (differentialSection R W δ) := by
  letI : Algebra R S := ι.toRingHom.toAlgebra
  change (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map _).app ⊤
    (((Scheme.Modules.pullback C.map).map δ.hom).app ⊤
      ((pullback_unit_iso (Curve S V) (Curve R W) C.map).inv.app ⊤ (1 : Γ(Curve S V, ⊤)))) = _
  have hunit : (pullback_unit_iso (Curve S V) (Curve R W) C.map).inv.app ⊤
      (1 : Γ(Curve S V, ⊤)) =
      Scheme.Modules.pullbackLocalSection C.map
        (L := (SheafOfModules.unit (Curve R W).ringCatSheaf : (Curve R W).Modules))
        (1 : Γ(Curve R W, ⊤)) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((pullback_unit_iso (Curve S V) (Curve R W) C.map).hom.app ⊤)).1
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    exact (pullback_unit_local_section (Curve S V) (Curve R W) C.map ⊤).symm
  rw [hunit]
  exact congrArg ((HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w).app ⊤)
    (Scheme.Modules.pullbackLocalSection_app C.map δ.hom (1 : Γ(Curve R W,⊤))).symm

lemma pull_differential_equation
    (U : (Curve R W).Opens) (x p : Γ(Curve R W,U))
    (s : Γ((structureMap R W).kaehler,⊤))
    (hn : ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U x =
      p • res (structureMap R W).kaehler le_top s) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S V) (C.map ⁻¹ᵁ U) (C.map.app U x) =
      C.map.app U p • res (structureMap S V).kaehler le_top (pullDifferential R S W V ι C s) := by
  letI : Algebra R S := ι.toRingHom.toAlgebra
  have hh := congrArg (fun t =>
    (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w).app (C.map ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection C.map t)) hn
  rw [HodgeBaseChange.differentialMap_D, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul] at hh
  rw [hh]
  congr 1
  change (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w).app (C.map ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection C.map (res (structureMap R W).kaehler le_top s)) =
    res (structureMap S V).kaehler le_top
      ((HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w).app ⊤
        (Scheme.Modules.pullbackLocalSection C.map s))
  rw [hom_res]
  congr 1
  exact (Scheme.Modules.map_homOfLE_pullbackLocalSection C.map (show U ≤ ⊤ from le_top) s).symm

lemma pull_differential_on_chart
    (χ : ChartRing R W →+* ChartRing S V)
    (hχ : chartInclusion S V ≫ C.map = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S V)
      (RelativeNormalizedDifferential.zOpen S V)
      (RelativeNormalizedDifferential.zSection S V (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective))) =
    RelativeNormalizedDifferential.zSection S V (χ (RelativeNormalizedDifferential.zP R W)) •
      res (structureMap S V).kaehler le_top
        (pullDifferential R S W V ι C (differentialSection R W δ)) := by
  have h := pull_differential_equation R S W V ι C _ _ _ _ (normalized_on_open R W δ hδ)
  have hr := congrArg (res (structureMap S V).kaehler (chart_preimage W V C.map χ hχ)) h
  rw [relativeD_res,res_smul,res_res] at hr
  change ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S V)
      (RelativeNormalizedDifferential.zOpen S V)
      (C.map.appLE _ _ (chart_preimage W V C.map χ hχ) _) =
    C.map.appLE _ _ (chart_preimage W V C.map χ hχ) _ • res (structureMap S V).kaehler le_top _ at hr
  rw [chart_section_natural W V C.map χ hχ,chart_section_natural W V C.map χ hχ] at hr
  exact hr


lemma pulledFrame_normalized (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    NormalizedFrame S V (pulledFrame R S W V ι C δ) := by
  apply normalized_of_open
  have hp : C.chartMap (zP R W) = zP S V := by
    have hc := chart_scalar_natural W V ι.toRingHom C.map C.cartesian.w
      C.chartMap C.chart_eq.symm
    have h1 : ι.toRingHom W.a₁ = V.a₁ := congrArg WeierstrassCurve.a₁ C.coefficients
    have h3 : ι.toRingHom W.a₃ = V.a₃ := congrArg WeierstrassCurve.a₃ C.coefficients
    simp only [zP,map_add,map_mul,map_ofNat,C.x_eq,C.y_eq,hc,h1,h3]
  have h := pull_differential_on_chart R S W V ι C C.chartMap C.chart_eq.symm δ hδ
  rw [C.x_eq,hp,← pulledFrame_one] at h
  exact h.trans (congrArg (fun s => zSection S V (zP S V) • s)
    (frame_section_restrict (structureMap S V) (pulledFrame R S W V ι C δ)
      ⊤ (zOpen S V) le_top))

lemma pull_hodge_generator (δ : CurveFrame R W) :
    pulledGenerator C δ =
      pullbackGlobalSection (origin S V) (structureMap S V).kaehler
        (pullDifferential R S W V ι C (differentialSection R W δ)) := by
  letI : Algebra R S := ι.toRingHom.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  unfold pulledGenerator
  rw [res_refl]
  change ((Scheme.Modules.pullback (origin S V)).map
    (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w)).app ⊤
    ((squarePullbackIso (baseMap R S ι.toRingHom) (origin R W) (origin S V) C.map C.pointed.symm
      (structureMap R W).kaehler).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (baseMap R S ι.toRingHom)
        (Scheme.Modules.pullbackLocalSection (origin R W) (differentialSection R W δ)))) = _
  have hsq := squarePullbackIso_section (baseMap R S ι.toRingHom) (origin R W) (origin S V) C.map
    C.pointed.symm (structureMap R W).kaehler ⊤ (differentialSection R W δ) ⊤ le_top le_top
  simp only [res_refl] at hsq
  erw [hsq]
  exact (Scheme.Modules.pullbackLocalSection_app (origin S V)
    (HodgeBaseChange.differentialMap (structureMap R W) (structureMap S V) C.map C.cartesian.w)
    (Scheme.Modules.pullbackLocalSection C.map (differentialSection R W δ))).symm

end RationalCoordinateHodge
open ArithmeticThetaGlobalFourTorsionR0190

theorem rational_coordinate_hodge :
    ∀ (R S : Type) [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
      (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve S) [V.IsElliptic]
      (ι : R →ₐ[ℚ] S) (C : CoordinateComparison R S W V ι.toRingHom)
      (δ : CurveFrame R W) (ε : CurveFrame S V),
      NormalizedFrame R W δ → NormalizedFrame S V ε →
        pulledGenerator C δ = hodgeGenerator S V ε := by
  intro R S _ _ _ _ W _ V _ ι C δ ε hδ hε
  have he := RationalNormalizedFrame.normalized_frames_equal S V ε
    (RationalCoordinateHodge.pulledFrame R S W V ι C δ) hε
    (RationalCoordinateHodge.pulledFrame_normalized R S W V ι C δ hδ)
  rw [RationalCoordinateHodge.pull_hodge_generator,
    ← RationalCoordinateHodge.pulledFrame_one, he]
  rfl

#print axioms rational_coordinate_hodge
end ArithmeticThetaRationalTateR0247
