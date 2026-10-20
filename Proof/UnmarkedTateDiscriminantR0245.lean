module

public import SchemeTateDiscriminantDefinitionsR0245

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaSchemeTateDiscriminantR0245
open ArithmeticThetaBoundaryHodgeR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 OpenDiscriminantFullTateExpansionR0182

/-- The intrinsic normalized discriminant has its complete coefficient in every
specified normalized frame, with no level marking or root of unity. -/
theorem unmarked_tate_discriminant :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 3 ≤ L → Even L →
      ∀ (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L),
      ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ →
      ∀ (d : TateSections k L), NormalizedDiscriminant k L d → FullExpansion k L δ d := by
  intro k _ _ L hL heven δ hδ d hd
  letI := TateFullLevelMarking.elliptic k L hL heven
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have geom := relative_curve_geometry (LaurentSeries k) (TateCurve k L)
  letI := geom.1
  letI := geom.2.1
  letI := geom.2.2.2.1
  letI := geom.2.2.2.2.1
  letI := geom.2.2.2.2.2.1
  have hpos : 0 < L := by omega
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k L hL hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k L hpos hL T M hM (zeroIndex L hpos) 1
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k L hpos hL T heven M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k L
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k L hpos hL T heven M hM s hs X Y hX hY a ha c hc
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k hL M hM
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k hL M hM s hs
  letI : IsLocallyNoetherian (genericScheme k M) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  have hEs : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k L) = genericStructure k M := hE.1
  have hOs : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k L) := hE.2.2
  obtain ⟨G₀, hG₀, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    k L hpos hL T heven M hM s hs
  have hei : E.inv ≫ genericStructure k M = structureMap (LaurentSeries k) (TateCurve k L) := by
    rw [← hEs, Iso.inv_hom_id_assoc]
  let H := ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport E.symm hei G₀
  have hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k L) H := by
    constructor
    · intro V t
      change (G₀.one t).val ≫ E.hom = _
      rw [hG₀.1]
      change (t ≫ genericPoint k M s hs.1) ≫ E.hom = _
      rw [Category.assoc, hOs]
    · intro V t x y
      change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E.symm hei t).symm
        (G₀.mul t _ _) =
        (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E.symm hei t).symm
        (G₀.mul t _ _)
      rw [hG₀.2]
  let G : ArithmeticThetaMarkedGroupLawR0146.Law k M := ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport E hEs H
  have hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G := by
    constructor
    · intro S t
      apply Subtype.ext
      change (H.one t).val ≫ E.inv = t ≫ genericPoint k M s hs.1
      rw [hH.1]
      change (t ≫ origin (LaurentSeries k) (TateCurve k L)) ≫ E.inv = _
      rw [← hOs]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro S t x y
      change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E hEs t).symm
        (H.mul t _ _) =
        (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E hEs t).symm
        (H.mul t _ _)
      rw [hH.2]
  obtain ⟨α,hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap E.hom
  obtain ⟨g,hg⟩ := GlobalFamilyDiscriminantR0180.normalized_exists
    (LaurentSeries k) (TateCurve k L) H hH 5 (by norm_num) (by norm_num)
  have hgm := normalized_kato_to_model k M s hs.1 (TateCurve k L)
    H hH G E hEs hOs
    (fun n => transported_schemeNsmul E hEs H n) α hα 5 (by norm_num) g hg
  obtain ⟨dm,hm,_,hex⟩ := ArithmeticThetaHodgeInitialR0163.geometric_discriminant_hodge
    k L hpos hL heven T M hM s hs G hG X Y hX hY (α g) hgm
  let e := pointedIso _ _ E hEs (genericPoint k M s hs.1) _ hOs
  let p := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (LaurentSeries k)))
  letI : IsIso p := by
    dsimp only [p]
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  let δm : ArithmeticThetaHodgeFourTorsionR0147.Frame k M := pulledCurveFrame _ _ E hEs δ
  have hnorm := model_pulled_frame_normalized k M s hs.1 hL hM hs X Y a ha c hc E hE
    δ hδ
  have heq := initial_section_comparison k M s hs.1 (TateCurve k L) H hH
    E hEs hOs α hα g d
    (ArithmeticThetaArbitraryDiscriminantR0243.ArbitraryWeierstrassDiscriminant.represents_initial
      (LaurentSeries k) (TateCurve k L) H hH d hd g hg) dm hm
  unfold FullExpansion
  apply transportSection_injective p _ _ (tensorComparison p _ _ e 24)
  rw [heq]
  rw [transportSection_smul, transportSection_tensor]
  have hgen := (transport_pointGenerator _ _ E hEs (genericPoint k M s hs.1) _
    hOs δ).trans
      (pointGenerator_frame (genericStructure k M) (genericPoint k M s hs.1) δm)
  change transportSection p _ _ e (hodgeGenerator k L δ) =
    ArithmeticThetaHodgeFourTorsionR0147.hodgeSection k M s hs.1 δm 1 at hgen
  rw [hgen]
  have hscalar : p.appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
        (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L) := by
    have hp : p = 𝟙 _ := by
      dsimp only [p]
      simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [hp]
    erw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
    rfl
  rw [hscalar]
  exact (hex δm hnorm).2

#print axioms unmarked_tate_discriminant
end ArithmeticThetaSchemeTateDiscriminantR0245
