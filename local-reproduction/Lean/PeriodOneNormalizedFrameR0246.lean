import PeriodOneDiscriminantDefinitionsR0246

/-! The normalized differential descends through every specified coordinate
comparison. The differential map is the derivative of that comparison. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
namespace ArithmeticThetaPeriodOneR0246
namespace NormalizedFrameProof
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential
open ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaTateCuspsR0181

/-- Reconcile global-section conventions before specializing to cubic curves. -/
lemma global_transport {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (a : Γ(M, ⊤)) :
    res N (by simp) (e.hom.app _ (Scheme.Modules.pullbackLocalSection f a)) =
      e.hom.app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection f M a) := by
  simp only [res_refl, Scheme.Hom.preimage_top]
  rfl

lemma boundary_generator (k : Type) [Field k] [CharZero k]
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k 4) :
    ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k 4 δ =
      hodgeGenerator (LaurentSeries k) (TateCurve k 4) δ := by
  unfold ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator
  rw [res_refl]
  rfl

/-- Transport the chart equation together with the open-immersion witness. -/
lemma chart_normalization_transport {R A : Type} [CommRing R] [CommRing A]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R))
    (δ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ f.kaehler)
    (j i : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] [IsOpenImmersion i]
    (h : j = i) (x y : A)
    (hn : relativeD f (j ''ᵁ ⊤) ((chartRingEquiv j).symm x) =
      (2 * (chartRingEquiv j).symm y) •
        Scheme.Modules.Hom.app δ.hom (j ''ᵁ ⊤) (1 : Γ(X, j ''ᵁ ⊤))) :
    relativeD f (i ''ᵁ ⊤) ((chartRingEquiv i).symm x) =
      (2 * (chartRingEquiv i).symm y) •
        Scheme.Modules.Hom.app δ.hom (i ''ᵁ ⊤) (1 : Γ(X, i ''ᵁ ⊤)) := by
  subst i
  exact hn

lemma boundary_normalized (k : Type) [Field k] [CharZero k]
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k 4)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k 4 δ) :
    NormalizedFrame (LaurentSeries k) (TateCurve k 4) δ := by
  have hp : RelativeNormalizedDifferential.zP (LaurentSeries k) (TateCurve k 4) =
      2 * WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k 4).toProjective := by
    change 2 * _ + ArithmeticThetaLegendreComparisonR0177.chartScalar _ _ 0 * _ +
      ArithmeticThetaLegendreComparisonR0177.chartScalar _ _ 0 = _
    rw [map_zero, zero_mul, add_zero, add_zero]
  apply normalized_of_open
  rw [hp, map_mul, map_ofNat]
  exact chart_normalization_transport _ δ
    (zLeg k 4 (Iso.refl (projectiveCurve k 4)))
    (ArithmeticThetaLegendreComparisonR0177.chartInclusion _ (TateCurve k 4))
    (by simp only [zLeg, Iso.refl_inv, Category.comp_id]; rfl) _ _ hδ

lemma unique_frame (k : Type) [Field k] [CharZero k]
    [(periodOneCurve k).IsElliptic] : ∃! δ : PeriodFrame k, Normalized k δ := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨δ, hδ, hu⟩ := relative_normalized_differential (LaurentSeries k) (periodOneCurve k)
  exact ⟨δ, hδ.1, fun ε hε => hu ε ⟨hε, hodge_generator_frame _ _ ε⟩⟩

/-- Equality of the actual curve differentials for a map preserving x and y.
The proof uses the accepted chart chain rule, followed by faithful restriction. -/
lemma coordinate_differential
    (R S : Type) [Field R] [CharZero R] [Field S] [CharZero S]
    (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve S) [V.IsElliptic]
    (G : Law R W) (H : Law S V) (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
    (χ : ArithmeticThetaLegendreComparisonR0177.ChartRing R W →+*
      ArithmeticThetaLegendreComparisonR0177.ChartRing S V)
    (hχ : ArithmeticThetaLegendreComparisonR0177.chartInclusion S V ≫ b =
      Spec.map (CommRingCat.ofHom χ) ≫ ArithmeticThetaLegendreComparisonR0177.chartInclusion R W)
    (hx : χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
      WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
      WeierstrassCurve.DrinfeldGlobal.yOverZ V.toProjective)
    (hW1 : W.a₁ = 0) (hW3 : W.a₃ = 0) (hV1 : V.a₁ = 0) (hV3 : V.a₃ = 0)
    (δ : CurveFrame R W) (ε : CurveFrame S V)
    (hδ : NormalizedFrame R W δ) (hε : NormalizedFrame S V ε) :
    pullDifferential R W G S V H ι b hb (differentialSection R W δ) =
      differentialSection S V ε := by
  letI := (relative_curve_geometry S V).1
  letI := RelativeNormalizedDifferential.zOpen_nonempty S V
  let U := RelativeNormalizedDifferential.zOpen S V
  let p := RelativeNormalizedDifferential.zSection S V (RelativeNormalizedDifferential.zP S V)
  have hp : p ≠ 0 := by
    intro hz
    apply RelativeNormalizedDifferential.zP_ne_zero S V
    apply (RelativeNormalizedDifferential.zSection S V).injective
    simpa only [map_zero] using hz
  have hP : χ (RelativeNormalizedDifferential.zP R W) =
      RelativeNormalizedDifferential.zP S V := by
    simp only [RelativeNormalizedDifferential.zP, hW1, hW3, hV1, hV3,
      map_zero, zero_mul, add_zero, map_mul, map_ofNat, hy]
  have hh := pull_differential_on_chart R W G S V H ι b hb χ hχ δ hδ
  rw [hx, hP, normalized_on_open S V ε hε] at hh
  apply frame_restrict_injective ε ⊤ U le_top
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app ε.inv U)).1
  have he := congrArg (Scheme.Modules.Hom.app ε.inv U) hh
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at he
  exact (mul_left_cancel₀ hp he).symm

lemma coordinate_hodge
    (R S : Type) [Field R] [CharZero R] [Field S] [CharZero S]
    (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve S) [V.IsElliptic]
    (G : Law R W) (H : Law S V) (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
    (χ : ArithmeticThetaLegendreComparisonR0177.ChartRing R W →+*
      ArithmeticThetaLegendreComparisonR0177.ChartRing S V)
    (hχ : ArithmeticThetaLegendreComparisonR0177.chartInclusion S V ≫ b =
      Spec.map (CommRingCat.ofHom χ) ≫ ArithmeticThetaLegendreComparisonR0177.chartInclusion R W)
    (hx : χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
      WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
      WeierstrassCurve.DrinfeldGlobal.yOverZ V.toProjective)
    (hW1 : W.a₁ = 0) (hW3 : W.a₃ = 0) (hV1 : V.a₁ = 0) (hV3 : V.a₃ = 0)
    (δ : CurveFrame R W) (ε : CurveFrame S V)
    (hδ : NormalizedFrame R W δ) (hε : NormalizedFrame S V ε) :
    pullAlpha R W G S V H ι b hb (hodgeGenerator R W δ) = hodgeGenerator S V ε := by
  rw [pull_hodge_generator,
    coordinate_differential R S W V G H ι b hb χ hχ hx hy hW1 hW3 hV1 hV3 δ ε hδ hε]
  rfl

/-- The arbitrary-comparison and relative-naturality APIs use the same derivative. -/
lemma comparison_pull (R S : Type) [Field R] [CharZero R] [Field S] [CharZero S]
    (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve S)
    (G : Law R W) (H : Law S V) (ι : R →+* S)
    (C : ArithmeticThetaArbitraryDiscriminantR0243.Comparison R S W V ι)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι C.map)
    (a : Γ(Hodge R W, ⊤)) :
    res _ (by simp)
      ((ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge C).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι)) a)) =
      pullAlpha R W G S V H ι C.map hb a := by
  have hi : ArithmeticThetaArbitraryDiscriminantR0243.comparisonHodge C =
      hodgeComparison R W G S V H ι C.map hb := rfl
  rw [hi]
  exact global_transport (Spec.map (CommRingCat.ofHom ι)) _ _
    (hodgeComparison R W G S V H ι C.map hb) a

lemma origin_law (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ G : Law R W, IsOriginLaw R W G := by
  obtain ⟨G, hc, ho⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
      W.toProjective (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  exact ⟨G, ho, hc⟩

end NormalizedFrameProof


open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaTateCuspsR0181

/-- The unique period-one normalized differential and its exact pullback through
 every coordinate-preserving pointed Cartesian comparison. -/
theorem period_one_normalized_frame :
    ∀ (k : Type) [Field k] [CharZero k] [hE : (ArithmeticThetaPeriodOneR0246.periodOneCurve k).IsElliptic], (∃! δ : ArithmeticThetaPeriodOneR0246.PeriodFrame k, ArithmeticThetaPeriodOneR0246.Normalized k δ) ∧ ∀ (ell : LaurentSeries k →+* LaurentSeries k), ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell → ∀ (C : ArithmeticThetaPeriodOneR0246.CoordinateComparison k ell) (δ : ArithmeticThetaPeriodOneR0246.PeriodFrame k), ArithmeticThetaPeriodOneR0246.Normalized k δ → ∀ (δ₄ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k 4), ArithmeticThetaBoundaryHodgeR0182.Normalized k 4 δ₄ → ArithmeticThetaPeriodOneR0246.pulledGenerator k C δ = ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k 4 δ₄ := by
  intro k _ _ hE
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  refine ⟨NormalizedFrameProof.unique_frame k, ?_⟩
  intro ell _hell C δ hδ δ₄ hδ₄
  letI := TateFullLevelMarking.elliptic k 4 (by decide) (by decide)
  obtain ⟨G, hG⟩ := NormalizedFrameProof.origin_law (LaurentSeries k) (periodOneCurve k)
  obtain ⟨H, hH⟩ := NormalizedFrameProof.origin_law (LaurentSeries k) (TateCurve k 4)
  have hb := ArithmeticThetaLegendreComparisonR0177.MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change
    G H hG hH ell C.map C.cartesian C.pointed
  have hg := NormalizedFrameProof.coordinate_hodge
    (LaurentSeries k) (LaurentSeries k) (periodOneCurve k) (TateCurve k 4)
    G H ell C.map hb C.chartMap C.chart_eq.symm C.x_eq C.y_eq
    rfl rfl rfl rfl δ δ₄ hδ (NormalizedFrameProof.boundary_normalized k δ₄ hδ₄)
  exact (NormalizedFrameProof.comparison_pull
    (LaurentSeries k) (LaurentSeries k) (periodOneCurve k) (TateCurve k 4)
    G H ell C.toComparison hb (generator k δ)).trans
      (hg.trans (NormalizedFrameProof.boundary_generator k δ₄).symm)

#print axioms ArithmeticThetaPeriodOneR0246.period_one_normalized_frame
end ArithmeticThetaPeriodOneR0246
