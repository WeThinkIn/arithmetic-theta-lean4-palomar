import RelativeFourTorsionRootR0190
import RelativeNormalizedDifferentialR0190

/-! Intrinsic relative four-torsion section: uniqueness of the coordinate formula
and existence as a frame. Naturality uses the actual differential comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaGlobalFourTorsionR0190
namespace RelativeAlphaNaturality
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177

lemma coordinates_unique {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {P : Base R ⟶ Curve R W} {x y x' y' : R}
    (h : HasCoordinates R W P x y) (h' : HasCoordinates R W P x' y') :
    x = x' ∧ y = y' := by
  obtain ⟨_, χ, hχ, hx, hy⟩ := h
  obtain ⟨_, ψ, hψ, hx', hy'⟩ := h'
  have hm : Mono (chartInclusion R W) :=
    inferInstanceAs (Mono (WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective))
  letI := hm
  have he := Spec.map_injective ((cancel_mono (chartInclusion R W)).mp (hχ.symm.trans hψ))
  have he' : χ = ψ := congrArg CommRingCat.Hom.hom he
  subst ψ
  exact ⟨hx.symm.trans hx', hy.symm.trans hy'⟩

lemma root_data_unique {R : Type u} [CommRing R] [IsDomain R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (G : Law R W) (L : ℕ)
    (M : FullLevel R W G L (𝟙 (Base R)))
    {e e' : Fin 3 → R} {x y g x' y' g' : R}
    (h : RootData R W G L M e x y g) (h' : RootData R W G L M e' x' y' g') :
    e = e' ∧ x = x' ∧ y = y' ∧ g = g' := by
  have he : e = e' := funext (fun i => (coordinates_unique W (h.1 i) (h'.1 i)).1)
  obtain ⟨hx, hy⟩ := coordinates_unique W h.2.2.1 h'.2.2.1
  subst e'; subst x'; subst y'
  refine ⟨rfl, rfl, rfl, ?_⟩
  have h2 : IsUnit (2 : R) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ R (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  exact mul_left_cancel₀ (h2.mul h.2.2.2.1).ne_zero
    (h.2.2.2.2.2.1.trans h'.2.2.2.2.2.1.symm)

lemma frame_unit_smul {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (s : Γ(F,U)) (hs : IsFrame F U s) (a : Γ(X,U)) (ha : IsUnit a) :
    IsFrame F U (a • s) := by
  intro V hV
  have hu := ha.map (X.presheaf.map (homOfLE hV).op).hom
  obtain ⟨v,hv⟩ := hu
  have hb : Function.Bijective (fun b : Γ(X,V) => b * (v : Γ(X,V))) := by
    constructor
    · intro b c h
      have hh := congrArg (fun z : Γ(X,V) => z * ↑(v⁻¹)) h
      simpa only [mul_assoc, Units.mul_inv, mul_one] using hh
    · intro b
      exact ⟨b * ↑(v⁻¹), by simp only [mul_assoc, Units.inv_mul, mul_one]⟩
  have hcomp := (hs V hV).comp hb
  simpa only [Function.comp_def, ← smul_smul, hv,
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.res_smul] using hcomp

section CoordinateComparison
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction

/-- An actual pointed projective isomorphism over an Artinian local base
supplies the coordinate change and its chart map, with the same scheme map. -/
lemma pointed_iso_chart {T : Type u} [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (W V : WeierstrassCurve T) [W.IsElliptic] [V.IsElliptic]
    (f : Curve T V ≅ Curve T W)
    (hf : f.hom ≫ structureMap T W = structureMap T V)
    (ho : origin T V ≫ f.hom = origin T W) :
    ∃ (C : WeierstrassCurve.VariableChange T) (χ : ChartRing T W →+* ChartRing T V),
      C • W = V ∧
      chartInclusion T V ≫ f.hom = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion T W ∧
      (∀ a, χ (chartScalar T W a) = chartScalar T V a) ∧
      χ (xOverZ W.toProjective) =
        chartScalar T V ((C.u : T)^2) * xOverZ V.toProjective + chartScalar T V C.r ∧
      χ (yOverZ W.toProjective) =
        chartScalar T V ((C.u : T)^3) * yOverZ V.toProjective +
        chartScalar T V ((C.u : T)^2*C.s) * xOverZ V.toProjective + chartScalar T V C.t := by
  have hfi : f.inv ≫ structureMap T V = structureMap T W := by
    rw [← hf, Iso.inv_hom_id_assoc]
  have hoi : origin T W ≫ f.inv = origin T V := by
    rw [← ho, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨C,hC,φ,hφ,hvc,hmap⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange.solution
      T W V W.isUnit_Δ V.isUnit_Δ f.symm hfi hoi
  subst V
  simp only [eqToHom_refl, Category.id_comp] at hmap
  obtain ⟨χ,hχ,hχc,hχx,hχy⟩ :=
    exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
      W.toProjective C φ hφ hvc
  rw [hmap] at hχ
  exact ⟨C,χ,rfl,hχ,by simpa only [chartScalar_apply] using hχc,
    by simpa only [chartScalar_apply] using hχx,
    by simpa only [chartScalar_apply] using hχy⟩

/-- Evaluation of chart functions follows the actual square of section maps. -/
lemma chart_evaluation_square {A B : Type u} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B)
    (ι : A →+* B) (b : Curve B V ⟶ Curve A W)
    (χ : ChartRing A W →+* ChartRing B V)
    (hχ : chartInclusion B V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W)
    (P : Base A ⟶ Curve A W) (Q : Base B ⟶ Curve B V)
    (hPQ : Q ≫ b = baseMap A B ι ≫ P)
    (φ : ChartRing A W →+* A) (ψ : ChartRing B V →+* B)
    (hP : P = Spec.map (CommRingCat.ofHom φ) ≫ chartInclusion A W)
    (hQ : Q = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion B V) :
    ψ.comp χ = ι.comp φ := by
  change (CommRingCat.ofHom (ψ.comp χ)).hom = (CommRingCat.ofHom (ι.comp φ)).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  let : Mono (chartInclusion A W) := inferInstanceAs (Mono (zChartι W.toProjective))
  apply (cancel_mono (chartInclusion A W)).mp
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hχ,
    ← Category.assoc, ← hQ, hPQ, hP, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

lemma chart_scalar_natural {A B : Type u} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B) (ι : A →+* B)
    (b : Curve B V ⟶ Curve A W)
    (hb : b ≫ structureMap A W = structureMap B V ≫ baseMap A B ι)
    (χ : ChartRing A W →+* ChartRing B V)
    (hχ : chartInclusion B V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W)
    (a : A) : χ (chartScalar A W a) = chartScalar B V (ι a) := by
  have hA : Spec.map (CommRingCat.ofHom (chartScalar A W)) =
      chartInclusion A W ≫ structureMap A W := Spec.map_preimage _
  have hB : Spec.map (CommRingCat.ofHom (chartScalar B V)) =
      chartInclusion B V ≫ structureMap B V := Spec.map_preimage _
  have h : CommRingCat.ofHom (chartScalar A W) ≫ CommRingCat.ofHom χ =
      CommRingCat.ofHom ι ≫ CommRingCat.ofHom (chartScalar B V) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hA, hB, ← Category.assoc, ← hχ,
      Category.assoc, hb, Category.assoc]
    rfl
  exact CategoryTheory.congr_fun h a

/-- A comparison to a field, even through a noninjective coefficient map,
induces a variable-change formula on its genuine affine chart. -/
lemma cartesian_field_chart {A F : Type u} [CommRing A] [Field F]
    (W : WeierstrassCurve A) [W.IsElliptic] (V : WeierstrassCurve F) [V.IsElliptic]
    (ι : A →+* F) (b : Curve F V ⟶ Curve A W)
    (hb : IsPullback b (structureMap F V) (structureMap A W) (baseMap A F ι))
    (ho : origin F V ≫ b = baseMap A F ι ≫ origin A W) :
    ∃ (C : WeierstrassCurve.VariableChange F) (χ : ChartRing A W →+* ChartRing F V),
      C • W.map ι = V ∧
      chartInclusion F V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W ∧
      (∀ a, χ (chartScalar A W a) = chartScalar F V (ι a)) ∧
      χ (xOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^2) * xOverZ V.toProjective + chartScalar F V C.r ∧
      χ (yOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^3) * yOverZ V.toProjective +
        chartScalar F V ((C.u : F)^2*C.s) * xOverZ V.toProjective + chartScalar F V C.t := by
  obtain ⟨φ,hφ,hcoef⟩ := exists_isCoefficientHom W.toProjective ι
  let c := Proj.map φ hφ
  have hc := isPullback_projMap_of_isCoefficientHom W.toProjective ι φ hφ hcoef
  obtain ⟨f,hf,hfc⟩ := OrderedLegendreParameterRigidity.cartesian_iso
    (structureMap A W) (structureMap A W) (structureMap F V) (structureMap F (W.map ι))
    (baseMap A F ι) b c hb hc (Iso.refl _) (by simp)
  simp only [Iso.refl_hom, Category.comp_id] at hfc
  have hfo : origin F V ≫ f.hom = origin F (W.map ι) := by
    apply hc.hom_ext
    · rw [Category.assoc, hfc, ho]
      exact (OrderedLegendreParameterRigidity.coefficient_origin W ι φ hφ hcoef).symm
    · change (origin F V ≫ f.hom) ≫ structureMap F (W.map ι) =
        origin F (W.map ι) ≫ structureMap F (W.map ι)
      rw [Category.assoc, hf]
      exact (kwZeroSect F V).property.trans (kwZeroSect F (W.map ι)).property.symm
  obtain ⟨C,ψ,hC,hψ,hψc,hψx,hψy⟩ := pointed_iso_chart (W.map ι) V f hf hfo
  obtain ⟨a,ha,hax,hay⟩ := OrderedLegendreParameterRigidity.coefficient_chart W ι φ hφ hcoef
  let χ := ψ.comp a
  have hχ : chartInclusion F V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W := by
    rw [← hfc, ← Category.assoc, hψ, Category.assoc, ha,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨C,χ,hC,hχ,chart_scalar_natural W V ι b hb.w χ hχ,?_,?_⟩
  · simpa only [χ,RingHom.comp_apply,hax] using hψx
  · simpa only [χ,RingHom.comp_apply,hay] using hψy

/-- Coordinate identities at a marked section are consequences of the same
scheme square, without an independent coordinate-evaluation assumption. -/
lemma coordinate_values_natural {A B : Type u} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B) (ι : A →+* B)
    (b : Curve B V ⟶ Curve A W)
    (χ : ChartRing A W →+* ChartRing B V)
    (hχ : chartInclusion B V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W)
    (P : Base A ⟶ Curve A W) (Q : Base B ⟶ Curve B V)
    (hPQ : Q ≫ b = baseMap A B ι ≫ P)
    (x y : A) (xs ys : B)
    (hP : HasCoordinates A W P x y) (hQ : HasCoordinates B V Q xs ys)
    (u r s t : B)
    (hx : χ (xOverZ W.toProjective) = chartScalar B V (u^2) * xOverZ V.toProjective + chartScalar B V r)
    (hy : χ (yOverZ W.toProjective) = chartScalar B V (u^3) * yOverZ V.toProjective +
      chartScalar B V (u^2*s) * xOverZ V.toProjective + chartScalar B V t) :
    ι x = u^2*xs+r ∧ ι y = u^3*ys+u^2*s*xs+t := by
  obtain ⟨hPo,φ,hφ,hφx,hφy⟩ := hP
  obtain ⟨hQo,ψ,hψ,hψx,hψy⟩ := hQ
  have he := chart_evaluation_square W V ι b χ hχ P Q hPQ φ ψ hφ hψ
  have hscalar (a : B) : ψ (chartScalar B V a) = a := by
    have hh := OrderedLegendreParameterRigidity.evaluation_scalar V ψ (hψ ▸ hQo) a
    simpa only [chartScalar_apply, OrderedLegendreParameterRigidity.scalar,
      ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.VariableChange.WMLocal.cZ,
      RingHom.comp_apply] using hh
  have hxe := RingHom.congr_fun he (xOverZ W.toProjective)
  have hye := RingHom.congr_fun he (yOverZ W.toProjective)
  simp only [RingHom.comp_apply,hx,hy,map_add,map_mul,hscalar,hψx,hψy,hφx,hφy] at hxe hye
  exact ⟨hxe.symm,hye.symm⟩

/-- Completing the square removes both shear coefficients of a genuine
Weierstrass change of variables. -/
lemma completed_y_variable {T : Type u} [CommRing T] [Algebra ℚ T]
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (x y : T) :
    completedY T W ((C.u : T)^2*x+C.r)
      ((C.u : T)^3*y+(C.u : T)^2*C.s*x+C.t) =
      (C.u : T)^3 * completedY T (C • W) x y := by
  have hhalf := TwoTorsionSplitCubicR0177.half_identity (R := T)
  have hinv : (C.u : T) * (↑(C.u⁻¹) : T) = 1 := Units.mul_inv C.u
  simp only [completedY,WeierstrassCurve.variableChange_a₁,WeierstrassCurve.variableChange_a₃]
  linear_combination
    -(C.u : T)^2*C.s*x*hhalf - C.t*hhalf -
    algebraMap ℚ T (1/2) *
      ((C.u : T)^2*(W.a₁+2*C.s)*x +
        ((C.u : T)^2*(↑(C.u⁻¹) : T)^2 + (C.u : T)*(↑(C.u⁻¹) : T) + 1)*
          (W.a₃+C.r*W.a₁+2*C.t)) * hinv

lemma completed_a2_variable {T : Type u} [CommRing T] [Algebra ℚ T]
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) :
    W.a₂ + algebraMap ℚ T (1/4)*W.a₁^2 + 3*C.r =
      (C.u : T)^2 * ((C • W).a₂ + algebraMap ℚ T (1/4)*(C • W).a₁^2) := by
  have hquarter : 4 * algebraMap ℚ T (1/4) = 1 := by
    have h := congrArg (algebraMap ℚ T) (show (4 : ℚ)*(1/4)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using h
  have hinv : (C.u : T) * (↑(C.u⁻¹) : T) = 1 := Units.mul_inv C.u
  simp only [WeierstrassCurve.variableChange_a₁,WeierstrassCurve.variableChange_a₂]
  linear_combination
    -(C.s*W.a₁+C.s^2)*hquarter -
    ((C.u : T)*(↑(C.u⁻¹) : T)+1)*
      (W.a₂-C.s*W.a₁+3*C.r-C.s^2+algebraMap ℚ T (1/4)*(W.a₁+2*C.s)^2)*hinv

lemma rational_map {A B : Type u} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (ι : A →+* B) (q : ℚ) : ι (algebraMap ℚ A q) = algebraMap ℚ B q := by
  exact RingHom.congr_fun (show ι.comp (algebraMap ℚ A) = algebraMap ℚ B from Subsingleton.elim _ _) q

lemma completed_y_map {A B : Type u} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (W : WeierstrassCurve A) (ι : A →+* B) (x y : A) :
    ι (completedY A W x y) = completedY B (W.map ι) (ι x) (ι y) := by
  simp only [completedY,map_add,map_mul,rational_map,WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₃]

lemma chart_preimage {A B : Type u} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B)
    (b : Curve B V ⟶ Curve A W) (χ : ChartRing A W →+* ChartRing B V)
    (hχ : chartInclusion B V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W) :
    RelativeNormalizedDifferential.zOpen B V ≤ b ⁻¹ᵁ RelativeNormalizedDifferential.zOpen A W := by
  intro z hz
  change b z ∈ RelativeNormalizedDifferential.zOpen A W
  rw [RelativeNormalizedDifferential.zOpen, Scheme.Hom.image_top_eq_opensRange] at hz ⊢
  obtain ⟨t,rfl⟩ := Scheme.Hom.mem_opensRange.mp hz
  change (chartInclusion B V ≫ b) t ∈ (chartInclusion A W).opensRange
  rw [hχ]
  exact Scheme.Hom.mem_opensRange.mpr ⟨(Spec.map (CommRingCat.ofHom χ)) t,rfl⟩

lemma chart_section_natural {A B : Type u} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B)
    (b : Curve B V ⟶ Curve A W) (χ : ChartRing A W →+* ChartRing B V)
    (hχ : chartInclusion B V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W)
    (a : ChartRing A W) :
    b.appLE (RelativeNormalizedDifferential.zOpen A W) (RelativeNormalizedDifferential.zOpen B V)
      (chart_preimage W V b χ hχ) (RelativeNormalizedDifferential.zSection A W a) =
        RelativeNormalizedDifferential.zSection B V (χ a) := by
  let j := chartInclusion A W
  let k := chartInclusion B V
  have hj : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤) := by rw [Scheme.Hom.preimage_image_eq]
  have hk : ⊤ ≤ k ⁻¹ᵁ (k ''ᵁ ⊤) := by rw [Scheme.Hom.preimage_image_eq]
  have h := ArithmeticThetaRelativeKatoNaturalityR0170.TorsionValueNaturality.evaluation_square
    χ b j k hχ (j ''ᵁ ⊤) (k ''ᵁ ⊤) (chart_preimage W V b χ hχ) hj hk
    (RelativeNormalizedDifferential.zSection A W a)
  rw [RelativeNormalizedDifferential.chart_app_section] at h
  have ha : (Scheme.ΓSpecIso (CommRingCat.of (ChartRing A W))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing A W))).inv a) = a :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (ChartRing A W))).inv_hom_id a
  rw [ha] at h
  apply (ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.chartRingEquiv k).injective
  rw [RingEquiv.apply_symm_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of (ChartRing B V))).hom
    ((k.appIso ⊤).hom _) = χ a
  rw [Scheme.Hom.appIso_hom']
  exact h

section CurveScalars
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

def curveScalar {T : Type u} [CommRing T] (V : WeierstrassCurve T) (a : T) : Γ(Curve T V,⊤) :=
  (structureMap T V).constToPresheaf.app (Opposite.op ⊤) a

lemma curve_scalar_restrict {T : Type u} [CommRing T] (V : WeierstrassCurve T)
    (U : (Curve T V).Opens) (a : T) :
    (Curve T V).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (curveScalar V a) =
      (structureMap T V).constToPresheaf.app (Opposite.op U) a := by
  have h := CategoryTheory.congr_fun
    ((structureMap T V).constToPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) a
  exact h.symm

lemma zsection_scalar {T : Type u} [CommRing T] (V : WeierstrassCurve T) (a : T) :
    RelativeNormalizedDifferential.zSection T V (chartScalar T V a) =
      (structureMap T V).constToPresheaf.app (Opposite.op (RelativeNormalizedDifferential.zOpen T V)) a := by
  letI : Algebra T (ChartRing T V) := (chartScalar T V).toAlgebra
  letI := (structureMap T V).sectionsAlgebra (RelativeNormalizedDifferential.zOpen T V)
  apply (chartRingEquiv (chartInclusion T V)).injective
  rw [RingEquiv.apply_symm_apply]
  exact (chartRingEquiv_algebraMap (structureMap T V) (chartInclusion T V)
    (Spec.map_preimage _).symm a).symm

lemma relativeD_constant {T : Type u} [CommRing T] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of T)) (U : X.Opens) (a : T) :
    relativeD f U (f.constToPresheaf.app (Opposite.op U) a) = 0 := by
  letI := f.sectionsAlgebra U
  change f.kaehlerToSectionsₗ U (KaehlerDifferential.D T Γ(X,U) (algebraMap T Γ(X,U) a)) = 0
  rw [Derivation.map_algebraMap, map_zero]

lemma relativeD_zsection_scalar {T : Type u} [CommRing T] (V : WeierstrassCurve T) (a : T) :
    relativeD (structureMap T V) (RelativeNormalizedDifferential.zOpen T V)
      (RelativeNormalizedDifferential.zSection T V (chartScalar T V a)) = 0 := by
  rw [zsection_scalar, relativeD_constant]

lemma origin_curve_scalar {T : Type u} [CommRing T] (V : WeierstrassCurve T) (a : T) :
    (origin T V).app ⊤ (curveScalar V a) = ArithmeticThetaOpenHodgeR0180.scalar T a := by
  change (origin T V).appTop ((structureMap T V).appTop (ArithmeticThetaOpenHodgeR0180.scalar T a)) = _
  have h : origin T V ≫ structureMap T V = 𝟙 (Base T) := (kwZeroSect T V).property
  change ((structureMap T V).appTop ≫ (origin T V).appTop) _ = _
  rw [← Scheme.Hom.comp_appTop, h]
  simp

end CurveScalars

lemma chart_ordinate_weight {A B : Type u} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B) (ι : A →+* B)
    (C : WeierstrassCurve.VariableChange B) (hC : C • W.map ι = V)
    (χ : ChartRing A W →+* ChartRing B V)
    (hc : ∀ a, χ (chartScalar A W a) = chartScalar B V (ι a))
    (hx : χ (xOverZ W.toProjective) = chartScalar B V ((C.u : B)^2)*xOverZ V.toProjective + chartScalar B V C.r)
    (hy : χ (yOverZ W.toProjective) = chartScalar B V ((C.u : B)^3)*yOverZ V.toProjective +
      chartScalar B V ((C.u : B)^2*C.s)*xOverZ V.toProjective + chartScalar B V C.t) :
    χ (RelativeNormalizedDifferential.zP A W) =
      chartScalar B V ((C.u : B)^3)*RelativeNormalizedDifferential.zP B V := by
  have ha1 : (C.u : B)*V.a₁ = ι W.a₁+2*C.s := by
    rw [← hC,WeierstrassCurve.variableChange_a₁,← mul_assoc,Units.mul_inv,one_mul]
    rfl
  have ha3 : (C.u : B)^3*V.a₃ = ι W.a₃+C.r*ι W.a₁+2*C.t := by
    rw [← hC,WeierstrassCurve.variableChange_a₃,← mul_assoc,← mul_pow,Units.mul_inv,one_pow,one_mul]
    rfl
  have h1 := congrArg (chartScalar B V) ha1
  have h3 := congrArg (chartScalar B V) ha3
  simp only [map_mul,map_add,map_pow,map_ofNat] at h1 h3
  simp only [RelativeNormalizedDifferential.zP,map_add,map_mul,map_ofNat,hc,hx,hy,map_pow]
  linear_combination -(chartScalar B V (C.u : B))^2*xOverZ V.toProjective*h1 - h3

end CoordinateComparison





variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))

/-- Normalization on the chart yields the actual differential equation on the
corresponding open of the projective curve. -/
lemma normalized_on_open (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W)
      (RelativeNormalizedDifferential.zOpen R W)
      (RelativeNormalizedDifferential.zSection R W (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective)) =
    RelativeNormalizedDifferential.zSection R W (RelativeNormalizedDifferential.zP R W) •
      res (structureMap R W).kaehler le_top (differentialSection R W δ) := by
  obtain ⟨ε,hεx,hεy⟩ := RelativeNormalizedDifferential.global_frame_on_open R W
  have he := RelativeNormalizedDifferential.normalized_of_open R W ε hεx
  have hEq := RelativeNormalizedDifferential.normalized_frames_equal R W ε δ he hδ
  subst δ
  rw [hεx]
  congr 1
  exact (ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.frame_section_restrict
    (structureMap R W) ε ⊤ (RelativeNormalizedDifferential.zOpen R W) le_top).symm

lemma labels_sum {e : Fin 3 → R} {x y g : R} (h : RootData R W G L M e x y g) :
    W.a₂ + algebraMap ℚ R (1/4)*W.a₁^2 = -(e 0+e 1+e 2) := by
  have hne (i j : Fin 3) (hij : i ≠ j) : e i ≠ e j :=
    sub_ne_zero.mp (h.2.1.1 i j hij).ne_zero
  exact (TwoTorsionSplitCubicR0177.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4)*W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2)*W.a₁*W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4)*W.a₃^2)
    (e 0) (e 1) (e 2) (hne 0 1 (by decide)) (hne 1 2 (by decide)) (hne 0 2 (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (h.1 0))
    (TwoTorsionSplitCubicR0177.root_equation (h.1 1))
    (TwoTorsionSplitCubicR0177.root_equation (h.1 2))).1

lemma realizes_unique {a a' : Γ(Hodge R W,⊤)}
    (ha : RealizesAlpha R W G L M a) (ha' : RealizesAlpha R W G L M a') : a = a' := by
  obtain ⟨e,x,y,g,δ,hr,hδ,rfl⟩ := ha
  obtain ⟨e',x',y',g',δ',hr',hδ',rfl⟩ := ha'
  obtain ⟨rfl,rfl,rfl,rfl⟩ := root_data_unique W G L M hr hr'
  rw [RelativeNormalizedDifferential.normalized_frames_equal R W δ δ' hδ hδ']

lemma realizes_frame {a : Γ(Hodge R W,⊤)}
    (ha : RealizesAlpha R W G L M a) : IsFrame (Hodge R W) ⊤ a := by
  obtain ⟨e,x,y,g,δ,hr,hδ,rfl⟩ := ha
  apply frame_unit_smul _ _ _ (RelativeNormalizedDifferential.hodge_generator_frame R W δ)
  have h2 : IsUnit (2 : R) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ R (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  exact (h2.mul hr.2.2.2.2.1).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Existence and uniqueness consume both accepted relative constructions. -/
lemma exists_unique_alpha (hG : IsOriginLaw R W G) (hL : 0 < L) (h4 : 4 ∣ L) :
    ∃! a : Γ(Hodge R W,⊤), RealizesAlpha R W G L M a ∧ IsFrame (Hodge R W) ⊤ a := by
  obtain ⟨e,x,y,g,hr⟩ := relative_four_torsion_root R W G hG L hL h4 M
  obtain ⟨δ,⟨hδ,_⟩,_⟩ := relative_normalized_differential R W
  let a := ArithmeticThetaOpenHodgeR0180.scalar R (2*g) • hodgeGenerator R W δ
  have ha : RealizesAlpha R W G L M a := ⟨e,x,y,g,δ,hr,hδ,rfl⟩
  exact ⟨a,⟨ha,realizes_frame R W G L M ha⟩,
    fun a' ha' => realizes_unique R W G L M ha'.1 ha⟩

section NaturalityAlgebra

/-- Polynomial covariance needs no injectivity of the coefficient map. -/
lemma numerator_covariance {A B : Type u} [CommRing A] [CommRing B]
    (ι : A →+* B) (e : Fin 3 → A) (es : Fin 3 → B) (x : A) (xs u r : B)
    (he : ∀ i, ι (e i) = u^2 * es i + r) (hx : ι x = u^2 * xs + r) :
    ι ((x-e 0)^2-(e 0-e 1)*(e 0-e 2)) =
      u^4 * ((xs-es 0)^2-(es 0-es 1)*(es 0-es 2)) := by
  simp only [map_sub, map_pow, map_mul, he, hx]
  ring

/-- The signed root, not just its square, has weight one under an actual
coordinate formula. The denominator remains cancellable after specialization. -/
lemma root_coefficient_covariance {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain B] [Algebra ℚ B] (ι : A →+* B)
    (e : Fin 3 → A) (es : Fin 3 → B) (x Y g : A) (xs Ys gs : B) (u : Bˣ) (r : B)
    (he : ∀ i, ι (e i) = (u : B)^2 * es i + r)
    (hx : ι x = (u : B)^2 * xs + r) (hY : ι Y = (u : B)^3 * Ys)
    (hYs : IsUnit Ys)
    (hg : 2*Y*g = (x-e 0)^2-(e 0-e 1)*(e 0-e 2))
    (hgs : 2*Ys*gs = (xs-es 0)^2-(es 0-es 1)*(es 0-es 2)) :
    ι g = (u : B)*gs := by
  have h2 : IsUnit (2 : B) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ B (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  apply mul_left_cancel₀ (h2.mul ((u.isUnit.pow 3).mul hYs)).ne_zero
  have h := congrArg ι hg
  rw [map_mul, map_mul, map_ofNat, hY, numerator_covariance ι e es x xs (u : B) r he hx] at h
  linear_combination h - (u : B)^4 * hgs

end NaturalityAlgebra

section ActualPullback
open ArithmeticThetaPullback ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
variable (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S)
  (Gs : Law S Ws) (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b)

lemma hodge_comparison_eq : hodgeComparison R W G S Ws Gs ι b hb =
    hodgeIso R W G S Ws Gs ι b hb := by
  unfold hodgeComparison hodgeIso
  rfl

/-- The curve differential pullback is the universal differential of the
specified Cartesian map and specified coefficient homomorphism. -/
def pullDifferential (s : Γ((structureMap R W).kaehler,⊤)) : Γ((structureMap S Ws).kaehler,⊤) := by
  letI : Algebra R S := ι.toAlgebra
  exact (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app ⊤
    (pullbackGlobalSection b (structureMap R W).kaehler s)

lemma pull_hodge_generator (δ : CurveFrame R W) :
    pullAlpha R W G S Ws Gs ι b hb (hodgeGenerator R W δ) =
      pullbackGlobalSection (origin S Ws) (structureMap S Ws).kaehler
        (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    (relative_curve_geometry R W).2.2.2.2.2.1
  change ((Scheme.Modules.pullback (origin S Ws)).map
    (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w)).app ⊤
    ((squarePullbackIso (baseMap R S ι) (origin R W) (origin S Ws) b hb.2.1.symm
      (structureMap R W).kaehler).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (baseMap R S ι)
        (Scheme.Modules.pullbackLocalSection (origin R W) (differentialSection R W δ)))) = _
  have hsq := squarePullbackIso_section (baseMap R S ι) (origin R W) (origin S Ws) b
    hb.2.1.symm (structureMap R W).kaehler ⊤ (differentialSection R W δ) ⊤ le_top le_top
  simp only [res_refl] at hsq
  erw [hsq]
  exact (Scheme.Modules.pullbackLocalSection_app (origin S Ws)
    (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w)
    (Scheme.Modules.pullbackLocalSection b (differentialSection R W δ))).symm

lemma pull_differential_equation
    (U : (Curve R W).Opens) (x p : Γ(Curve R W,U))
    (s : Γ((structureMap R W).kaehler,⊤))
    (hn : ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U x =
      p • res (structureMap R W).kaehler le_top s) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S Ws) (b ⁻¹ᵁ U) (b.app U x) =
      b.app U p • res (structureMap S Ws).kaehler le_top (pullDifferential R W G S Ws Gs ι b hb s) := by
  letI : Algebra R S := ι.toAlgebra
  have hh := congrArg (fun t =>
    (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app (b ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection b t)) hn
  rw [differentialMap_D, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul] at hh
  rw [hh]
  congr 1
  change (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app (b ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection b (res (structureMap R W).kaehler le_top s)) =
    res (structureMap S Ws).kaehler le_top
      ((differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app ⊤
        (Scheme.Modules.pullbackLocalSection b s))
  rw [hom_res]
  congr 1
  exact (Scheme.Modules.map_homOfLE_pullbackLocalSection b (show U ≤ ⊤ from le_top) s).symm

lemma pull_differential_on_chart
    (χ : ChartRing R W →+* ChartRing S Ws)
    (hχ : chartInclusion S Ws ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S Ws)
      (RelativeNormalizedDifferential.zOpen S Ws)
      (RelativeNormalizedDifferential.zSection S Ws (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective))) =
    RelativeNormalizedDifferential.zSection S Ws (χ (RelativeNormalizedDifferential.zP R W)) •
      res (structureMap S Ws).kaehler le_top
        (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) := by
  have h := pull_differential_equation R W G S Ws Gs ι b hb _ _ _ _ (normalized_on_open R W δ hδ)
  have hr := congrArg (res (structureMap S Ws).kaehler (chart_preimage W Ws b χ hχ)) h
  rw [relativeD_res,res_smul,res_res] at hr
  change ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S Ws)
      (RelativeNormalizedDifferential.zOpen S Ws)
      (b.appLE _ _ (chart_preimage W Ws b χ hχ) _) =
    b.appLE _ _ (chart_preimage W Ws b χ hχ) _ • res (structureMap S Ws).kaehler le_top _ at hr
  rw [chart_section_natural W Ws b χ hχ,chart_section_natural W Ws b χ hχ] at hr
  exact hr

lemma differential_weight [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] [Ws.IsElliptic]
    (C : WeierstrassCurve.VariableChange S) (hC : C • W.map ι = Ws)
    (χ : ChartRing R W →+* ChartRing S Ws)
    (hχ : chartInclusion S Ws ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (hc : ∀ a, χ (chartScalar R W a) = chartScalar S Ws (ι a))
    (hx : χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^2)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.r)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^3)*WeierstrassCurve.DrinfeldGlobal.yOverZ Ws.toProjective +
      chartScalar S Ws ((C.u : S)^2*C.s)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.t)
    (δ : CurveFrame R W) (δs : CurveFrame S Ws)
    (hδ : NormalizedFrame R W δ) (hδs : NormalizedFrame S Ws δs) :
    pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ) =
      curveScalar Ws (↑(C.u⁻¹) : S) • differentialSection S Ws δs := by
  letI := (relative_curve_geometry S Ws).1
  letI := RelativeNormalizedDifferential.zOpen_nonempty S Ws
  let U := RelativeNormalizedDifferential.zOpen S Ws
  let z := RelativeNormalizedDifferential.zSection S Ws
  let p := z (RelativeNormalizedDifferential.zP S Ws)
  let c := z (chartScalar S Ws (C.u : S))
  let ci := z (chartScalar S Ws (↑(C.u⁻¹) : S))
  have hunit : IsUnit c := (C.u.isUnit.map (chartScalar S Ws)).map z.toRingHom
  have hp : p ≠ 0 := by
    intro hp
    apply RelativeNormalizedDifferential.zP_ne_zero S Ws
    apply z.injective
    simpa only [map_zero] using hp
  have hinv : c*ci = 1 := by
    dsimp [c,ci]
    rw [← map_mul,← map_mul,Units.mul_inv,map_one,map_one]
  have h := pull_differential_on_chart R W G S Ws Gs ι b hb χ hχ δ hδ
  rw [hx,map_add,map_mul,
    ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.relativeD_add,
    ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.relativeD_mul,
    relativeD_zsection_scalar,relativeD_zsection_scalar,smul_zero,add_zero,add_zero,
    normalized_on_open S Ws δs hδs,chart_ordinate_weight W Ws ι C hC χ hc hx hy,
    map_mul,map_pow,map_pow,map_pow,map_pow,smul_smul] at h
  change (c^2*p) • res (structureMap S Ws).kaehler le_top (differentialSection S Ws δs) =
    (c^3*p) • res (structureMap S Ws).kaehler le_top
      (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) at h
  apply ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.frame_restrict_injective
    δs ⊤ U le_top
  change res (structureMap S Ws).kaehler (show U ≤ ⊤ from le_top)
      (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) =
    res (structureMap S Ws).kaehler (show U ≤ ⊤ from le_top)
      (curveScalar Ws (↑(C.u⁻¹) : S) • differentialSection S Ws δs)
  rw [res_smul,curve_scalar_restrict,← zsection_scalar]
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app δs.inv U)).1
  have hh := congrArg (Scheme.Modules.Hom.app δs.inv U) h
  rw [Scheme.Modules.Hom.app_smul,Scheme.Modules.Hom.app_smul] at hh
  have he : (c^3*p)*ci = c^2*p := by
    calc
      (c^3*p)*ci = (c^2*p)*(c*ci) := by ring
      _ = c^2*p := by rw [hinv,mul_one]
  rw [Scheme.Modules.Hom.app_smul]
  change _ = ci * _
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hunit.ne_zero) hp)
  change (c^3*p)*_ = (c^3*p)*(ci*_)
  rw [← mul_assoc,he]
  exact hh.symm

lemma hodge_differential_weight [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] [Ws.IsElliptic]
    (C : WeierstrassCurve.VariableChange S) (hC : C • W.map ι = Ws)
    (χ : ChartRing R W →+* ChartRing S Ws)
    (hχ : chartInclusion S Ws ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (hc : ∀ a, χ (chartScalar R W a) = chartScalar S Ws (ι a))
    (hx : χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^2)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.r)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^3)*WeierstrassCurve.DrinfeldGlobal.yOverZ Ws.toProjective +
      chartScalar S Ws ((C.u : S)^2*C.s)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.t)
    (δ : CurveFrame R W) (δs : CurveFrame S Ws)
    (hδ : NormalizedFrame R W δ) (hδs : NormalizedFrame S Ws δs) :
    pullAlpha R W G S Ws Gs ι b hb (hodgeGenerator R W δ) =
      scalar S (↑(C.u⁻¹) : S) • hodgeGenerator S Ws δs := by
  rw [pull_hodge_generator,differential_weight R W G S Ws Gs ι b hb C hC χ hχ hc hx hy δ δs hδ hδs]
  change Scheme.Modules.pullbackLocalSection (origin S Ws)
    (curveScalar Ws (↑(C.u⁻¹) : S) • differentialSection S Ws δs) = _
  rw [Scheme.Modules.pullbackLocalSection_smul,origin_curve_scalar]
  rfl

lemma scalar_pullback (v : R) :
    (baseMap R S ι).app ⊤ (scalar R v) = scalar S (ι v) := by
  change (baseMap R S ι).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv v) =
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv (ι v)
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι)
  exact (CategoryTheory.congr_fun h v).symm

lemma pull_alpha_smul (v : R) (a : Γ(Hodge R W,⊤)) :
    pullAlpha R W G S Ws Gs ι b hb (scalar R v • a) =
      scalar S (ι v) • pullAlpha R W G S Ws Gs ι b hb a := by
  unfold pullAlpha
  change (hodgeComparison R W G S Ws Gs ι b hb).hom.app ⊤
    (Scheme.Modules.pullbackLocalSection (baseMap R S ι) (scalar R v • a)) = _
  rw [Scheme.Modules.pullbackLocalSection_smul, scalar_pullback R S ι,
    Scheme.Modules.Hom.app_smul]
  rfl

include hb in
lemma quarter_point_natural
    (Ms : FullLevel S Ws Gs L (𝟙 (Base S)))
    (hy : Ms.y.val ≫ b = baseMap R S ι ≫ M.y.val) :
    quarterPoint S Ws Gs L Ms ≫ b = baseMap R S ι ≫ quarterPoint R W G L M := by
  unfold quarterPoint
  rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
    ← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
    Category.assoc, hb.2.2, ← Category.assoc, hy, Category.assoc]

/-- The algebraic and differential weights cancel in the genuine Hodge map.
The coordinate and differential formulas are explicit bridge obligations. -/
lemma alpha_formula_natural [Algebra ℚ S]
    (e : Fin 3 → R) (es : Fin 3 → S) (x y g : R) (xs ys gs : S)
    (δ : CurveFrame R W) (δs : CurveFrame S Ws) (u : Sˣ) (r : S)
    (he : ∀ i, ι (e i) = (u : S)^2 * es i + r)
    (hx : ι x = (u : S)^2 * xs + r)
    (hY : ι (completedY R W x y) = (u : S)^3 * completedY S Ws xs ys)
    (hYs : IsUnit (completedY S Ws xs ys))
    (hg : 2*completedY R W x y*g = (x-e 0)^2-(e 0-e 1)*(e 0-e 2))
    (hgs : 2*completedY S Ws xs ys*gs = (xs-es 0)^2-(es 0-es 1)*(es 0-es 2))
    (hδ : pullAlpha R W G S Ws Gs ι b hb (hodgeGenerator R W δ) =
      scalar S (↑(u⁻¹) : S) • hodgeGenerator S Ws δs) :
    pullAlpha R W G S Ws Gs ι b hb (scalar R (2*g) • hodgeGenerator R W δ) =
      scalar S (2*gs) • hodgeGenerator S Ws δs := by
  have hroot := root_coefficient_covariance ι e es x (completedY R W x y) g
    xs (completedY S Ws xs ys) gs u r he hx hY hYs hg hgs
  rw [pull_alpha_smul, hδ, smul_smul]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of S)).inv (ι (2*g)) *
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv (↑(u⁻¹) : S) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (2*gs)
  rw [← map_mul]
  congr 1
  rw [map_mul, map_ofNat, hroot]
  calc
    2 * ((u : S) * gs) * ↑(u⁻¹) = 2 * gs * ((u : S) * ↑(u⁻¹)) := by ring
    _ = 2 * gs := by rw [Units.mul_inv, mul_one]

end ActualPullback

/-- The actual comparison, the two marking squares, and the root constructions
supply the signed weight formula over every field specialization. -/
lemma field_root_weight (F : Type u) [Field F] [Algebra ℚ F]
    (V : WeierstrassCurve F) [V.IsElliptic] (H : Law F V)
    (N : FullLevel F V H L (𝟙 (Base F)))
    (ι : R →+* F) (b : Curve F V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F V H ι b)
    (hMx : N.x.val ≫ b = baseMap R F ι ≫ M.x.val)
    (hMy : N.y.val ≫ b = baseMap R F ι ≫ M.y.val)
    (e : Fin 3 → R) (es : Fin 3 → F) (x y g : R) (xs ys gs : F)
    (hr : RootData R W G L M e x y g) (hs : RootData F V H L N es xs ys gs) :
    ∃ (C : WeierstrassCurve.VariableChange F) (χ : ChartRing R W →+* ChartRing F V),
      C • W.map ι = V ∧
      chartInclusion F V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧
      (∀ a, χ (chartScalar R W a) = chartScalar F V (ι a)) ∧
      χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^2) * WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective + chartScalar F V C.r ∧
      χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^3) * WeierstrassCurve.DrinfeldGlobal.yOverZ V.toProjective +
        chartScalar F V ((C.u : F)^2*C.s) * WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective + chartScalar F V C.t ∧
      ι g = (C.u : F)*gs := by
  obtain ⟨C,χ,hC,hχ,hχc,hχx,hχy⟩ := cartesian_field_chart W V ι b hb.1 hb.2.1
  have hn (P : NeronModelInfra.SchemeHomOver (𝟙 (Base R)) (structureMap R W))
      (Q : NeronModelInfra.SchemeHomOver (𝟙 (Base F)) (structureMap F V))
      (hPQ : Q.val ≫ b = baseMap R F ι ≫ P.val) (n : ℕ) :
      (H.nsmul (𝟙 _) n Q).val ≫ b = baseMap R F ι ≫ (G.nsmul (𝟙 _) n P).val := by
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      ← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      Category.assoc,hb.2.2,← Category.assoc,hPQ,Category.assoc]
  have h0 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.x N.x hMx (L/2))
    _ _ _ _ (hr.1 0) (hs.1 0) (C.u : F) C.r C.s C.t hχx hχy
  have h1 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.y N.y hMy (L/2))
    _ _ _ _ (hr.1 1) (hs.1 1) (C.u : F) C.r C.s C.t hχx hχy
  have hq := coordinate_values_natural W V ι b χ hχ _ _ (hn M.y N.y hMy (L/4))
    _ _ _ _ hr.2.2.1 hs.2.2.1 (C.u : F) C.r C.s C.t hχx hχy
  have ha := congrArg ι (labels_sum R W G L M hr)
  simp only [map_add,map_mul,map_pow,map_neg,rational_map] at ha
  have has := labels_sum F V H L N hs
  have hc2 := completed_a2_variable (W.map ι) C
  rw [hC] at hc2
  change ι W.a₂ + algebraMap ℚ F (1/4)*(ι W.a₁)^2 + 3*C.r =
    (C.u : F)^2*(V.a₂+algebraMap ℚ F (1/4)*V.a₁^2) at hc2
  have he2 : ι (e 2) = (C.u : F)^2*es 2+C.r := by
    linear_combination ha - hc2 - h0.1 - h1.1 - (C.u : F)^2*has
  have he (i : Fin 3) : ι (e i) = (C.u : F)^2*es i+C.r := by
    fin_cases i
    · exact h0.1
    · exact h1.1
    · exact he2
  have hY : ι (completedY R W x y) = (C.u : F)^3*completedY F V xs ys := by
    rw [completed_y_map,hq.1,hq.2,completed_y_variable,hC]
  exact ⟨C,χ,hC,hχ,hχc,hχx,hχy,
    root_coefficient_covariance ι e es x (completedY R W x y) g xs
      (completedY F V xs ys) gs C.u C.r he hq.1 hY hs.2.2.2.1
      hr.2.2.2.2.2.1 hs.2.2.2.2.2.1⟩

lemma alpha_field_naturality (F : Type u) [Field F] [Algebra ℚ F]
    (V : WeierstrassCurve F) [V.IsElliptic] (H : Law F V)
    (N : FullLevel F V H L (𝟙 (Base F)))
    (ι : R →+* F) (b : Curve F V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F V H ι b)
    (hMx : N.x.val ≫ b = baseMap R F ι ≫ M.x.val)
    (hMy : N.y.val ≫ b = baseMap R F ι ≫ M.y.val)
    (a : Γ(Hodge R W,⊤)) (af : Γ(Hodge F V,⊤))
    (ha : RealizesAlpha R W G L M a) (haf : RealizesAlpha F V H L N af) :
    pullAlpha R W G F V H ι b hb a = af := by
  obtain ⟨e,x,y,g,δ,hr,hδ,rfl⟩ := ha
  obtain ⟨es,xs,ys,gs,δs,hs,hδs,rfl⟩ := haf
  obtain ⟨C,χ,hC,hχ,hχc,hχx,hχy,hg⟩ := field_root_weight R W G L M F V H N ι b hb
    hMx hMy e es x y g xs ys gs hr hs
  rw [pull_alpha_smul,hodge_differential_weight R W G F V H ι b hb C hC χ hχ hχc hχx hχy δ δs hδ hδs,
    smul_smul]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of F)).inv (ι (2*g)) *
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv (↑(C.u⁻¹) : F) =
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv (2*gs)
  rw [← map_mul]
  congr 1
  rw [map_mul,map_ofNat,hg]
  calc
    2*((C.u : F)*gs)*↑(C.u⁻¹) = 2*gs*((C.u : F)*↑(C.u⁻¹)) := by ring
    _ = 2*gs := by rw [Units.mul_inv,mul_one]

section GenericComposition
open ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

lemma local_section_comp {X Y Z T : Scheme.{u}} (p : T ⟶ X) (N : T.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(N,p ⁻¹ᵁ U))
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z,U))
    (B : T.Opens) (h₁ : B ≤ p ⁻¹ᵁ ((f ≫ g) ⁻¹ᵁ U))
    (h₂ : B ≤ p ⁻¹ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ U))) :
    res N h₁ (d _ ((f ≫ g).app U a)) =
      res N h₂ (d _ (f.app _ (g.app U a))) := rfl

set_option maxHeartbeats 200000 in
lemma local_comparison_comp {X Y Z A B C : Scheme.{u}}
    (o : A ⟶ X) (p : B ⟶ Y) (q : C ⟶ Z)
    (i : B ⟶ A) (k : C ⟶ B) (l : C ⟶ A) (hl : l = k ≫ i)
    (b : Y ⟶ X) (c : Z ⟶ Y)
    (hb : p ≫ b = i ≫ o) (hc : q ≫ c = k ≫ p) (hd : q ≫ (c ≫ b) = l ≫ o)
    (M : A.Modules) (N : B.Modules) (P : C.Modules)
    (dx : ∀ U : X.Opens, Γ(X,U) → Γ(M,o ⁻¹ᵁ U))
    (dy : ∀ U : Y.Opens, Γ(Y,U) → Γ(N,p ⁻¹ᵁ U))
    (dz : ∀ U : Z.Opens, Γ(Z,U) → Γ(P,q ⁻¹ᵁ U))
    (hf : ∀ t : A, ∃ (U : X.Opens) (a : Γ(X,U)), o t ∈ U ∧ IsFrame M (o ⁻¹ᵁ U) (dx U a))
    (e₁ : (Scheme.Modules.pullback i).obj M ≅ N)
    (e₂ : (Scheme.Modules.pullback k).obj N ≅ P)
    (e₃ : (Scheme.Modules.pullback l).obj M ≅ P)
    (h₁ : ∀ U a V (ha : V ≤ i ⁻¹ᵁ (o ⁻¹ᵁ U)) (hb : V ≤ p ⁻¹ᵁ (b ⁻¹ᵁ U)),
      res N ha (e₁.hom.app _ (Scheme.Modules.pullbackLocalSection i (dx U a))) = res N hb (dy _ (b.app U a)))
    (h₂ : ∀ U a V (ha : V ≤ k ⁻¹ᵁ (p ⁻¹ᵁ U)) (hb : V ≤ q ⁻¹ᵁ (c ⁻¹ᵁ U)),
      res P ha (e₂.hom.app _ (Scheme.Modules.pullbackLocalSection k (dy U a))) = res P hb (dz _ (c.app U a)))
    (h₃ : ∀ U a V (ha : V ≤ l ⁻¹ᵁ (o ⁻¹ᵁ U)) (hb : V ≤ q ⁻¹ᵁ ((c ≫ b) ⁻¹ᵁ U)),
      res P ha (e₃.hom.app _ (Scheme.Modules.pullbackLocalSection l (dx U a))) = res P hb (dz _ ((c ≫ b).app U a))) :
    e₃ = composeComparison i k l hl M N P e₁ e₂ := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  obtain ⟨U,a,hx,hframe⟩ := hf (l x)
  let Q := l ⁻¹ᵁ (o ⁻¹ᵁ U)
  have hQ : Q ≤ k ⁻¹ᵁ (i ⁻¹ᵁ (o ⁻¹ᵁ U)) := by
    intro y hy
    change (k ≫ i) y ∈ o ⁻¹ᵁ U
    rw [← hl]
    exact hy
  have hB : i ⁻¹ᵁ (o ⁻¹ᵁ U) ≤ p ⁻¹ᵁ (b ⁻¹ᵁ U) := by
    intro y hy
    change (p ≫ b) y ∈ U
    rw [hb]
    exact hy
  have hD : Q ≤ q ⁻¹ᵁ ((c ≫ b) ⁻¹ᵁ U) := by
    intro y hy
    change (q ≫ (c ≫ b)) y ∈ U
    rw [hd]
    exact hy
  have hC : Q ≤ q ⁻¹ᵁ (c ⁻¹ᵁ (b ⁻¹ᵁ U)) := hD
  refine ⟨Q,Scheme.Modules.pullbackLocalSection l (dx U a),hx,pullback_frame _ _ _ hframe,?_⟩
  have hleft := h₃ U a Q le_rfl hD
  have hcomp := composeComparison_section i k l hl M N P e₁ e₂ (o ⁻¹ᵁ U) (dx U a) Q le_rfl hQ
  have hinner := h₁ U a (i ⁻¹ᵁ (o ⁻¹ᵁ U)) le_rfl hB
  rw [res_refl] at hinner
  rw [hinner,← InitialSectionNaturality.pullback_res,← hom_res,res_res] at hcomp
  rw [h₂ (b ⁻¹ᵁ U) (b.app U a) Q (fun y hy => hB (hQ hy)) hC] at hcomp
  have he := local_section_comp q P dz c b U a Q hD hC
  rw [he] at hleft
  simpa only [res_refl] using hleft.trans hcomp.symm

lemma global_comparison_comp {X Y Z : Scheme.{u}}
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) (hr : r = q ≫ p)
    (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (g : (Scheme.Modules.pullback r).obj M ≅ P)
    (hg : g = composeComparison p q r hr M N P e f) (a : Γ(M,⊤)) :
    g.hom.app ⊤ (pullbackGlobalSection r M a) =
      f.hom.app ⊤ (pullbackGlobalSection q N (e.hom.app ⊤ (pullbackGlobalSection p M a))) := by
  subst g
  have hh := composeComparison_section p q r hr M N P e f ⊤ a ⊤ le_top le_top
  simpa only [res_refl, Scheme.Modules.pullbackLocalSection, pullbackGlobalSection, Scheme.Hom.preimage_top] using hh

end GenericComposition
section Composition
open ArithmeticThetaPullback ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
variable (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
  (V : WeierstrassCurve S) [V.IsElliptic] (H : Law S V)
  (T : Type u) [CommRing T] [IsDomain T] (Z : WeierstrassCurve T) (J : Law T Z)
  (ι : R →+* S) (κ : S →+* T) (b : Curve S V ⟶ Curve R W) (c : Curve T Z ⟶ Curve S V)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
  (hc : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange S V H T Z J κ c)
  (hd : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G T Z J (κ.comp ι) (c ≫ b))

set_option maxHeartbeats 200000 in
set_option maxHeartbeats 200000 in
lemma hodge_comparison_comp :
    hodgeIso R W G T Z J (κ.comp ι) (c ≫ b) hd =
      composeComparison (baseMap R S ι) (baseMap S T κ) (baseMap R T (κ.comp ι))
        (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom κ))
        (Hodge R W) (Hodge S V) (Hodge T Z)
        (hodgeIso R W G S V H ι b hb) (hodgeIso S V H T Z J κ c hc) := by
  have hf : ∀ t : Base R, ∃ (U : (Curve R W).Opens) (a : Γ(Curve R W,U)),
      origin R W t ∈ U ∧ IsFrame (Hodge R W) (origin R W ⁻¹ᵁ U) (localDifferential R W U a) := by
    letI : SmoothOfRelativeDimension 1 (structureMap R W) := (relative_curve_geometry R W).2.2.2.2.2.1
    intro t
    obtain ⟨U,a,ht,hf⟩ := exists_exact_differential_frame (structureMap R W) (origin R W t)
    exact ⟨U,a,ht,pullback_frame _ _ _ hf⟩
  exact local_comparison_comp (origin R W) (origin S V) (origin T Z)
    (baseMap R S ι) (baseMap S T κ) (baseMap R T (κ.comp ι))
    (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom κ)) b c hb.2.1 hc.2.1 hd.2.1
    (Hodge R W) (Hodge S V) (Hodge T Z)
    (localDifferential R W) (localDifferential S V) (localDifferential T Z) hf
    (hodgeIso R W G S V H ι b hb) (hodgeIso S V H T Z J κ c hc)
    (hodgeIso R W G T Z J (κ.comp ι) (c ≫ b) hd)
    (hodgeIso_D R W G S V H ι b hb) (hodgeIso_D S V H T Z J κ c hc)
    (hodgeIso_D R W G T Z J (κ.comp ι) (c ≫ b) hd)

set_option maxHeartbeats 200000 in
lemma pull_alpha_comp (a : Γ(Hodge R W,⊤)) :
    pullAlpha R W G T Z J (κ.comp ι) (c ≫ b) hd a =
      pullAlpha S V H T Z J κ c hc (pullAlpha R W G S V H ι b hb a) := by
  unfold pullAlpha
  simp only [hodge_comparison_eq]
  exact global_comparison_comp (baseMap R S ι) (baseMap S T κ) (baseMap R T (κ.comp ι))
    (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom κ))
    (Hodge R W) (Hodge S V) (Hodge T Z)
    (hodgeIso R W G S V H ι b hb) (hodgeIso S V H T Z J κ c hc)
    (hodgeIso R W G T Z J (κ.comp ι) (c ≫ b) hd)
    (hodge_comparison_comp R W G S V H T Z J ι κ b c hb hc hd) a

end Composition

section Faithfulness
open ArithmeticThetaPullback ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

lemma pull_alpha_injective
    (S : Type u) [CommRing S] [IsDomain S] (V : WeierstrassCurve S) (H : Law S V)
    (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
    (hi : Function.Injective ι) : Function.Injective (pullAlpha R W G S V H ι b hb) := by
  obtain ⟨δ,⟨_,hf⟩,_⟩ := relative_normalized_differential R W
  let d := hodgeGenerator R W δ
  have hpf : IsFrame (Hodge S V) ⊤ (pullAlpha R W G S V H ι b hb d) :=
    ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      (hodgeComparison R W G S V H ι b hb) _ (pullback_frame _ _ _ hf)
  intro a a' he
  obtain ⟨v,hv⟩ := (hf ⊤ le_rfl).2 a
  obtain ⟨w,hw⟩ := (hf ⊤ le_rfl).2 a'
  simp only [res_refl] at hv hw
  let r : R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom v
  let t : R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom w
  have hr : scalar R r = v := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id v
  have ht : scalar R t = w := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id w
  rw [← hv,← hw,← hr,← ht,pull_alpha_smul,pull_alpha_smul] at he
  have he' : scalar S (ι r) = scalar S (ι t) := (hpf ⊤ le_rfl).1 (by simpa only [res_refl] using he)
  have hrt : r = t := hi ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1 he')
  rw [← hv,← hw,← hr,← ht,hrt]

end Faithfulness

set_option maxHeartbeats 200000 in
lemma alpha_naturality (hG : IsOriginLaw R W G) (hL : 0 < L) (h4 : 4 ∣ L)
    (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
    (V : WeierstrassCurve S) [V.IsElliptic] (H : Law S V) (hH : IsOriginLaw S V H)
    (N : FullLevel S V H L (𝟙 (Base S)))
    (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
    (hMx : N.x.val ≫ b = baseMap R S ι ≫ M.x.val)
    (hMy : N.y.val ≫ b = baseMap R S ι ≫ M.y.val)
    (a : Γ(Hodge R W,⊤)) (as_ : Γ(Hodge S V,⊤))
    (ha : RealizesAlpha R W G L M a) (has : RealizesAlpha S V H L N as_) :
    pullAlpha R W G S V H ι b hb a = as_ := by
  letI := (relative_curve_geometry S V).1
  letI := (relative_curve_geometry S V).2.1
  letI := (relative_curve_geometry S V).2.2.2.1
  letI := (relative_curve_geometry S V).2.2.2.2.1
  obtain ⟨C⟩ := relative_generic_comparison S V H hH
  let K := FractionRing S
  let Z := V.map (algebraMap S K)
  let κ : S →+* K := algebraMap S K
  have hc : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange S V H K Z C.law κ C.map :=
    ⟨C.cartesian,C.origin_eq,C.multiplication_eq⟩
  have hd : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G K Z C.law (κ.comp ι) (C.map ≫ b) := by
    refine ⟨?_,?_,?_⟩
    · rw [CommRingCat.ofHom_comp,Spec.map_comp]
      exact C.cartesian.paste_horiz hb.1
    · rw [← Category.assoc,hc.2.1,Category.assoc,hb.2.1,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
    · intro n
      rw [← Category.assoc,C.multiplication_eq,Category.assoc,hb.2.2,Category.assoc]
  let B : FullLevel S V H L ((𝟙 (Base K)) ≫ baseMap S K κ) :=
    BaseChange.restrict N (baseMap S K κ) (by simp)
  let Nk : FullLevel K Z C.law L (𝟙 (Base K)) := BaseChange.up hc hH C.originLaw B
  have hNx : Nk.x.val ≫ C.map = baseMap S K κ ≫ N.x.val := BaseChange.up_x hc hH C.originLaw B
  have hNy : Nk.y.val ≫ C.map = baseMap S K κ ≫ N.y.val := BaseChange.up_y hc hH C.originLaw B
  have hKx : Nk.x.val ≫ (C.map ≫ b) = baseMap R K (κ.comp ι) ≫ M.x.val := by
    rw [← Category.assoc,hNx,Category.assoc,hMx]
    simp only [baseMap,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  have hKy : Nk.y.val ≫ (C.map ≫ b) = baseMap R K (κ.comp ι) ≫ M.y.val := by
    rw [← Category.assoc,hNy,Category.assoc,hMy]
    simp only [baseMap,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  obtain ⟨ak,hak,_⟩ := exists_unique_alpha K Z C.law L Nk C.originLaw hL h4
  apply pull_alpha_injective S V H K Z C.law κ C.map hc (IsFractionRing.injective S K)
  rw [← pull_alpha_comp R W G S V H K Z C.law ι κ b C.map hb hc hd a,
    alpha_field_naturality R W G L M K Z C.law Nk (κ.comp ι) (C.map ≫ b) hd hKx hKy a ak ha hak.1,
    alpha_field_naturality S V H L N K Z C.law Nk κ C.map hc hNx hNy as_ ak has hak.1]

end RelativeAlphaNaturality

/-- The intrinsic section is a unique frame and is natural under every specified
pointed Cartesian comparison preserving both full marking sections. -/
theorem relative_alpha_naturality :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ), 0 < L → 4 ∣ L → ∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), (∃! a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L M a ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W) ⊤ a) ∧ (∀ (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (Ms : ArithmeticThetaFullLevelCoverR0175.FullLevel S Ws Gs L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b), CategoryTheory.CategoryStruct.comp (Ms.x.val) (b) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (M.x.val) → CategoryTheory.CategoryStruct.comp (Ms.y.val) (b) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (M.y.val) → ∀ (a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤)) (as_ : (ArithmeticThetaRelativeDiscriminantR0171.Hodge S Ws).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L M a → ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha S Ws Gs L Ms as_ → ArithmeticThetaGlobalFourTorsionR0190.pullAlpha R W G S Ws Gs ι b hb a = as_) := by
  intro R _ _ _ _ _ W _ G hG L hL h4 M
  refine ⟨RelativeAlphaNaturality.exists_unique_alpha R W G L M hG hL h4, ?_⟩
  intro S _ _ _ _ _ Ws _ Gs hGs Ms ι b hb hx hy a as_ ha has
  exact RelativeAlphaNaturality.alpha_naturality R W G L M hG hL h4
    S Ws Gs hGs Ms ι b hb hx hy a as_ ha has

end ArithmeticThetaGlobalFourTorsionR0190
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.coordinates_unique
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.root_data_unique
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.frame_unit_smul
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pointed_iso_chart
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.chart_evaluation_square
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.chart_scalar_natural
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.cartesian_field_chart
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.coordinate_values_natural
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.completed_y_variable
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.completed_a2_variable
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.rational_map
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.completed_y_map
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.chart_preimage
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.chart_section_natural
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.curveScalar
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.curve_scalar_restrict
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.zsection_scalar
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.relativeD_constant
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.relativeD_zsection_scalar
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.origin_curve_scalar
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.chart_ordinate_weight
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.normalized_on_open
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.labels_sum
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.realizes_unique
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.realizes_frame
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.exists_unique_alpha
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.numerator_covariance
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.root_coefficient_covariance
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.hodge_comparison_eq
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pullDifferential
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pull_hodge_generator
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pull_differential_equation
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pull_differential_on_chart
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.differential_weight
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.hodge_differential_weight
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.scalar_pullback
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pull_alpha_smul
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.quarter_point_natural
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.alpha_formula_natural
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.field_root_weight
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.alpha_field_naturality
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.local_section_comp
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.local_comparison_comp
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.global_comparison_comp
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.hodge_comparison_comp
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pull_alpha_comp
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.pull_alpha_injective
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.alpha_naturality
#print axioms ArithmeticThetaGlobalFourTorsionR0190.relative_alpha_naturality
