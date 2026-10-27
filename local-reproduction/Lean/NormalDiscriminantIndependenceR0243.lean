import ArbitraryDiscriminantDefinitionsR0243
import Theorems.Thm_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing

/-! Normal-model independence over arbitrary rational coefficient rings.
All comparisons retain their specified scheme maps and canonical differentials. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaArbitraryDiscriminantR0243
namespace NormalDiscriminantIndependence
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

def comparisonTargetEq {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} {V V' : WeierstrassCurve S} {ι : R →+* S}
    (C : Comparison R S W V ι) (h : V = V') : Comparison R S W V' ι := by
  cases h
  exact C

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
def coefficientGradedMap {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map ι).toProjective :=
  (exists_isCoefficientHom W.toProjective ι).choose

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem coefficientGradedMap_irrelevant {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    HomogeneousIdeal.irrelevant (projModelGradingCR (W.map ι).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map
        (coefficientGradedMap W ι) :=
  (exists_isCoefficientHom W.toProjective ι).choose_spec.choose

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem coefficientGradedMap_spec {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    IsCoefficientHom W.toProjective ι (coefficientGradedMap W ι) :=
  (exists_isCoefficientHom W.toProjective ι).choose_spec.choose_spec

/-- The actual coefficient morphism, with its graded coordinate map retained. -/
def coefficientComparison {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    Comparison R S W (W.map ι) ι where
  map := Proj.map (coefficientGradedMap W ι) (coefficientGradedMap_irrelevant W ι)
  cartesian := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
    W.toProjective ι _ _ (coefficientGradedMap_spec W ι)
  pointed := ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.coefficient_origin
    W ι _ _ (coefficientGradedMap_spec W ι)

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem coefficientGradedMap_unique {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map ι).toProjective)
    (hφ : IsCoefficientHom W.toProjective ι φ) : φ = coefficientGradedMap W ι := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : φ.toRingHom.comp (Ideal.Quotient.mk _) =
      (coefficientGradedMap W ι).toRingHom.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact (hφ.1 a).trans ((coefficientGradedMap_spec W ι).1 a).symm
    · intro i
      exact (hφ.2 i).trans ((coefficientGradedMap_spec W ι).2 i).symm
  exact RingHom.congr_fun h p

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem coefficientComparison_map {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map ι).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map ι).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hc : IsCoefficientHom W.toProjective ι φ) :
    (coefficientComparison W ι).map = Proj.map φ hφ := by
  have he := coefficientGradedMap_unique W ι φ hc
  subst φ
  rfl

namespace CoefficientComposition
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem graded_ext {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (φ ψ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR V.toProjective)
    (hc : ∀ a, φ (cls W.toProjective (MvPolynomial.C a)) =
      ψ (cls W.toProjective (MvPolynomial.C a)))
    (hx : ∀ i, φ (cls W.toProjective (MvPolynomial.X i)) =
      ψ (cls W.toProjective (MvPolynomial.X i))) : φ = ψ := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : φ.toRingHom.comp (Ideal.Quotient.mk _) =
      ψ.toRingHom.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · exact hc
    · exact hx
  exact RingHom.congr_fun h p

theorem coefficient_comp_aux {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (W : WeierstrassCurve R) (ι : R →+* S) (ρ : S →+* T)
    (Z : WeierstrassCurve T) (hZ : (W.map ι).map ρ = Z)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR Z.toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR Z.toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hc : ∀ a, φ (cls W.toProjective (MvPolynomial.C a)) =
      cls Z.toProjective (MvPolynomial.C (ρ (ι a))))
    (hx : ∀ i, φ (cls W.toProjective (MvPolynomial.X i)) =
      cls Z.toProjective (MvPolynomial.X i)) :
    (coefficientComparison (W.map ι) ρ).map ≫ (coefficientComparison W ι).map =
      eqToHom (congrArg (Curve T) hZ) ≫ Proj.map φ hφ := by
  subst Z
  rw [eqToHom_refl, Category.id_comp]
  change Proj.map _ _ ≫ Proj.map _ _ = _
  rw [← Proj.map_comp]
  have he : (coefficientGradedMap (W.map ι) ρ).comp (coefficientGradedMap W ι) = φ := by
    apply graded_ext W ((W.map ι).map ρ)
    · intro a
      rw [GradedRingHom.comp_apply, (coefficientGradedMap_spec W ι).1,
        (coefficientGradedMap_spec (W.map ι) ρ).1, hc]
    · intro i
      rw [GradedRingHom.comp_apply, (coefficientGradedMap_spec W ι).2,
        (coefficientGradedMap_spec (W.map ι) ρ).2, hx]
  subst φ
  rfl

theorem coefficient_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (W : WeierstrassCurve R) (ι : R →+* S) (ρ : S →+* T) :
    (coefficientComparison (W.map ι) ρ).map ≫ (coefficientComparison W ι).map =
      eqToHom (congrArg (Curve T) (W.map_map ι ρ)) ≫
        (coefficientComparison W (ρ.comp ι)).map :=
  coefficient_comp_aux W ι ρ _ (W.map_map ι ρ) _ _
    (coefficientGradedMap_spec W (ρ.comp ι)).1
    (coefficientGradedMap_spec W (ρ.comp ι)).2

end CoefficientComposition

#print axioms CoefficientComposition.coefficient_comp

theorem homFamily_transport {A : Type*} (X Y : A → Scheme.{u})
    (f : ∀ a, X a ⟶ Y a) {a b : A} (h : a = b) :
    f b ≫ eqToHom (congrArg Y h).symm =
      eqToHom (congrArg X h).symm ≫ f a := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

theorem comparisonTargetEq_map {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} {V V' : WeierstrassCurve S} {ι : R →+* S}
    (C : Comparison R S W V ι) (h : V = V') :
    (comparisonTargetEq C h).map = eqToHom (congrArg (Curve S) h).symm ≫ C.map := by
  cases h
  exact (Category.id_comp _).symm

theorem coefficientComparison_target_transport
    {R S : Type u} [CommRing R] [CommRing S]
    {W V : WeierstrassCurve R} (h : W = V) (ι : R →+* S) :
    (coefficientComparison V ι).map ≫ eqToHom (congrArg (Curve R) h).symm =
      eqToHom (congrArg (fun E : WeierstrassCurve R => Curve S (E.map ι)) h).symm ≫
        (coefficientComparison W ι).map := by
  exact homFamily_transport (fun E : WeierstrassCurve R => Curve S (E.map ι)) (Curve R)
    (fun E : WeierstrassCurve R => (coefficientComparison E ι).map) h

theorem coefficientComparison_scalar_transport
    {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) {ι ρ : R →+* S} (h : ι = ρ) :
    (coefficientComparison W ι).map =
      eqToHom (congrArg (Curve S) (congrArg W.map h)) ≫
        (coefficientComparison W ρ).map := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

set_option maxHeartbeats 1600000 in
/-- Coefficient composition respects a specified equation identification and
the actual equality of the composite scalar maps. -/
theorem coefficientComparison_transport_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (ι : R →+* S) (ρ : S →+* T) (σ : R →+* T)
    (hV : W.map ι = V) (hσ : ρ.comp ι = σ)
    (hZ : W.map σ = V.map ρ) :
    (coefficientComparison V ρ).map ≫
        (comparisonTargetEq (coefficientComparison W ι) hV).map =
      (comparisonTargetEq (coefficientComparison W σ) hZ).map := by
  rw [comparisonTargetEq_map, comparisonTargetEq_map, ← Category.assoc,
    coefficientComparison_target_transport hV ρ, Category.assoc,
    CoefficientComposition.coefficient_comp,
    coefficientComparison_scalar_transport W hσ]
  simp only [← Category.assoc, eqToHom_trans]

#print axioms coefficientComparison_transport_comp


/-- Every specified comparison factors through its coefficient base change by
an actual pointed isomorphism. This reduction is valid scheme-theoretically
over arbitrary rings, including nonreduced rings. -/
theorem comparison_factor_iso {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} {ι : R →+* S}
    (C : Comparison R S W V ι) :
    ∃ e : Curve S V ≅ Curve S (W.map ι),
      e.hom ≫ (coefficientComparison W ι).map = C.map ∧
      e.hom ≫ structureMap S (W.map ι) = structureMap S V ∧
      origin S V ≫ e.hom = origin S (W.map ι) := by
  let D := coefficientComparison W ι
  let e := C.cartesian.isoIsPullback _ _ D.cartesian
  have he₁ : e.hom ≫ D.map = C.map := C.cartesian.isoIsPullback_hom_fst _ _ D.cartesian
  have he₂ : e.hom ≫ structureMap S (W.map ι) = structureMap S V :=
    C.cartesian.isoIsPullback_hom_snd _ _ D.cartesian
  refine ⟨e, he₁, he₂, ?_⟩
  apply D.cartesian.hom_ext
  · rw [Category.assoc, he₁, C.pointed, D.pointed]
  · rw [Category.assoc, he₂]
    exact (WeierstrassProjModel.kwZeroSect S V).property.trans
      (WeierstrassProjModel.kwZeroSect S (W.map ι)).property.symm

set_option maxHeartbeats 3200000 in
/-- On normal bases, pointedness alone supplies multiplication compatibility.
Rigidity is applied to the actual Cartesian lift into the source base change. -/
theorem comparison_nsmul
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsIntegrallyClosed S] [Algebra ℚ S]
    {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic] {ι : R →+* S}
    (C : Comparison R S W V ι)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (H : Law S V) (hH : IsOriginLaw S V H) (n : ℕ) :
    H.schemeNsmul n ≫ C.map = C.map ≫ G.schemeNsmul n := by
  let q := Spec.map (CommRingCat.ofHom ι)
  let g := ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G
  let h := ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ H
  let k := g.baseChange q
  let f : SchemeHomOver (structureMap S V) (pullback.snd (structureMap R W) q) :=
    ⟨pullback.lift C.map (structureMap S V) C.cartesian.w, pullback.lift_snd _ _ _⟩
  letI := (relative_curve_geometry R W).2.2.2.2.2.1
  letI := (relative_curve_geometry R W).2.2.2.2.2.2
  letI := (relative_curve_geometry S V).2.2.2.2.2.1
  letI := (relative_curve_geometry S V).2.2.2.2.2.2
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsProper (structureMap S V) :=
    WeierstrassProjModel.projModelStrCR_isProper V.toProjective
  have hone {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
      NeronModelInfra.schemeHomOverComp (h.one t) f = k.one t := by
    apply Subtype.ext
    apply pullback.hom_ext
    · change (H.one t).val ≫ f.val ≫ pullback.fst _ _ =
        (pullback.lift (G.one (t ≫ q)).val t _ ≫ pullback.fst _ _)
      simp only [f, pullback.lift_fst, hH.1 t, hG.1 (t ≫ q), Category.assoc]
      rw [C.pointed]
    · change (H.one t).val ≫ f.val ≫ pullback.snd _ _ =
        (pullback.lift (G.one (t ≫ q)).val t _ ≫ pullback.snd _ _)
      rw [f.property, pullback.lift_snd]
      exact (H.one t).property
  have hmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (x y : SchemeHomOver t (structureMap S V)) :
      NeronModelInfra.schemeHomOverComp (h.mul t x y) f =
        k.mul t (NeronModelInfra.schemeHomOverComp x f)
          (NeronModelInfra.schemeHomOverComp y f) := by
    apply Subtype.ext
    exact ArithmeticThetaRelativeCyclicQuotientR0173.PointedRelativeGroupHom.relative_rigidity
      h k f hone t x y
  have hn {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (x : SchemeHomOver t (structureMap S V)) (j : ℕ) :
      NeronModelInfra.schemeHomOverComp (h.nsmul t j x) f =
        k.nsmul t j (NeronModelInfra.schemeHomOverComp x f) := by
    induction j with
    | zero => exact hone t
    | succ j ih =>
      rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ,
        GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, hmul, ih]
  have hh := congrArg (fun z =>
      (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase q z).val)
    (hn (structureMap S V) WeierstrassProjModel.RelativeGroupLaw.idPoint n)
  rw [ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180.baseChange_nsmul]
    at hh
  have hnat := congrArg Subtype.val
    (g.nsmul_natural (structureMap R W) (structureMap S V ≫ q)
      C.map C.cartesian.w n GoodReductionJacobian.RelativeGroupLaw.idPoint)
  have hp : GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase q
      (NeronModelInfra.schemeHomOverComp WeierstrassProjModel.RelativeGroupLaw.idPoint f) =
      GoodReductionJacobian.schemeHomOverComp C.map C.cartesian.w
        GoodReductionJacobian.RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    simp [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase,
      NeronModelInfra.schemeHomOverComp, GoodReductionJacobian.schemeHomOverComp, f]
  rw [hp] at hh
  simp only [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe,
    NeronModelInfra.schemeHomOverComp_coe, Category.assoc, f,
    pullback.lift_fst] at hh
  have he := hh.trans hnat.symm
  simpa only [h, g,
    ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ_nsmul,
    GoodReductionJacobian.schemeHomOverComp,
    WeierstrassProjModel.RelativeGroupLaw.schemeNsmul,
    WeierstrassProjModel.RelativeGroupLaw.idPoint,
    GoodReductionJacobian.RelativeGroupLaw.idPoint]
    using he

/-- The new comparison is literally the accepted differential comparison when
the specified pointed map also commutes with multiplication. -/
theorem comparisonPower_eq {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι)
    (G : Law R W) (H : Law S V)
    (hn : ∀ n, H.schemeNsmul n ≫ C.map = C.map ≫ G.schemeNsmul n) :
    comparisonPower C = hodgePowerIso R W G S V H ι C.map
      ⟨C.cartesian, C.pointed, hn⟩ 24 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The frozen tensor comparison has the required action on actual local
differentials over every target ring, with no reducedness hypothesis. -/
theorem comparisonPower_spec_aux {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι) (n : ℕ) :
    IsPowerBaseChange R W S V ι C.map n
      (tensorComparison (baseMap R S ι) (Hodge R W) (Hodge S V) (comparisonHodge C) n) := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  intro U a Z h₁ h₂
  change res _ h₁ ((tensorComparison _ _ _ _ n).hom.app _
    (Scheme.Modules.pullbackLocalSection _
      (ArithmeticThetaTensorPower.tensorPowerSection _ _ n _
        (localDifferential R W U a)))) = _
  rw [tensorComparison_section]
  change (ArithmeticThetaTensorPower.tensorPower (Base S) (Hodge S V) n).presheaf.map
      (homOfLE h₁).op (ArithmeticThetaTensorPower.tensorPowerSection _ _ n _ _) =
    (ArithmeticThetaTensorPower.tensorPower (Base S) (Hodge S V) n).presheaf.map
      (homOfLE h₂).op (ArithmeticThetaTensorPower.tensorPowerSection _ _ n _ _)
  rw [ArithmeticThetaTensorPower.tensorPowerSection_restrict,
    ArithmeticThetaTensorPower.tensorPowerSection_restrict]
  exact congrArg (ArithmeticThetaTensorPower.tensorPowerSection (Base S) (Hodge S V) n Z)
    (pointedDifferentialIso_D (structureMap R W) (structureMap S V) C.map C.cartesian
      (origin R W) (origin S V) C.pointed U a Z h₁ h₂)

/-- Weight-24 specialization of the general differential-power comparison. -/
theorem comparisonPower_spec {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι) :
    IsPowerBaseChange R W S V ι C.map 24 (comparisonPower C) :=
  comparisonPower_spec_aux C 24

/-- Composition uses the specified geometric maps and scalar maps. -/
def comparisonCompose {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} {Z : WeierstrassCurve T}
    {ι : R →+* S} {ρ : S →+* T}
    (C : Comparison R S W V ι) (D : Comparison S T V Z ρ) :
    Comparison R T W Z (ρ.comp ι) := by
  have hs : Spec.map (CommRingCat.ofHom (ρ.comp ι)) =
      Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom ι) := by
    exact Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom ρ)
  refine ⟨D.map ≫ C.map, ?_, ?_⟩
  · rw [hs]
    exact D.cartesian.paste_horiz C.cartesian
  · rw [← Category.assoc, D.pointed, Category.assoc, C.pointed, hs,
      Category.assoc]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
/-- Canonical differential powers compose over arbitrary rings. -/
theorem comparisonPower_refinement
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic] {Z : WeierstrassCurve T}
    {ι : R →+* S} {ρ : S →+* T} {σ : R →+* T}
    (C : Comparison R S W V ι) (D : Comparison S T V Z ρ)
    (E : Comparison R T W Z σ) (hm : D.map ≫ C.map = E.map)
    (hbase : baseMap R T σ = baseMap S T ρ ≫ baseMap R S ι) (n : ℕ) :
    tensorComparison (baseMap R T σ) (Hodge R W) (Hodge T Z) (comparisonHodge E) n =
      composeComparison (baseMap R S ι) (baseMap S T ρ) (baseMap R T σ)
        hbase (HodgePower R W n) (HodgePower S V n) (HodgePower T Z n)
        (tensorComparison (baseMap R S ι) (Hodge R W) (Hodge S V) (comparisonHodge C) n)
        (tensorComparison (baseMap S T ρ) (Hodge S V) (Hodge T Z) (comparisonHodge D) n) := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  obtain ⟨U, a, hx, hframe⟩ := exists_exact_differential_frame (structureMap R W)
    (origin R W (baseMap R T σ x))
  let B := baseMap R T σ ⁻¹ᵁ (origin R W ⁻¹ᵁ U)
  have hB : B ≤ baseMap S T ρ ⁻¹ᵁ (baseMap R S ι ⁻¹ᵁ (origin R W ⁻¹ᵁ U)) := by
    intro y hy
    change (baseMap S T ρ ≫ baseMap R S ι) y ∈ origin R W ⁻¹ᵁ U
    rw [← hbase]
    exact hy
  have hC : baseMap R S ι ⁻¹ᵁ (origin R W ⁻¹ᵁ U) ≤
      origin S V ⁻¹ᵁ (C.map ⁻¹ᵁ U) := by
    intro y hy
    change (origin S V ≫ C.map) y ∈ U
    rw [C.pointed]
    exact hy
  have hE : B ≤ origin T Z ⁻¹ᵁ (E.map ⁻¹ᵁ U) := by
    intro y hy
    change (origin T Z ≫ E.map) y ∈ U
    rw [E.pointed]
    exact hy
  have hD : B ≤ origin T Z ⁻¹ᵁ (D.map ⁻¹ᵁ (C.map ⁻¹ᵁ U)) := by
    intro y hy
    change (origin T Z ≫ D.map ≫ C.map) y ∈ U
    rw [hm]
    exact hE hy
  refine ⟨B, Scheme.Modules.pullbackLocalSection (baseMap R T σ)
    (localPower R W n U a), hx, ?_, ?_⟩
  · apply pullback_frame
    apply tensorPower_frame
    exact pullback_frame (origin R W) (structureMap R W).kaehler _ hframe
  · have hleft := comparisonPower_spec_aux E n U a B le_rfl hE
    have hcomp := composeComparison_section (baseMap R S ι) (baseMap S T ρ)
      (baseMap R T σ) hbase (HodgePower R W n) (HodgePower S V n) (HodgePower T Z n)
      (tensorComparison (baseMap R S ι) (Hodge R W) (Hodge S V) (comparisonHodge C) n)
      (tensorComparison (baseMap S T ρ) (Hodge S V) (Hodge T Z) (comparisonHodge D) n)
      (origin R W ⁻¹ᵁ U) (localPower R W n U a) B le_rfl hB
    have hinner := comparisonPower_spec_aux C n U a
      (baseMap R S ι ⁻¹ᵁ (origin R W ⁻¹ᵁ U)) le_rfl hC
    rw [res_refl] at hinner
    rw [hinner, ← InitialSectionNaturality.pullback_res, ← hom_res, res_res] at hcomp
    rw [comparisonPower_spec_aux D n (C.map ⁻¹ᵁ U) (C.map.app U a) B
      (fun y hy => hC (hB hy)) hD] at hcomp
    have hvalue : res (HodgePower T Z n) hD
        (localPower T Z n (D.map ⁻¹ᵁ (C.map ⁻¹ᵁ U)) (D.map.app _ (C.map.app U a))) =
        res (HodgePower T Z n) hE (localPower T Z n (E.map ⁻¹ᵁ U) (E.map.app U a)) := by
      exact localPower_map_congr Z (D.map ≫ C.map) E.map hm n U a B hD hE
    rw [hvalue] at hcomp
    simpa only [res_refl] using hleft.trans hcomp.symm

set_option maxRecDepth 4096 in
/-- Pulling the section along two specified comparisons equals pulling along
their actual composite, without a normality assumption on the target. -/
theorem pull_refinement
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic] {Z : WeierstrassCurve T}
    {ι : R →+* S} {ρ : S →+* T} {σ : R →+* T}
    (C : Comparison R S W V ι) (D : Comparison S T V Z ρ)
    (E : Comparison R T W Z σ) (hm : D.map ≫ C.map = E.map)
    (hbase : baseMap R T σ = baseMap S T ρ ≫ baseMap R S ι)
    (d : Sections (HodgePower R W 24)) :
    pull E d = pull D (pull C d) := by
  have h := composeComparison_section (baseMap R S ι) (baseMap S T ρ)
    (baseMap R T σ) hbase (HodgePower R W 24) (HodgePower S V 24) (HodgePower T Z 24)
    (comparisonPower C) (comparisonPower D) ⊤ d ⊤ (by simp) (by simp)
  have he : comparisonPower E =
      composeComparison (baseMap R S ι) (baseMap S T ρ) (baseMap R T σ)
        hbase (HodgePower R W 24) (HodgePower S V 24) (HodgePower T Z 24)
        (comparisonPower C) (comparisonPower D) :=
    comparisonPower_refinement C D E hm hbase 24
  rw [← he] at h
  simpa only [pull, baseMap, Scheme.Hom.preimage_top, res_refl] using h

#print axioms comparisonPower_refinement
#print axioms pull_refinement


/-- Exact specialization of the accepted normalized section, retaining the
specified map rather than replacing it by a chosen coordinate map. -/
theorem value_eq_localD_of_nsmul
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (M : NormalModel R W)
    (hn : ∀ n, G.schemeNsmul n ≫ M.comparison.map =
      M.comparison.map ≫ M.law.schemeNsmul n) :
    value M = localD R W G hG := by
  have h := localD_naturality M.ring M.equation M.law M.originLaw
    R W G hG M.scalar.toRingHom M.comparison.map
    ⟨M.comparison.cartesian, M.comparison.pointed, hn⟩
  unfold value pull
  change res (HodgePower R W 24) le_rfl
    ((comparisonPower M.comparison).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (baseMap M.ring R M.scalar.toRingHom)
        (localD M.ring M.equation M.law M.originLaw))) = _
  rw [res_refl]
  rw [comparisonPower_eq M.comparison M.law G hn]
  unfold InitialBaseChange at h
  exact h.trans (res_refl _ _)

/-- A model over a normal target recovers the accepted normalized initial
section for any actual origin law on that target. -/
theorem value_eq_localD
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (M : NormalModel R W) :
    value M = localD R W G hG :=
  value_eq_localD_of_nsmul R W G hG M
    (comparison_nsmul M.comparison M.law M.originLaw G hG)

/-- Normal-source naturality expressed directly through the frozen comparison
and pull operations, without bundling an auxiliary normal model. -/
theorem normal_comparison_pull
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsIntegrallyClosed S] [Algebra ℚ S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} [V.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    [IsIntegral (Curve S V)] [IsLocallyNoetherian (Curve S V)]
    [IsIntegral (GenericCurve S V)] [IsLocallyNoetherian (GenericCurve S V)]
    {ι : R →+* S} (C : Comparison R S W V ι)
    (G : Law R W) (hG : IsOriginLaw R W G) (H : Law S V) (hH : IsOriginLaw S V H) :
    pull C (localD R W G hG) = localD S V H hH := by
  have hn := comparison_nsmul C G hG H hH
  have h := localD_naturality R W G hG S V H hH ι C.map
    ⟨C.cartesian, C.pointed, hn⟩
  change res (HodgePower S V 24) le_rfl ((comparisonPower C).hom.app ⊤
    (Scheme.Modules.pullbackLocalSection (baseMap R S ι) (localD R W G hG))) = _
  rw [res_refl, comparisonPower_eq C G H hn]
  exact h.trans (res_refl _ _)

/-- Independence over normal Noetherian targets, with the target law and all
curve geometry constructed from the equation. This is a special case of the
frozen arbitrary-ring obligation, not a replacement for it. -/
theorem independence_normal
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (M N : NormalModel R W) :
    value M = value N := by
  have hgeom := relative_curve_geometry R W
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  letI := hgeom.2.2.2.2.2.1
  have htwo : IsUnit (2 : R) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  letI : Invertible (2 : R) := htwo.invertible
  obtain ⟨_, _, _, G, _, hone, hcomm⟩ := WeierstrassProjModel.relativeGroupLaw_exists
    W (inferInstance : Smooth (structureMap R W)) hgeom.2.2.2.2.2.2 W.isUnit_Δ
  exact (value_eq_localD R W G ⟨hone, hcomm⟩ M).trans
    (value_eq_localD R W G ⟨hone, hcomm⟩ N).symm

/-- The empty-spectrum case does not require a nontrivial target algebra. -/
theorem independence_subsingleton
    (R : Type u) [CommRing R] [Algebra ℚ R] [Subsingleton R]
    (W : WeierstrassCurve R) (M N : NormalModel R W) : value M = value N := by
  letI : Subsingleton (Γ(Spec (CommRingCat.of R), ⊤)) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1.subsingleton
  letI : Subsingleton (Sections (HodgePower R W 24)) :=
    Module.subsingleton (Γ(Spec (CommRingCat.of R), ⊤)) _
  exact Subsingleton.elim _ _


namespace ChangeParameters

abbrev Poly (R : Type u) [CommRing R] := MvPolynomial (Fin 4) R
abbrev Ring (R : Type u) [CommRing R] := Localization.Away (MvPolynomial.X (0 : Fin 4) : Poly R)

def parameter (R : Type u) [CommRing R] (i : Fin 4) : Ring R :=
  algebraMap (Poly R) (Ring R) (MvPolynomial.X i)

theorem parameter_zero_unit (R : Type u) [CommRing R] : IsUnit (parameter R 0) :=
  IsLocalization.Away.algebraMap_isUnit (S := Ring R) (MvPolynomial.X (0 : Fin 4))

/-- The normal parameter space for a unit scale and three translations. -/
def universal (R : Type u) [CommRing R] : WeierstrassCurve.VariableChange (Ring R) :=
  ⟨(parameter_zero_unit R).unit, parameter R 1, parameter R 2, parameter R 3⟩

def evaluation {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (C : WeierstrassCurve.VariableChange S) : Poly R →+* S :=
  MvPolynomial.eval₂Hom ι ![(C.u : S), C.r, C.s, C.t]

/-- Specialization is defined for arbitrary target rings, including nilpotents. -/
def specialize {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (C : WeierstrassCurve.VariableChange S) : Ring R →+* S :=
  IsLocalization.Away.lift (MvPolynomial.X (0 : Fin 4)) (by
    change IsUnit (evaluation ι C (MvPolynomial.X 0))
    simp [evaluation])

theorem specialize_parameter {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (C : WeierstrassCurve.VariableChange S) (i : Fin 4) :
    specialize ι C (parameter R i) = ![(C.u : S), C.r, C.s, C.t] i := by
  unfold specialize parameter
  rw [IsLocalization.Away.lift_eq]
  simp [evaluation]

theorem specialize_scalar {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (C : WeierstrassCurve.VariableChange S) (r : R) :
    specialize ι C (algebraMap R (Ring R) r) = ι r := by
  change specialize ι C (algebraMap (Poly R) (Ring R) (MvPolynomial.C r)) = _
  unfold specialize
  rw [IsLocalization.Away.lift_eq]
  simp [evaluation]

theorem specialize_universal {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (C : WeierstrassCurve.VariableChange S) :
    (universal R).map (specialize ι C) = C := by
  ext <;> simp [universal, specialize_parameter, IsUnit.unit_spec]

/-- The transformed equation specializes to the literal requested coordinate
change of the coefficient-specialized equation. -/
theorem specialize_transformed {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (C : WeierstrassCurve.VariableChange S) (W : WeierstrassCurve R) :
    ((universal R) • (W.map (algebraMap R (Ring R)))).map (specialize ι C) =
      C • (W.map ι) := by
  have hs : (specialize ι C).comp (algebraMap R (Ring R)) = ι :=
    RingHom.ext (specialize_scalar ι C)
  rw [← WeierstrassCurve.map_variableChange, specialize_universal,
    WeierstrassCurve.map_map, hs]

theorem polynomial_normal (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | succ n ih =>
    letI := ih
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

theorem normal_parameters (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] :
    IsDomain (Ring R) ∧ IsNoetherianRing (Ring R) ∧ IsIntegrallyClosed (Ring R) := by
  have hx : (MvPolynomial.X (0 : Fin 4) : Poly R) ≠ 0 := MvPolynomial.X_ne_zero _
  letI : IsDomain (Ring R) := Localization.Away.isDomain hx
  letI : IsIntegrallyClosed (Poly R) := polynomial_normal R 4
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact isIntegrallyClosed_of_isLocalization (R := Poly R) (Ring R)
    (Submonoid.powers (MvPolynomial.X (0 : Fin 4) : Poly R))
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx))

end ChangeParameters

namespace CoefficientParameters

abbrev Poly (k : Type u) [CommRing k] := MvPolynomial (Fin 5) k

/-- Five independent Weierstrass coefficients, before inverting the discriminant. -/
def polynomialEquation (k : Type u) [CommRing k] : WeierstrassCurve (Poly k) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
    MvPolynomial.X 3, MvPolynomial.X 4⟩

def evaluation {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) : Poly k →+* R :=
  MvPolynomial.eval₂Hom ι ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem evaluation_equation {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) :
    (polynomialEquation k).map (evaluation ι W) = W := by
  ext <;> simp [polynomialEquation, evaluation, WeierstrassCurve.map]

theorem evaluation_discriminant {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) :
    evaluation ι W (polynomialEquation k).Δ = W.Δ := by
  rw [← WeierstrassCurve.map_Δ, evaluation_equation]

theorem discriminant_ne_zero (k : Type u) [Field k] [CharZero k] :
    (polynomialEquation k).Δ ≠ 0 := by
  let W : WeierstrassCurve k := ⟨0, 0, 0, -1, 0⟩
  intro hz
  have h : W.Δ = 0 := by
    rw [← evaluation_discriminant (RingHom.id k) W, hz, map_zero]
  norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈] at h

abbrev Ring (k : Type u) [CommRing k] := Localization.Away (polynomialEquation k).Δ

def universal (k : Type u) [CommRing k] : WeierstrassCurve (Ring k) :=
  (polynomialEquation k).map (algebraMap (Poly k) (Ring k))

instance universal_elliptic (k : Type u) [CommRing k] : (universal k).IsElliptic := by
  constructor
  rw [universal, WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit (S := Ring k) (polynomialEquation k).Δ

instance ring_domain (k : Type u) [Field k] [CharZero k] : IsDomain (Ring k) :=
  Localization.Away.isDomain (discriminant_ne_zero k)

instance ring_normal (k : Type u) [Field k] [CharZero k] : IsIntegrallyClosed (Ring k) := by
  letI : IsIntegrallyClosed (Poly k) := ChangeParameters.polynomial_normal k 5
  exact isIntegrallyClosed_of_isLocalization (R := Poly k) (Ring k)
    (Submonoid.powers (polynomialEquation k).Δ)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (discriminant_ne_zero k)))

theorem normal_coefficients (k : Type u) [Field k] [CharZero k] :
    IsDomain (Ring k) ∧ IsNoetherianRing (Ring k) ∧ IsIntegrallyClosed (Ring k) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A classifying scalar map exists for every elliptic equation, including
equations over nonreduced and non-Noetherian target rings. -/
def classifying {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic] : Ring k →+* R :=
  IsLocalization.Away.lift (polynomialEquation k).Δ (by
    change IsUnit (evaluation ι W (polynomialEquation k).Δ)
    rw [evaluation_discriminant]
    exact W.isUnit_Δ)

theorem classifying_poly {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic] (p : Poly k) :
    classifying ι W (algebraMap (Poly k) (Ring k) p) = evaluation ι W p :=
  IsLocalization.Away.lift_eq _ _ _

theorem classifying_universal {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic] :
    (universal k).map (classifying ι W) = W := by
  ext <;> simp [universal, polynomialEquation, WeierstrassCurve.map,
    classifying_poly, evaluation]

theorem classifying_scalar {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic] (a : k) :
    classifying ι W (algebraMap k (Ring k) a) = ι a := by
  change classifying ι W (algebraMap (Poly k) (Ring k) (MvPolynomial.C a)) = _
  rw [classifying_poly]
  simp [evaluation]

theorem classifying_naturality {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    (ι : k →+* R) (ρ : R →+* S) (W : WeierstrassCurve R) [W.IsElliptic] :
    ρ.comp (classifying ι W) = classifying (ρ.comp ι) (W.map ρ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (polynomialEquation k).Δ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, classifying_poly, evaluation]
  · intro i
    fin_cases i <;> simp [RingHom.comp_apply, classifying_poly, evaluation, WeierstrassCurve.map]

/-- The classifying scalar homomorphism is realized by a genuine pointed
Cartesian map to the universal equation. -/
def classifyingComparison {k R : Type u} [CommRing k] [CommRing R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic] :
    Comparison (Ring k) R (universal k) W (classifying ι W) :=
  comparisonTargetEq (coefficientComparison (universal k) (classifying ι W))
    (classifying_universal ι W)

section Normalized

variable (k : Type u) [Field k] [CharZero k] [Algebra ℚ k]

instance universal_integral : IsIntegral (Curve (Ring k) (universal k)) :=
  (relative_curve_geometry (Ring k) (universal k)).1

instance universal_locallyNoetherian : IsLocallyNoetherian (Curve (Ring k) (universal k)) :=
  (relative_curve_geometry (Ring k) (universal k)).2.1

instance universal_genericIntegral : IsIntegral (GenericCurve (Ring k) (universal k)) :=
  (relative_curve_geometry (Ring k) (universal k)).2.2.2.1

instance universal_genericLocallyNoetherian :
    IsLocallyNoetherian (GenericCurve (Ring k) (universal k)) :=
  (relative_curve_geometry (Ring k) (universal k)).2.2.2.2.1

theorem universal_law_exists : ∃ G : Law (Ring k) (universal k),
    IsOriginLaw (Ring k) (universal k) G := by
  have hg := relative_curve_geometry (Ring k) (universal k)
  letI := hg.2.2.2.2.2.1
  have htwo : IsUnit (2 : Ring k) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ (Ring k))
  letI : Invertible (2 : Ring k) := htwo.invertible
  obtain ⟨_, _, _, G, _, hone, hcomm⟩ := WeierstrassProjModel.relativeGroupLaw_exists
    (universal k) (inferInstance : Smooth (structureMap (Ring k) (universal k)))
    hg.2.2.2.2.2.2 (universal k).isUnit_Δ
  exact ⟨G, hone, hcomm⟩

def universalLaw : Law (Ring k) (universal k) := (universal_law_exists k).choose

theorem universalLaw_origin : IsOriginLaw (Ring k) (universal k) (universalLaw k) :=
  (universal_law_exists k).choose_spec

/-- The universal section is the accepted five-Kato initial section itself. -/
def initialSection : Sections (HodgePower (Ring k) (universal k) 24) :=
  localD (Ring k) (universal k) (universalLaw k) (universalLaw_origin k)

theorem normal_classifying_pull
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) :
    pull (classifyingComparison ι W) (initialSection k) = localD R W G hG :=
  normal_comparison_pull (classifyingComparison ι W)
    (universalLaw k) (universalLaw_origin k) G hG

end Normalized

end CoefficientParameters

namespace CoefficientParameters

/-- The actual classifying morphisms commute with coefficient specialization. -/
theorem classifyingComparison_comp
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    (ι : k →+* R) (ρ : R →+* S) (W : WeierstrassCurve R) [W.IsElliptic] :
    (coefficientComparison W ρ).map ≫ (classifyingComparison ι W).map =
      (classifyingComparison (ρ.comp ι) (W.map ρ)).map :=
  coefficientComparison_transport_comp (universal k) W (classifying ι W) ρ
    (classifying (ρ.comp ι) (W.map ρ)) (classifying_universal ι W)
    (classifying_naturality ι ρ W) (classifying_universal (ρ.comp ι) (W.map ρ))

/-- A candidate over every base, defined by the accepted section over the
normal universal coefficient ring and its actual coefficient morphism. -/
def coefficientSection {k R : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] (ι : k →+* R) (W : WeierstrassCurve R) [W.IsElliptic] :
    Sections (HodgePower R W 24) :=
  pull (classifyingComparison ι W) (initialSection k)

theorem coefficientSection_naturality
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [CommRing S]
    (ι : k →+* R) (ρ : R →+* S) (W : WeierstrassCurve R) [W.IsElliptic] :
    pull (coefficientComparison W ρ) (coefficientSection ι W) =
      coefficientSection (ρ.comp ι) (W.map ρ) := by
  apply Eq.symm
  apply pull_refinement (classifyingComparison ι W) (coefficientComparison W ρ)
    (classifyingComparison (ρ.comp ι) (W.map ρ)) (classifyingComparison_comp ι ρ W)
  rw [← classifying_naturality ι ρ W]
  exact Spec.map_comp (CommRingCat.ofHom (classifying ι W)) (CommRingCat.ofHom ρ)

end CoefficientParameters

#print axioms CoefficientParameters.classifyingComparison_comp
#print axioms CoefficientParameters.coefficientSection_naturality

set_option maxRecDepth 4096 in
theorem pull_frame {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι)
    (d : Sections (HodgePower R W 24)) (hd : IsFrame (HodgePower R W 24) ⊤ d) :
    IsFrame (HodgePower S V 24) ⊤ (pull C d) :=
  frame_restrict _ (by simp) _
    (frame_iso (comparisonPower C) _ (pullback_frame _ _ d hd))

theorem value_frame {R : Type u} [CommRing R] [Algebra ℚ R]
    {W : WeierstrassCurve R} (M : NormalModel R W) :
    IsFrame (HodgePower R W 24) ⊤ (value M) :=
  pull_frame M.comparison _ (localD_frame M.ring M.equation M.law M.originLaw)

/-- Localization at every maximal ideal detects equality of sections when
one global section is a frame. This detects nilpotents as well. -/
theorem sections_eq_of_localizations {R : Type u} [CommRing R]
    (M : (Base R).Modules) (s t : Sections M) (hs : IsFrame M ⊤ s)
    (h : ∀ (m : Ideal R) (_ : m.IsMaximal),
      Scheme.Modules.pullbackLocalSection
        (baseMap R (Localization.AtPrime m) (algebraMap R (Localization.AtPrime m))) s =
      Scheme.Modules.pullbackLocalSection
        (baseMap R (Localization.AtPrime m) (algebraMap R (Localization.AtPrime m))) t) :
    s = t := by
  have hframe : Function.Bijective (fun a : Γ(Base R, ⊤) => a • s) := by
    simpa only [res_refl] using hs ⊤ le_rfl
  obtain ⟨a, ha⟩ := hframe.2 t
  change a • s = t at ha
  have haone : a = 1 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [map_one]
    apply sub_eq_zero.mp
    apply eq_zero_of_localization
    intro m hm
    letI := hm
    let S := Localization.AtPrime m
    let f := baseMap R S (algebraMap R S)
    have hf : Function.Injective (fun b : Γ(Base S, f ⁻¹ᵁ ⊤) =>
        b • Scheme.Modules.pullbackLocalSection f s) := by
      have hh := pullback_frame f M s hs
      simpa only [res_refl] using (hh (f ⁻¹ᵁ ⊤) le_rfl).1
    have hb : f.app ⊤ a = 1 := by
      apply hf
      change f.app ⊤ a • Scheme.Modules.pullbackLocalSection f s =
        (1 : Γ(Base S, f ⁻¹ᵁ ⊤)) • Scheme.Modules.pullbackLocalSection f s
      rw [one_smul]
      rw [← Scheme.Modules.pullbackLocalSection_smul, ha]
      exact (h m hm).symm
    have hbtop : f.appTop a = 1 := by
      change f.appLE ⊤ ⊤ (by simp) a = 1
      simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply, hb, map_one]
    have hn := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))) a
    change (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (f.appTop a) =
      algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) at hn
    rw [hbtop, map_one] at hn
    rw [map_sub, map_one, ← hn, sub_self]
  rw [haone, one_smul] at ha
  exact ha

#print axioms pull_frame
#print axioms value_frame
#print axioms sections_eq_of_localizations


/-- A coordinate change gives an actual pointed Cartesian comparison. -/
theorem variable_comparison_exists {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    Nonempty (Comparison R R W (C • W) (RingHom.id R)) := by
  obtain ⟨b, _, hb, hover, horigin, _⟩ :=
    ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.variable_comparison W C
  letI := hb
  have hs : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (CommRingCat.of R)) :=
    Spec.map_id _
  refine ⟨⟨b, ?_, ?_⟩⟩
  · rw [hs]
    exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hover⟩
  · simpa only [hs, Category.id_comp] using horigin

/-- The universal coordinate change is a pointed family map over the normal
parameter ring. This supplies the geometric map used before specialization. -/
theorem universal_comparison_exists {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) :
    Nonempty (Comparison R (ChangeParameters.Ring R) W
      ((ChangeParameters.universal R) • (W.map (algebraMap R (ChangeParameters.Ring R))))
      (algebraMap R (ChangeParameters.Ring R))) := by
  let T := ChangeParameters.Ring R
  let D := coefficientComparison W (algebraMap R T)
  obtain ⟨E⟩ := variable_comparison_exists (W.map (algebraMap R T))
    (ChangeParameters.universal R)
  have hs : Spec.map (CommRingCat.ofHom (RingHom.id T)) = 𝟙 (Spec (CommRingCat.of T)) :=
    Spec.map_id _
  refine ⟨⟨E.map ≫ D.map, ?_, ?_⟩⟩
  · simpa only [hs, Category.id_comp] using E.cartesian.paste_horiz D.cartesian
  · rw [← Category.assoc, E.pointed, hs, Category.id_comp, D.pointed]

/- Universe-polymorphic proofs of the chart providers used by coordinate
reconstruction. These are explicit adaptations of the corresponding library
proofs; the provenance and transformations are recorded separately. -/
namespace CoordinateUniverse
set_option maxHeartbeats 6400000
set_option maxRecDepth 4096
namespace Algebra


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open Polynomial
open scoped Polynomial.Bivariate

namespace VarChangeAlgAux

variable {T : Type u} [CommRing T]

noncomputable def φ₁ (v₁ r : T) : T[X] →+* T[X] := eval₂RingHom C (C v₁ * X + C r)

@[scoped simp] theorem φ₁_C (v₁ r a : T) : φ₁ v₁ r (C a) = C a := by simp [φ₁]
@[scoped simp] theorem φ₁_X (v₁ r : T) : φ₁ v₁ r X = C v₁ * X + C r := by simp [φ₁]

noncomputable def σ (v₁ v₂ r s' t : T) : T[X][Y] →+* T[X][Y] :=
  eval₂RingHom (C.comp (φ₁ v₁ r)) (C (C v₂) * X + C (C s' * X + C t))

@[scoped simp] theorem σ_C (v₁ v₂ r s' t : T) (p : T[X]) : σ v₁ v₂ r s' t (C p) = C (φ₁ v₁ r p) := by simp [σ]
@[scoped simp] theorem σ_X (v₁ v₂ r s' t : T) : σ v₁ v₂ r s' t X = C (C v₂) * X + C (C s' * X + C t) := by simp [σ]

noncomputable def Lpoly (W : WeierstrassCurve T) (v₁ v₂ r s' t : T) : T[X] :=
  C v₂ * (2 * (C s' * X + C t) + (C W.a₁ * (C v₁ * X + C r) + C W.a₃))
noncomputable def Kpoly (W : WeierstrassCurve T) (v₁ v₂ r s' t : T) : T[X] :=
  (C s' * X + C t) ^ 2 + (C W.a₁ * (C v₁ * X + C r) + C W.a₃) * (C s' * X + C t)
    - ((C v₁ * X + C r) ^ 3 + C W.a₂ * (C v₁ * X + C r) ^ 2 + C W.a₄ * (C v₁ * X + C r) + C W.a₆)

theorem σ_polynomial (W : WeierstrassCurve T) (v₁ v₂ r s' t : T) :
    σ v₁ v₂ r s' t W.toAffine.polynomial =
      C (C v₂ ^ 2) * X ^ 2 + C (Lpoly W v₁ v₂ r s' t) * X + C (Kpoly W v₁ v₂ r s' t) := by
  simp only [WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow, σ_C, σ_X, φ₁_C, φ₁_X,
    Lpoly, Kpoly, map_ofNat]
  ring

end VarChangeAlgAux
p2m_reactivate "ArithmeticThetaArbitraryDiscriminantR0243.NormalDiscriminantIndependence.CoordinateUniverse.Algebra.VarChangeAlgAux"

namespace VarChangeAlgAux

theorem coeffs_eq_zero_of_cubic {T : Type u} [CommRing T] (k₀ k₁ k₂ k₃ : T)
    (h : C k₀ + C k₁ * X + C k₂ * X ^ 2 + C k₃ * X ^ 3 = (0 : T[X])) :
    k₀ = 0 ∧ k₁ = 0 ∧ k₂ = 0 ∧ k₃ = 0 := by
  have h0 := congrArg (fun p : T[X] => p.coeff 0) h
  have h1 := congrArg (fun p : T[X] => p.coeff 1) h
  have h2 := congrArg (fun p : T[X] => p.coeff 2) h
  have h3 := congrArg (fun p : T[X] => p.coeff 3) h
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_zero] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem coeffs_eq_zero_of_linear {T : Type u} [CommRing T] (k₀ k₁ : T)
    (h : C k₀ + C k₁ * X = (0 : T[X])) : k₀ = 0 ∧ k₁ = 0 := by
  have := coeffs_eq_zero_of_cubic k₀ k₁ 0 0 (by rw [h]; simp)
  exact ⟨this.1, this.2.1⟩

end VarChangeAlgAux
p2m_reactivate "ArithmeticThetaArbitraryDiscriminantR0243.NormalDiscriminantIndependence.CoordinateUniverse.Algebra.VarChangeAlgAux"

open VarChangeAlgAux in
theorem solution
    (T : Type u) [CommRing T] (W W' : WeierstrassCurve T)
    (g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
      (v₁ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ r)
    (hy : g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
      (v₂ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
        s' • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ t) :
    ∃ C : WeierstrassCurve.VariableChange T,
      C • W = W' ∧ ((C.u : T) ^ 2 = v₁ ∧ (C.u : T) ^ 3 = v₂) ∧ C.r = r ∧ (C.u : T) ^ 2 * C.s = s' ∧ C.t = t := by
  classical
  rcases subsingleton_or_nontrivial T with hT | hT
  · refine ⟨⟨v₁, r, 0, t⟩, ?_, ⟨?_, ?_⟩, rfl, ?_, rfl⟩ <;> first | exact Subsingleton.elim _ _ | skip
    exact WeierstrassCurve.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)

  set σ' := σ (v₁ : T) (v₂ : T) r s' t with hσ'
  have hmkC : ∀ (V : WeierstrassCurve T) (a : T),
      WeierstrassCurve.Affine.CoordinateRing.mk V (C (C a)) = algebraMap T V.toAffine.CoordinateRing a := by
    intro V a; rfl
  have key : g.toRingHom.comp (WeierstrassCurve.Affine.CoordinateRing.mk W) =
      (WeierstrassCurve.Affine.CoordinateRing.mk W').comp σ' := by
    apply Polynomial.ringHom_ext
    · intro p

      revert p
      suffices h : (g.toRingHom.comp (WeierstrassCurve.Affine.CoordinateRing.mk W)).comp C =
          ((WeierstrassCurve.Affine.CoordinateRing.mk W').comp σ').comp C from fun p => RingHom.congr_fun h p
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, hσ', σ_C, φ₁_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hmkC,
          AlgHom.commutes]
      · simp only [RingHom.comp_apply, hσ', σ_C, φ₁_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hx,
          map_add, map_mul, hmkC, Algebra.smul_def]
    · simp only [RingHom.comp_apply, hσ', σ_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hy, map_add,
        map_mul, hmkC, Algebra.smul_def]
      ring

  have hdvd : W'.toAffine.polynomial ∣ σ' W.toAffine.polynomial := by
    rw [← AdjoinRoot.mk_eq_zero]
    have := RingHom.congr_fun key W.toAffine.polynomial
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    rw [show WeierstrassCurve.Affine.CoordinateRing.mk W' = AdjoinRoot.mk _ from rfl] at this
    rw [← this, show WeierstrassCurve.Affine.CoordinateRing.mk W = AdjoinRoot.mk _ from rfl, AdjoinRoot.mk_self,
      map_zero]

  obtain ⟨Q, hQ⟩ := hdvd
  rw [hσ', σ_polynomial] at hQ
  set L := Lpoly W (v₁ : T) (v₂ : T) r s' t with hL
  set K := Kpoly W (v₁ : T) (v₂ : T) r s' t with hK
  set A₁ : T[X] := L - C (v₂ : T) ^ 2 * (C W'.a₁ * X + C W'.a₃) with hA₁
  set A₀ : T[X] := K + C (v₂ : T) ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) with hA₀
  have hmon : W'.toAffine.polynomial.Monic := WeierstrassCurve.Affine.monic_polynomial
  have hsplit : (C A₁ * X + C A₀) + W'.toAffine.polynomial * C (C (v₂ : T) ^ 2) =
      C (C (v₂ : T) ^ 2) * X ^ 2 + C L * X + C K := by
    simp only [hA₁, hA₀, WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow]
    ring
  have hdeg2 : W'.toAffine.polynomial.degree = 2 := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, WeierstrassCurve.Affine.natDegree_polynomial]; rfl
  have hdegr : (C A₁ * X + C A₀).degree < W'.toAffine.polynomial.degree := by
    rw [hdeg2]
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hu1 := Polynomial.div_modByMonic_unique (C (C (v₂ : T) ^ 2)) (C A₁ * X + C A₀) hmon ⟨hsplit, hdegr⟩
  have hu2 := Polynomial.div_modByMonic_unique (f := C (C (v₂ : T) ^ 2) * X ^ 2 + C L * X + C K) Q 0 hmon
    ⟨by rw [zero_add]; exact hQ.symm, by
    rw [degree_zero, hdeg2]; exact WithBot.bot_lt_coe _⟩
  have hrem : C A₁ * X + C A₀ = 0 := hu1.2.symm.trans hu2.2
  have hA : A₀ = 0 ∧ A₁ = 0 := by
    have := VarChangeAlgAux.coeffs_eq_zero_of_linear A₀ A₁ (by rw [← hrem]; ring)
    exact this
  obtain ⟨hA₀0, hA₁0⟩ := hA

  have hLin : C ((v₂ : T) * (2 * t + W.a₁ * r + W.a₃) - (v₂ : T) ^ 2 * W'.a₃) +
      C ((v₂ : T) * (2 * s' + W.a₁ * v₁) - (v₂ : T) ^ 2 * W'.a₁) * X = (0 : T[X]) := by
    rw [← hA₁0, hA₁, hL, Lpoly]
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow, map_ofNat]
    ring
  obtain ⟨e₃, e₁⟩ := VarChangeAlgAux.coeffs_eq_zero_of_linear _ _ hLin
  have hCub : C (t ^ 2 + (W.a₁ * r + W.a₃) * t - (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆) + (v₂ : T) ^ 2 * W'.a₆) +
      C (2 * s' * t + W.a₁ * (v₁ : T) * t + (W.a₁ * r + W.a₃) * s' - (3 * (v₁ : T) * r ^ 2 + 2 * W.a₂ * v₁ * r + W.a₄ * v₁)
        + (v₂ : T) ^ 2 * W'.a₄) * X +
      C (s' ^ 2 + W.a₁ * (v₁ : T) * s' - (3 * (v₁ : T) ^ 2 * r + W.a₂ * (v₁ : T) ^ 2) + (v₂ : T) ^ 2 * W'.a₂) * X ^ 2 +
      C (-(v₁ : T) ^ 3 + (v₂ : T) ^ 2) * X ^ 3 = (0 : T[X]) := by
    rw [← hA₀0, hA₀, hK, Kpoly]
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow, Polynomial.C_neg, map_ofNat]
    ring
  obtain ⟨e₆, e₄, e₂, e₀⟩ := VarChangeAlgAux.coeffs_eq_zero_of_cubic _ _ _ _ hCub

  set w₁ : T := ↑v₁⁻¹ with hw₁
  set w₂ : T := ↑v₂⁻¹ with hw₂
  have hv₁ : (v₁ : T) * w₁ = 1 := by rw [hw₁]; exact Units.mul_inv v₁
  have hv₂ : (v₂ : T) * w₂ = 1 := by rw [hw₂]; exact Units.mul_inv v₂
  have hrel : (v₁ : T) ^ 3 = (v₂ : T) ^ 2 := by linear_combination (-1 : T) * e₀
  have f₁ : W'.a₁ = w₂ * (2 * s' + W.a₁ * v₁) := by
    linear_combination (-w₂ ^ 2) * e₁ + (w₂ * (2 * s' + W.a₁ * v₁) - W'.a₁ * ((v₂ : T) * w₂ - 1) - 2 * W'.a₁) * hv₂
  have f₃ : W'.a₃ = w₂ * (2 * t + W.a₁ * r + W.a₃) := by
    linear_combination (-w₂ ^ 2) * e₃ + (w₂ * (2 * t + W.a₁ * r + W.a₃) - W'.a₃ * ((v₂ : T) * w₂ - 1) - 2 * W'.a₃) * hv₂
  have f₂ : W'.a₂ = w₂ ^ 2 * (3 * (v₁ : T) ^ 2 * r + W.a₂ * (v₁ : T) ^ 2 - s' ^ 2 - W.a₁ * v₁ * s') := by
    linear_combination (w₂ ^ 2) * e₂ + (-(W'.a₂) * ((v₂ : T) * w₂ - 1) - 2 * W'.a₂) * hv₂
  have f₄ : W'.a₄ = w₂ ^ 2 * (3 * (v₁ : T) * r ^ 2 + 2 * W.a₂ * v₁ * r + W.a₄ * v₁ - 2 * s' * t - W.a₁ * v₁ * t
      - (W.a₁ * r + W.a₃) * s') := by
    linear_combination (w₂ ^ 2) * e₄ + (-(W'.a₄) * ((v₂ : T) * w₂ - 1) - 2 * W'.a₄) * hv₂
  have f₆ : W'.a₆ = w₂ ^ 2 * (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆ - t ^ 2 - (W.a₁ * r + W.a₃) * t) := by
    linear_combination (w₂ ^ 2) * e₆ + (-(W'.a₆) * ((v₂ : T) * w₂ - 1) - 2 * W'.a₆) * hv₂
  have hu : (((v₂ * v₁⁻¹ : Tˣ))⁻¹ : Tˣ) = v₁ * v₂⁻¹ := by rw [mul_inv_rev, inv_inv]
  refine ⟨⟨v₂ * v₁⁻¹, r, s' * w₁, t⟩, ?_, ⟨?_, ?_⟩, rfl, ?_, rfl⟩
  · apply WeierstrassCurve.ext
    · simp only [WeierstrassCurve.variableChange_a₁, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₁ + (2 * w₂ * s') * hv₁
    · simp only [WeierstrassCurve.variableChange_a₂, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₂ + (w₂ ^ 2 * (-((v₁ : T) * s' * W.a₁) - s' ^ 2 * ((v₁ : T) * w₁ + 1))) * hv₁
    · simp only [WeierstrassCurve.variableChange_a₃, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₃ + ((W.a₃ + r * W.a₁ + 2 * t) * w₂ ^ 3) * hrel
        + ((W.a₃ + r * W.a₁ + 2 * t) * w₂ * ((v₂ : T) * w₂ + 1)) * hv₂
    · simp only [WeierstrassCurve.variableChange_a₄, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₄
        + ((W.a₄ - s' * w₁ * W.a₃ + 2 * r * W.a₂ - (t + r * (s' * w₁)) * W.a₁ + 3 * r ^ 2 - 2 * (s' * w₁) * t)
            * (v₁ : T) * w₂ ^ 4) * hrel
        + ((W.a₄ - s' * w₁ * W.a₃ + 2 * r * W.a₂ - (t + r * (s' * w₁)) * W.a₁ + 3 * r ^ 2 - 2 * (s' * w₁) * t)
            * (v₁ : T) * w₂ ^ 2 * ((v₂ : T) * w₂ + 1)) * hv₂
        + (w₂ ^ 2 * (-(s' * W.a₃) - r * s' * W.a₁ - 2 * s' * t)) * hv₁
    · simp only [WeierstrassCurve.variableChange_a₆, hu, Units.val_mul, ← hw₂]
      linear_combination (-1 : T) * f₆
        + ((W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁) * w₂ ^ 6
            * ((v₁ : T) ^ 3 + (v₂ : T) ^ 2)) * hrel
        + ((W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁) * w₂ ^ 2
            * (((v₂ : T) * w₂) ^ 3 + ((v₂ : T) * w₂) ^ 2 + (v₂ : T) * w₂ + 1)) * hv₂
  · rw [Units.val_mul, mul_pow]
    linear_combination (-w₁ ^ 2) * hrel + ((v₁ : T) * ((v₁ : T) * w₁ + 1)) * hv₁
  · rw [Units.val_mul, mul_pow]
    linear_combination (-(v₂ : T) * w₁ ^ 3) * hrel + ((v₂ : T) * (((v₁ : T) * w₁) ^ 2 + (v₁ : T) * w₁ + 1)) * hv₁
  · rw [Units.val_mul]
    linear_combination (-(s') * w₁ ^ 3) * hrel + (s' * (((v₁ : T) * w₁) ^ 2 + (v₁ : T) * w₁ + 1)) * hv₁

end Algebra

namespace ChartIso


set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WMLocal

section Cover

open MvPolynomial TopologicalSpace

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

section ZeroSection

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev cY : T →+* OriginChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem not_mem_basicOpen_iff_mem_range_kwZeroSect (x : ↥(projModelCR W.toProjective)) :
    x ∉ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) ↔
      x ∈ Set.range (kwZeroSect T W).1 := by
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let χ₀ := kwYChartEval T W
  have hχc : ∀ t, χ₀ (cY W t) = t := fun t => RingHom.congr_fun (kwYChartEval_section T W) t
  have hpre : originChartι W.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) =
      PrimeSpectrum.basicOpen (zOverY W.toProjective) := by
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) one_pos
      (coord_mem W.toProjective 2) one_pos, isLocalizationElem_eq_zOverY]
  constructor
  · intro hx

    have hx1 : x ∈ (originChartι W.toProjective).opensRange := by
      rw [Proj.opensRange_awayι]
      exact (mem_basicOpen_or W.toProjective x).elim id fun h => absurd h hx
    obtain ⟨p, rfl⟩ := hx1

    have hz : zOverY W.toProjective ∈ p.asIdeal := by
      by_contra h
      have hp : p ∈ originChartι W.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
        rw [hpre]; exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
      exact hx hp
    have hrel := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      exact WeierstrassCurve.DrinfeldGlobal.originChart_rel W (RingHom.id _) (fun t => rfl)
    simp only [RingHom.id_apply] at hrel
    have hx3 : xOverY W.toProjective ^ 3 ∈ p.asIdeal := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      have : xOverY W.toProjective ^ 3 =
          zOverY W.toProjective * (1 + algebraMap T _ W.a₁ * xOverY W.toProjective +
            algebraMap T _ W.a₃ * zOverY W.toProjective - algebraMap T _ W.a₂ * xOverY W.toProjective ^ 2 -
            algebraMap T _ W.a₄ * xOverY W.toProjective * zOverY W.toProjective -
            algebraMap T _ W.a₆ * zOverY W.toProjective ^ 2) := by
        linear_combination (-1 : OriginChartRing W.toProjective) * hrel
      rw [this]
      exact Ideal.mul_mem_right _ _ hz
    have hxm : xOverY W.toProjective ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 hx3

    have hker : RingHom.ker χ₀ ≤ p.asIdeal := by
      rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hχc, hχx, hχz, map_zero, map_zero,
        sub_zero, sub_zero, Ideal.span_le]
      rintro a (rfl | rfl)
      · exact hxm
      · exact hz
    let t : ↥(Spec (CommRingCat.of T)) := Spec.map (CommRingCat.ofHom (cY W)) p
    have hpt : Spec.map (CommRingCat.ofHom χ₀) t = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap χ₀ (Ideal.comap (cY W) p.asIdeal) = p.asIdeal
      ext a
      simp only [Ideal.mem_comap]
      have hdiff : a - cY W (χ₀ a) ∈ p.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hχc, sub_self])
      constructor
      · intro h
        have := p.asIdeal.add_mem hdiff h
        rwa [sub_add_cancel] at this
      · intro h
        have := p.asIdeal.sub_mem h hdiff
        rwa [sub_sub_cancel] at this
    refine ⟨t, ?_⟩
    rw [hO', Scheme.Hom.comp_apply, hpt]
  · rintro ⟨t, rfl⟩ hmem
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have : Spec.map (CommRingCat.ofHom χ₀) t ∈ originChartι W.toProjective ⁻¹ᵁ
        Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := hmem
    rw [hpre] at this
    refine (PrimeSpectrum.mem_basicOpen _ _).mp this ?_
    change χ₀ (zOverY W.toProjective) ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

end ZeroSection

section Restrict

variable {T : Type u} [CommRing T] (W W' : WeierstrassCurve T)

noncomputable abbrev cZ : T →+* ZChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem zChartι_comp_projModelStrCR :
    zChartι W.toProjective ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom (cZ W)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem preimage_opensRange_zChartι (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange = (zChartι W.toProjective).opensRange := by
  ext x
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  change Ψ.hom x ∈ Proj.basicOpen (projModelGradingCR W'.toProjective) (coord W'.toProjective 2) ↔
    x ∈ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2)
  rw [← not_iff_not, not_mem_basicOpen_iff_mem_range_kwZeroSect W', not_mem_basicOpen_iff_mem_range_kwZeroSect W]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hinj : Function.Injective Ψ.hom := (Scheme.homeoOfIso Ψ).injective
    apply hinj
    rw [← ht, ← Scheme.Hom.comp_apply, hΨO]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [← Scheme.Hom.comp_apply, hΨO]⟩

theorem exists_ringEquiv_zChartRing_of_iso (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (cZ W' t) = cZ W t) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by

  have hrange : Set.range (zChartι W.toProjective ≫ Ψ.hom) = Set.range (zChartι W'.toProjective) := by
    have h := preimage_opensRange_zChartι W W' Ψ hΨO
    have hsurj : Function.Surjective Ψ.hom := (Scheme.homeoOfIso Ψ).surjective
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      have : zChartι W.toProjective p ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        rw [h]; exact ⟨p, rfl⟩
      simpa [Scheme.Hom.comp_apply] using this
    · rintro ⟨p', rfl⟩
      obtain ⟨x, hx⟩ := hsurj (zChartι W'.toProjective p')
      have : x ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        show Ψ.hom x ∈ (zChartι W'.toProjective).opensRange
        rw [hx]; exact ⟨p', rfl⟩
      rw [h] at this
      obtain ⟨p, rfl⟩ := this
      exact ⟨p, by rw [Scheme.Hom.comp_apply, hx]⟩
  let δ : Spec (CommRingCat.of (ZChartRing W.toProjective)) ≅ Spec (CommRingCat.of (ZChartRing W'.toProjective)) :=
    IsOpenImmersion.isoOfRangeEq (zChartι W.toProjective ≫ Ψ.hom) (zChartι W'.toProjective) hrange
  have hδ : δ.hom ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange

  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective δ.hom
  obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective δ.inv
  have h12 : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.hom_inv_id, Spec.map_id])
  have h21 : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.inv_hom_id, Spec.map_id])
  let e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective :=
    RingEquiv.ofRingHom φ₁.hom φ₂.hom (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h12 a)
      (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h21 a)
  have he : CommRingCat.ofHom e.toRingHom = φ₁ := rfl
  refine ⟨e, ?_, by rw [he, hφ₁, hδ]⟩

  have h2 : Spec.map φ₁ ≫ Spec.map (CommRingCat.ofHom (cZ W')) = Spec.map (CommRingCat.ofHom (cZ W)) := by
    rw [← zChartι_comp_projModelStrCR W', hφ₁, ← Category.assoc, hδ, Category.assoc, hΨ, zChartι_comp_projModelStrCR W]
  have h3 : CommRingCat.ofHom (cZ W') ≫ φ₁ = CommRingCat.ofHom (cZ W) :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  intro t
  have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (ZChartRing W.toProjective) => f.hom t) h3
  change φ₁.hom (cZ W' t) = cZ W t at this
  exact this

end Restrict

end WMLocal

theorem solution
    (T : Type u) [CommRing T] (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (fromZeroRingHom (projModelGradingCR W'.toProjective) _ (algebraMap T ((projModelGradingCR W'.toProjective) 0) t)) =
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
  WMLocal.exists_ringEquiv_zChartRing_of_iso W W' Ψ hΨ hΨO

end ChartIso

namespace Filtration

attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace WMLocal

variable {T : Type u} [CommRing T]

abbrev cZ (V : WeierstrassCurve T) : T →+* ZChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T (projModelGradingCR V.toProjective 0))

abbrev cY (V : WeierstrassCurve T) : T →+* OriginChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T (projModelGradingCR V.toProjective 0))

abbrev ofPS (T : Type u) [CommRing T] : PowerSeries T →+* LaurentSeries T := HahnSeries.ofPowerSeries ℤ T

theorem formalW_eq_X_pow_three_mul (V : WeierstrassCurve T) :
    ∃ v : PowerSeries T, V.formalW = PowerSeries.X ^ 3 * v ∧ PowerSeries.constantCoeff v = 1 := by
  obtain ⟨v, hv⟩ := V.isUnit_wUnitFactor.exists_right_inv
  refine ⟨v, ?_, ?_⟩
  · calc V.formalW = V.formalW * (V.wUnitFactor * v) := by rw [hv, mul_one]
      _ = PowerSeries.X ^ 3 * v := by rw [← mul_assoc, V.formalW_mul_wUnitFactor]
  · have h := congrArg PowerSeries.constantCoeff hv
    rwa [map_mul, V.constantCoeff_wUnitFactor, one_mul, map_one] at h

theorem zChart_ringHom_ext (V : WeierstrassCurve T) {B : Type u} [CommRing B]
    (g₁ g₂ : ZChartRing V.toProjective →+* B) (h0 : g₁.comp (cZ V) = g₂.comp (cZ V))
    (hx : g₁ (xOverZ V.toProjective) = g₂ (xOverZ V.toProjective))
    (hy : g₁ (yOverZ V.toProjective) = g₂ (yOverZ V.toProjective)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V.toProjective := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V.toProjective := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = cZ V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext a
    have := RingHom.congr_fun h' (e a)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

section laurent
variable (V : WeierstrassCurve T)

theorem single_one_mul_single_neg_one :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-1 : ℤ) (1 : T) = 1 := by
  rw [HahnSeries.single_mul_single, mul_one]; norm_num

theorem single_neg (n : ℕ) :
    (HahnSeries.single (-(n : ℤ)) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ n := by
  rw [HahnSeries.single_pow, one_pow]; congr 1; simp

theorem single_neg_two :
    (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ 2 := single_neg 2

theorem single_neg_three :
    (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ 3 := single_neg 3

theorem single_one_pow_three_mul_single_neg_three :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-3 : ℤ) (1 : T) = 1 := by
  rw [single_neg_three]
  calc (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-1 : ℤ) (1 : T) ^ 3
      = (HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single (-1 : ℤ) (1 : T)) ^ 3 := by ring
    _ = 1 := by rw [single_one_mul_single_neg_one, one_pow]

theorem laurent_equation :
    ((V.map (HahnSeries.C : T →+* LaurentSeries T)).toAffine.polynomial).evalEval
      (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
      (-(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) = 0 := by
  set U : LaurentSeries T := ofPS T V.wUnitFactor with hU
  set F : LaurentSeries T := ofPS T V.formalW with hF
  set Zp : LaurentSeries T := HahnSeries.single (1 : ℤ) (1 : T) with hZp
  set Zm : LaurentSeries T := HahnSeries.single (-1 : ℤ) (1 : T) with hZm
  have hpm : Zp * Zm = 1 := single_one_mul_single_neg_one
  have h2 : (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = Zm ^ 2 := single_neg 2
  have h3 : (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = Zm ^ 3 := single_neg 3
  rw [h2, h3]
  set ι : LaurentSeries T := U * Zm ^ 3 with hι
  have hFU : F * U = Zp ^ 3 := by
    rw [hF, hU, ← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
  have hFι : F * ι = 1 := by
    rw [hι, ← mul_assoc, hFU]
    calc Zp ^ 3 * Zm ^ 3 = (Zp * Zm) ^ 3 := by ring
      _ = 1 := by rw [hpm, one_pow]
  have hx : U * Zm ^ 2 = ι * Zp := by
    rw [hι]
    calc U * Zm ^ 2 = U * Zm ^ 2 * (Zp * Zm) := by rw [hpm, mul_one]
      _ = U * Zm ^ 3 * Zp := by ring
  have hrel : F = Zp ^ 3 + HahnSeries.C V.a₁ * Zp * F + HahnSeries.C V.a₂ * Zp ^ 2 * F
      + HahnSeries.C V.a₃ * F ^ 2 + HahnSeries.C V.a₄ * Zp * F ^ 2 + HahnSeries.C V.a₆ * F ^ 3 := by
    have h := congrArg (ofPS T) V.formalW_eq
    simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C] at h
    rw [hF, hZp]
    exact h
  rw [WeierstrassCurve.Affine.evalEval_polynomial]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆]
  rw [hx]
  linear_combination (ι ^ 3) * hrel
    - (ι ^ 2 - HahnSeries.C V.a₁ * Zp * ι ^ 2 - HahnSeries.C V.a₂ * Zp ^ 2 * ι ^ 2
        - HahnSeries.C V.a₃ * ι * (ι * F + 1)
        - HahnSeries.C V.a₄ * Zp * ι * (ι * F + 1)
        - HahnSeries.C V.a₆ * (ι ^ 2 * F ^ 2 + ι * F + 1)) * hFι

end laurent

section embed
variable (V : WeierstrassCurve T)

theorem exists_laurentEmbedding_core :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t, lam (cZ V t) = HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T) ∧
      lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  set xL : LaurentSeries T := ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T) with hxL
  set yL : LaurentSeries T := -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) with hyL
  let ev : Polynomial (Polynomial T) →+* LaurentSeries T :=
    (Polynomial.evalEvalRingHom xL yL).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (HahnSeries.C : T →+* LaurentSeries T)))
  have hevCC : ∀ t : T, ev (Polynomial.C (Polynomial.C t)) = HahnSeries.C t := by
    intro t; simp [ev]
  have hevCX : ev (Polynomial.C Polynomial.X) = xL := by simp [ev]
  have hevX : ev Polynomial.X = yL := by simp [ev]
  have hev : ev (WeierstrassCurve.Affine.polynomial V.toAffine) = 0 := by
    have h1 : ev (WeierstrassCurve.Affine.polynomial V.toAffine)
        = ((V.map (HahnSeries.C : T →+* LaurentSeries T)).toAffine.polynomial).evalEval xL yL := by
      rw [WeierstrassCurve.Affine.map_polynomial]
      rfl
    rw [h1]
    exact laurent_equation V
  let lam0 : (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine}) →+* LaurentSeries T :=
    Ideal.Quotient.lift _ ev (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hev, mul_zero])
  have hfx : f (xOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X : Polynomial (Polynomial T)) := by
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this
  have hfy : f (yOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.X : Polynomial (Polynomial T)) := by
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this
  refine ⟨lam0.comp f, ?_, ?_, ?_⟩
  · intro t
    rw [RingHom.comp_apply, show f (cZ V t) = algebraMap T _ t from RingHom.congr_fun hcomp t,
      IsScalarTower.algebraMap_apply T (Polynomial (Polynomial T)), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show lam0 (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C t))) = _
    rw [Ideal.Quotient.lift_mk, hevCC]
  · rw [RingHom.comp_apply, hfx]
    show lam0 (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hevCX]
  · rw [RingHom.comp_apply, hfy]
    show lam0 (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hevX]

theorem laurentEmbedding_mul_formalW (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    lam (xOverZ V.toProjective) * ofPS T V.formalW = ofPS T PowerSeries.X ∧
      lam (yOverZ V.toProjective) * ofPS T V.formalW = -1 := by
  have hFU : ofPS T V.formalW * ofPS T V.wUnitFactor = HahnSeries.single (1 : ℤ) (1 : T) ^ 3 := by
    rw [← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
  constructor
  · rw [hx, mul_comm, ← mul_assoc, hFU, single_neg_two, HahnSeries.ofPowerSeries_X]
    calc (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-1 : ℤ) (1 : T) ^ 2
        = HahnSeries.single (1 : ℤ) (1 : T) * (HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single (-1 : ℤ) (1 : T)) ^ 2 := by ring
      _ = HahnSeries.single (1 : ℤ) (1 : T) := by rw [single_one_mul_single_neg_one, one_pow, mul_one]
  · rw [hy, neg_mul, mul_comm, ← mul_assoc, hFU, single_one_pow_three_mul_single_neg_three]

theorem exists_laurentEmbedding (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t, Φ (cY V t) = PowerSeries.C t) (hΦx : Φ (xOverY V.toProjective) = -PowerSeries.X)
    (hΦz : Φ (zOverY V.toProjective) = -V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t, lam (cZ V t) = HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1 := by
  obtain ⟨lam, hc, hx, hy⟩ := exists_laurentEmbedding_core V
  obtain ⟨h1, h2⟩ := laurentEmbedding_mul_formalW V lam hx hy
  refine ⟨lam, hc, ?_, ?_⟩
  · rw [hΦz, hΦx, map_neg, map_neg, mul_neg, h1]
  · rw [hΦz, map_neg, mul_neg, h2, neg_neg]

theorem laurentEmbedding_unique (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦz : Φ (zOverY V.toProjective) = -V.formalW)
    (lam lam' : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)))
    (hy : lam (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1)
    (hc' : ∀ t, lam' (cZ V t) = HahnSeries.C t)
    (hx' : lam' (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)))
    (hy' : lam' (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1) : lam = lam' := by

  have hunit : IsUnit (ofPS T (Φ (zOverY V.toProjective))) := by
    rw [hΦz, map_neg, IsUnit.neg_iff]
    refine isUnit_iff_exists_inv.mpr ⟨ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T), ?_⟩
    rw [← mul_assoc, ← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X,
      single_one_pow_three_mul_single_neg_three]
  apply zChart_ringHom_ext V
  · exact RingHom.ext fun t => (hc t).trans (hc' t).symm
  · exact hunit.mul_right_cancel (hx.trans hx'.symm)
  · exact hunit.mul_right_cancel (hy.trans hy'.symm)

end embed

section lead
variable (V : WeierstrassCurve T)

theorem coeff_ofPS_mul_single (g : PowerSeries T) (k n : ℤ) :
    (ofPS T g * HahnSeries.single k (1 : T)).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs g := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  exact PowerSeries.coeff_coe g (n - k)

theorem laurentEmbedding_lead (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    (∀ n : ℤ, n < -2 → (lam (xOverZ V.toProjective)).coeff n = 0) ∧
      (lam (xOverZ V.toProjective)).coeff (-2) = 1 ∧
      (∀ n : ℤ, n < -3 → (lam (yOverZ V.toProjective)).coeff n = 0) ∧
      (lam (yOverZ V.toProjective)).coeff (-3) = -1 := by
  have h0 : PowerSeries.coeff 0 V.wUnitFactor = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact V.constantCoeff_wUnitFactor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hx, coeff_ofPS_mul_single, if_pos (by omega)]
  · rw [hx, coeff_ofPS_mul_single, if_neg (by norm_num)]
    norm_num
    exact V.constantCoeff_wUnitFactor
  · intro n hn
    rw [hy, HahnSeries.coeff_neg, coeff_ofPS_mul_single, if_pos (by omega), neg_zero]
  · rw [hy, HahnSeries.coeff_neg, coeff_ofPS_mul_single, if_neg (by norm_num)]
    norm_num
    exact V.constantCoeff_wUnitFactor

end lead

section extras
variable (V : WeierstrassCurve T)

theorem coeff_single_neg_mul_ofPS (k : ℕ) (γ : PowerSeries T) :
    (∀ n : ℤ, n < -(k : ℤ) → (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS T γ).coeff n = 0) ∧
      (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS T γ).coeff (-(k : ℤ)) = PowerSeries.constantCoeff γ := by
  constructor
  · intro n hn
    rw [mul_comm, coeff_ofPS_mul_single, if_pos (by omega)]
  · rw [mul_comm, coeff_ofPS_mul_single, if_neg (by omega), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    congr 1
    simp

theorem isUnit_ofPS_X : IsUnit (ofPS T PowerSeries.X) := by
  rw [HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_exists_inv.mpr ⟨HahnSeries.single (-1 : ℤ) (1 : T), single_one_mul_single_neg_one⟩

theorem isUnit_ofPS_of_isUnit {f : PowerSeries T} (hf : IsUnit f) : IsUnit (ofPS T f) := hf.map _

theorem exists_ringEquiv_zChartRing_coordinateRing :
    ∃ e : ZChartRing V.toProjective ≃+* (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine}),
      (∀ t, e (cZ V t) = Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C t))) ∧
      e (xOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X : Polynomial (Polynomial T)) ∧
      e (yOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.X : Polynomial (Polynomial T)) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  refine ⟨RingEquiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro t
    show f (cZ V t) = _
    rw [show f (cZ V t) = algebraMap T _ t from RingHom.congr_fun hcomp t,
      IsScalarTower.algebraMap_apply T (Polynomial (Polynomial T)), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · show f _ = _
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this
  · show f _ = _
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this

end extras

section filtration
variable (V : WeierstrassCurve T)

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem single_mul_eval₂_xL (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p : Polynomial T) (d : ℕ)
    (hd : p.natDegree ≤ d) :
    ∃ G : PowerSeries T,
      HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) *
          Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) p
        = ofPS T G ∧ PowerSeries.constantCoeff G = p.coeff d := by
  classical
  refine ⟨∑ i ∈ Finset.range (d + 1), PowerSeries.C (p.coeff i) * u ^ i * PowerSeries.X ^ (2 * (d - i)), ?_, ?_⟩
  · rw [Polynomial.eval₂_eq_sum, Polynomial.sum_over_range' _ _ (d + 1) (by omega), Finset.mul_sum, map_sum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hid : i ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
      rw [map_mul, map_mul, map_pow, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, mul_pow,
        single_neg_two, ← pow_mul]

      have hZ : (HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) : LaurentSeries T)
          = HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i) := by
        rw [← pow_add, HahnSeries.single_pow, one_pow]
        congr 1
        have : 2 * (d - i) + 2 * i = 2 * d := by omega
        rw [this]
        simp
      rw [hZ]
      have hpm : (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ (2 * i) * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i) = 1 := by
        rw [← mul_pow, single_one_mul_single_neg_one, one_pow]
      calc HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i)
            * (HahnSeries.C (p.coeff i) * ((ofPS T u) ^ i * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i)))
          = HahnSeries.C (p.coeff i) * (ofPS T u) ^ i * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i))
            * (HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i) * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i)) := by ring
        _ = HahnSeries.C (p.coeff i) * (ofPS T u) ^ i * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) := by
          rw [hpm, mul_one]
    · intro n; simp
  · rw [map_sum]
    rw [Finset.sum_eq_single d]
    · simp [hu]
    · intro i hi hne
      have hid : i < d := lt_of_le_of_ne (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) hne
      have : 2 * (d - i) ≠ 0 := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h

theorem coeff_neg_of_single_mul_eq_ofPS {N : ℕ} {f : LaurentSeries T} {G : PowerSeries T}
    (h : HahnSeries.single (N : ℤ) (1 : T) * f = ofPS T G) : f.coeff (-(N : ℤ)) = PowerSeries.constantCoeff G := by
  have := congrArg (fun g : LaurentSeries T => g.coeff 0) h
  rw [show (0 : ℤ) = -(N : ℤ) + N by ring, HahnSeries.coeff_single_mul_add, one_mul] at this
  rw [this, show -(N : ℤ) + N = ((0 : ℕ) : ℤ) by simp, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end filtration

section filtration2
variable (V : WeierstrassCurve T)

theorem single_mul_eval₂_xL_mul_yL (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (q : Polynomial T) (d : ℕ)
    (hd : q.natDegree ≤ d) :
    ∃ G : PowerSeries T,
      HahnSeries.single ((2 * d + 3 : ℕ) : ℤ) (1 : T) *
          (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
            * -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T)))
        = ofPS T G ∧ PowerSeries.constantCoeff G = -q.coeff d := by
  obtain ⟨G, hG, hG0⟩ := single_mul_eval₂_xL u hu q d hd
  refine ⟨-(G * u), ?_, by rw [map_neg, map_mul, hG0, hu, mul_one]⟩
  have hsplit : (HahnSeries.single ((2 * d + 3 : ℕ) : ℤ) (1 : T) : LaurentSeries T)
      = HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) * HahnSeries.single (3 : ℤ) (1 : T) := by
    rw [HahnSeries.single_mul_single, mul_one]
    norm_num
  have h33 : (HahnSeries.single (3 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-3 : ℤ) (1 : T) = 1 := by
    rw [HahnSeries.single_mul_single, mul_one]; norm_num
  rw [hsplit, map_neg, map_mul, ← hG]
  calc HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) * HahnSeries.single (3 : ℤ) (1 : T)
        * (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T)))
      = -(HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T)
          * Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * ofPS T u * (HahnSeries.single (3 : ℤ) (1 : T) * HahnSeries.single (-3 : ℤ) (1 : T))) := by ring
    _ = _ := by rw [h33, mul_one]

theorem laurentEmbedding_normalForm (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)))
    (a : ZChartRing V.toProjective) :
    ∃ p q : Polynomial T,
      a = Polynomial.eval₂ (cZ V) (xOverZ V.toProjective) p + Polynomial.eval₂ (cZ V) (xOverZ V.toProjective) q * yOverZ V.toProjective ∧
      lam a = Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) p
        + Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) := by
  classical
  obtain ⟨e, hec, hex, hey⟩ := exists_ringEquiv_zChartRing_coordinateRing V

  let evB : Polynomial (Polynomial T) →+* ZChartRing V.toProjective :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (cZ V) (xOverZ V.toProjective)) (yOverZ V.toProjective)
  have hfacB : e.symm.toRingHom.comp (Ideal.Quotient.mk _) = evB := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · refine RingHom.ext fun t => ?_
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C]
        apply e.injective; rw [RingEquiv.apply_symm_apply]; exact (hec t).symm
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C, Polynomial.eval₂_X]
        apply e.injective; rw [RingEquiv.apply_symm_apply, hex]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      apply e.injective; rw [RingEquiv.apply_symm_apply, hey]
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := V.toAffine) (e a)
  have hpq' : e a = Ideal.Quotient.mk _ (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
    rw [← hpq, WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one,
      map_add, map_mul]
    rfl
  have ha : a = evB (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
    rw [← hfacB, RingHom.comp_apply, ← hpq']
    simp
  refine ⟨p, q, ?_, ?_⟩
  · rw [ha]
    simp only [evB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
  · rw [ha]
    simp only [evB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, map_add, map_mul, hy]
    congr 2 <;> rw [Polynomial.hom_eval₂, hx] <;> congr 1 <;> exact RingHom.ext hc

end filtration2

section filtration3
variable (V : WeierstrassCurve T)

theorem coeff_of_single_mul_eq_ofPS {K : ℕ} {f : LaurentSeries T} {G : PowerSeries T}
    (h : HahnSeries.single (K : ℤ) (1 : T) * f = ofPS T G) :
    (∀ n : ℤ, n < -(K : ℤ) → f.coeff n = 0) ∧ f.coeff (-(K : ℤ)) = PowerSeries.constantCoeff G := by
  have hf : f = HahnSeries.single (-(K : ℤ)) (1 : T) * ofPS T G := by
    rw [← h, ← mul_assoc, HahnSeries.single_mul_single, mul_one, neg_add_cancel, HahnSeries.single_zero_one, one_mul]
  rw [hf]
  exact coeff_single_neg_mul_ofPS K G

abbrev Ex (u : PowerSeries T) (p : Polynomial T) : LaurentSeries T :=
  Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) p

abbrev yLs (u : PowerSeries T) : LaurentSeries T := -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T))

theorem single_nat_eq_ofPS_X_pow (k : ℕ) :
    (HahnSeries.single (k : ℤ) (1 : T) : LaurentSeries T) = ofPS T (PowerSeries.X ^ k) := by
  rw [map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow]; simp

theorem coeff_even (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p q : Polynomial T) (m : ℕ)
    (hp : p.natDegree ≤ m) (hq : q = 0 ∨ q.natDegree + 2 ≤ m) :
    (Ex u p + Ex u q * yLs u).coeff (-((2 * m : ℕ) : ℤ)) = p.coeff m := by
  obtain ⟨Gp, hGp, hGp0⟩ := single_mul_eval₂_xL u hu p m hp
  rw [HahnSeries.coeff_add, (coeff_of_single_mul_eq_ofPS hGp).2, hGp0]
  rcases hq with rfl | hq
  · simp
  · obtain ⟨Gq, hGq, -⟩ := single_mul_eval₂_xL_mul_yL u hu q (m - 2) (by omega)
    have hvan := (coeff_of_single_mul_eq_ofPS hGq).1 (-((2 * m : ℕ) : ℤ)) (by push_cast; omega)
    rw [hvan, add_zero]

theorem coeff_odd (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p q : Polynomial T) (m : ℕ)
    (hp : p.natDegree ≤ m + 1) (hq : q.natDegree ≤ m) :
    (Ex u p + Ex u q * yLs u).coeff (-((2 * m + 3 : ℕ) : ℤ)) = -q.coeff m := by
  obtain ⟨Gq, hGq, hGq0⟩ := single_mul_eval₂_xL_mul_yL u hu q m hq
  obtain ⟨Gp, hGp, -⟩ := single_mul_eval₂_xL u hu p (m + 2) (by omega)
  rw [HahnSeries.coeff_add, (coeff_of_single_mul_eq_ofPS hGq).2, hGq0]

  obtain ⟨Gp', hGp', -⟩ := single_mul_eval₂_xL u hu p (m + 1) hp
  have h' : HahnSeries.single ((2 * m + 3 : ℕ) : ℤ) (1 : T) * (Ex u p) = ofPS T (PowerSeries.X * Gp') := by
    have hs : (HahnSeries.single ((2 * m + 3 : ℕ) : ℤ) (1 : T) : LaurentSeries T)
        = HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single ((2 * (m + 1) : ℕ) : ℤ) (1 : T) := by
      rw [HahnSeries.single_mul_single, one_mul]; norm_num; ring
    rw [hs, mul_assoc, hGp', map_mul, HahnSeries.ofPowerSeries_X]
  rw [(coeff_of_single_mul_eq_ofPS h').2, map_mul, PowerSeries.constantCoeff_X, zero_mul, zero_add]

theorem laurentEmbedding_filtration (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ : T, a = cZ V c₁ * xOverZ V.toProjective + cZ V c₀ ∧ c₁ = (lam a).coeff (-2)) ∧
    (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ c₂ : T, a = cZ V c₂ * yOverZ V.toProjective + cZ V c₁ * xOverZ V.toProjective + cZ V c₀ ∧
        c₂ = -((lam a).coeff (-3))) := by
  classical
  have hu := V.constantCoeff_wUnitFactor

  have keyq : ∀ (p q : Polynomial T) (M : ℕ), (∀ n : ℤ, n < -(M : ℤ) → (Ex V.wUnitFactor p + Ex V.wUnitFactor q * yLs V.wUnitFactor).coeff n = 0) →
      q ≠ 0 → 2 * q.natDegree + 3 ≤ M := by
    intro p q M hvan hq0
    by_contra hlt
    push Not at hlt
    by_cases hpq : p.natDegree ≤ q.natDegree + 1
    · have h := coeff_odd V.wUnitFactor hu p q q.natDegree hpq le_rfl
      rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
      exact hq0 (Polynomial.leadingCoeff_eq_zero.mp (neg_eq_zero.mp h.symm))
    · push Not at hpq
      have hp0 : p ≠ 0 := by rintro rfl; simp at hpq
      have h := coeff_even V.wUnitFactor hu p q p.natDegree le_rfl (Or.inr (by omega))
      rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
      exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h.symm)
  have keyp : ∀ (p q : Polynomial T) (M : ℕ), (∀ n : ℤ, n < -(M : ℤ) → (Ex V.wUnitFactor p + Ex V.wUnitFactor q * yLs V.wUnitFactor).coeff n = 0) →
      (q = 0 ∨ q.natDegree + 2 ≤ 2) → M < 4 → p.natDegree ≤ 1 := by
    intro p q M hvan hq hM
    by_contra hlt
    push Not at hlt
    have hp0 : p ≠ 0 := by rintro rfl; simp at hlt
    have hq' : q = 0 ∨ q.natDegree + 2 ≤ p.natDegree := hq.imp id (fun h => by omega)
    have h := coeff_even V.wUnitFactor hu p q p.natDegree le_rfl hq'
    rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h.symm)
  constructor
  · intro a hvan
    obtain ⟨p, q, ha, hla⟩ := laurentEmbedding_normalForm V lam hc hx hy a
    rw [hla] at hvan
    have hq : q = 0 := by
      by_contra hq0
      have := keyq p q 2 (by exact_mod_cast hvan) hq0
      omega
    subst hq
    have hp : p.natDegree ≤ 1 := keyp p 0 2 (by exact_mod_cast hvan) (Or.inl rfl) (by norm_num)
    have hpeq := Polynomial.eq_X_add_C_of_natDegree_le_one hp
    refine ⟨p.coeff 0, p.coeff 1, ?_, ?_⟩
    · rw [ha, hpeq]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    · have h := coeff_even V.wUnitFactor hu p 0 1 hp (Or.inl rfl)
      rw [hla]
      exact_mod_cast h.symm
  · intro a hvan
    obtain ⟨p, q, ha, hla⟩ := laurentEmbedding_normalForm V lam hc hx hy a
    rw [hla] at hvan
    have hq : q.natDegree = 0 := by
      by_cases hq0 : q = 0
      · rw [hq0, Polynomial.natDegree_zero]
      · have := keyq p q 3 (by exact_mod_cast hvan) hq0
        omega
    have hp : p.natDegree ≤ 1 := keyp p q 3 (by exact_mod_cast hvan) (Or.inr (by omega)) (by norm_num)
    have hpeq := Polynomial.eq_X_add_C_of_natDegree_le_one hp
    have hqeq := Polynomial.eq_C_of_natDegree_eq_zero hq
    refine ⟨p.coeff 0, p.coeff 1, q.coeff 0, ?_, ?_⟩
    · rw [ha, hpeq, hqeq]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
      ring_nf
    · have h := coeff_odd V.wUnitFactor hu p q 0 (by omega) (by omega)
      rw [hla]
      have h2 : (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T)
            (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) p
          + Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T)
            (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) q
            * -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))).coeff (-3) = -q.coeff 0 := by
        simpa using h
      rw [h2, neg_neg]

end filtration3

end WMLocal

end

theorem solution
    (T : Type u) [CommRing T] (V : WeierstrassCurve T)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t : T, lam (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
        HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) =
        HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) = 1 ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₁ = (lam a).coeff (-2)) ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ c₂ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₂) *
            yOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₂ = -((lam a).coeff (-3))) := by
  obtain ⟨lam, hc, hx, hy⟩ := WMLocal.exists_laurentEmbedding_core V
  obtain ⟨h1, h2⟩ := WMLocal.laurentEmbedding_mul_formalW V lam hx hy
  obtain ⟨hF2, hF3⟩ := WMLocal.laurentEmbedding_filtration V lam hc hx hy
  refine ⟨lam, hc, ?_, ?_, hF2, hF3⟩
  · rw [hΦz, hΦx, map_neg, map_neg, mul_neg, h1]
  · rw [hΦz, map_neg, mul_neg, h2, neg_neg]

end Filtration

namespace Laurent


set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace OverlapAux

section Away

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

noncomputable abbrev toOverlapY : OriginChartRing V →+* Away (projModelGradingCR V) (coord V 1 * coord V 2) :=
  awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)

noncomputable abbrev toOverlapZ : ZChartRing V →+* Away (projModelGradingCR V) (coord V 1 * coord V 2) :=
  awayMap (projModelGradingCR V) (coord_mem V 1)
    ((rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2).trans (mul_comm _ _))

theorem overlap_identities :
    toOverlapZ V (xOverZ V) * toOverlapY V (zOverY V) = toOverlapY V (xOverY V) ∧
    toOverlapZ V (yOverZ V) * toOverlapY V (zOverY V) = 1 := by
  constructor
  · unfold toOverlapZ toOverlapY xOverZ zOverY xOverY
    rw [awayMap_mk, awayMap_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one]
    ring
  · unfold toOverlapZ toOverlapY yOverZ zOverY
    rw [awayMap_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, Away.val_mk, Localization.mk_mul]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one, mul_one]
    ring

theorem exists_overlap_hom_of_specMap_comp_eq {S : Type u} [CommRing S]
    (a : OriginChartRing V →+* S) (b : ZChartRing V →+* S)
    (h : Spec.map (CommRingCat.ofHom a) ≫ originChartι V = Spec.map (CommRingCat.ofHom b) ≫ zChartι V) :
    ∃ c : Away (projModelGradingCR V) (coord V 1 * coord V 2) →+* S,
      c.comp (toOverlapY V) = a ∧ c.comp (toOverlapZ V) = b := by
  let P := pullback.lift (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) h
  let e := Proj.pullbackAwayιIso (projModelGradingCR V) (coord_mem V 1) one_pos (coord_mem V 2) one_pos
    (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)
  obtain ⟨c, hc⟩ := Spec.map_surjective (P ≫ e.hom)
  have ha : Spec.map c ≫ Spec.map (CommRingCat.ofHom (toOverlapY V)) = Spec.map (CommRingCat.ofHom a) := by
    rw [hc, Category.assoc]
    erw [Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left]
    exact pullback.lift_fst _ _ _
  have hb : Spec.map c ≫ Spec.map (CommRingCat.ofHom (toOverlapZ V)) = Spec.map (CommRingCat.ofHom b) := by
    rw [hc, Category.assoc]
    erw [Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right]
    exact pullback.lift_snd _ _ _
  rw [← Spec.map_comp] at ha hb
  have ha' := Spec.map_injective ha
  have hb' := Spec.map_injective hb
  refine ⟨c.hom, ?_, ?_⟩
  · ext r; exact congrArg (fun φ => φ.hom r) ha'
  · ext r; exact congrArg (fun φ => φ.hom r) hb'

theorem zChart_mul_originChart_of_specMap_comp_eq {S : Type u} [CommRing S]
    (a : OriginChartRing V →+* S) (b : ZChartRing V →+* S)
    (h : Spec.map (CommRingCat.ofHom a) ≫ originChartι V = Spec.map (CommRingCat.ofHom b) ≫ zChartι V) :
    b (xOverZ V) * a (zOverY V) = a (xOverY V) ∧ b (yOverZ V) * a (zOverY V) = 1 := by
  obtain ⟨c, hca, hcb⟩ := exists_overlap_hom_of_specMap_comp_eq V a b h
  obtain ⟨h1, h2⟩ := overlap_identities V
  subst hca hcb
  simp only [RingHom.comp_apply]
  refine ⟨?_, ?_⟩
  · calc c (toOverlapZ V (xOverZ V)) * c (toOverlapY V (zOverY V))
        = c (toOverlapZ V (xOverZ V) * toOverlapY V (zOverY V)) := (map_mul c _ _).symm
      _ = c (toOverlapY V (xOverY V)) := congrArg c h1
  · calc c (toOverlapZ V (yOverZ V)) * c (toOverlapY V (zOverY V))
        = c (toOverlapZ V (yOverZ V) * toOverlapY V (zOverY V)) := (map_mul c _ _).symm
      _ = c 1 := congrArg c h2
      _ = 1 := map_one c

end Away

end OverlapAux

namespace OverlapAux

section Str

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

noncomputable def zStr : T →+* ZChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

noncomputable def oStr : T →+* OriginChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

theorem zChartι_comp_projModelStrCR : zChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (zStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem originChartι_comp_projModelStrCR :
    originChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (oStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem zChart_ringHom_ext {B : Type u} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (zStr V) = g₂.comp (zStr V))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = zStr V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

end Str

section Laurent

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  unfold Away.isLocalizationElem zOverY
  congr 1
  exact pow_one _

theorem specMap_comp_zChartι_eq_of_laurent
    (Φ : OriginChartRing V →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t)) =
      PowerSeries.C t)
    (lam : ZChartRing V →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ V) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V)))
    (hlamy : lam (yOverZ V) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)) = 1)
    (hunit : IsUnit (HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)))) :
    Spec.map (CommRingCat.ofHom lam) ≫ zChartι V =
      Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ T).comp Φ)) ≫ originChartι V := by
  classical
  set a : OriginChartRing V →+* LaurentSeries T := (HahnSeries.ofPowerSeries ℤ T).comp Φ with ha

  have hrange : Set.range (Spec.map (CommRingCat.ofHom a) ≫ originChartι V).base ⊆ Set.range (zChartι V).base := by
    rintro _ ⟨p, rfl⟩
    have hmem : (Spec.map (CommRingCat.ofHom a)).base p ∈
        originChartι V ⁻¹ᵁ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
      rw [Proj.awayι_preimage_basicOpen _ _ _ (coord_mem V 2) one_pos, isLocalizationElem_eq_zOverY]
      show a (zOverY V) ∉ p.asIdeal
      exact fun h => p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hunit)
    have : (originChartι V).base ((Spec.map (CommRingCat.ofHom a)).base p) ∈ (zChartι V).opensRange := by
      rw [Proj.opensRange_awayι]; exact hmem
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp this
    exact ⟨y, by rw [Scheme.Hom.comp_base]; exact hy⟩

  obtain ⟨μ, hμ⟩ := Spec.map_surjective
    (IsOpenImmersion.lift (zChartι V) (Spec.map (CommRingCat.ofHom a) ≫ originChartι V) hrange)
  have hfac : Spec.map μ ≫ zChartι V = Spec.map (CommRingCat.ofHom a) ≫ originChartι V := by
    rw [hμ]; exact IsOpenImmersion.lift_fac _ _ _

  have hμlam : μ.hom = lam := by
    apply zChart_ringHom_ext V
    ·
      have h1 := congrArg (· ≫ projModelStrCR V) hfac
      simp only [Category.assoc, zChartι_comp_projModelStrCR, originChartι_comp_projModelStrCR, ← Spec.map_comp] at h1
      have h2 := Spec.map_injective h1
      refine RingHom.ext fun t => ?_
      have h3 := congrArg (fun φ => φ.hom t) h2
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h3
      rw [RingHom.comp_apply, RingHom.comp_apply, h3]
      have e1 : a (oStr V t) = HahnSeries.C t := by
        show HahnSeries.ofPowerSeries ℤ T
          (Φ (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t))) = _
        rw [hΦc, HahnSeries.ofPowerSeries_C]
      have e2 : lam (zStr V t) = HahnSeries.C t := hlamc t
      rw [e1, e2]
    · obtain ⟨e1, -⟩ := zChart_mul_originChart_of_specMap_comp_eq V a μ.hom hfac.symm
      have : μ.hom (xOverZ V) * a (zOverY V) = lam (xOverZ V) * a (zOverY V) := by rw [e1, ha]; exact hlamx.symm
      exact hunit.mul_right_cancel this
    · obtain ⟨-, e2⟩ := zChart_mul_originChart_of_specMap_comp_eq V a μ.hom hfac.symm
      have : μ.hom (yOverZ V) * a (zOverY V) = lam (yOverZ V) * a (zOverY V) := by rw [e2, ha]; exact hlamy.symm
      exact hunit.mul_right_cancel this
  have : CommRingCat.ofHom lam = μ := by rw [← hμlam]; rfl
  rw [this, hfac]

end Laurent

end OverlapAux

namespace WMLocal

section Cover

open MvPolynomial TopologicalSpace

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

section ZeroSection

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev cY : T →+* OriginChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem not_mem_basicOpen_iff_mem_range_kwZeroSect (x : ↥(projModelCR W.toProjective)) :
    x ∉ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) ↔
      x ∈ Set.range (kwZeroSect T W).1 := by
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let χ₀ := kwYChartEval T W
  have hχc : ∀ t, χ₀ (cY W t) = t := fun t => RingHom.congr_fun (kwYChartEval_section T W) t
  have hpre : originChartι W.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) =
      PrimeSpectrum.basicOpen (zOverY W.toProjective) := by
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) one_pos
      (coord_mem W.toProjective 2) one_pos, isLocalizationElem_eq_zOverY]
  constructor
  · intro hx

    have hx1 : x ∈ (originChartι W.toProjective).opensRange := by
      rw [Proj.opensRange_awayι]
      exact (mem_basicOpen_or W.toProjective x).elim id fun h => absurd h hx
    obtain ⟨p, rfl⟩ := hx1

    have hz : zOverY W.toProjective ∈ p.asIdeal := by
      by_contra h
      have hp : p ∈ originChartι W.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
        rw [hpre]; exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
      exact hx hp
    have hrel := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      exact WeierstrassCurve.DrinfeldGlobal.originChart_rel W (RingHom.id _) (fun t => rfl)
    simp only [RingHom.id_apply] at hrel
    have hx3 : xOverY W.toProjective ^ 3 ∈ p.asIdeal := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      have : xOverY W.toProjective ^ 3 =
          zOverY W.toProjective * (1 + algebraMap T _ W.a₁ * xOverY W.toProjective +
            algebraMap T _ W.a₃ * zOverY W.toProjective - algebraMap T _ W.a₂ * xOverY W.toProjective ^ 2 -
            algebraMap T _ W.a₄ * xOverY W.toProjective * zOverY W.toProjective -
            algebraMap T _ W.a₆ * zOverY W.toProjective ^ 2) := by
        linear_combination (-1 : OriginChartRing W.toProjective) * hrel
      rw [this]
      exact Ideal.mul_mem_right _ _ hz
    have hxm : xOverY W.toProjective ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 hx3

    have hker : RingHom.ker χ₀ ≤ p.asIdeal := by
      rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hχc, hχx, hχz, map_zero, map_zero,
        sub_zero, sub_zero, Ideal.span_le]
      rintro a (rfl | rfl)
      · exact hxm
      · exact hz
    let t : ↥(Spec (CommRingCat.of T)) := Spec.map (CommRingCat.ofHom (cY W)) p
    have hpt : Spec.map (CommRingCat.ofHom χ₀) t = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap χ₀ (Ideal.comap (cY W) p.asIdeal) = p.asIdeal
      ext a
      simp only [Ideal.mem_comap]
      have hdiff : a - cY W (χ₀ a) ∈ p.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hχc, sub_self])
      constructor
      · intro h
        have := p.asIdeal.add_mem hdiff h
        rwa [sub_add_cancel] at this
      · intro h
        have := p.asIdeal.sub_mem h hdiff
        rwa [sub_sub_cancel] at this
    refine ⟨t, ?_⟩
    rw [hO', Scheme.Hom.comp_apply, hpt]
  · rintro ⟨t, rfl⟩ hmem
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have : Spec.map (CommRingCat.ofHom χ₀) t ∈ originChartι W.toProjective ⁻¹ᵁ
        Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := hmem
    rw [hpre] at this
    refine (PrimeSpectrum.mem_basicOpen _ _).mp this ?_
    change χ₀ (zOverY W.toProjective) ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

end ZeroSection

section Restrict

variable {T : Type u} [CommRing T] (W W' : WeierstrassCurve T)

noncomputable abbrev cZ : T →+* ZChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem zChartι_comp_projModelStrCR :
    zChartι W.toProjective ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom (cZ W)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem preimage_opensRange_zChartι (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange = (zChartι W.toProjective).opensRange := by
  ext x
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  change Ψ.hom x ∈ Proj.basicOpen (projModelGradingCR W'.toProjective) (coord W'.toProjective 2) ↔
    x ∈ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2)
  rw [← not_iff_not, not_mem_basicOpen_iff_mem_range_kwZeroSect W', not_mem_basicOpen_iff_mem_range_kwZeroSect W]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hinj : Function.Injective Ψ.hom := (Scheme.homeoOfIso Ψ).injective
    apply hinj
    rw [← ht, ← Scheme.Hom.comp_apply, hΨO]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [← Scheme.Hom.comp_apply, hΨO]⟩

theorem exists_ringEquiv_zChartRing_of_iso (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (cZ W' t) = cZ W t) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by

  have hrange : Set.range (zChartι W.toProjective ≫ Ψ.hom) = Set.range (zChartι W'.toProjective) := by
    have h := preimage_opensRange_zChartι W W' Ψ hΨO
    have hsurj : Function.Surjective Ψ.hom := (Scheme.homeoOfIso Ψ).surjective
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      have : zChartι W.toProjective p ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        rw [h]; exact ⟨p, rfl⟩
      simpa [Scheme.Hom.comp_apply] using this
    · rintro ⟨p', rfl⟩
      obtain ⟨x, hx⟩ := hsurj (zChartι W'.toProjective p')
      have : x ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        show Ψ.hom x ∈ (zChartι W'.toProjective).opensRange
        rw [hx]; exact ⟨p', rfl⟩
      rw [h] at this
      obtain ⟨p, rfl⟩ := this
      exact ⟨p, by rw [Scheme.Hom.comp_apply, hx]⟩
  let δ : Spec (CommRingCat.of (ZChartRing W.toProjective)) ≅ Spec (CommRingCat.of (ZChartRing W'.toProjective)) :=
    IsOpenImmersion.isoOfRangeEq (zChartι W.toProjective ≫ Ψ.hom) (zChartι W'.toProjective) hrange
  have hδ : δ.hom ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange

  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective δ.hom
  obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective δ.inv
  have h12 : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.hom_inv_id, Spec.map_id])
  have h21 : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.inv_hom_id, Spec.map_id])
  let e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective :=
    RingEquiv.ofRingHom φ₁.hom φ₂.hom (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h12 a)
      (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h21 a)
  have he : CommRingCat.ofHom e.toRingHom = φ₁ := rfl
  refine ⟨e, ?_, by rw [he, hφ₁, hδ]⟩

  have h2 : Spec.map φ₁ ≫ Spec.map (CommRingCat.ofHom (cZ W')) = Spec.map (CommRingCat.ofHom (cZ W)) := by
    rw [← zChartι_comp_projModelStrCR W', hφ₁, ← Category.assoc, hδ, Category.assoc, hΨ, zChartι_comp_projModelStrCR W]
  have h3 : CommRingCat.ofHom (cZ W') ≫ φ₁ = CommRingCat.ofHom (cZ W) :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  intro t
  have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (ZChartRing W.toProjective) => f.hom t) h3
  change φ₁.hom (cZ W' t) = cZ W t at this
  exact this

end Restrict

section FormalPoint

variable {T : Type u} [CommRing T] [IsLocalRing T] (W W' : WeierstrassCurve T)

omit [IsLocalRing T] in
theorem originChartι_comp_projModelStrCR (V : WeierstrassCurve T) :
    originChartι V.toProjective ≫ projModelStrCR V.toProjective = Spec.map (CommRingCat.ofHom (cY V)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_formalChart_of_iso
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY W t) = PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW) :
    ∃ χ' : OriginChartRing W'.toProjective →+* PowerSeries T,
      (∀ t : T, χ' (cY W' t) = PowerSeries.C t) ∧
      PowerSeries.constantCoeff (χ' (xOverY W'.toProjective)) = 0 ∧
      PowerSeries.constantCoeff (χ' (zOverY W'.toProjective)) = 0 ∧
      Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective =
        Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom := by
  haveI : IsLocalRing (PowerSeries T) := inferInstanceAs (IsLocalRing (MvPowerSeries Unit T))
  obtain ⟨hO', hχx', hχz'⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W'.toProjective
  have hO'' : (kwZeroSect T W').1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W')) ≫ originChartι W'.toProjective := hO'
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hOW : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let P : Spec (CommRingCat.of (PowerSeries T)) ⟶ projModelCR W'.toProjective :=
    Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom

  have hred : (PowerSeries.constantCoeff (R := T)).comp Φ = kwYChartEval T W := by
    apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W
    · intro t
      have h := hΦc t
      have h2 := RingHom.congr_fun (kwYChartEval_section T W) t
      simp only [RingHom.comp_apply, RingHom.id_apply] at h h2
      rw [RingHom.comp_apply, h, PowerSeries.constantCoeff_C]
      exact h2.symm
    · rw [RingHom.comp_apply, hΦx, map_neg, PowerSeries.constantCoeff_X, neg_zero]; exact hχx.symm
    · rw [RingHom.comp_apply, hΦz, map_neg, WeierstrassCurve.constantCoeff_formalW, neg_zero]; exact hχz.symm

  have hrange : Set.range P ⊆ Set.range (originChartι W'.toProjective) := by

    let c := IsLocalRing.closedPoint (PowerSeries T)
    have hc : P c ∈ Set.range (originChartι W'.toProjective) := by

      have hcc : Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := T))) (IsLocalRing.closedPoint T) = c := by
        apply PrimeSpectrum.ext
        change Ideal.comap (PowerSeries.constantCoeff (R := T)) (IsLocalRing.maximalIdeal T) =
          IsLocalRing.maximalIdeal (PowerSeries T)
        haveI : IsLocalHom (PowerSeries.constantCoeff (R := T)) :=
          ⟨fun a ha => (PowerSeries.isUnit_iff_constantCoeff).mpr ha⟩
        exact congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := T)))
      have h1 : P c = ((kwZeroSect T W).1 ≫ Ψ.hom) (IsLocalRing.closedPoint T) := by
        rw [← hcc, hOW]
        simp only [P, ← Scheme.Hom.comp_apply, Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hred]
      rw [h1, hΨO, hO'', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rintro _ ⟨z, rfl⟩
    have hz : z ⤳ c := (PrimeSpectrum.le_iff_specializes z c).mp (IsLocalRing.le_maximalIdeal z.isPrime.ne_top)
    have hPz : P z ⤳ P c := hz.map P.continuous
    have hopen : IsOpen (Set.range (originChartι W'.toProjective)) := (originChartι W'.toProjective).isOpenEmbedding.isOpen_range
    exact hPz.mem_open hopen hc

  let Q := IsOpenImmersion.lift (originChartι W'.toProjective) P hrange
  have hQ : Q ≫ originChartι W'.toProjective = P := IsOpenImmersion.lift_fac _ _ hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective Q

  have hmod : Spec.map (CommRingCat.ofHom ((PowerSeries.constantCoeff (R := T)).comp φ.hom)) ≫
      originChartι W'.toProjective = (kwZeroSect T W').1 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, show CommRingCat.ofHom φ.hom = φ from rfl, hφ, hQ]
    simp only [P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hred]
    rw [← hOW, hΨO]
  rw [hO''] at hmod
  have hmod' : (PowerSeries.constantCoeff (R := T)).comp φ.hom = kwYChartEval T W' := by
    have := Spec.map_injective ((cancel_mono (originChartι W'.toProjective)).mp hmod)
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨φ.hom, ?_, by rw [← RingHom.comp_apply, hmod']; exact hχx',
    by rw [← RingHom.comp_apply, hmod']; exact hχz', by rw [show CommRingCat.ofHom φ.hom = φ from rfl, hφ, hQ]⟩
  ·
    have h2 : Spec.map φ ≫ Spec.map (CommRingCat.ofHom (cY W')) = Spec.map (CommRingCat.ofHom (Φ.comp (cY W))) := by
      rw [← originChartι_comp_projModelStrCR W', hφ, ← Category.assoc, hQ]
      simp only [P, Category.assoc, hΨ]
      rw [originChartι_comp_projModelStrCR W, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : CommRingCat.ofHom (cY W') ≫ φ = CommRingCat.ofHom (Φ.comp (cY W)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact h2)
    intro t
    have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (PowerSeries T) => f.hom t) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    exact this.trans (hΦc t)

end FormalPoint

section Subst

variable {T : Type u} [CommRing T] [IsLocalRing T]

theorem formalChart_zOverY_eq (V : WeierstrassCurve T)
    (χ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hc : ∀ t : T, χ (cY V t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ (xOverY V.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ (zOverY V.toProjective)) = 0)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY V t) = PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    χ (zOverY V.toProjective) = - PowerSeries.subst (- χ (xOverY V.toProjective)) V.formalW := by
  haveI : IsLocalRing (PowerSeries T) := inferInstanceAs (IsLocalRing (MvPowerSeries Unit T))
  set α : PowerSeries T := - χ (xOverY V.toProjective) with hα
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0

  let ρ : OriginChartRing V.toProjective →+* PowerSeries T := (PowerSeries.substAlgHom (R := T) hαs).toRingHom.comp Φ
  have hρc : ∀ t : T, ρ (cY V t) = PowerSeries.C t := by
    intro t
    show PowerSeries.substAlgHom (R := T) hαs (Φ (cY V t)) = _
    rw [hΦc, PowerSeries.coe_substAlgHom, PowerSeries.subst_C]; rfl
  have hρx : ρ (xOverY V.toProjective) = χ (xOverY V.toProjective) := by
    show PowerSeries.substAlgHom (R := T) hαs (Φ (xOverY V.toProjective)) = _
    rw [hΦx, map_neg, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, hα, neg_neg]
  have hρz : ρ (zOverY V.toProjective) = - PowerSeries.subst α V.formalW := by
    show PowerSeries.substAlgHom (R := T) hαs (Φ (zOverY V.toProjective)) = _
    rw [hΦz, map_neg, PowerSeries.coe_substAlgHom]

  have mem_of_cc : ∀ f : PowerSeries T, PowerSeries.constantCoeff f = 0 → f ∈ IsLocalRing.maximalIdeal (PowerSeries T) := by
    intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, hf]
    exact not_isUnit_zero
  have h1 := WeierstrassCurve.DrinfeldGlobal.originChart_rel V χ
    (fun t => by change χ ((cY V) t) = _; rw [hc t, PowerSeries.algebraMap_eq])
  have h2 := WeierstrassCurve.DrinfeldGlobal.originChart_rel V ρ
    (fun t => by change ρ ((cY V) t) = _; rw [hρc t, PowerSeries.algebraMap_eq])
  rw [hρx, hρz] at h2
  rw [← hρz] at h2 ⊢
  refine WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal _ _ _ _ _ _ _ _
    (mem_of_cc _ hx0) (mem_of_cc _ hz0) (mem_of_cc _ ?_) h1 h2
  rw [hρz, map_neg, neg_eq_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hα0 _ V.constantCoeff_formalW

theorem formalChart_eq_subst_comp (V : WeierstrassCurve T)
    (χ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hc : ∀ t : T, χ (cY V t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ (xOverY V.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ (zOverY V.toProjective)) = 0)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY V t) = PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW)
    (hαs : PowerSeries.HasSubst (- χ (xOverY V.toProjective))) :
    χ = (PowerSeries.substAlgHom (R := T) hαs).toRingHom.comp Φ := by
  apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext V
  · intro t
    change χ (cY V t) = PowerSeries.substAlgHom (R := T) hαs (Φ (cY V t))
    rw [hc, hΦc, PowerSeries.coe_substAlgHom, PowerSeries.subst_C]; rfl
  · change _ = PowerSeries.substAlgHom (R := T) hαs (Φ (xOverY V.toProjective))
    rw [hΦx, map_neg, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, neg_neg]
  · change _ = PowerSeries.substAlgHom (R := T) hαs (Φ (zOverY V.toProjective))
    rw [hΦz, map_neg, PowerSeries.coe_substAlgHom, formalChart_zOverY_eq V χ hc hx0 hz0 Φ hΦc hΦx hΦz]

end Subst

section UnitCoeff

variable {T : Type u} [CommRing T] [IsLocalRing T] (W W' : WeierstrassCurve T)

theorem isUnit_coeff_one_formalChart
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY W t) = PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (Φ' : OriginChartRing W'.toProjective →+* PowerSeries T)
    (hΦc' : ∀ t : T, Φ' (cY W' t) = PowerSeries.C t)
    (hΦx' : Φ' (xOverY W'.toProjective) = - PowerSeries.X) (hΦz' : Φ' (zOverY W'.toProjective) = - W'.formalW)
    (χ' : OriginChartRing W'.toProjective →+* PowerSeries T)
    (hc' : ∀ t : T, χ' (cY W' t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ' (xOverY W'.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ' (zOverY W'.toProjective)) = 0)
    (hχ' : Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective =
        Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom) :
    IsUnit (PowerSeries.coeff 1 (χ' (xOverY W'.toProjective))) := by

  have hΨ' : Ψ.inv ≫ projModelStrCR W.toProjective = projModelStrCR W'.toProjective := by
    rw [← hΨ, Iso.inv_hom_id_assoc]
  have hΨO' : (kwZeroSect T W').1 ≫ Ψ.inv = (kwZeroSect T W).1 := by
    rw [← hΨO, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨χ'', hc'', hx0'', hz0'', hχ''⟩ := exists_formalChart_of_iso W' W Ψ.symm hΨ' hΨO' Φ' hΦc' hΦx' hΦz'
  simp only [Iso.symm_hom] at hχ''

  set α : PowerSeries T := - χ' (xOverY W'.toProjective) with hα
  set β : PowerSeries T := - χ'' (xOverY W.toProjective) with hβ
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hβ0 : PowerSeries.constantCoeff β = 0 := by rw [hβ, map_neg, hx0'', neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hβs : PowerSeries.HasSubst β := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have e1 := formalChart_eq_subst_comp W' χ' hc' hx0 hz0 Φ' hΦc' hΦx' hΦz' hαs
  have e2 := formalChart_eq_subst_comp W χ'' hc'' hx0'' hz0'' Φ hΦc hΦx hΦz hβs

  have key : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective =
      Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom) ≫
          Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective := by
    have h1 : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective =
        Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective ≫ Ψ.inv := by
      rw [← Category.assoc, hχ', Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : Spec.map (CommRingCat.ofHom χ') =
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫ Spec.map (CommRingCat.ofHom Φ') := by
      rw [e1, CommRingCat.ofHom_comp, Spec.map_comp]
    have h3 : Spec.map (CommRingCat.ofHom χ'') =
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom) ≫ Spec.map (CommRingCat.ofHom Φ) := by
      rw [e2, CommRingCat.ofHom_comp, Spec.map_comp]
    calc Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective
        = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective ≫ Ψ.inv := h1
      _ = Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom Φ') ≫ originChartι W'.toProjective ≫ Ψ.inv) := by
          rw [h2, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom χ'') ≫ originChartι W.toProjective) := by rw [hχ'']
      _ = _ := by rw [h3, Category.assoc]
  have key2 : CommRingCat.ofHom Φ =
      CommRingCat.ofHom Φ ≫ CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom ≫
        CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (originChartι W.toProjective)).mp
    simpa only [Spec.map_comp, Category.assoc] using key

  have hsub : PowerSeries.subst α β = PowerSeries.X := by
    have := congrArg (fun f : CommRingCat.of (OriginChartRing W.toProjective) ⟶ CommRingCat.of (PowerSeries T) =>
      f.hom (xOverY W.toProjective)) key2
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    rw [hΦx] at this
    change -PowerSeries.X = PowerSeries.substAlgHom (R := T) hαs (PowerSeries.substAlgHom (R := T) hβs (-PowerSeries.X)) at this
    rw [map_neg, map_neg, PowerSeries.coe_substAlgHom hβs, PowerSeries.subst_X hβs,
      PowerSeries.coe_substAlgHom hαs] at this
    exact (neg_inj.mp this).symm

  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hα0
  obtain ⟨b, hb⟩ := PowerSeries.X_dvd_iff.mpr hβ0
  have hprod : PowerSeries.X * (a * PowerSeries.subst α b) = PowerSeries.X * 1 := by
    calc PowerSeries.X * (a * PowerSeries.subst α b) = (PowerSeries.X * a) * PowerSeries.subst α b := by ring
      _ = PowerSeries.subst α (PowerSeries.X : PowerSeries T) * PowerSeries.subst α b := by rw [← ha, PowerSeries.subst_X hαs]
      _ = PowerSeries.subst α β := by rw [← PowerSeries.subst_mul hαs, ← hb]
      _ = PowerSeries.X * 1 := by rw [hsub, mul_one]
  have hone : a * PowerSeries.subst α b = 1 := by
    ext n
    have := congrArg (PowerSeries.coeff (n + 1)) hprod
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at this
  have hau : IsUnit a := ⟨⟨a, PowerSeries.subst α b, hone, (mul_comm _ _).trans hone⟩, rfl⟩
  have hcoeff : PowerSeries.coeff 1 (χ' (xOverY W'.toProjective)) = - PowerSeries.constantCoeff a := by
    have : χ' (xOverY W'.toProjective) = - (PowerSeries.X * a) := by rw [← ha, hα, neg_neg]
    rw [this, map_neg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hcoeff]
  exact ((PowerSeries.isUnit_iff_constantCoeff).mp hau).neg

end UnitCoeff

section LaurentCore

variable {T : Type u} [CommRing T]

local notation "ofPS" => HahnSeries.ofPowerSeries ℤ T

theorem single_one_mul_single_neg_one' :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-1 : ℤ) (1 : T) = 1 := by
  rw [HahnSeries.single_mul_single, mul_one]; norm_num

theorem coeff_ofPS_mul_single' (g : PowerSeries T) (k n : ℤ) :
    (ofPS g * HahnSeries.single k (1 : T)).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs g := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  exact PowerSeries.coeff_coe g (n - k)

theorem coeff_single_neg_mul_ofPS' (k : ℕ) (γ : PowerSeries T) :
    (∀ n : ℤ, n < -(k : ℤ) → (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS γ).coeff n = 0) ∧
      (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS γ).coeff (-(k : ℤ)) = PowerSeries.constantCoeff γ := by
  constructor
  · intro n hn
    rw [mul_comm, coeff_ofPS_mul_single', if_pos (by omega)]
  · rw [mul_comm, coeff_ofPS_mul_single', if_neg (by omega), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    congr 1
    simp

theorem laurent_core (α a w u : PowerSeries T) (hα : α = PowerSeries.X * a) (ha : IsUnit (PowerSeries.constantCoeff a))
    (hwu : w * u = PowerSeries.X ^ 3) (hu : PowerSeries.constantCoeff u = 1) (hαs : PowerSeries.HasSubst α)
    (Lx Ly : LaurentSeries T)
    (hx : Lx * HahnSeries.ofPowerSeries ℤ T (-(PowerSeries.subst α w)) = HahnSeries.ofPowerSeries ℤ T (-α))
    (hy : Ly * HahnSeries.ofPowerSeries ℤ T (-(PowerSeries.subst α w)) = 1) :
    (∀ n : ℤ, n < -2 → Lx.coeff n = 0) ∧ IsUnit (Lx.coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → Ly.coeff n = 0) ∧ IsUnit (Ly.coeff (-3)) := by

  have haU : IsUnit a := PowerSeries.isUnit_iff_constantCoeff.mpr ha
  have huU : IsUnit u := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hu]; exact isUnit_one)
  obtain ⟨ai, hai⟩ : ∃ ai, a * ai = 1 := ⟨↑haU.unit⁻¹, haU.mul_val_inv⟩
  set su := PowerSeries.subst α u with hsu
  have hsuU : IsUnit su := by rw [hsu, ← PowerSeries.coe_substAlgHom hαs]; exact huU.map _

  have hsw : PowerSeries.subst α w * su = PowerSeries.X ^ 3 * a ^ 3 := by
    rw [hsu, ← PowerSeries.subst_mul hαs, hwu, ← PowerSeries.coe_substAlgHom hαs, map_pow,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, hα, mul_pow]

  set Z : LaurentSeries T := HahnSeries.single (1 : ℤ) (1 : T) with hZ
  set Zi : LaurentSeries T := HahnSeries.single (-1 : ℤ) (1 : T) with hZi
  have hZZi : Z * Zi = 1 := single_one_mul_single_neg_one'
  have hofX : ofPS PowerSeries.X = Z := HahnSeries.ofPowerSeries_X
  have haai : ofPS a * ofPS ai = 1 := by rw [← map_mul, hai, map_one]

  have ex : Lx * (Z ^ 3 * ofPS a ^ 3) = Z * ofPS a * ofPS su := by
    have := congrArg (fun v => - v * ofPS su) hx
    simp only [map_neg, mul_neg, neg_neg, neg_mul] at this
    rw [mul_assoc, ← map_mul, hsw, map_mul, map_pow, map_pow, hofX, hα, map_mul, hofX] at this
    rw [this]
  have ey : Ly * (Z ^ 3 * ofPS a ^ 3) = - ofPS su := by
    have := congrArg (fun v => - v * ofPS su) hy
    simp only [map_neg, mul_neg, neg_neg, neg_mul, one_mul] at this
    rw [mul_assoc, ← map_mul, hsw, map_mul, map_pow, map_pow, hofX] at this
    rw [this]
  have hU : IsUnit (Z ^ 3 * ofPS a ^ 3) :=
    ((IsUnit.of_mul_eq_one Zi hZZi).pow 3).mul ((haU.map (HahnSeries.ofPowerSeries ℤ T)).pow 3)

  have hLx : Lx = HahnSeries.single (-2 : ℤ) (1 : T) * ofPS (su * ai ^ 2) := by
    apply hU.mul_right_cancel
    rw [ex]
    have : (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = Zi ^ 2 := by
      rw [hZi, HahnSeries.single_pow, one_pow]; norm_num
    rw [this, map_mul, map_pow]
    calc Z * ofPS a * ofPS su
        = Z * ofPS a * ofPS su * (Z * Zi) ^ 2 * (ofPS a * ofPS ai) ^ 2 := by rw [hZZi, haai]; ring
      _ = Zi ^ 2 * (ofPS su * ofPS ai ^ 2) * (Z ^ 3 * ofPS a ^ 3) := by ring
  have hLy : Ly = HahnSeries.single (-3 : ℤ) (1 : T) * ofPS (-(su * ai ^ 3)) := by
    apply hU.mul_right_cancel
    rw [ey]
    have : (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = Zi ^ 3 := by
      rw [hZi, HahnSeries.single_pow, one_pow]; norm_num
    rw [this, map_neg, map_mul, map_pow]
    calc - ofPS su = - ofPS su * (Z * Zi) ^ 3 * (ofPS a * ofPS ai) ^ 3 := by rw [hZZi, haai]; ring
      _ = Zi ^ 3 * -(ofPS su * ofPS ai ^ 3) * (Z ^ 3 * ofPS a ^ 3) := by ring

  have haiU : IsUnit (PowerSeries.constantCoeff ai) :=
    IsUnit.of_mul_eq_one (PowerSeries.constantCoeff a) (by rw [mul_comm, ← map_mul, hai, map_one])
  have hsu0 : IsUnit (PowerSeries.constantCoeff su) := PowerSeries.isUnit_iff_constantCoeff.mp hsuU
  obtain ⟨h2a, h2b⟩ := coeff_single_neg_mul_ofPS' (T := T) 2 (su * ai ^ 2)
  obtain ⟨h3a, h3b⟩ := coeff_single_neg_mul_ofPS' (T := T) 3 (-(su * ai ^ 3))
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_, ?_⟩
  · rw [hLx]; exact h2a n (by exact_mod_cast hn)
  · rw [hLx, show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, h2b, map_mul, map_pow]
    exact hsu0.mul (haiU.pow 2)
  · rw [hLy]; exact h3a n (by exact_mod_cast hn)
  · rw [hLy, show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, h3b, map_neg, map_mul, map_pow]
    exact (hsu0.mul (haiU.pow 3)).neg

end LaurentCore

section Glue

open OverlapAux

theorem w3_main
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) := by

  obtain ⟨Φ', hΦc', hΦx', hΦz'⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W'
  obtain ⟨χ', hc', hx0, hz0, hχ'⟩ := exists_formalChart_of_iso W W' Ψ hΨ hΨO Φ hΦc hΦx hΦz

  have hwU : IsUnit (HahnSeries.ofPowerSeries ℤ T W.formalW) := by
    have h3 : IsUnit (HahnSeries.ofPowerSeries ℤ T (W.formalW * W.wUnitFactor)) := by
      rw [W.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
      exact (IsUnit.of_mul_eq_one _ single_one_mul_single_neg_one').pow 3
    rw [map_mul] at h3
    exact isUnit_of_mul_isUnit_left h3
  have hunit : IsUnit (HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective))) := by
    rw [hΦz, map_neg]; exact hwU.neg
  have hO2 := OverlapAux.specMap_comp_zChartι_eq_of_laurent W.toProjective Φ hΦc lam hlamc hlamx hlamy hunit

  have hpt : Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ T).comp χ')) ≫ originChartι W'.toProjective =
      Spec.map (CommRingCat.ofHom (lam.comp e)) ≫ zChartι W'.toProjective := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hχ', CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, he, ← Category.assoc (Spec.map (CommRingCat.ofHom lam)), hO2, CommRingCat.ofHom_comp,
      Spec.map_comp]
    simp only [Category.assoc]
  obtain ⟨h1, h2⟩ := OverlapAux.zChart_mul_originChart_of_specMap_comp_eq W'.toProjective
    ((HahnSeries.ofPowerSeries ℤ T).comp χ') (lam.comp e) hpt
  simp only [RingHom.comp_apply] at h1 h2

  set α : PowerSeries T := - χ' (xOverY W'.toProjective) with hα
  have hξ : χ' (xOverY W'.toProjective) = - α := by rw [hα, neg_neg]
  have hζ : χ' (zOverY W'.toProjective) = - PowerSeries.subst α W'.formalW :=
    formalChart_zOverY_eq W' χ' hc' hx0 hz0 Φ' hΦc' hΦx' hΦz'
  rw [hξ, hζ] at h1
  rw [hζ] at h2
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hα0
  have haU : IsUnit (PowerSeries.constantCoeff a) := by
    have h := isUnit_coeff_one_formalChart W W' Ψ hΨ hΨO Φ hΦc hΦx hΦz Φ' hΦc' hΦx' hΦz' χ' hc' hx0 hz0 hχ'
    rw [hξ, ha, map_neg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    simpa using h
  exact laurent_core α a W'.formalW W'.wUnitFactor ha haU W'.formalW_mul_wUnitFactor W'.constantCoeff_wUnitFactor hαs
    _ _ h1 h2

end Glue

end WMLocal

theorem solution
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) :=
  WMLocal.w3_main T W W' Ψ hΨ hΨO e he Φ hΦc hΦx hΦz lam hlamc hlamx hlamy

end Laurent

namespace Extensionality


set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DenseExtAux

section Affine

theorem specMap_appTop_injective {B B' : Type u} [CommRing B] [CommRing B'] (l : B →+* B') (hl : Function.Injective l) :
    Function.Injective (Spec.map (CommRingCat.ofHom l)).appTop := by
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom l)

  intro a b hab
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom l =
      (Spec.map (CommRingCat.ofHom l)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom := hnat.symm
  have h2 := congrArg (fun φ => φ.hom a) h1
  have h3 := congrArg (fun φ => φ.hom b) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  rw [hab] at h2
  have h4 : l ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom a) = l ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom b) := by
    rw [h2, h3]
  have h5 := hl h4
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1
  exact hinj h5

theorem hom_ext_of_specMap_comp_eq_of_injective {B B' : Type u} [CommRing B] [CommRing B']
    {Y : Scheme.{u}} [Y.IsSeparated] (u v : Spec (CommRingCat.of B) ⟶ Y)
    (l : B →+* B') (hl : Function.Injective l)
    (h : Spec.map (CommRingCat.ofHom l) ≫ u = Spec.map (CommRingCat.ofHom l) ≫ v) : u = v := by
  let e := equalizer.ι u v
  let k := equalizer.lift (Spec.map (CommRingCat.ofHom l)) h
  have hk : k ≫ e = Spec.map (CommRingCat.ofHom l) := equalizer.lift_ι _ _
  have hinj : Function.Injective e.appTop := by
    have h1 := specMap_appTop_injective l hl
    rw [← hk, Scheme.Hom.comp_appTop] at h1
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h1
    exact h1.of_comp
  haveI : IsIso e := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  rw [← cancel_epi e]
  exact equalizer.condition u v

end Affine

section NZD

open MvPolynomial in

theorem mem_span_of_X_one_mul_mem {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)
    (p : MvPolynomial (Fin 2) T)
    (hp : X 1 * p ∈ Ideal.span {MvPolynomial.aeval
        (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial}) :
    p ∈ Ideal.span {MvPolynomial.aeval
        (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial} := by
  classical
  set F : MvPolynomial (Fin 2) T := MvPolynomial.aeval
        (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial with hF
  let e := MvPolynomial.finSuccEquiv T 1

  set z : MvPolynomial (Fin 1) T := MvPolynomial.X 0 with hz
  set g : Polynomial (MvPolynomial (Fin 1) T) :=
    Polynomial.X ^ 3 + Polynomial.C (MvPolynomial.C V.a₂ * z) * Polynomial.X ^ 2
      + Polynomial.C (MvPolynomial.C V.a₄ * z ^ 2 - MvPolynomial.C V.a₁ * z) * Polynomial.X
      + Polynomial.C (MvPolynomial.C V.a₆ * z ^ 3 - z - MvPolynomial.C V.a₃ * z ^ 2) with hg
  have heF : e F = -g := by
    rw [hF, hg, hz, WeierstrassCurve.Projective.polynomial]
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      MvPolynomial.algebraMap_eq]
    have e0 : e (MvPolynomial.X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
    have e1 : e (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by
      have := @MvPolynomial.finSuccEquiv_X_succ T _ 1 (0 : Fin 1)
      simpa using this
    have eC : ∀ a : T, e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := fun a => by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; rfl
    simp only [e0, e1, eC, map_one]
    try simp only [map_sub, map_mul, map_pow, map_add, Polynomial.C_mul, Polynomial.C_pow]
    ring
  have hgm : g.Monic := by
    rw [hg]
    monicity!

  have hmap : (Ideal.span {F}).map (e : MvPolynomial (Fin 2) T →+* _) = Ideal.span {g} := by
    rw [Ideal.map_span, Set.image_singleton]
    show Ideal.span {e F} = _
    rw [heF, Ideal.span_singleton_neg]
  have hp' : Polynomial.C z * e p ∈ Ideal.span {g} := by
    have : e (MvPolynomial.X 1 * p) ∈ (Ideal.span {F}).map (e : MvPolynomial (Fin 2) T →+* _) :=
      Ideal.mem_map_of_mem _ hp
    rw [hmap, map_mul] at this
    have e1 : e (MvPolynomial.X 1) = Polynomial.C z := by
      have := @MvPolynomial.finSuccEquiv_X_succ T _ 1 (0 : Fin 1)
      simpa [hz] using this
    rwa [e1] at this

  rw [Ideal.mem_span_singleton] at hp'
  have h0 : (Polynomial.C z * e p) %ₘ g = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hgm).mpr hp'
  rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic] at h0
  have h1 : e p %ₘ g = 0 := by
    refine Polynomial.ext fun n => ?_
    have hc := congrArg (fun r => Polynomial.coeff r n) h0
    simp only [Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] at hc
    rw [Polynomial.coeff_zero]
    have hreg : IsLeftRegular z := by rw [hz]; exact (MvPolynomial.isRegular_X).left
    exact hreg (show z * _ = z * 0 by rw [mul_zero]; exact hc)
  have h2 : g ∣ e p := (Polynomial.modByMonic_eq_zero_iff_dvd hgm).mp h1
  obtain ⟨H, hH⟩ := h2
  have hsg : e.symm g = -F := by
    have : g = -e F := by rw [heF, neg_neg]
    rw [this, map_neg, AlgEquiv.symm_apply_apply]
  have hp2 : p = -F * e.symm H := by
    rw [← e.symm_apply_apply p, hH, map_mul, hsg]
  rw [hp2]
  exact Ideal.mul_mem_right _ _ ((Ideal.span {F}).neg_mem (Ideal.mem_span_singleton_self F))

theorem zOverY_mul_eq_zero {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)
    (b : OriginChartRing V) (hb : zOverY V * b = 0) : b = 0 := by
  classical
  obtain ⟨f, hbij, hsc, hval⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing V

  have hfz : f (zOverY V) = Ideal.Quotient.mk _ (MvPolynomial.X 1) := by
    have := hval 1 (MvPolynomial.X 2) (by simpa using MvPolynomial.isHomogeneous_X T 2)
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    convert this using 2
    rfl
  obtain ⟨pb, hpb⟩ := Ideal.Quotient.mk_surjective (f b)
  have h1 : f (zOverY V * b) = 0 := by rw [hb, map_zero]
  rw [map_mul, hfz, ← hpb, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : pb ∈ Ideal.span (Set.range fun _ : Fin 1 =>
      MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial) := by
    have hset : (Set.range fun _ : Fin 1 =>
        MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial) =
        {MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial} := by
      ext x; simp
    rw [hset] at h1 ⊢
    exact mem_span_of_X_one_mul_mem V pb h1
  have h3 : f b = 0 := by rw [← hpb]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  exact hbij.1 (by rw [h3, map_zero])

end NZD

section Charts

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem polynomial_add_X0_cube :
    V.polynomial + MvPolynomial.X 0 ^ 3 = MvPolynomial.X 2 * (MvPolynomial.X 1 ^ 2 + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
      + MvPolynomial.C V.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2
      - MvPolynomial.C V.a₂ * MvPolynomial.X 0 ^ 2 - MvPolynomial.C V.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2
      - MvPolynomial.C V.a₆ * MvPolynomial.X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    show (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (MvPolynomial.X 0)) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (MvPolynomial.X i : MvPolynomial (Fin 3) T))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR T V hz)

end Charts

end DenseExtAux

namespace DenseExtAux

section Glue

variable {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem zOverY_pow_mem_nonZeroDivisors (n : ℕ) : zOverY V ^ n ∈ nonZeroDivisors (OriginChartRing V) := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem _
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem ih (by
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun b hb => zOverY_mul_eq_zero V b hb, fun b hb => zOverY_mul_eq_zero V b (by rw [mul_comm]; exact hb)⟩)

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  unfold Away.isLocalizationElem zOverY
  congr 1
  exact pow_one _

theorem awayMap_injective :
    Function.Injective (awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)) := by
  letI := (awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)).toAlgebra
  have hloc := Away.isLocalization_mul (𝒜 := projModelGradingCR V) (coord_mem V 1) (coord_mem V 2)
    (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2) one_ne_zero
  have hM : Submonoid.powers (Away.isLocalizationElem (𝒜 := projModelGradingCR V) (coord_mem V 1) (coord_mem V 2)) ≤
      nonZeroDivisors (OriginChartRing V) := by
    rintro _ ⟨n, rfl⟩
    rw [isLocalizationElem_eq_zOverY]
    exact zOverY_pow_mem_nonZeroDivisors V n
  haveI := hloc
  exact IsLocalization.injective (Away (projModelGradingCR V) (coord V 1 * coord V 2)) hM

theorem hom_ext_originChart {Y : Scheme.{u}} [Y.IsSeparated] (u v : Spec (CommRingCat.of (OriginChartRing V)) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 2)
        (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2))) ≫ u =
      Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 2)
        (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2))) ≫ v) : u = v :=
  hom_ext_of_specMap_comp_eq_of_injective u v _ (awayMap_injective V) h

theorem specMap_awayMap_comp_originChartι :
    Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 2)
        (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2))) ≫ originChartι V =
      Proj.awayι (projModelGradingCR V) (coord V 1 * coord V 2)
        (SetLike.mul_mem_graded (coord_mem V 1) (coord_mem V 2)) (by norm_num) :=
  Proj.SpecMap_awayMap_awayι _ _ _ _ _

theorem specMap_awayMap_comp_zChartι :
    Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR V) (coord_mem V 1)
        (mul_comm (coord V 2) (coord V 1) ▸ rfl : coord V 1 * coord V 2 = coord V 2 * coord V 1))) ≫ zChartι V =
      Proj.awayι (projModelGradingCR V) (coord V 1 * coord V 2)
        (SetLike.mul_mem_graded (coord_mem V 1) (coord_mem V 2)) (by norm_num) :=
  Proj.SpecMap_awayMap_awayι _ _ _ _ _

noncomputable def twoChartCover : (projModelCR V).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => cond b (Spec (CommRingCat.of (ZChartRing V))) (Spec (CommRingCat.of (OriginChartRing V))))
    (fun b => match b with
      | true => zChartι V
      | false => originChartι V)
    (by
      intro x
      by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
      · have hx : x ∈ (zChartι V).opensRange := by
          rw [Proj.opensRange_awayι, Proj.mem_basicOpen]
          exact fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
        obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
        exact ⟨true, y, hy⟩
      · have hx : x ∈ (originChartι V).opensRange := by
          rw [Proj.opensRange_awayι, Proj.mem_basicOpen]
          exact h1
        obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
        exact ⟨false, y, hy⟩)
    (fun b => by
      cases b
      · show IsOpenImmersion (originChartι V); infer_instance
      · show IsOpenImmersion (zChartι V); infer_instance)

end Glue

end DenseExtAux

open DenseExtAux

theorem solution
    (T : Type u) [CommRing T] (W : WeierstrassCurve T)
    {Y : Scheme.{u}} [Y.IsSeparated]
    (f g : projModelCR W.toProjective ⟶ Y)
    (h : zChartι W.toProjective ≫ f = zChartι W.toProjective ≫ g) : f = g := by
  have hY : originChartι W.toProjective ≫ f = originChartι W.toProjective ≫ g := by
    apply hom_ext_originChart W.toProjective
    have e1 := specMap_awayMap_comp_originChartι W.toProjective
    have e2 := specMap_awayMap_comp_zChartι W.toProjective
    rw [← Category.assoc, e1, ← e2, Category.assoc, h, ← Category.assoc, e2, ← e1, Category.assoc]
  exact Scheme.Cover.hom_ext (twoChartCover W.toProjective) f g (fun b => by
    cases b
    · exact hY
    · exact h)

end Extensionality

end CoordinateUniverse

namespace CoordinateUniverse.Specialization
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (T T' : Type u) [CommRing T] [CommRing T'] (f : T →+* T')
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (hmap : (C • W).map f = C.map f • W.map f)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hφC : IsVariableChangeHom W.toProjective C φ)
    (φ' : projModelGradingCR (W.map f).toProjective →+*ᵍ projModelGradingCR (C.map f • W.map f).toProjective)
    (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective)).map φ')
    (hφ'C : IsVariableChangeHom (W.map f).toProjective (C.map f) φ')
    (γ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hγ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map γ)
    (hγf : IsCoefficientHom W.toProjective f γ)
    (γC : projModelGradingCR (C • W).toProjective →+*ᵍ projModelGradingCR ((C • W).map f).toProjective)
    (hγC : HomogeneousIdeal.irrelevant (projModelGradingCR ((C • W).map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective)).map γC)
    (hγCf : IsCoefficientHom (C • W).toProjective f γC) :
    Proj.map γC hγC ≫ Proj.map φ hφ =
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hmap)) ≫ Proj.map φ' hφ' ≫ Proj.map γ hγ := by

  obtain ⟨hγCa0, hγCX0⟩ := hγCf
  have hγCa : ∀ a : T, γC (cls (C • W).toProjective (MvPolynomial.C a)) =
      cls ((C • W).map f).toProjective (MvPolynomial.C (f a)) := hγCa0
  have hγCX : ∀ i : Fin 3, γC (cls (C • W).toProjective (MvPolynomial.X i)) =
      cls ((C • W).map f).toProjective (MvPolynomial.X i) := hγCX0
  clear hγCa0 hγCX0
  revert γC hγC hγCa hγCX hmap
  generalize (C • W).map f = V
  intro hmap γC hγC hγCa hγCX
  subst hmap
  rw [eqToHom_refl, Category.id_comp]

  obtain ⟨hφa, hφ0, hφ1, hφ2⟩ := hφC
  obtain ⟨hφ'a, hφ'0, hφ'1, hφ'2⟩ := hφ'C
  obtain ⟨hγa, hγX⟩ := hγf
  simp only [cls] at hφa hφ0 hφ1 hφ2 hφ'a hφ'0 hφ'1 hφ'2 hγa hγX hγCa hγCX
  have key : γC.comp φ = φ'.comp γ := by
    apply GradedRingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    set F := (γC.comp φ).toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal)
      with hFdef
    set G := (φ'.comp γ).toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal)
      with hGdef
    have hF : F = G := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
          hφa, hγCa, hγa, hφ'a]
      · intro i
        fin_cases i
        · change F (MvPolynomial.X 0) = G (MvPolynomial.X 0)
          simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
            hφ0, hγX, hφ'0]
          simp only [map_add, map_mul, map_pow, hγCX, hγCa, WeierstrassCurve.VariableChange.map_u,
            WeierstrassCurve.VariableChange.map_r, Units.coe_map, MonoidHom.coe_coe]
        · change F (MvPolynomial.X 1) = G (MvPolynomial.X 1)
          simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
            hφ1, hγX, hφ'1]
          simp only [map_add, map_mul, map_pow, hγCX, hγCa, WeierstrassCurve.VariableChange.map_u,
            WeierstrassCurve.VariableChange.map_s, WeierstrassCurve.VariableChange.map_t, Units.coe_map,
            MonoidHom.coe_coe]
        · change F (MvPolynomial.X 2) = G (MvPolynomial.X 2)
          simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
            hφ2, hγX, hφ'2, hγCX]
    exact RingHom.congr_fun hF p
  have gen : ∀ (ψ₁ ψ₂ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C.map f • W.map f).toProjective)
      (h₁ : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map ψ₁)
      (h₂ : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map ψ₂),
      ψ₁ = ψ₂ → Proj.map ψ₁ h₁ = Proj.map ψ₂ h₂ := by
    rintro _ _ _ _ rfl; rfl
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact gen _ _ _ _ key

end CoordinateUniverse.Specialization

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
def variableGradedMap {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R) :
    projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (B • W).toProjective :=
  (exists_isVariableChangeHom_isIso_projMap W.toProjective B).choose

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem variableGradedMap_irrelevant {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R) :
    HomogeneousIdeal.irrelevant (projModelGradingCR (B • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map
        (variableGradedMap W B) :=
  (exists_isVariableChangeHom_isIso_projMap W.toProjective B).choose_spec.choose

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem variableGradedMap_spec {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R) :
    IsVariableChangeHom W.toProjective B (variableGradedMap W B) ∧
      IsIso (Proj.map (variableGradedMap W B) (variableGradedMap_irrelevant W B)) ∧
      Proj.map (variableGradedMap W B) (variableGradedMap_irrelevant W B) ≫
        projModelStrCR W.toProjective = projModelStrCR (B • W).toProjective :=
  (exists_isVariableChangeHom_isIso_projMap W.toProjective B).choose_spec.choose_spec

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
def variableComparison {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R) :
    Comparison R R W (B • W) (RingHom.id R) := by
  let b : Curve R (B • W) ⟶ Curve R W := Proj.map (variableGradedMap W B) (variableGradedMap_irrelevant W B)
  have hb := variableGradedMap_spec W B
  letI : IsIso b := hb.2.1
  have hover : b ≫ structureMap R W = structureMap R (B • W) := hb.2.2
  have hs : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (CommRingCat.of R)) :=
    Spec.map_id _
  refine ⟨b, ?_, ?_⟩
  · rw [hs]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hover⟩
  · rw [hs, Category.id_comp]
    exact kwZeroSect_comp_projMap_of_isVariableChangeHom W B _ _ hb.1

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem variableGradedMap_unique {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (B • W).toProjective)
    (hc : IsVariableChangeHom W.toProjective B φ) : φ = variableGradedMap W B := by
  apply CoefficientComposition.graded_ext W (B • W)
  · intro a
    exact (hc.1 a).trans ((variableGradedMap_spec W B).1.1 a).symm
  · intro i
    fin_cases i
    · exact hc.2.1.trans (variableGradedMap_spec W B).1.2.1.symm
    · exact hc.2.2.1.trans (variableGradedMap_spec W B).1.2.2.1.symm
    · exact hc.2.2.2.trans (variableGradedMap_spec W B).1.2.2.2.symm

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
theorem variableComparison_map {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (B • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (B • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hc : IsVariableChangeHom W.toProjective B φ) :
    (variableComparison W B).map = Proj.map φ hφ := by
  have he := variableGradedMap_unique W B φ hc
  subst φ
  rfl

theorem variableComparison_specialize {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R) (ι : R →+* S) :
    (coefficientComparison (B • W) ι).map ≫ (variableComparison W B).map =
      eqToHom (congrArg (Curve S) (WeierstrassCurve.map_variableChange W B ι).symm) ≫
        (variableComparison (W.map ι) (B.map ι)).map ≫ (coefficientComparison W ι).map := by
  exact CoordinateUniverse.Specialization.solution R S ι W B
    (WeierstrassCurve.map_variableChange W B ι).symm
    _ _ (variableGradedMap_spec W B).1 _ _ (variableGradedMap_spec (W.map ι) (B.map ι)).1
    _ _ (coefficientGradedMap_spec W ι) _ _ (coefficientGradedMap_spec (B • W) ι)

#print axioms variableComparison_specialize



namespace CoordinateUniverse.Reconstruction
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

p2m_open "HomogeneousLocalization Polynomial AlgebraicGeometry.Polynomial"

namespace WMLocal
variable {T : Type u} [CommRing T]

noncomputable abbrev cZ (V : WeierstrassCurve T) : T →+* ZChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T ((projModelGradingCR V.toProjective) 0))
end WMLocal

namespace WMLocal

section Ext

theorem zChart_ringHom_ext {T : Type u} [CommRing T] (V : WeierstrassCurve.Projective T) {B : Type u} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0)))) = g₂.comp (((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0)))))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = ((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))) r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

end Ext

section W4

theorem triangular_of_coeff {T : Type*} [CommRing T] {A A' : Type*} [CommRing A] [CommRing A']
    (c : T →+* A) (x y : A) (x' y' : A') (g : A' →+* A) (lam : A →+* LaurentSeries T)
    (hF2 : ∀ a : A, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ : T, a = c c₁ * x + c c₀ ∧ c₁ = (lam a).coeff (-2))
    (hF3 : ∀ a : A, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ c₂ : T, a = c c₂ * y + c c₁ * x + c c₀ ∧ c₂ = -((lam a).coeff (-3)))
    (hx₁ : ∀ n : ℤ, n < -2 → (lam (g x')).coeff n = 0) (hx₂ : IsUnit ((lam (g x')).coeff (-2)))
    (hy₁ : ∀ n : ℤ, n < -3 → (lam (g y')).coeff n = 0) (hy₂ : IsUnit ((lam (g y')).coeff (-3))) :
    ∃ (v₁ v₂ : Tˣ) (r s' t : T),
      g x' = c v₁ * x + c r ∧ g y' = c v₂ * y + c s' * x + c t := by
  obtain ⟨p₀, p₁, hex, hp₁⟩ := hF2 (g x') hx₁
  obtain ⟨q₀, q₁, q₂, hey, hq₂⟩ := hF3 (g y') hy₁
  have hu₁ : IsUnit p₁ := hp₁ ▸ hx₂
  have hu₂ : IsUnit q₂ := by rw [hq₂]; exact hy₂.neg
  refine ⟨hu₁.unit, hu₂.unit, p₀, q₁, q₀, ?_, ?_⟩
  · rw [hu₁.unit_spec, hex]
  · rw [hu₂.unit_spec, hey]

end W4

section Generic

theorem symm_triangular {T : Type*} [CommRing T] {A A' : Type*} [CommRing A] [CommRing A']
    (c : T →+* A) (c' : T →+* A') (x y : A) (x' y' : A') (e : A' ≃+* A) (he : ∀ t, e (c' t) = c t)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : e x' = c v₁ * x + c r) (hy : e y' = c v₂ * y + c s' * x + c t) :
    e.symm x = c' ↑v₁⁻¹ * x' + c' (-(↑v₁⁻¹ * r)) ∧
      e.symm y = c' ↑v₂⁻¹ * y' + c' (-(↑v₂⁻¹ * s' * ↑v₁⁻¹)) * x' + c' (↑v₂⁻¹ * (s' * ↑v₁⁻¹ * r - t)) := by
  have he' : ∀ t, e.symm (c t) = c' t := fun t => by rw [← he, RingEquiv.symm_apply_apply]
  have hx' : x' = c' v₁ * e.symm x + c' r := by
    have := congrArg e.symm hx
    rwa [RingEquiv.symm_apply_apply, map_add, map_mul, he', he'] at this
  have hy' : y' = c' v₂ * e.symm y + c' s' * e.symm x + c' t := by
    have := congrArg e.symm hy
    rwa [RingEquiv.symm_apply_apply, map_add, map_add, map_mul, map_mul, he', he', he'] at this
  have hv₁ : c' ↑v₁⁻¹ * c' v₁ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hv₂ : c' ↑v₂⁻¹ * c' v₂ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have ex0 : e.symm x = c' ↑v₁⁻¹ * x' - c' ↑v₁⁻¹ * c' r := by
    linear_combination (-(c' ↑v₁⁻¹)) * hx' + (-(e.symm x)) * hv₁
  have ey0 : e.symm y = c' ↑v₂⁻¹ * y' - c' ↑v₂⁻¹ * c' s' * c' ↑v₁⁻¹ * x' +
      c' ↑v₂⁻¹ * (c' s' * c' ↑v₁⁻¹ * c' r - c' t) := by
    linear_combination (-(c' ↑v₂⁻¹)) * hy' + (-(e.symm y)) * hv₂ + (-(c' ↑v₂⁻¹ * c' s')) * ex0
  constructor
  · simp only [map_neg, map_mul]
    linear_combination ex0
  · simp only [map_neg, map_mul, map_sub]
    linear_combination ey0

theorem exists_algHom_triangular_of_charts {T : Type*} [CommRing T] {A A' C C' : Type*}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C'] [Algebra T C] [Algebra T C']
    (c : T →+* A) (c' : T →+* A') (x y : A) (x' y' : A')
    (fA : A →+* C) (hfA : Function.Bijective fA) (hfAc : fA.comp c = algebraMap T C)
    (fA' : A' →+* C') (hfA'c : fA'.comp c' = algebraMap T C')
    (ε : A →+* A') (hε : ∀ t, ε (c t) = c' t)
    (a b k d m : T) (hx : ε x = c' a * x' + c' b) (hy : ε y = c' k * y' + c' d * x' + c' m) :
    ∃ g : C →ₐ[T] C', g (fA x) = a • fA' x' + algebraMap T C' b ∧
      g (fA y) = k • fA' y' + d • fA' x' + algebraMap T C' m := by
  let E : A ≃+* C := RingEquiv.ofBijective fA hfA
  have hE : ∀ z, E.symm (fA z) = z := fun z => E.symm_apply_apply z
  have hc : ∀ t, fA (c t) = algebraMap T C t := fun t => RingHom.congr_fun hfAc t
  have hc' : ∀ t, fA' (c' t) = algebraMap T C' t := fun t => RingHom.congr_fun hfA'c t
  let g₀ : C →+* C' := fA'.comp (ε.comp E.symm.toRingHom)
  have hg₀ : ∀ z, g₀ (fA z) = fA' (ε z) := fun z => by
    show fA' (ε (E.symm (fA z))) = _; rw [hE]
  let g : C →ₐ[T] C' :=
    { toRingHom := g₀
      commutes' := fun t => by
        show g₀ (algebraMap T C t) = algebraMap T C' t
        rw [← hc, hg₀, hε, hc'] }
  refine ⟨g, ?_, ?_⟩
  · show g₀ (fA x) = _
    rw [hg₀, hx, map_add, map_mul, hc', hc', Algebra.smul_def]
  · show g₀ (fA y) = _
    rw [hg₀, hy, map_add, map_add, map_mul, map_mul, hc', hc', hc', Algebra.smul_def, Algebra.smul_def]

end Generic

section Charts

variable {T : Type u} [CommRing T]

theorem exists_zChart_to_coordinateRing (V : WeierstrassCurve T) :
    ∃ f : ZChartRing V.toProjective →+* V.toAffine.CoordinateRing, Function.Bijective f ∧
      f.comp (cZ V) = algebraMap T V.toAffine.CoordinateRing ∧
      f (xOverZ V.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk V (C X) ∧
      f (yOverZ V.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk V X := by
  obtain ⟨f, hbij, hc, hval⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  refine ⟨f, hbij, hc, ?_, ?_⟩
  · have := hval 1 (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X T 0)
    refine (Eq.trans ?_ this).trans ?_
    · rfl
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      simp [MvPolynomial.aeval_X]
  · have := hval 1 (MvPolynomial.X 1) (by simpa using MvPolynomial.isHomogeneous_X T 1)
    refine (Eq.trans ?_ this).trans ?_
    · rfl
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      simp [MvPolynomial.aeval_X]

theorem exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv (W W' : WeierstrassCurve T)
    (e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective) (he : ∀ t, e (cZ W' t) = cZ W t)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : e (xOverZ W'.toProjective) = cZ W v₁ * xOverZ W.toProjective + cZ W r)
    (hy : e (yOverZ W'.toProjective) = cZ W v₂ * yOverZ W.toProjective + cZ W s' * xOverZ W.toProjective + cZ W t) :
    ∃ g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing,
      g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
        ((v₁⁻¹ : Tˣ) : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ (-(↑v₁⁻¹ * r)) ∧
      g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
        ((v₂⁻¹ : Tˣ) : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
          (-(↑v₂⁻¹ * s' * ↑v₁⁻¹)) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) +
          algebraMap T _ (↑v₂⁻¹ * (s' * ↑v₁⁻¹ * r - t)) := by
  obtain ⟨fW, hbW, hcW, hxW, hyW⟩ := exists_zChart_to_coordinateRing W
  obtain ⟨fW', -, hcW', hxW', hyW'⟩ := exists_zChart_to_coordinateRing W'
  obtain ⟨ex, ey⟩ := symm_triangular (cZ W) (cZ W') (xOverZ W.toProjective) (yOverZ W.toProjective)
    (xOverZ W'.toProjective) (yOverZ W'.toProjective) e he v₁ v₂ r s' t hx hy
  have he' : ∀ t, e.symm (cZ W t) = cZ W' t := fun t => by rw [← he, RingEquiv.symm_apply_apply]
  obtain ⟨g, hgx, hgy⟩ := exists_algHom_triangular_of_charts (cZ W) (cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) fW hbW hcW fW' hcW'
    e.symm.toRingHom he' _ _ _ _ _ ex ey
  rw [hxW, hxW'] at hgx
  rw [hyW, hyW', hxW'] at hgy
  exact ⟨g, hgx, hgy⟩

end Charts

end WMLocal


end CoordinateUniverse.Reconstruction


/- Coordinate reconstruction for a pointed isomorphism over an arbitrary local
ring in Type u. The proof reuses the library chart reconstruction and Laurent
filtration helpers, without an Artinian or reducedness hypothesis. The equality
identifies the actual projective map, not only its points.

Adapted from the proof of the library Artinian coordinate-change theorem;
its chart providers have the weaker hypotheses used here. -/
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4096 in
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization in
open CoordinateUniverse.Reconstruction in
theorem local_pointed_iso_coordinate_change
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ (C : WeierstrassCurve.VariableChange T) (hC : C • W = W')
      (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      IsVariableChangeHom W.toProjective C φ ∧
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = Ψ.inv := by
  classical

  obtain ⟨e, hec, heι⟩ := CoordinateUniverse.ChartIso.solution T W W' Ψ hΨ hΨO

  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W
  obtain ⟨lam, hlc, hlx, hly, hF2, hF3⟩ := CoordinateUniverse.Filtration.solution T W Φ hΦc hΦx hΦz

  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := CoordinateUniverse.Laurent.solution T W W' Ψ hΨ hΨO
    e.toRingHom heι Φ hΦc hΦx hΦz lam hlc hlx hly

  obtain ⟨v₁, v₂, r, s', t, hex, hey⟩ := WMLocal.triangular_of_coeff (WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e.toRingHom lam hF2 hF3 hx₁ hx₂ hy₁ hy₂

  obtain ⟨g, hgx, hgy⟩ := WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv W W' e hec v₁ v₂ r s' t hex hey
  obtain ⟨ex, ey⟩ := WMLocal.symm_triangular (WMLocal.cZ W) (WMLocal.cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e hec v₁ v₂ r s' t hex hey
  generalize hw₁ : v₁⁻¹ = w₁ at hgx hgy ex ey
  generalize hw₂ : v₂⁻¹ = w₂ at hgx hgy ex ey
  generalize hr₁ : (-(↑w₁ * r) : T) = r₁ at hgx ex
  generalize hs₁ : (-(↑w₂ * s' * ↑w₁) : T) = s₁ at hgy ey
  generalize ht₁ : (↑w₂ * (s' * ↑w₁ * r - t) : T) = t₁ at hgy ey
  obtain ⟨C, hC, ⟨hu2, hu3⟩, hCr, hCs, hCt⟩ :=
    CoordinateUniverse.Algebra.solution T W W' g w₁ w₂ r₁ s₁ t₁ hgx hgy
  subst hC

  obtain ⟨φ, hφ, hvc, _, _⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W.toProjective C
  refine ⟨C, rfl, φ, hφ, hvc, ?_⟩
  simp only [eqToHom_refl, Category.id_comp]

  obtain ⟨a, haι, hac, hax, hay⟩ := WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom W.toProjective C φ hφ hvc
  have hec' : ∀ b : T, e.symm (WMLocal.cZ W b) = WMLocal.cZ (C • W) b := fun b => by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hec b).symm
  have hae : a = e.symm.toRingHom := by
    apply WMLocal.zChart_ringHom_ext W.toProjective
    · refine RingHom.ext fun b => ?_
      change a (WMLocal.cZ W b) = e.symm (WMLocal.cZ W b)
      rw [hec']
      exact hac b
    · change a (xOverZ W.toProjective) = e.symm (xOverZ W.toProjective)
      rw [hax, ex, hu2, hCr]
      rfl
    · change a (yOverZ W.toProjective) = e.symm (yOverZ W.toProjective)
      rw [hay, ey, hCs, hu3, hCt]
      rfl
  apply CoordinateUniverse.Extensionality.solution T (C • W)
  rw [haι, hae]

  have hcomp : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => ?_
    show e.symm (e z) = z
    exact e.symm_apply_apply z
  have hee : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, hcomp, Spec.map_id]
  symm
  calc zChartι (C • W).toProjective ≫ Ψ.inv
      = (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
          zChartι (C • W).toProjective ≫ Ψ.inv := by rw [hee, Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι (C • W).toProjective) ≫ Ψ.inv) := by
        simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ ((zChartι W.toProjective ≫ Ψ.hom) ≫ Ψ.inv) := by rw [heι]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ zChartι W.toProjective := by
        rw [Category.assoc, Ψ.hom_inv_id, Category.comp_id]


open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal in
/-- Over a local ring in Type u, the specified Cartesian map is literally a
projective coordinate-change map followed by coefficient base change. -/
theorem local_comparison_coordinates
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing S]
    {W : WeierstrassCurve R} {V : WeierstrassCurve S} {ι : R →+* S}
    (C : Comparison R S W V ι) :
    ∃ (B : WeierstrassCurve.VariableChange S) (hB : B • W.map ι = V)
      (φ : projModelGradingCR (W.map ι).toProjective →+*ᵍ
        projModelGradingCR (B • W.map ι).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (B • W.map ι).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR (W.map ι).toProjective)).map φ),
      IsVariableChangeHom (W.map ι).toProjective B φ ∧
      C.map = (eqToHom (congrArg projModelCR
        (congrArg WeierstrassCurve.toProjective hB)).symm ≫ Proj.map φ hφ) ≫
          (coefficientComparison W ι).map := by
  obtain ⟨e, hemap, heover, heorigin⟩ := comparison_factor_iso C
  have hiOver : e.inv ≫ structureMap S V = structureMap S (W.map ι) := by
    rw [← heover, e.inv_hom_id_assoc]
  have hiOrigin : origin S (W.map ι) ≫ e.inv = origin S V := by
    rw [← heorigin, Category.assoc, e.hom_inv_id, Category.comp_id]
  obtain ⟨B, hB, φ, hφ, hvar, he⟩ := local_pointed_iso_coordinate_change S
    (W.map ι) V e.symm hiOver hiOrigin
  refine ⟨B, hB, φ, hφ, hvar, ?_⟩
  rw [he]
  exact hemap.symm

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

theorem topRes_injective {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (h : ⊤ ≤ U) : Function.Injective (res M h) := by
  intro s t he
  have hh := congrArg (res M (show U ≤ ⊤ from le_top)) he
  simpa only [res_res, res_refl] using hh

set_option maxRecDepth 4096 in
theorem pull_eq_iff {R S : Type u} [CommRing R] [CommRing S]
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S}
    {ι : R →+* S} (C : Comparison R S W V ι)
    (s t : Sections (HodgePower R W 24)) :
    pull C s = pull C t ↔
      Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι)) s =
        Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom ι)) t := by
  constructor
  · intro h
    have hh := topRes_injective (HodgePower S V 24) (by simp) h
    exact (ConcreteCategory.bijective_of_isIso ((comparisonPower C).hom.app _)).1 hh
  · intro h
    unfold pull
    rw [h]

#print axioms pull_eq_iff


theorem normal_originLaw_exists
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ G : Law R W, IsOriginLaw R W G := by
  have hg := relative_curve_geometry R W
  letI := hg.2.2.2.2.2.1
  have htwo : IsUnit (2 : R) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  letI : Invertible (2 : R) := htwo.invertible
  obtain ⟨_, _, _, G, _, hone, hcomm⟩ := WeierstrassProjModel.relativeGroupLaw_exists
    W (inferInstance : Smooth (structureMap R W)) hg.2.2.2.2.2.2 W.isUnit_Δ
  exact ⟨G, hone, hcomm⟩

namespace CoefficientParameters

/-- Over normal bases the universal coefficient section recovers the accepted
initial section, hence is natural for every specified pointed Cartesian map. -/
theorem normal_coefficientSection_pull
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
    (ι : k →+* R) (κ : k →+* S)
    {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} [V.IsElliptic]
    {ρ : R →+* S} (C : Comparison R S W V ρ) :
    pull C (coefficientSection ι W) = coefficientSection κ V := by
  have hgR := relative_curve_geometry R W
  have hgS := relative_curve_geometry S V
  letI := hgR.1
  letI := hgR.2.1
  letI := hgR.2.2.2.1
  letI := hgR.2.2.2.2.1
  letI := hgS.1
  letI := hgS.2.1
  letI := hgS.2.2.2.1
  letI := hgS.2.2.2.2.1
  obtain ⟨G, hG⟩ := normal_originLaw_exists R W
  obtain ⟨H, hH⟩ := normal_originLaw_exists S V
  unfold coefficientSection
  rw [normal_classifying_pull k R ι W G hG, normal_classifying_pull k S κ V H hH]
  exact normal_comparison_pull C G hG H hH

end CoefficientParameters

#print axioms CoefficientParameters.normal_coefficientSection_pull


/-- Base change keeps the same normal source and composes its specified map. -/
def baseChangeModel {R S : Type u} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] {W : WeierstrassCurve R}
    (M : NormalModel R W) (ρ : R →ₐ[ℚ] S) : NormalModel S (W.map ρ.toRingHom) where
  ring := M.ring
  equation := M.equation
  law := M.law
  originLaw := M.originLaw
  scalar := ρ.comp M.scalar
  comparison := comparisonCompose M.comparison (coefficientComparison W ρ.toRingHom)

theorem value_baseChange {R S : Type u} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] {W : WeierstrassCurve R} [W.IsElliptic]
    (M : NormalModel R W) (ρ : R →ₐ[ℚ] S) :
    value (baseChangeModel M ρ) = pull (coefficientComparison W ρ.toRingHom) (value M) := by
  apply pull_refinement M.comparison (coefficientComparison W ρ.toRingHom)
    (comparisonCompose M.comparison (coefficientComparison W ρ.toRingHom)) rfl
  exact Spec.map_comp (CommRingCat.ofHom M.scalar.toRingHom) (CommRingCat.ofHom ρ.toRingHom)

/-- This reduction uses local rings themselves and therefore preserves the
nonreduced information required by the frozen independence statement. -/
theorem value_eq_of_localizations {R : Type u} [CommRing R] [Algebra ℚ R]
    {W : WeierstrassCurve R} [W.IsElliptic] (M N : NormalModel R W)
    (h : ∀ (m : Ideal R) (_ : m.IsMaximal),
      value (baseChangeModel M (IsScalarTower.toAlgHom ℚ R (Localization.AtPrime m))) =
        value (baseChangeModel N (IsScalarTower.toAlgHom ℚ R (Localization.AtPrime m)))) :
    value M = value N := by
  apply sections_eq_of_localizations (HodgePower R W 24) (value M) (value N) (value_frame M)
  intro m hm
  let ρ := IsScalarTower.toAlgHom ℚ R (Localization.AtPrime m)
  apply (pull_eq_iff (coefficientComparison W ρ.toRingHom) (value M) (value N)).mp
  rw [← value_baseChange M ρ, ← value_baseChange N ρ]
  exact h m hm

#print axioms value_baseChange
#print axioms value_eq_of_localizations


theorem pull_square
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic]
    {Z : WeierstrassCurve T} {F : WeierstrassCurve U} [F.IsElliptic]
    {ι : R →+* S} {ρ : S →+* T} {κ : R →+* U} {τ : U →+* T}
    (C : Comparison R S W V ι) (D : Comparison S T V Z ρ)
    (A : Comparison R U W F κ) (B : Comparison U T F Z τ)
    (hm : D.map ≫ C.map = B.map ≫ A.map)
    (hscalar : ρ.comp ι = τ.comp κ) (d : Sections (HodgePower R W 24)) :
    pull D (pull C d) = pull B (pull A d) := by
  let E := comparisonCompose C D
  have h₁ : pull E d = pull D (pull C d) :=
    pull_refinement C D E rfl (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom ρ)) d
  have hbase : baseMap R T (ρ.comp ι) = baseMap U T τ ≫ baseMap R U κ := by
    rw [hscalar]
    exact Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom τ)
  exact h₁.symm.trans (pull_refinement A B E hm.symm hbase d)

theorem variableComparison_square {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (B : WeierstrassCurve.VariableChange R) (ι : R →+* S) :
    (comparisonTargetEq (coefficientComparison (B • W) ι)
      (WeierstrassCurve.map_variableChange W B ι).symm).map ≫
        (variableComparison W B).map =
      (variableComparison (W.map ι) (B.map ι)).map ≫ (coefficientComparison W ι).map := by
  rw [comparisonTargetEq_map, Category.assoc, variableComparison_specialize,
    ← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]

theorem pull_variable_specialization {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (B : WeierstrassCurve.VariableChange R) (ι : R →+* S)
    (d : Sections (HodgePower R W 24)) :
    pull (comparisonTargetEq (coefficientComparison (B • W) ι)
      (WeierstrassCurve.map_variableChange W B ι).symm) (pull (variableComparison W B) d) =
      pull (variableComparison (W.map ι) (B.map ι)) (pull (coefficientComparison W ι) d) :=
  pull_square (variableComparison W B) _ (coefficientComparison W ι) _
    (variableComparison_square W B ι) (by ext; rfl) d

namespace CoefficientParameters

theorem coefficientSection_target_naturality
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [CommRing S]
    (ι : k →+* R) (ρ : R →+* S) (W : WeierstrassCurve R) [W.IsElliptic]
    (V : WeierstrassCurve S) [V.IsElliptic] (hV : W.map ρ = V) :
    pull (comparisonTargetEq (coefficientComparison W ρ) hV) (coefficientSection ι W) =
      coefficientSection (ρ.comp ι) V := by
  subst V
  exact coefficientSection_naturality ι ρ W

/-- The accepted normal-base variable-change identity remains valid after
arbitrary coefficient specialization of that actual variable change. -/
theorem variable_specialization_naturality
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    [CommRing S] (ι : k →+* R) (ρ : R →+* S)
    (W : WeierstrassCurve R) [W.IsElliptic] (B : WeierstrassCurve.VariableChange R) :
    pull (variableComparison (W.map ρ) (B.map ρ))
      (coefficientSection (ρ.comp ι) (W.map ρ)) =
        coefficientSection (ρ.comp ι) (B.map ρ • W.map ρ) := by
  have hs := pull_variable_specialization W B ρ (coefficientSection ι W)
  rw [normal_coefficientSection_pull ι ι (variableComparison W B),
    coefficientSection_target_naturality,
    coefficientSection_naturality] at hs
  exact hs.symm

end CoefficientParameters

#print axioms pull_variable_specialization
#print axioms CoefficientParameters.variable_specialization_naturality


namespace CoefficientParameters

/-- Transport the complete dependent equivariance proposition before any
concrete universal equation is expanded. -/
theorem variable_equation_transport
    {k S : Type u} [Field k] [CharZero k] [Algebra ℚ k] [CommRing S]
    (ι κ : k →+* S) (hι : ι = κ)
    (W V : WeierstrassCurve S) [W.IsElliptic] [V.IsElliptic] (hW : W = V)
    (B C : WeierstrassCurve.VariableChange S) (hB : B = C)
    (h : pull (variableComparison W B) (coefficientSection ι W) =
      coefficientSection ι (B • W)) :
    pull (variableComparison V C) (coefficientSection κ V) =
      coefficientSection κ (C • V) := by
  subst κ
  subst V
  subst C
  exact h

/-- Universal normal change parameters spread out every coordinate change,
including changes over nonreduced and non-Noetherian rings. -/
theorem variable_naturality
    {k S : Type u} [Field k] [CharZero k] [Algebra ℚ k] [CommRing S]
    (ι : k →+* S) (W : WeierstrassCurve S) [W.IsElliptic]
    (B : WeierstrassCurve.VariableChange S) :
    pull (variableComparison W B) (coefficientSection ι W) =
      coefficientSection ι (B • W) := by
  let R := Ring k
  let T := ChangeParameters.Ring R
  have hn := ChangeParameters.normal_parameters R
  letI : IsDomain T := hn.1
  letI : IsNoetherianRing T := hn.2.1
  letI : IsIntegrallyClosed T := hn.2.2
  let A := (universal k).map (algebraMap R T)
  let C := ChangeParameters.universal R
  let φ := ChangeParameters.specialize (classifying ι W) B
  have hscalar : φ.comp (algebraMap k T) = ι := by
    ext a
    change φ (algebraMap R T (algebraMap k R a)) = ι a
    rw [ChangeParameters.specialize_scalar, classifying_scalar]
  have hbase : φ.comp (algebraMap R T) = classifying ι W :=
    RingHom.ext (ChangeParameters.specialize_scalar (classifying ι W) B)
  have hA : A.map φ = W := by
    change ((universal k).map (algebraMap R T)).map φ = W
    rw [WeierstrassCurve.map_map, hbase, classifying_universal]
  have hC : C.map φ = B := ChangeParameters.specialize_universal _ _
  have h := variable_specialization_naturality (algebraMap k T) φ A C
  exact variable_equation_transport (φ.comp (algebraMap k T)) ι hscalar
    (A.map φ) W hA (C.map φ) B hC h

theorem variable_target_naturality
    {k S : Type u} [Field k] [CharZero k] [Algebra ℚ k] [CommRing S]
    (ι : k →+* S) (W : WeierstrassCurve S) [W.IsElliptic]
    (B : WeierstrassCurve.VariableChange S)
    (V : WeierstrassCurve S) [V.IsElliptic] (hV : B • W = V) :
    pull (comparisonTargetEq (variableComparison W B) hV) (coefficientSection ι W) =
      coefficientSection ι V := by
  subst V
  exact variable_naturality ι W B

/-- Over local targets the statement applies to every specified pointed
Cartesian map, because the map itself admits the checked coordinate form. -/
theorem local_comparison_naturality
    {k R S : Type u} [Field k] [CharZero k] [Algebra ℚ k]
    [CommRing R] [CommRing S] [IsLocalRing S]
    (ι : k →+* R) {W : WeierstrassCurve R} [W.IsElliptic]
    {V : WeierstrassCurve S} [V.IsElliptic] {ρ : R →+* S}
    (C : Comparison R S W V ρ) :
    pull C (coefficientSection ι W) = coefficientSection (ρ.comp ι) V := by
  obtain ⟨B, hB, φ, hφ, hc, hm⟩ := local_comparison_coordinates C
  let D := comparisonTargetEq (variableComparison (W.map ρ) B) hB
  have hmap : D.map ≫ (coefficientComparison W ρ).map = C.map := by
    rw [comparisonTargetEq_map, variableComparison_map _ _ φ hφ hc]
    exact hm.symm
  have hbase : baseMap R S ρ = baseMap S S (RingHom.id S) ≫ baseMap R S ρ := by
    change Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (𝟙 (CommRingCat.of S)) ≫ Spec.map (CommRingCat.ofHom ρ)
    rw [Spec.map_id, Category.id_comp]
  rw [pull_refinement (coefficientComparison W ρ) D C hmap hbase,
    coefficientSection_naturality]
  exact variable_target_naturality (ρ.comp ι) (W.map ρ) B V hB

end CoefficientParameters

#print axioms CoefficientParameters.variable_naturality
#print axioms CoefficientParameters.local_comparison_naturality


instance rationalLift_charZero : CharZero (ULift.{u} ℚ) := algebraRat.charZero _

def rationalMap (R : Type u) [CommRing R] [Algebra ℚ R] : ULift.{u} ℚ →+* R :=
  (algebraMap ℚ R).comp ULift.ringEquiv.toRingHom

theorem rationalMap_naturality {R S : Type u} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] (f : R →ₐ[ℚ] S) :
    f.toRingHom.comp (rationalMap R) = rationalMap S := by
  ext q
  exact f.commutes q.down

theorem value_local {R : Type u} [CommRing R] [Algebra ℚ R] [IsLocalRing R]
    {W : WeierstrassCurve R} [W.IsElliptic] (M : NormalModel R W) :
    value M = CoefficientParameters.coefficientSection (rationalMap R) W := by
  have hn := CoefficientParameters.normal_classifying_pull (ULift.{u} ℚ)
    M.ring (rationalMap M.ring) M.equation M.law M.originLaw
  change CoefficientParameters.coefficientSection (rationalMap M.ring) M.equation =
    localD M.ring M.equation M.law M.originLaw at hn
  unfold value
  rw [← hn, CoefficientParameters.local_comparison_naturality,
    rationalMap_naturality M.scalar]

theorem independence_local
    (R : Type u) [CommRing R] [Algebra ℚ R] [IsLocalRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (M N : NormalModel R W) :
    value M = value N :=
  (value_local M).trans (value_local N).symm

#print axioms value_local
#print axioms independence_local

end NormalDiscriminantIndependence

/-- The normalized five-Kato initial section has the same pullback through
every normal-source pointed Cartesian model, over an arbitrary rational base. -/
theorem normal_discriminant_independence
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (M N : NormalModel R W) :
    value M = value N := by
  apply NormalDiscriminantIndependence.value_eq_of_localizations M N
  intro m hm
  letI := hm
  exact NormalDiscriminantIndependence.independence_local _ _ _ _

#print axioms normal_discriminant_independence

namespace NormalDiscriminantIndependence


#print axioms CoordinateUniverse.Algebra.solution
#print axioms CoordinateUniverse.ChartIso.solution
#print axioms CoordinateUniverse.Filtration.solution
#print axioms CoordinateUniverse.Laurent.solution
#print axioms CoordinateUniverse.Extensionality.solution
#print axioms local_pointed_iso_coordinate_change
#print axioms CoefficientParameters.normal_coefficients
#print axioms CoefficientParameters.classifying_universal
#print axioms CoefficientParameters.classifying_scalar
#print axioms CoefficientParameters.classifying_naturality
#print axioms CoefficientParameters.normal_classifying_pull
#print axioms local_comparison_coordinates
#print axioms ChangeParameters.specialize_universal
#print axioms ChangeParameters.specialize_scalar
#print axioms ChangeParameters.specialize_transformed
#print axioms ChangeParameters.normal_parameters
#print axioms variable_comparison_exists
#print axioms universal_comparison_exists

#print axioms coefficientComparison
#print axioms comparison_factor_iso
#print axioms comparison_nsmul
#print axioms comparisonPower_eq
#print axioms comparisonPower_spec
#print axioms value_eq_localD_of_nsmul
#print axioms value_eq_localD
#print axioms independence_normal
#print axioms independence_subsingleton

end NormalDiscriminantIndependence
end ArithmeticThetaArbitraryDiscriminantR0243
