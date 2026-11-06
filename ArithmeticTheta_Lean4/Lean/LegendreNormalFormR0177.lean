import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Theorems.Thm_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit
import TwoTorsionAffineCoordinatesR0177
import TwoTorsionSplitCubicR0177
import StandardLegendreTwoMarkingR0177
import Theorems.Thm_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
import Theorems.Thm_WeierstrassProjModel_kwZeroSect_comp_projMap_of_isVariableChangeHom

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
namespace NormalFormConstruction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176

/-- The ordered cross ratio lies in the original ring, with both excluded
values avoided by units. No field division or extension is needed here. -/
theorem exists_parameter {R : Type u} [CommRing R] (e : Fin 3 → R)
    (he : ∀ i j, i ≠ j → IsUnit (e i - e j)) :
    ∃ lam : R, IsUnit (lam * (lam - 1)) ∧
      lam * (e 1 - e 0) = e 2 - e 0 := by
  obtain ⟨d, hd⟩ := he 1 0 (by decide)
  let lam : R := (e 2 - e 0) * ↑(d⁻¹)
  have hlam : lam * (e 1 - e 0) = e 2 - e 0 := by
    rw [← hd]
    simp [lam, mul_assoc]
  have hunit : IsUnit lam := (he 2 0 (by decide)).mul (d⁻¹).isUnit
  have hsub : (lam - 1) * (e 1 - e 0) = e 2 - e 1 := by
    linear_combination hlam
  have hunit' : IsUnit (lam - 1) :=
    (IsUnit.mul_iff.mp (hsub.symm ▸ he 2 1 (by decide))).1
  exact ⟨lam, hunit.mul hunit', hlam⟩

/-- The universal Legendre parameter map associated to a permitted parameter. -/
theorem exists_parameterMap (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (lam : S) (hlam : IsUnit (lam * (lam - 1))) :
    ∃ f : LegendreRing k →ₐ[k] S, f (parameter k) = lam := by
  let f : Polynomial k →ₐ[k] S := Polynomial.aeval lam
  have hu : IsUnit (f (Polynomial.X * (Polynomial.X - 1))) := by
    simpa [f] using hlam
  refine ⟨IsLocalization.Away.liftAlgHom (Polynomial.X * (Polynomial.X - 1)) hu, ?_⟩
  change IsLocalization.Away.lift _ hu (algebraMap (Polynomial k) (LegendreRing k) Polynomial.X) = lam
  rw [IsLocalization.Away.lift_eq]
  simp [f]

/-- A nonsquare over a normal domain stays nonsquare in its fraction field. -/
theorem nonsquare_fraction {R : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (d : R) (hd : ¬ ∃ r : R, r^2 = d) :
    ∀ x : FractionRing R, x^2 ≠ algebraMap R (FractionRing R) d := by
  intro x hx
  have hi : IsIntegral R (x^2) := hx.symm ▸ isIntegral_algebraMap
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by decide : 0 < 2) hi
  apply hd
  refine ⟨r, IsFractionRing.injective R (FractionRing R) ?_⟩
  rw [map_pow, hr, hx]

/-- A connected normal finite étale square-root algebra, with its actual
module degree. The split case uses the base itself. -/
structure SquareRootCover (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (d : R) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [baseAlgebra : Algebra R ring]
  [algebra : Algebra k ring]
  [tower : IsScalarTower k R ring]
  [finite : Module.Finite R ring]
  [free : Module.Free R ring]
  [etale : Algebra.Etale R ring]
  degree : Module.finrank R ring = 1 ∨ Module.finrank R ring = 2
  scaling : ringˣ
  scaling_eq : (scaling : ring)^2 = algebraMap R ring d

attribute [instance] SquareRootCover.commRing SquareRootCover.domain
  SquareRootCover.noetherian SquareRootCover.normal SquareRootCover.baseAlgebra
  SquareRootCover.algebra SquareRootCover.tower SquareRootCover.finite
  SquareRootCover.free SquareRootCover.etale

open Polynomial in
/-- Normality rules out new square roots in the fraction field. Thus adjoining
a root in the nonsquare case gives a domain of rank two. -/
theorem exists_squareRootCover (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    [Algebra k R] (d : R) (hd : IsUnit d) : Nonempty (SquareRootCover k R d) := by
  classical
  by_cases hs : ∃ r : R, r^2 = d
  · obtain ⟨r, hr⟩ := hs
    have hu : IsUnit r := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hr.symm ▸ hd)
    exact ⟨{ ring := R
             degree := Or.inl (Module.finrank_self R)
             scaling := hu.unit
             scaling_eq := by simpa using hr }⟩
  · let f : R[X] := X^2 - C d
    have hfm : f.Monic := monic_X_pow_sub_C d (by decide)
    have hfi : Irreducible f := by
      apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := FractionRing R) hfm).mpr
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr (nonsquare_fraction d hs)
    have hroot : (AdjoinRoot.root f)^2 = algebraMap R (AdjoinRoot f) d := by
      have h := AdjoinRoot.mk_self (f := f)
      change AdjoinRoot.mk f (X^2 - C d) = 0 at h
      simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero,
        AdjoinRoot.algebraMap_eq] using h
    have hu : IsUnit (AdjoinRoot.root f) :=
      (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hroot.symm ▸ hd.map (algebraMap R (AdjoinRoot f)))
    have htwo : IsUnit (2 : R) := by
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    have hder : IsUnit (AdjoinRoot.mk f (derivative f)) := by
      have ht : IsUnit (2 : AdjoinRoot f) := by
        simpa only [map_ofNat] using htwo.map (algebraMap R (AdjoinRoot f))
      convert ht.mul hu using 1 <;> simp [f, ← two_mul, map_ofNat]
    obtain ⟨hdom, hnormal⟩ := AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative
      R f hfm hfi hder
    letI := hdom
    letI := hnormal
    obtain ⟨hetale, hfinite⟩ := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit 2 d htwo hd
    letI : Algebra.Etale R (AdjoinRoot f) := hetale
    letI : Module.Finite R (AdjoinRoot f) := hfinite
    letI : Module.Free R (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
    letI : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite R (AdjoinRoot f)
    refine ⟨{ ring := AdjoinRoot f
              degree := Or.inr ?_
              scaling := hu.unit
              scaling_eq := by simpa using hroot }⟩
    rw [(AdjoinRoot.powerBasis' hfm).finrank]
    exact natDegree_X_pow_sub_C

/-- The cover's algebraic rank is its geometric rank at every base point. -/
theorem squareRootCover_geometry {k R : Type u} [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] {d : R} (C : SquareRootCover k R d) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))) ∧
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))) ∧
    ∀ z, 0 < (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))).finrank z ∧
      (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))).finrank z ≤ 2 := by
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have he : Etale (Spec.map (CommRingCat.ofHom (algebraMap R C.ring))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  refine ⟨hf, he, ⟨Algebra.IsIntegral.comap_surjective R C.ring⟩, ?_⟩
  intro z
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rcases C.degree with h | h <;> rw [h] <;> norm_num

/-- Completing the square and translating the first root gives the split
cubic with roots zero, `s-r`, and `t-r`. -/
theorem translated_curve {R : Type u} [CommRing R] [IsDomain R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (r s t : R)
    (ha : W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2 = -(r+s+t))
    (hb : W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃ = r*s+r*t+s*t)
    (hc : W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2 = -(r*s*t)) :
    (⟨1, r, -algebraMap ℚ R (1/2) * W.a₁,
      -algebraMap ℚ R (1/2) * (W.a₃ + r * W.a₁)⟩ : WeierstrassCurve.VariableChange R) • W =
    (⟨0, 2*r-s-t, 0, (s-r)*(t-r), 0⟩ : WeierstrassCurve R) := by
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have hrat (q : ℚ) : algebraMap R (FractionRing R) (algebraMap ℚ R q) =
      (q : FractionRing R) := map_ratCast ((algebraMap R (FractionRing R)).comp (algebraMap ℚ R)) q
  have ha' := congrArg (algebraMap R (FractionRing R)) ha
  have hb' := congrArg (algebraMap R (FractionRing R)) hb
  have hc' := congrArg (algebraMap R (FractionRing R)) hc
  simp only [map_add, map_neg, map_mul, map_pow, hrat] at ha' hb' hc'
  rw [WeierstrassCurve.variableChange_def]
  ext <;> dsimp only <;> simp only [inv_one, Units.val_one, one_pow, one_mul]
  all_goals
    apply IsFractionRing.injective R (FractionRing R)
    simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_zero, map_ofNat, hrat]
  · ring
  · linear_combination ha'
  · ring
  · linear_combination hb' + 2 * algebraMap R (FractionRing R) r * ha'
  · linear_combination hc' + algebraMap R (FractionRing R) r * hb' +
      (algebraMap R (FractionRing R) r)^2 * ha'

/-- Scaling the translated roots gives exactly the Legendre coefficients. -/
theorem scaled_curve {R : Type u} [CommRing R] (r s t lam : R) (v : Rˣ)
    (hv : (v : R)^2 = s-r) (hlam : lam * (s-r) = t-r) :
    (⟨v, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) •
      (⟨0, 2*r-s-t, 0, (s-r)*(t-r), 0⟩ : WeierstrassCurve R) = legendreAt R lam := by
  have h₂ : 2*r-s-t = -(lam+1)*(v : R)^2 := by
    rw [hv]
    linear_combination hlam
  have h₄ : (s-r)*(t-r) = lam*(v : R)^4 := by
    rw [← hlam, ← hv]
    ring
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp only [legendreAt, mul_zero, zero_mul, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), zero_add]
  · rw [h₂]
    calc (↑v⁻¹ : R)^2 * (-(lam+1)*(v : R)^2) =
          -(lam+1) * ((↑v⁻¹ : R)*(v : R))^2 := by ring
         _ = -(lam+1) := by rw [Units.inv_mul]; ring
  · rw [h₄]
    calc (↑v⁻¹ : R)^4 * (lam*(v : R)^4) = lam * ((↑v⁻¹ : R)*(v : R))^4 := by ring
         _ = lam := by rw [Units.inv_mul]; ring

/-- The admissible coordinate change has the required scaling, translation,
and completed-square ordinate. -/
theorem normalized_curve {R : Type u} [CommRing R] [IsDomain R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (r s t lam : R) (v : Rˣ)
    (ha : W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2 = -(r+s+t))
    (hb : W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃ = r*s+r*t+s*t)
    (hc : W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2 = -(r*s*t))
    (hv : (v : R)^2 = s-r) (hlam : lam * (s-r) = t-r) :
    (⟨v, r, -algebraMap ℚ R (1/2) * W.a₁,
      -algebraMap ℚ R (1/2) * (W.a₃ + r * W.a₁)⟩ : WeierstrassCurve.VariableChange R) • W =
        legendreAt R lam := by
  let A : WeierstrassCurve.VariableChange R :=
    ⟨1, r, -algebraMap ℚ R (1/2) * W.a₁, -algebraMap ℚ R (1/2) * (W.a₃ + r * W.a₁)⟩
  let B : WeierstrassCurve.VariableChange R := ⟨v, 0, 0, 0⟩
  have he : B * A =
      (⟨v, r, -algebraMap ℚ R (1/2) * W.a₁,
        -algebraMap ℚ R (1/2) * (W.a₃ + r * W.a₁)⟩ : WeierstrassCurve.VariableChange R) := by
    ext <;> simp [A, B, WeierstrassCurve.VariableChange.mul_def]
  rw [← he, mul_smul, show A • W = _ from translated_curve W r s t ha hb hc]
  exact scaled_curve r s t lam v hv hlam

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

/-- Identify the scalar map in the frozen definition with the actual chart
algebra structure. -/
theorem chartScalar_eq {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    chartScalar R W = algebraMap R (ChartRing R W) := by
  unfold chartScalar chartInclusion structureMap
  rw [kw_pbac_awayι_comp_projModelStrCR R W.toProjective 2]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom _))).hom = _
  rw [Spec.preimage_map]
  rfl

theorem chartScalar_apply {R : Type u} [CommRing R] (W : WeierstrassCurve R) (r : R) :
    chartScalar R W r = fromZeroRingHom (projModelGradingCR W.toProjective) _
      (algebraMap R ((projModelGradingCR W.toProjective) 0) r) := by
  unfold chartScalar chartInclusion structureMap projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rw [Spec.preimage_map]
  rfl

/-- The coefficient-change morphism preserves the actual zero section. -/
theorem coefficient_origin {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (f : R →+* S)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective f φ) :
    origin S (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ origin R W := by
  obtain ⟨hO, hx, hz⟩ := isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  obtain ⟨hO', hx', hz'⟩ := isOriginChartSection_kwZeroSect_kwYChartEval (W.map f).toProjective
  obtain ⟨χ, hχ, hc, hχx, hχz⟩ :=
    exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom W.toProjective f φ hφ hcoef
      (kwYChartEval S (W.map f))
  have he : χ = f.comp (kwYChartEval R W) := by
    apply ringHom_originChartRing_ext W χ (f.comp (kwYChartEval R W))
    · intro r
      rw [hc]
      change kwYChartEval S (W.map f) (TwoTorsionAffineCoordinates.cY (W.map f) (f r)) =
        f (kwYChartEval R W (TwoTorsionAffineCoordinates.cY W r))
      have hcS : ∀ z, kwYChartEval S (W.map f) (TwoTorsionAffineCoordinates.cY (W.map f) z) = z :=
        fun z => RingHom.congr_fun (kwYChartEval_section S (W.map f)) z
      have hcR : ∀ z, kwYChartEval R W (TwoTorsionAffineCoordinates.cY W z) = z :=
        fun z => RingHom.congr_fun (kwYChartEval_section R W) z
      rw [hcS, hcR]
    · simpa only [RingHom.comp_apply, hx, hx', map_zero] using hχx
    · simpa only [RingHom.comp_apply, hz, hz', map_zero] using hχz
  change (kwZeroSect S (W.map f)).val ≫ Proj.map φ hφ =
    Spec.map (CommRingCat.ofHom f) ≫ (kwZeroSect R W).val
  rw [hO', Category.assoc, hχ, he, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hO]

/-- The marked Weierstrass model has its actual coefficient base change,
including a compatible map of affine coordinate rings. -/
theorem coefficient_comparison {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (f : R →+* S) :
    ∃ (b : Curve S (W.map f) ⟶ Curve R W)
      (a : ChartRing R W →+* ChartRing S (W.map f)),
      IsPullback b (structureMap S (W.map f)) (structureMap R W) (Spec.map (CommRingCat.ofHom f)) ∧
      origin S (W.map f) ≫ b = Spec.map (CommRingCat.ofHom f) ≫ origin R W ∧
      Spec.map (CommRingCat.ofHom a) ≫ chartInclusion R W = chartInclusion S (W.map f) ≫ b ∧
      a (xOverZ W.toProjective) = xOverZ (W.map f).toProjective ∧
      a (yOverZ W.toProjective) = yOverZ (W.map f).toProjective ∧
      ∀ (P : Base R ⟶ Curve R W) (x y : R), HasCoordinates R W P x y →
        ∃ Q : Base S ⟶ Curve S (W.map f), HasCoordinates S (W.map f) Q (f x) (f y) ∧
          Q ≫ b = Spec.map (CommRingCat.ofHom f) ≫ P := by
  obtain ⟨φ, hφ, hc⟩ := exists_isCoefficientHom W.toProjective f
  obtain ⟨a, ha, hx, hy⟩ := exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
    W.toProjective f φ hφ hc
  have hb := isPullback_projMap_of_isCoefficientHom W.toProjective f φ hφ hc
  refine ⟨Proj.map φ hφ, a, hb, coefficient_origin W f φ hφ hc, ha.symm, hx, hy, ?_⟩
  intro P x y hP
  let Q := hb.lift (Spec.map (CommRingCat.ofHom f) ≫ P) (𝟙 (Base S)) (by
    change (Spec.map (CommRingCat.ofHom f) ≫ P) ≫ structureMap R W = _
    rw [Category.assoc, hP.1, Category.comp_id, Category.id_comp])
  have hQ : Q ≫ structureMap S (W.map f) = 𝟙 (Base S) := hb.lift_snd _ _ _
  have hQb : Q ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ P := hb.lift_fst _ _ _
  refine ⟨Q, ⟨hQ, ?_⟩, hQb⟩
  exact isSectionThrough_map_of_comp_projMap_eq_of_isCoefficientHom W.toProjective f φ hφ hc
    ⟨P, hP.1⟩ x y hP.2 ⟨Q, hQ⟩ hQb

/-- An affine section evaluates base scalars by the identity. -/
theorem coordinate_scalar {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (P : Base R ⟶ Curve R W) (hP : P ≫ structureMap R W = 𝟙 _)
    (χ : ChartRing R W →+* R)
    (hχ : P = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W) (r : R) :
    χ (chartScalar R W r) = r := by
  have he : Spec.map (CommRingCat.ofHom ((χ.comp (chartScalar R W)))) = 𝟙 (Base R) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    unfold chartScalar
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← Category.assoc, ← hχ, hP]
  have hh : CommRingCat.ofHom (χ.comp (chartScalar R W)) = 𝟙 (CommRingCat.of R) :=
    Spec.map_injective (he.trans (Spec.map_id _).symm)
  exact congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of R => g.hom r) hh

/-- A projective variable change, tied to its affine chart formulas. -/
theorem variable_comparison {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    ∃ (b : Curve R (C • W) ⟶ Curve R W)
      (a : ChartRing R W →+* ChartRing R (C • W)),
      IsIso b ∧ b ≫ structureMap R W = structureMap R (C • W) ∧
      origin R (C • W) ≫ b = origin R W ∧
      Spec.map (CommRingCat.ofHom a) ≫ chartInclusion R W = chartInclusion R (C • W) ≫ b ∧
      a (xOverZ W.toProjective) = chartScalar R (C • W) ((C.u : R)^2) *
        xOverZ (C • W).toProjective + chartScalar R (C • W) C.r ∧
      a (yOverZ W.toProjective) = chartScalar R (C • W) ((C.u : R)^3) *
        yOverZ (C • W).toProjective + chartScalar R (C • W) ((C.u : R)^2 * C.s) *
        xOverZ (C • W).toProjective + chartScalar R (C • W) C.t := by
  obtain ⟨φ, hφ, hc, hi, hb⟩ := exists_isVariableChangeHom_isIso_projMap W.toProjective C
  obtain ⟨a, ha, _, hx, hy⟩ :=
    exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
      W.toProjective C φ hφ hc
  refine ⟨Proj.map φ hφ, a, hi, hb,
    kwZeroSect_comp_projMap_of_isVariableChangeHom W C φ hφ hc, ha.symm, ?_, ?_⟩
  · simpa only [chartScalar_apply] using hx
  · simpa only [chartScalar_apply] using hy

/-- Chart formulas determine the images of actual affine sections. -/
theorem coordinates_under_map {R : Type u} [CommRing R]
    (W V : WeierstrassCurve R) (b : Curve R V ⟶ Curve R W)
    (hb : b ≫ structureMap R W = structureMap R V)
    (a : ChartRing R W →+* ChartRing R V)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ chartInclusion R W = chartInclusion R V ≫ b)
    (u2 r u3 s t : R)
    (hx : a (xOverZ W.toProjective) = chartScalar R V u2 * xOverZ V.toProjective + chartScalar R V r)
    (hy : a (yOverZ W.toProjective) = chartScalar R V u3 * yOverZ V.toProjective +
      chartScalar R V s * xOverZ V.toProjective + chartScalar R V t)
    (P : Base R ⟶ Curve R V) (x y : R) (hP : HasCoordinates R V P x y) :
    HasCoordinates R W (P ≫ b) (u2*x+r) (u3*y+s*x+t) := by
  obtain ⟨hPo, χ, hχ, hχx, hχy⟩ := hP
  refine ⟨by rw [Category.assoc, hb, hPo], χ.comp a, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha, ← Category.assoc, ← hχ]
  · change χ (a _) = _
    rw [hx, map_add, map_mul, coordinate_scalar V P hPo χ hχ, coordinate_scalar V P hPo χ hχ, hχx]
  · change χ (a _) = _
    rw [hy, map_add, map_add, map_mul, map_mul,
      coordinate_scalar V P hPo χ hχ, coordinate_scalar V P hPo χ hχ,
      coordinate_scalar V P hPo χ hχ, hχx, hχy]

end NormalFormConstruction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open NormalFormConstruction WeierstrassCurve.DrinfeldGlobal

/-- An ordered full two-torsion marking admits a pointed Legendre presentation
over a connected normal finite étale cover of degree at most two. -/
theorem legendre_normal_form :
    ∀ (k : Type u) [Field k] [CharZero k] (R : Type u) [CommRing R] [IsDomain R]
      [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
      (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
      (M : FullLevel R W G 2 (CategoryTheory.CategoryStruct.id (Base R))),
      Nonempty (NormalForm k R W G M) := by
  intro k _ _ R _ _ _ _ _ _ W _ G hG M
  obtain ⟨e, he⟩ := two_torsion_affine_coordinates R W G hG M
  have hs := two_torsion_split_cubic R W G hG M e he
  obtain ⟨lam, hlam, hpar⟩ := exists_parameter e hs.1
  obtain ⟨D⟩ := exists_squareRootCover k R (e 1 - e 0) (hs.1 1 0 (by decide))
  let S := D.ring
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  letI : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
  have hrat (q : ℚ) : f (algebraMap ℚ R q) = algebraMap ℚ S q := rfl
  have hi := TwoTorsionSplitCubicR0177.roots_injective G hG M he
  obtain ⟨h₂, h₄, h₆⟩ := TwoTorsionSplitCubicR0177.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2) (e 0) (e 1) (e 2)
    (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))
  have h₂S := congrArg f h₂
  have h₄S := congrArg f h₄
  have h₆S := congrArg f h₆
  simp only [map_add, map_mul, map_pow, map_neg, hrat] at h₂S h₄S h₆S
  have hv : (D.scaling : S)^2 = f (e 1) - f (e 0) := by
    change (D.scaling : D.ring)^2 = algebraMap R D.ring (e 1) - algebraMap R D.ring (e 0)
    simpa only [map_sub] using D.scaling_eq
  have hpS : f lam * (f (e 1) - f (e 0)) = f (e 2) - f (e 0) := by
    simpa only [map_mul, map_sub] using congrArg f hpar
  let C : WeierstrassCurve.VariableChange S :=
    ⟨D.scaling, f (e 0), -f (algebraMap ℚ R (1/2)) * f W.a₁,
      -f (algebraMap ℚ R (1/2)) * (f W.a₃ + f (e 0) * f W.a₁)⟩
  have hnorm : C • W.map f.toRingHom = legendreAt S (f lam) :=
    normalized_curve (W.map f.toRingHom) (f (e 0)) (f (e 1)) (f (e 2)) (f lam)
      D.scaling h₂S h₄S h₆S hv hpS
  have hlu : IsUnit (f lam * (f lam - 1)) := by
    simpa only [map_mul, map_sub, map_one] using hlam.map f
  obtain ⟨pmap, hpmap⟩ := exists_parameterMap k S (f lam) hlu
  let V := (legendre k).map pmap.toRingHom
  have hV : V = legendreAt S (f lam) := by
    ext <;> simp [V, legendre, legendreAt, hpmap] <;> ring
  have hCV : C • W.map f.toRingHom = V := hnorm.trans hV.symm
  obtain ⟨b, a, hb, hbO, ha, hax, hay, hlift⟩ := coefficient_comparison W f.toRingHom
  have hvc := variable_comparison (W.map f.toRingHom) C
  rw [hCV] at hvc
  obtain ⟨c, ac, hcI, hc, hcO, hac, hacx, hacy⟩ := hvc
  letI := hcI
  obtain ⟨hVE, GV, hGV, MV, hP, hQ, _⟩ := standard_legendre_two_marking S (f lam) hlu
  have hpoints : ∃ P Q : Base S ⟶ Curve S V,
      HasCoordinates S V P 0 0 ∧ HasCoordinates S V Q 1 0 := by
    rw [hV]
    exact ⟨MV.x.val, MV.y.val, hP, hQ⟩
  obtain ⟨P, Q, hP, hQ⟩ := hpoints
  obtain ⟨PX, hPX, hPXb⟩ := hlift M.x.val (e 0)
    (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 0 + W.a₃)) (he 0)
  obtain ⟨QY, hQY, hQYb⟩ := hlift M.y.val (e 1)
    (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 1 + W.a₃)) (he 1)
  have hPc := coordinates_under_map (W.map f.toRingHom) V c hc ac hac
    ((C.u : S)^2) C.r ((C.u : S)^3) ((C.u : S)^2 * C.s) C.t hacx hacy P 0 0 hP
  have hQc := coordinates_under_map (W.map f.toRingHom) V c hc ac hac
    ((C.u : S)^2) C.r ((C.u : S)^3) ((C.u : S)^2 * C.s) C.t hacx hacy Q 1 0 hQ
  have hPc' : HasCoordinates S (W.map f.toRingHom) (P ≫ c) (f (e 0))
      (f (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 0 + W.a₃))) := by
    convert hPc using 1 <;> simp only [C, map_mul, map_neg, map_add, mul_zero, add_zero, zero_add] <;> ring
  have hQc' : HasCoordinates S (W.map f.toRingHom) (Q ≫ c) (f (e 1))
      (f (-(algebraMap ℚ R (1/2)) * (W.a₁ * e 1 + W.a₃))) := by
    convert hQc using 1 <;> simp only [C, map_mul, map_neg, map_add, mul_zero, add_zero, zero_add, mul_one, hv] <;> ring
  have hPe : P ≫ c = PX := TwoTorsionSplitCubicR0177.coordinates_ext hPc' hPX
  have hQe : Q ≫ c = QY := TwoTorsionSplitCubicR0177.coordinates_ext hQc' hQY
  obtain ⟨hfinite, hetale, hsurj, hdegree⟩ := squareRootCover_geometry D
  refine ⟨{ ring := S
            inclusion := f
            finite := hfinite
            etale := hetale
            surjective := hsurj
            degree := hdegree
            roots := e
            coordinates := he
            parameter := lam
            parameter_unit := hlam
            parameter_eq := hpar
            scaling := D.scaling
            scaling_eq := D.scaling_eq
            parameterMap := pmap
            parameterMap_eq := hpmap
            map := c ≫ b
            cartesian := ?_
            origin_eq := ?_
            affineMap := ac.comp a
            affine_eq := ?_
            x_eq := ?_
            y_eq := ?_
            point0 := P
            point1 := Q
            point0_coordinates := hP
            point1_coordinates := hQ
            point0_eq := ?_
            point1_eq := ?_ }⟩
  · have hcP : IsPullback c (structureMap S V) (structureMap S (W.map f.toRingHom)) (𝟙 (Base S)) :=
      IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hc⟩
    simpa only [Category.id_comp] using hcP.paste_horiz hb
  · rw [← Category.assoc, hcO, hbO]
  · rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha,
      ← Category.assoc, hac, Category.assoc]
  · rw [RingHom.comp_apply, hax, hacx]
  · rw [RingHom.comp_apply, hay, hacy, RingHom.comp_apply, hax, hacx]
    simp only [C, map_mul, map_add, map_neg]
    ring
  · rw [← Category.assoc, hPe, hPXb]
  · rw [← Category.assoc, hQe, hQYb]

#print axioms legendre_normal_form
end ArithmeticThetaLegendreComparisonR0177
