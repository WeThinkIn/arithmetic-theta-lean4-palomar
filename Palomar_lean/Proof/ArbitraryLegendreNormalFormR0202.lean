module

public import ArbitraryAffineLevelDefinitionsR0202
public import ArbitraryTwoCoordinatesR0202
public import ArbitrarySplitCubicR0202
public import LegendreNormalFormR0177

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202
namespace ArbitraryNormalForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction

/-- The whole quadratic torsor, without choosing a connected component. -/
structure SquareRootCover (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (d : R) where
  ring : Type u
  [commRing : CommRing ring]
  [baseAlgebra : Algebra R ring]
  [algebra : Algebra k ring]
  [tower : IsScalarTower k R ring]
  finite : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R ring)))
  etale : Etale (Spec.map (CommRingCat.ofHom (algebraMap R ring)))
  surjective : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R ring)))
  degree : ∀ z, (Spec.map (CommRingCat.ofHom (algebraMap R ring))).finrank z = 2
  scaling : ringˣ
  scaling_eq : (scaling : ring)^2 = algebraMap R ring d
attribute [instance] SquareRootCover.commRing SquareRootCover.baseAlgebra
  SquareRootCover.algebra SquareRootCover.tower

open Polynomial in
lemma exists_squareRootCover (k R : Type u) [Field k] [CommRing R]
    [Algebra ℚ R] [Algebra k R] (d : R) (hd : IsUnit d) :
    Nonempty (SquareRootCover k R d) := by
  classical
  let f : R[X] := X^2 - C d
  have hfm : f.Monic := monic_X_pow_sub_C d (by decide)
  have hroot : (AdjoinRoot.root f)^2 = algebraMap R (AdjoinRoot f) d := by
    have h := AdjoinRoot.mk_self (f := f)
    change AdjoinRoot.mk f (X^2 - C d) = 0 at h
    simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero,
      AdjoinRoot.algebraMap_eq] using h
  have hu : IsUnit (AdjoinRoot.root f) :=
    (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
      (hroot.symm ▸ hd.map (algebraMap R (AdjoinRoot f)))
  have htwo : IsUnit (2 : R) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  obtain ⟨hetale, hfinite⟩ := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit 2 d htwo hd
  letI : Algebra.Etale R (AdjoinRoot f) := hetale
  letI : Module.Finite R (AdjoinRoot f) := hfinite
  letI : Module.Free R (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have he : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  letI := hf
  letI := he
  have hdegree : ∀ z, (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))).finrank z = 2 := by
    intro z
    letI : Nontrivial R := PrimeSpectrum.nontrivial z
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free,
      (AdjoinRoot.powerBasis' hfm).finrank]
    exact natDegree_X_pow_sub_C
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))) := by
    apply (Scheme.Hom.one_le_finrank_iff_surjective _).mp
    intro z
    rw [hdegree]
    norm_num
  exact ⟨{ ring := AdjoinRoot f
           finite := hf
           etale := he
           surjective := hsurj
           degree := hdegree
           scaling := hu.unit
           scaling_eq := by simpa using hroot }⟩

theorem translated_curve {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (r s t : R)
    (ha : W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2 = -(r+s+t))
    (hb : W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃ = r*s+r*t+s*t)
    (hc : W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2 = -(r*s*t)) :
    (⟨1, r, -algebraMap ℚ R (1/2) * W.a₁,
      -algebraMap ℚ R (1/2) * (W.a₃ + r * W.a₁)⟩ : WeierstrassCurve.VariableChange R) • W =
    (⟨0, 2*r-s-t, 0, (s-r)*(t-r), 0⟩ : WeierstrassCurve R) := by
  have hh : algebraMap ℚ R (1/2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  have hq : algebraMap ℚ R (1/4) * 4 = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 4, ← map_mul]
    norm_num
  have hqh : algebraMap ℚ R (1/2) ^ 2 = algebraMap ℚ R (1/4) := by
    rw [← map_pow]
    norm_num
  rw [WeierstrassCurve.variableChange_def]
  ext <;> dsimp only <;> simp only [inv_one, Units.val_one, one_pow, one_mul]
  · linear_combination -W.a₁ * hh
  · linear_combination ha + W.a₁^2 * hqh - W.a₁^2 * algebraMap ℚ R (1/2) * hh
  · linear_combination -(W.a₃ + r * W.a₁) * hh
  · linear_combination hb + 2 * r * ha + 2 * r * W.a₁^2 * hqh -
      (2*r*W.a₁^2 + W.a₁*W.a₃) * algebraMap ℚ R (1/2) * hh
  · linear_combination hc + r * hb + r^2 * ha +
      (W.a₃^2 + r^2 * W.a₁^2) * hqh -
      (W.a₃^2 + r * W.a₁ * W.a₃ + r^2 * W.a₁^2) * algebraMap ℚ R (1/2) * hh

theorem normalized_curve {R : Type u} [CommRing R] [Algebra ℚ R]
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

end ArbitraryNormalForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction
open WeierstrassCurve.DrinfeldGlobal

theorem arbitrary_legendre_normal_form :
    ∀ (k : Type u) [Field k] [CharZero k] (R : Type u) [CommRing R]
      [Algebra ℚ R] [Algebra k R]
      (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
      (M : FullLevel R W G 2 (CategoryTheory.CategoryStruct.id (Base R))),
      Nonempty (ArithmeticThetaArbitraryAffineR0202.NormalForm k R W G M) := by
  intro k _ _ R _ _ _ W _ G hG M
  obtain ⟨e, he⟩ := arbitrary_two_coordinates R W G hG M
  have hs := arbitrary_split_cubic R W G hG M e he
  obtain ⟨lam, hlam, hpar⟩ := exists_parameter e hs.1
  obtain ⟨D⟩ := ArbitraryNormalForm.exists_squareRootCover k R (e 1 - e 0) (hs.1 1 0 (by decide))
  let S := D.ring
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  letI : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
  have hrat (q : ℚ) : f (algebraMap ℚ R q) = algebraMap ℚ S q := rfl
  obtain ⟨h₂, h₄, h₆⟩ := ArbitrarySplitCubic.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2) (e 0) (e 1) (e 2)
    (hs.1 0 1 (by decide)) (hs.1 1 2 (by decide)) (hs.1 0 2 (by decide))
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
    ArbitraryNormalForm.normalized_curve (W.map f.toRingHom) (f (e 0)) (f (e 1)) (f (e 2)) (f lam)
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
  have hpoints : ∃ P Q : Base S ⟶ Curve S V,
      HasCoordinates S V P 0 0 ∧ HasCoordinates S V Q 1 0 := by
    rw [hV]
    obtain ⟨P, hP⟩ := StandardMarking.exists_coordinate_section (legendreAt S (f lam)) 0 0 (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [legendreAt])
    obtain ⟨Q, hQ⟩ := StandardMarking.exists_coordinate_section (legendreAt S (f lam)) 1 0 (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [legendreAt])
    exact ⟨P, Q, hP, hQ⟩
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
  refine ⟨{ ring := S
            inclusion := f
            finite := D.finite
            etale := D.etale
            surjective := D.surjective
            degree := D.degree
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


#print axioms arbitrary_legendre_normal_form
end ArithmeticThetaArbitraryAffineR0202
