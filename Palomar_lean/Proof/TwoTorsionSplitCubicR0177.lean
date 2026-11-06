module

public import LegendreComparisonDefinitionsR0177
public import FullLevelTorsionSplittingR0175
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
namespace TwoTorsionSplitCubicR0177
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open WeierstrassCurve.DrinfeldGlobal

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

lemma sectionThrough {P : Base R ⟶ Curve R W} {x y : R}
    (h : HasCoordinates R W P x y) :
    IsSectionThrough (W := W.toProjective) ⟨P, h.1⟩ x y := h.2

lemma equation {P : Base R ⟶ Curve R W} {x y : R}
    (h : HasCoordinates R W P x y) : W.toAffine.Equation x y := by
  exact (equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    W.toProjective).1 x y |>.mpr ⟨⟨P, h.1⟩, sectionThrough h⟩

lemma coordinates_ext {P Q : Base R ⟶ Curve R W} {x y : R}
    (hP : HasCoordinates R W P x y) (hQ : HasCoordinates R W Q x y) : P = Q := by
  have h := (equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    W.toProjective).2 ⟨P, hP.1⟩ ⟨Q, hQ.1⟩ x y x y
      (sectionThrough hP) (sectionThrough hQ)
  exact congrArg Subtype.val (h.mpr ⟨rfl, rfl⟩)


lemma twoPoint_eq_coordinate (G : Law R W)
    (M : FullLevel R W G 2 (𝟙 (Base R))) (i : Fin 3) :
    twoPoint R W G M i = coordinatePoint R W G M
      (![1, 0, 1] i) (![0, 1, 1] i) := by
  fin_cases i <;> simp [twoPoint, coordinatePoint,
    G.nsmul_zero, G.one_mul, G.mul_one]

lemma point_ne [IsDomain R] (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 2 (𝟙 (Base R))) {i j : Fin 3} (hij : i ≠ j) :
    twoPoint R W G M i ≠ twoPoint R W G M j := by
  have hp : ((![1, 0, 1] i, ![0, 1, 1] i) : Fin 2 × Fin 2) ≠
      (![1, 0, 1] j, ![0, 1, 1] j) := by
    fin_cases i <;> fin_cases j <;> simp_all
  have hd := FullLevelTorsionSplittingR0175.coordinates_disjoint G hG
    (by decide : 0 < 2) M _ _ hp
  rw [← twoPoint_eq_coordinate G M i, ← twoPoint_eq_coordinate G M j] at hd
  intro he
  let z : Base R := ⟨⊥, Ideal.isPrime_bot⟩
  exact Set.disjoint_left.mp hd ⟨z, rfl⟩ ⟨z, by rw [he]⟩

lemma roots_injective [IsDomain R] [Algebra ℚ R]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 2 (𝟙 (Base R))) {e : Fin 3 → R}
    (h : TwoCoordinates R W G M e) : Function.Injective e := by
  intro i j he
  by_contra hij
  apply point_ne G hG M hij
  exact coordinates_ext (h i) (by simpa only [he] using h j)

lemma half_identity [Algebra ℚ R] :
    2 * algebraMap ℚ R (1/2) = 1 := by
  have h := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1/2) = 1 by norm_num)
  simpa only [map_mul, map_ofNat, map_one] using h

lemma quarter_identity [Algebra ℚ R] :
    algebraMap ℚ R (1/4) = (algebraMap ℚ R (1/2))^2 := by
  rw [← map_pow]
  norm_num

lemma root_equation [Algebra ℚ R] {P : Base R ⟶ Curve R W} {x : R}
    (h : HasCoordinates R W P x
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * x + W.a₃))) :
    x^3 + (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2) * x^2 +
      (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃) * x +
      (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2) = 0 := by
  have he := equation h
  rw [WeierstrassCurve.Affine.equation_iff] at he
  rw [quarter_identity]
  linear_combination -he +
    (algebraMap ℚ R (1/2)) * ((W.a₁ * x + W.a₃)^2 - W.a₁ * W.a₃ * x) * (half_identity (R := R))

lemma cubic_coefficients [IsDomain R] (a b c r s t : R)
    (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t)
    (hr : r^3 + a*r^2 + b*r + c = 0)
    (hs : s^3 + a*s^2 + b*s + c = 0)
    (ht : t^3 + a*t^2 + b*t + c = 0) :
    a = -(r+s+t) ∧ b = r*s+r*t+s*t ∧ c = -(r*s*t) := by
  have h₁ : r^2+r*s+s^2+a*(r+s)+b = 0 := by
    apply (mul_eq_zero.mp (show (r-s)*(r^2+r*s+s^2+a*(r+s)+b) = 0 by
      linear_combination hr-hs)).resolve_left (sub_ne_zero.mpr hrs)
  have h₂ : s^2+s*t+t^2+a*(s+t)+b = 0 := by
    apply (mul_eq_zero.mp (show (s-t)*(s^2+s*t+t^2+a*(s+t)+b) = 0 by
      linear_combination hs-ht)).resolve_left (sub_ne_zero.mpr hst)
  have ha : a = -(r+s+t) := by
    have h₃ : r+s+t+a = 0 :=
      (mul_eq_zero.mp (show (r-t)*(r+s+t+a) = 0 by
        linear_combination h₁-h₂)).resolve_left (sub_ne_zero.mpr hrt)
    linear_combination h₃
  have hb : b = r*s+r*t+s*t := by linear_combination h₁-(r+s)*ha
  exact ⟨ha, hb, by linear_combination hr-r^2*ha-r*hb⟩


set_option maxRecDepth 4096 in
lemma discriminant_from_coefficients [IsDomain R] [Algebra ℚ R]
    (r s t : R)
    (ha : W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2 = -(r+s+t))
    (hb : W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃ = r*s+r*t+s*t)
    (hc : W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2 = -(r*s*t)) :
    W.Δ = 16 * (r-s)^2 * (r-t)^2 * (s-t)^2 := by
  have ha' : W.a₂ = -(r+s+t) - algebraMap ℚ R (1/4) * W.a₁^2 := by
    linear_combination ha
  have hb' : W.a₄ = r*s+r*t+s*t - algebraMap ℚ R (1/2) * W.a₁ * W.a₃ := by
    linear_combination hb
  have hc' : W.a₆ = -(r*s*t) - algebraMap ℚ R (1/4) * W.a₃^2 := by
    linear_combination hc
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha', hb', hc']
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  apply IsFractionRing.injective R (FractionRing R)
  have hrat (q : ℚ) : algebraMap R (FractionRing R) (algebraMap ℚ R q) =
      (q : FractionRing R) :=
    map_ratCast ((algebraMap R (FractionRing R)).comp (algebraMap ℚ R)) q
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, hrat]
  norm_num
  ring

lemma factorization [Algebra ℚ R] (e : Fin 3 → R)
    (ha : W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2 = -(e 0+e 1+e 2))
    (hb : W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃ = e 0*e 1+e 0*e 2+e 1*e 2)
    (hc : W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2 = -(e 0*e 1*e 2)) :
    completedCubic R W = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (e i)) := by
  simp only [completedCubic, ha, hb, hc, Fin.prod_univ_three,
    map_neg, map_add, map_mul]
  ring

end TwoTorsionSplitCubicR0177

open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

/-- The three marked nonidentity two-torsion coordinates split the completed
cubic, and ellipticity makes all root differences units on the entire base. -/
theorem two_torsion_split_cubic :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 2 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (e : Fin 3 → R), ArithmeticThetaLegendreComparisonR0177.TwoCoordinates R W G M e → ArithmeticThetaLegendreComparisonR0177.SplitCubic R W e := by
  intro R _ _ _ _ _ W _ G hG M e he
  have hi := TwoTorsionSplitCubicR0177.roots_injective G hG M he
  obtain ⟨ha, hb, hc⟩ := TwoTorsionSplitCubicR0177.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
    (e 0) (e 1) (e 2)
    (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))
  have hd := TwoTorsionSplitCubicR0177.discriminant_from_coefficients
    (e 0) (e 1) (e 2) ha hb hc
  have hu := W.isUnit_Δ
  rw [hd] at hu
  simp only [IsUnit.mul_iff, isUnit_pow_iff (by decide : 2 ≠ 0)] at hu
  have h01 : IsUnit (e 0 - e 1) := hu.1.1.2
  have h02 : IsUnit (e 0 - e 2) := hu.1.2
  have h12 : IsUnit (e 1 - e 2) := hu.2
  have h10 : IsUnit (e 1 - e 0) := by convert h01.neg using 1 <;> ring
  have h20 : IsUnit (e 2 - e 0) := by convert h02.neg using 1 <;> ring
  have h21 : IsUnit (e 2 - e 1) := by convert h12.neg using 1 <;> ring
  refine ⟨?_, TwoTorsionSplitCubicR0177.factorization e ha hb hc⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try { exact (hij rfl).elim }
  · exact h01
  · exact h02
  · exact h10
  · exact h12
  · exact h20
  · exact h21
end ArithmeticThetaLegendreComparisonR0177
