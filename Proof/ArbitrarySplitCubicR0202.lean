module

public import TwoTorsionSplitCubicR0177

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaArbitraryAffineR0202
namespace ArbitrarySplitCubic
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open WeierstrassCurve.DrinfeldGlobal
open P2MW.S_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough.SectionThroughBody

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

/-- Equality of coordinates after a ring map gives equality of the actual
sections after precomposition by the corresponding affine scheme map. -/
lemma coordinates_comp {S : Type u} [CommRing S] (f : R →+* S)
    {P Q : Base R ⟶ Curve R W} {x y x' y' : R}
    (hP : HasCoordinates R W P x y) (hQ : HasCoordinates R W Q x' y')
    (hx : f x = f x') (hy : f y = f y') :
    Spec.map (CommRingCat.ofHom f) ≫ P =
      Spec.map (CommRingCat.ofHom f) ≫ Q := by
  obtain ⟨hPo, χ, hχ, hχx, hχy⟩ := hP
  obtain ⟨hQo, ψ, hψ, hψx, hψy⟩ := hQ
  obtain ⟨g, hbij, hC, hX, hY⟩ := exists_equiv W.toProjective
  let E := RingEquiv.ofBijective g hbij
  have hχeval := comp_symm_mk_eq W.toProjective
    (S := ⟨P, hPo⟩) hχ g hbij hC hX hY
  have hψeval := comp_symm_mk_eq W.toProjective
    (S := ⟨Q, hQo⟩) hψ g hbij hC hX hY
  have hpoly : (f.comp (χ.comp E.symm.toRingHom)).comp (mkCR W.toProjective) =
      (f.comp (ψ.comp E.symm.toRingHom)).comp (mkCR W.toProjective) := by
    change f.comp ((χ.comp E.symm.toRingHom).comp (mkCR W.toProjective)) =
      f.comp ((ψ.comp E.symm.toRingHom).comp (mkCR W.toProjective))
    rw [hχeval, hψeval,
      hχx, hχy, hψx, hψy]
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        simp
      · simpa using hx
    · simpa using hy
  have hquot := Ideal.Quotient.ringHom_ext hpoly
  have hmap : f.comp χ = f.comp ψ := by
    ext a
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] using
      congrArg (fun k : CR W.toProjective →+* S => k (E a)) hquot
  rw [hχ, hψ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun k : ChartRing R W →+* S =>
    Spec.map (CommRingCat.ofHom k) ≫ chartInclusion R W) hmap

lemma differences_units [Algebra ℚ R] (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 2 (𝟙 (Base R))) {e : Fin 3 → R}
    (he : TwoCoordinates R W G M e) (i j : Fin 3) (hij : i ≠ j) :
    IsUnit (e i - e j) := by
  classical
  by_contra hu
  obtain ⟨m, hm, hem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
  letI : m.IsMaximal := hm
  let f := Ideal.Quotient.mk m
  have hx : f (e i) = f (e j) := Ideal.Quotient.eq.mpr hem
  have hy : f (-(algebraMap ℚ R (1/2)) * (W.a₁ * e i + W.a₃)) =
      f (-(algebraMap ℚ R (1/2)) * (W.a₁ * e j + W.a₃)) := by
    simp only [map_mul, map_add, hx]
  have hp := coordinates_comp f (he i) (he j) hx hy
  have hab : ((![1, 0, 1] i, ![0, 1, 1] i) : Fin 2 × Fin 2) ≠
      (![1, 0, 1] j, ![0, 1, 1] j) := by
    fin_cases i <;> fin_cases j <;> simp_all
  have hd := FullLevelTorsionSplittingR0175.coordinates_disjoint G hG
    (by decide : 0 < 2) M _ _ hab
  rw [← TwoTorsionSplitCubicR0177.twoPoint_eq_coordinate G M i,
    ← TwoTorsionSplitCubicR0177.twoPoint_eq_coordinate G M j] at hd
  let z : Base (R ⧸ m) := ⟨⊥, Ideal.isPrime_bot⟩
  have hz := congrArg (fun k : Base (R ⧸ m) ⟶ Curve R W => k z) hp
  exact Set.disjoint_left.mp hd
    ⟨Spec.map (CommRingCat.ofHom f) z, rfl⟩
    ⟨Spec.map (CommRingCat.ofHom f) z, hz.symm⟩

/-- Unit differences permit coefficient comparison in the original ring,
without passing to a reduced quotient. -/
lemma cubic_coefficients (a b c r s t : R)
    (hrs : IsUnit (r-s)) (hst : IsUnit (s-t)) (hrt : IsUnit (r-t))
    (hr : r^3 + a*r^2 + b*r + c = 0)
    (hs : s^3 + a*s^2 + b*s + c = 0)
    (ht : t^3 + a*t^2 + b*t + c = 0) :
    a = -(r+s+t) ∧ b = r*s+r*t+s*t ∧ c = -(r*s*t) := by
  have h₁ : r^2+r*s+s^2+a*(r+s)+b = 0 := by
    apply hrs.mul_left_cancel
    rw [mul_zero]
    linear_combination hr-hs
  have h₂ : s^2+s*t+t^2+a*(s+t)+b = 0 := by
    apply hst.mul_left_cancel
    rw [mul_zero]
    linear_combination hs-ht
  have ha : a = -(r+s+t) := by
    have h₃ : r+s+t+a = 0 := by
      apply hrt.mul_left_cancel
      rw [mul_zero]
      linear_combination h₁-h₂
    linear_combination h₃
  have hb : b = r*s+r*t+s*t := by linear_combination h₁-(r+s)*ha
  exact ⟨ha, hb, by linear_combination hr-r^2*ha-r*hb⟩

end ArbitrarySplitCubic

open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177

/-- Actual marked two-torsion coordinates split the completed cubic over every
commutative rational base ring, with every pairwise difference a unit. -/
theorem arbitrary_split_cubic :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 2 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (e : Fin 3 → R), ArithmeticThetaLegendreComparisonR0177.TwoCoordinates R W G M e → ArithmeticThetaLegendreComparisonR0177.SplitCubic R W e := by
  intro R _ _ W _ G hG M e he
  have hu := ArbitrarySplitCubic.differences_units G hG M he
  obtain ⟨ha, hb, hc⟩ := ArbitrarySplitCubic.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
    (e 0) (e 1) (e 2)
    (hu 0 1 (by decide)) (hu 1 2 (by decide)) (hu 0 2 (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))
  exact ⟨hu, TwoTorsionSplitCubicR0177.factorization e ha hb hc⟩

end ArithmeticThetaArbitraryAffineR0202
