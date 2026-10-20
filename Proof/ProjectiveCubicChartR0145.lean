module

public import CompactifiedDifferentialDefinitionsR0145
public import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompactifiedDifferentialR0145
namespace ProjectiveCubicChart
open CategoryTheory AlgebraicGeometry MvPolynomial
open ArithmeticThetaCubicModelR0144
open WeierstrassCurve.DrinfeldGlobal
open WeierstrassProjModel

variable (R : Type u) [CommRing R]

def toMv : Polynomial (Polynomial R) →+* MvPolynomial (Fin 2) R :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (X 0)) (X 1)

def fromMv : MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R) :=
  eval₂Hom (Polynomial.C.comp Polynomial.C) ![Polynomial.C Polynomial.X, Polynomial.X]

lemma toMv_fromMv : (toMv R).comp (fromMv R) = RingHom.id _ := by
  ext i <;> simp [toMv, fromMv]
  fin_cases i <;> simp

lemma fromMv_toMv : (fromMv R).comp (toMv R) = RingHom.id _ := by
  ext <;> simp [toMv, fromMv]

def polynomialEquiv : Polynomial (Polynomial R) ≃+* MvPolynomial (Fin 2) R :=
  RingEquiv.ofRingHom (toMv R) (fromMv R)
    (toMv_fromMv R) (fromMv_toMv R)

variable (k : Type u) [Field k] [CharZero k] (r : ℕ)

omit [CharZero k] in
lemma polynomial_relation :
    polynomialEquiv (LaurentSeries k) (curve k r).toAffine.polynomial =
      cubicPolynomial k r := by
  simp [polynomialEquiv, toMv, WeierstrassCurve.Affine.polynomial,
    curve, cubicPolynomial, root, Fin.prod_univ_succ, Polynomial.eval₂_pow]
  ring

def affineEquiv :
    (Polynomial (Polynomial (LaurentSeries k)) ⧸ Ideal.span {(curve k r).toAffine.polynomial})
      ≃+* CubicRing k r :=
  Ideal.quotientEquiv _ _ (polynomialEquiv (LaurentSeries k)) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {cubicPolynomial k r} = Ideal.span {polynomialEquiv _ _}
    rw [polynomial_relation])

def chartScalar : LaurentSeries k →+* ChartRing k r :=
  (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR (curve k r).toProjective)
    (Submonoid.powers (coord (curve k r).toProjective 2))).comp
      (algebraMap (LaurentSeries k) (projModelGradingCR (curve k r).toProjective 0))

omit [CharZero k] in
lemma chart_structure : chartInclusion k r ≫ projectiveStructure k r =
    Spec.map (CommRingCat.ofHom (chartScalar k r)) := by
  rw [chartInclusion, projectiveStructure, projModelStrCR,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

omit [CharZero k] in
lemma exists_chartEquiv : ∃ e : ChartRing k r ≃+* CubicRing k r,
    (∀ a, e (chartScalar k r a) = algebraMap (LaurentSeries k) (CubicRing k r) a) ∧
    e (xOverZ (curve k r).toProjective) = cubicCoordinate k r false ∧
    e (yOverZ (curve k r).toProjective) = cubicCoordinate k r true := by
  obtain ⟨f, hf, hc, hm⟩ := exists_zChartAway_equiv_coordinateRing (curve k r).toProjective
  let e := (RingEquiv.ofBijective f hf).trans (affineEquiv k r)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a
    change affineEquiv k r (f (chartScalar k r a)) = _
    rw [show f (chartScalar k r a) = _ from RingHom.congr_fun hc a]
    change affineEquiv k r (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C a))) =
      Ideal.Quotient.mk _ (C a)
    simp [affineEquiv, polynomialEquiv, toMv]
  · have hb : (X 0 : MvPolynomial (Fin 3) (LaurentSeries k)) ∈
        homogeneousSubmodule (Fin 3) (LaurentSeries k) (1 • 1) := by
      simpa using (isHomogeneous_X (LaurentSeries k) (0 : Fin 3))
    have h := hm 1 (X 0) hb
    change f (xOverZ (curve k r).toProjective) = _ at h
    simp only [aeval_X, Matrix.cons_val_zero] at h
    change affineEquiv k r (f (xOverZ (curve k r).toProjective)) = _
    rw [h]
    simp [affineEquiv, polynomialEquiv, toMv, cubicCoordinate]
  · have hb : (X 1 : MvPolynomial (Fin 3) (LaurentSeries k)) ∈
        homogeneousSubmodule (Fin 3) (LaurentSeries k) (1 • 1) := by
      simpa using (isHomogeneous_X (LaurentSeries k) (1 : Fin 3))
    have h := hm 1 (X 1) hb
    change f (yOverZ (curve k r).toProjective) = _ at h
    simp only [aeval_X, Matrix.cons_val_one] at h
    change affineEquiv k r (f (yOverZ (curve k r).toProjective)) = _
    rw [h]
    simp [affineEquiv, polynomialEquiv, toMv, cubicCoordinate]

lemma spec_map_section {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom f)) a).symm

def specIso {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op

lemma specIso_hom {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    (specIso e).hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

lemma exists_chartIso : ∃ c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)),
    IsChartIso k r c := by
  obtain ⟨e, hc, hx, hy⟩ := exists_chartEquiv k r
  let c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)) :=
    specIso e
  refine ⟨c, ?_, ?_⟩
  · dsimp only [c]
    rw [specIso_hom]
    rw [chart_structure, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext hc
  · intro odd
    dsimp only [c, cubicScheme]
    rw [specIso_hom]
    rw [spec_map_section]
    cases odd
    · exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv hx
    · exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv hy

omit [CharZero k] in
lemma inverse_coordinates
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (hc : IsChartIso k r c) (odd : Bool) :
    c.inv.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
      (cubicCoordinate k r odd)) =
    (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv
      (if odd then yOverZ (curve k r).toProjective else xOverZ (curve k r).toProjective) := by
  have h := congrArg (fun a => c.inv.appTop a) (hc.2 odd)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, c.inv_hom_id,
    Scheme.Hom.id_appTop] at h
  exact h.symm

lemma chartIso_unique
    (c d : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (hc : IsChartIso k r c) (hd : IsChartIso k r d) : c = d := by
  have hi : c.inv = d.inv := by
    apply ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.cubicScheme_hom_ext k r
    · calc
        c.inv ≫ cubicStructure k r = chartInclusion k r ≫ projectiveStructure k r := by
          rw [← hc.1, ← Category.assoc, c.inv_hom_id, Category.id_comp]
        _ = d.inv ≫ cubicStructure k r := by
          rw [← hd.1, ← Category.assoc, d.inv_hom_id, Category.id_comp]
    · intro odd
      exact (inverse_coordinates k r c hc odd).trans (inverse_coordinates k r d hd odd).symm
  apply Iso.ext
  calc
    c.hom = c.hom ≫ d.inv ≫ d.hom := by simp
    _ = d.hom := by rw [← hi, ← Category.assoc, c.hom_inv_id, Category.id_comp]

end ProjectiveCubicChart

/-- The specified projective Z-chart is uniquely the accepted split affine cubic. -/
theorem projective_cubic_chart :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ r : ℕ,
    ∃! c : CategoryTheory.Iso (ArithmeticThetaCubicModelR0144.cubicScheme k r)
      (AlgebraicGeometry.Spec (CommRingCat.of (ChartRing k r))), IsChartIso k r c := by
  intro k _ _ r
  obtain ⟨c, hc⟩ := ProjectiveCubicChart.exists_chartIso k r
  exact ⟨c, hc, fun d hd => ProjectiveCubicChart.chartIso_unique k r d c hd hc⟩

end ArithmeticThetaCompactifiedDifferentialR0145
