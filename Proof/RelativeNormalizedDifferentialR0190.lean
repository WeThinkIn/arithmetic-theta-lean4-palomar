module

public import GlobalFourTorsionDefinitionsR0190

@[expose] public section

/-! Construction of the relative Weierstrass differential. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaGlobalFourTorsionR0190
namespace RelativeNormalizedDifferential
open CategoryTheory AlgebraicGeometry MvPolynomial
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open P2MW.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one.WeierstrassProjModel

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)

/-- Every genuine global curve frame generates the pullback Hodge sheaf. -/
lemma hodge_generator_frame (δ : CurveFrame R W) :
    IsFrame (Hodge R W) ⊤ (hodgeGenerator R W δ) := by
  have hunit : IsFrame (SheafOfModules.unit (Curve R W).ringCatSheaf :
      (Curve R W).Modules) ⊤ (1 : Γ(Curve R W, ⊤)) := by
    intro U hU
    change Function.Bijective (fun a : Γ(Curve R W, U) =>
      a * (Curve R W).presheaf.map (homOfLE hU).op 1)
    simp only [map_one, mul_one]
    exact Function.bijective_id
  exact pullback_frame (origin R W) _ _
    (ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso δ _ hunit)

lemma origin_pderiv_zero :
    pderiv 0 (originPolynomial W) = originPolyV W := by
  simp [originPolynomial, originPolyV, pderiv_mul, pderiv_pow]
  ring

lemma origin_pderiv_one :
    pderiv 1 (originPolynomial W) = -originPolyU W := by
  simp [originPolynomial, originPolyU, pderiv_mul, pderiv_pow]
  ring

/-- Smoothness rules out a common zero of the two origin-chart coefficients.
The quotient and coefficients are those of the actual Weierstrass Y chart. -/
lemma origin_coefficients_coprime [W.IsElliptic] :
    IsCoprime (originQ W (originPolyU W)) (originQ W (originPolyV W)) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  letI := hm
  let M : Ideal (MvPolynomial (Fin 2) R) :=
    Ideal.comap (Ideal.Quotient.mk (Ideal.span {originPolynomial W})) m
  have hM : M.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hp : originPolyU W ∈ M :=
    hle ((show Ideal.span {originQ W (originPolyU W)} ≤ _ from le_sup_left)
      (Ideal.subset_span (Set.mem_singleton _)))
  have hq : originPolyV W ∈ M :=
    hle ((show Ideal.span {originQ W (originPolyV W)} ≤ _ from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _)))
  have hf : originPolynomial W ∈ M := by
    change Ideal.Quotient.mk _ (originPolynomial W) ∈ m
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
    exact m.zero_mem
  have he : srd1_ydeCR_W_Y W.toProjective = originPolynomial W :=
    srd1_ydeCR_W_Y_eq W.toProjective
  apply srd1_ycdCR_no_maximal_over_triple W.toProjective M hM
  · rwa [he]
  · rwa [he, origin_pderiv_zero]
  · rw [he, origin_pderiv_one]
    exact M.neg_mem hp

/-- The origin-chart differential exists over an arbitrary elliptic base ring. -/
lemma origin_frame [W.IsElliptic] :
    ∃! e : DifferentialFrame R (OriginQuotient W),
      KaehlerDifferential.D R (OriginQuotient W) (originQ W (X 0)) =
        originQ W (originPolyU W) • e 1 ∧
      KaehlerDifferential.D R (OriginQuotient W) (originQ W (X 1)) =
        originQ W (originPolyV W) • e 1 :=
  frame_of_coprime _ _ _ _ (origin_coefficients_coprime R W) (originTangent W)
    (originTangent_u W) (originTangent_v W) (origin_differential_relation W)
    (origin_derivation_ext W)

section AffineAlgebra
variable {B : Type u} [CommRing B] [Algebra R B]

/-- The two tangent coefficients generate the unit ideal over the entire base. -/
lemma affine_coefficients_coprime [W.IsElliptic] (x y : B)
    (he : (W.map (algebraMap R B)).toAffine.Equation x y) :
    IsCoprime (2*y + algebraMap R B W.a₁*x + algebraMap R B W.a₃)
      (3*x^2 + 2*algebraMap R B W.a₂*x + algebraMap R B W.a₄ - algebraMap R B W.a₁*y) := by
  let p := 2*y + algebraMap R B W.a₁*x + algebraMap R B W.a₃
  let q := 3*x^2 + 2*algebraMap R B W.a₂*x + algebraMap R B W.a₄ - algebraMap R B W.a₁*y
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  letI := hm
  have hp : Ideal.Quotient.mk m p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hle ((show Ideal.span {p} ≤ _ from le_sup_left)
      (Ideal.subset_span (Set.mem_singleton _))))
  have hq : Ideal.Quotient.mk m q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hle ((show Ideal.span {q} ≤ _ from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))))
  have hs := (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (he.map (Ideal.Quotient.mk m)))
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hs
  simp only [p, q, map_add, map_sub, map_mul, map_pow, map_ofNat] at hp hq
  simp only [WeierstrassCurve.Affine.map, WeierstrassCurve.map, WeierstrassCurve.toAffine] at hs
  rcases hs.2 with h | h
  · apply h
    change Ideal.Quotient.mk m (algebraMap R B W.a₁) * Ideal.Quotient.mk m y - _ = 0
    linear_combination -hq
  · exact h hp
end AffineAlgebra

section AffinePresentation

def affinePolynomial : MvPolynomial (Fin 2) R :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)

abbrev AffineQuotient := MvPolynomial (Fin 2) R ⧸ Ideal.span {affinePolynomial R W}
abbrev affineQ : MvPolynomial (Fin 2) R →ₐ[R] AffineQuotient R W := Ideal.Quotient.mkₐ _ _

def affinePolyP : MvPolynomial (Fin 2) R := 2 * X 1 + C W.a₁ * X 0 + C W.a₃
def affinePolyQ : MvPolynomial (Fin 2) R :=
  3 * X 0 ^ 2 + 2 * C W.a₂ * X 0 + C W.a₄ - C W.a₁ * X 1

lemma affine_relation :
    (W.map (algebraMap R (AffineQuotient R W))).toAffine.Equation
      (affineQ R W (X 0)) (affineQ R W (X 1)) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  have h : affineQ R W (affinePolynomial R W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [WeierstrassCurve.map, WeierstrassCurve.toAffine, affinePolynomial, map_sub, map_add, map_mul, map_pow,
    show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using h

def affinePolyTangent : Derivation R (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) R) :=
  MvPolynomial.mkDerivation _ (fun i => if i = 0 then affinePolyP R W else affinePolyQ R W)

lemma affinePolyTangent_relation : affinePolyTangent R W (affinePolynomial R W) = 0 := by
  simp [affinePolynomial, affinePolyTangent, affinePolyP, affinePolyQ,
    Derivation.leibniz, pow_succ, smul_eq_mul]
  ring

lemma affinePolyTangent_preserves (p : MvPolynomial (Fin 2) R) (hp : affineQ R W p = 0) :
    affineQ R W (affinePolyTangent R W p) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  have hz : affineQ R W (affinePolynomial R W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  simp [Derivation.leibniz, affinePolyTangent_relation, smul_eq_mul]

def affineTangent : Derivation R (AffineQuotient R W) (AffineQuotient R W) :=
  Derivation.liftOfSurjective (f := affineQ R W) Ideal.Quotient.mk_surjective
    (affinePolyTangent_preserves R W)

lemma affineTangent_x : affineTangent R W (affineQ R W (X 0)) = affineQ R W (affinePolyP R W) := by
  rw [affineTangent, Derivation.liftOfSurjective_apply]
  simp [affinePolyTangent]

lemma affineTangent_y : affineTangent R W (affineQ R W (X 1)) = affineQ R W (affinePolyQ R W) := by
  rw [affineTangent, Derivation.liftOfSurjective_apply]
  simp [affinePolyTangent]

lemma affine_derivation_ext {N : Type u} [AddCommGroup N] [Module (AffineQuotient R W) N]
    [Module R N] [IsScalarTower R (AffineQuotient R W) N]
    (d e : Derivation R (AffineQuotient R W) N)
    (hx : d (affineQ R W (X 0)) = e (affineQ R W (X 0)))
    (hy : d (affineQ R W (X 1)) = e (affineQ R W (X 1))) : d = e := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change d (affineQ R W p) = e (affineQ R W p)
  induction p using MvPolynomial.induction_on with
  | C c =>
    change d (algebraMap R (AffineQuotient R W) c) = e (algebraMap R (AffineQuotient R W) c)
    simp only [Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    have hi : d (affineQ R W (X i)) = e (affineQ R W (X i)) := by
      fin_cases i
      · exact hx
      · exact hy
    simp only [map_mul, Derivation.leibniz, hp, hi]

lemma affine_differential_relation :
    affineQ R W (affinePolyP R W) • KaehlerDifferential.D R (AffineQuotient R W) (affineQ R W (X 1)) =
      affineQ R W (affinePolyQ R W) • KaehlerDifferential.D R (AffineQuotient R W) (affineQ R W (X 0)) := by
  have he := affine_relation R W
  rw [WeierstrassCurve.Affine.equation_iff] at he
  have h := congrArg (KaehlerDifferential.D R (AffineQuotient R W)) he
  dsimp only [WeierstrassCurve.map, WeierstrassCurve.toAffine] at h
  simp only [map_add, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    Derivation.leibniz_pow, smul_smul] at h
  simp only [affinePolyP, affinePolyQ, map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp only [show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl]
  linear_combination (norm := module) h

lemma affine_frame [W.IsElliptic] :
    ∃! e : DifferentialFrame R (AffineQuotient R W),
      KaehlerDifferential.D R (AffineQuotient R W) (affineQ R W (X 0)) =
        affineQ R W (affinePolyP R W) • e 1 ∧
      KaehlerDifferential.D R (AffineQuotient R W) (affineQ R W (X 1)) =
        affineQ R W (affinePolyQ R W) • e 1 := by
  have hc : IsCoprime (affineQ R W (affinePolyP R W)) (affineQ R W (affinePolyQ R W)) := by
    simpa only [affinePolyP, affinePolyQ, map_add, map_sub, map_mul, map_pow, map_ofNat,
      show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using
      affine_coefficients_coprime R W _ _ (affine_relation R W)
  exact frame_of_coprime _ _ _ _ hc (affineTangent R W)
    (affineTangent_x R W) (affineTangent_y R W) (affine_differential_relation R W)
    (affine_derivation_ext R W)

end AffinePresentation

section ActualCharts
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
open ArithmeticThetaLegendreComparisonR0177

lemma polynomial_equiv_relation :
    ProjectiveCubicChart.polynomialEquiv R W.toAffine.polynomial = affinePolynomial R W := by
  simp [ProjectiveCubicChart.polynomialEquiv, ProjectiveCubicChart.toMv,
    WeierstrassCurve.Affine.polynomial, affinePolynomial, Polynomial.eval₂_pow, WeierstrassCurve.toAffine]
  ring

def affineQuotientEquiv :
    (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial}) ≃+* AffineQuotient R W :=
  Ideal.quotientEquiv _ _ (ProjectiveCubicChart.polynomialEquiv R) (by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p => Ideal.span {p}) (polynomial_equiv_relation R W).symm)

lemma chart_scalar_formula :
    ArithmeticThetaLegendreComparisonR0177.chartScalar R W =
      (fromZeroRingHom (projModelGradingCR W.toProjective)
        (Submonoid.powers (coord W.toProjective 2))).comp
        (algebraMap R (projModelGradingCR W.toProjective 0)) := by
  have he : CommRingCat.ofHom (ArithmeticThetaLegendreComparisonR0177.chartScalar R W) =
      CommRingCat.ofHom ((fromZeroRingHom (projModelGradingCR W.toProjective)
        (Submonoid.powers (coord W.toProjective 2))).comp
        (algebraMap R (projModelGradingCR W.toProjective 0))) := by
    apply Spec.map_injective
    change Spec.map (Spec.preimage (ArithmeticThetaLegendreComparisonR0177.chartInclusion R W ≫ structureMap R W)) = _
    rw [Spec.map_preimage]
    change zChartι W.toProjective ≫ projModelStrCR W.toProjective = _
    rw [zChartι, projModelStrCR, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom he

lemma chart_structure : ArithmeticThetaLegendreComparisonR0177.chartInclusion R W ≫ structureMap R W =
    Spec.map (CommRingCat.ofHom (ArithmeticThetaLegendreComparisonR0177.chartScalar R W)) :=
  (Spec.map_preimage _).symm

lemma exists_chart_equiv :
    ∃ e : ArithmeticThetaLegendreComparisonR0177.ChartRing R W ≃+* AffineQuotient R W,
      (∀ a, e (ArithmeticThetaLegendreComparisonR0177.chartScalar R W a) =
        algebraMap R (AffineQuotient R W) a) ∧
      e (xOverZ W.toProjective) = affineQ R W (X 0) ∧
      e (yOverZ W.toProjective) = affineQ R W (X 1) := by
  obtain ⟨f, hf, hc, hm⟩ := exists_zChartAway_equiv_coordinateRing W.toProjective
  let e := (RingEquiv.ofBijective f hf).trans (affineQuotientEquiv R W)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a
    change affineQuotientEquiv R W (f (ArithmeticThetaLegendreComparisonR0177.chartScalar R W a)) = _
    rw [chart_scalar_formula, show f (_) = _ from RingHom.congr_fun hc a]
    change affineQuotientEquiv R W (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C a))) =
      Ideal.Quotient.mk _ (C a)
    simp [affineQuotientEquiv, ProjectiveCubicChart.polynomialEquiv, ProjectiveCubicChart.toMv]
  · have hb : (X 0 : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R (1 • 1) := by
      simpa using (isHomogeneous_X R (0 : Fin 3))
    have h := hm 1 (X 0) hb
    change f (xOverZ W.toProjective) = _ at h
    simp only [aeval_X, Matrix.cons_val_zero] at h
    change affineQuotientEquiv R W (f (xOverZ W.toProjective)) = _
    rw [h]
    simp [affineQuotientEquiv, ProjectiveCubicChart.polynomialEquiv, ProjectiveCubicChart.toMv]
  · have hb : (X 1 : MvPolynomial (Fin 3) R) ∈ homogeneousSubmodule (Fin 3) R (1 • 1) := by
      simpa using (isHomogeneous_X R (1 : Fin 3))
    have h := hm 1 (X 1) hb
    change f (yOverZ W.toProjective) = _ at h
    simp only [aeval_X, Matrix.cons_val_one] at h
    change affineQuotientEquiv R W (f (yOverZ W.toProjective)) = _
    rw [h]
    simp [affineQuotientEquiv, ProjectiveCubicChart.polynomialEquiv, ProjectiveCubicChart.toMv]

local instance chartAlgebra : Algebra R (ArithmeticThetaLegendreComparisonR0177.ChartRing R W) :=
  (ArithmeticThetaLegendreComparisonR0177.chartScalar R W).toAlgebra

lemma actual_affine_frame [W.IsElliptic] :
    ∃ e : DifferentialFrame R (ArithmeticThetaLegendreComparisonR0177.ChartRing R W),
      KaehlerDifferential.D R _ (xOverZ W.toProjective) =
        (2*yOverZ W.toProjective + algebraMap R _ W.a₁*xOverZ W.toProjective +
          algebraMap R _ W.a₃) • e 1 ∧
      KaehlerDifferential.D R _ (yOverZ W.toProjective) =
        (3*xOverZ W.toProjective^2 + 2*algebraMap R _ W.a₂*xOverZ W.toProjective +
          algebraMap R _ W.a₄ - algebraMap R _ W.a₁*yOverZ W.toProjective) • e 1 := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_chart_equiv R W
  let ψ : ArithmeticThetaLegendreComparisonR0177.ChartRing R W ≃ₐ[R] AffineQuotient R W :=
    { φ with commutes' := hφ }
  have hx' : ψ.symm (affineQ R W (X 0)) = xOverZ W.toProjective := ψ.symm_apply_eq.mpr hx.symm
  have hy' : ψ.symm (affineQ R W (X 1)) = yOverZ W.toProjective := ψ.symm_apply_eq.mpr hy.symm
  have hc (a : R) : ψ.symm (affineQ R W (C a)) = algebraMap R _ a := ψ.symm.commutes a
  obtain ⟨e, he, _⟩ := affine_frame R W
  refine ⟨frameTransport ψ.symm e, ?_, ?_⟩
  · have h := frameTransport_normalization ψ.symm e _ _ he.1
    simpa only [affinePolyP, map_add, map_mul, map_ofNat, hx', hy', hc] using h
  · have h := frameTransport_normalization ψ.symm e _ _ he.2
    simpa only [affinePolyQ, map_add, map_sub, map_mul, map_pow, map_ofNat, hx', hy', hc] using h

attribute [local instance] originAlgebra

lemma actual_origin_frame [W.IsElliptic] :
    ∃ e : DifferentialFrame R (OriginRing W),
      KaehlerDifferential.D R _ (xOverY W) =
        (-(1 + algebraMap R _ W.a₁*xOverY W + 2*algebraMap R _ W.a₃*zOverY W -
          algebraMap R _ W.a₂*xOverY W^2 - 2*algebraMap R _ W.a₄*xOverY W*zOverY W -
          3*algebraMap R _ W.a₆*zOverY W^2)) • e 1 ∧
      KaehlerDifferential.D R _ (zOverY W) =
        (algebraMap R _ W.a₁*zOverY W - 3*xOverY W^2 -
          2*algebraMap R _ W.a₂*xOverY W*zOverY W - algebraMap R _ W.a₄*zOverY W^2) • e 1 := by
  obtain ⟨e, he, _⟩ := origin_frame R W
  let φ := (originEquiv W).symm
  have hx : φ (originQ W (X 0)) = xOverY W := originFromQuotient_x W
  have hy : φ (originQ W (X 1)) = zOverY W := originFromQuotient_v W
  have hc (a : R) : φ (originQ W (C a)) = algebraMap R _ a := φ.commutes a
  refine ⟨frameTransport φ e, ?_, ?_⟩
  · have h := frameTransport_normalization φ e _ _ he.1
    simpa only [originPolyU, map_neg, map_add, map_sub, map_mul, map_pow, map_one,
      map_ofNat, hx, hy, hc] using h
  · have h := frameTransport_normalization φ e _ _ he.2
    simpa only [originPolyV, map_add, map_sub, map_mul, map_pow, map_ofNat, hx, hy, hc] using h

end ActualCharts

section OverlapAlgebra
variable {B N : Type u} [CommRing B] [AddCommGroup N] [Module B N]

def originU (a₁ a₂ a₃ a₄ a₆ u v : B) : B :=
  -(1 + a₁*u + 2*a₃*v - a₂*u^2 - 2*a₄*u*v - 3*a₆*v^2)
def originV (a₁ a₂ a₄ u v : B) : B := a₁*v - 3*u^2 - 2*a₂*u*v - a₄*v^2

lemma transition_x (a₁ a₂ a₃ a₄ a₆ x y u v : B)
    (hxu : x*v = u) (hyv : y*v = 1)
    (he : v + a₁*u*v + a₃*v^2 = u^3 + a₂*u^2*v + a₄*u*v^2 + a₆*v^3) :
    v*originU a₁ a₂ a₃ a₄ a₆ u v - u*originV a₁ a₂ a₄ u v =
      v^2*(2*y+a₁*x+a₃) := by
  dsimp [originU, originV]
  linear_combination -3*he - 2*v*hyv - a₁*v*hxu

lemma transition_y (a₁ a₂ a₄ x y u v : B) (hxu : x*v = u) (hyv : y*v = 1) :
    -originV a₁ a₂ a₄ u v = v^2*(3*x^2+2*a₂*x+a₄-a₁*y) := by
  dsimp [originV]
  linear_combination -3*(x*v+u)*hxu - 2*a₂*v*hxu + a₁*v*hyv

/-- Equality of frames on the overlap uses both tangent coefficients, so no
division by the possibly vanishing coefficient of dx is used. -/
lemma overlap_module (x y u v p q U V : B) (δ ε : N)
    (hcp : IsCoprime p q) (hvunit : IsUnit v)
    (hxu : x*v = u) (hyv : y*v = 1)
    (hp : v*U-u*V = v^2*p) (hq : -V = v^2*q)
    (hu : x • (V • ε) + v • (p • δ) = U • ε)
    (hv : y • (V • ε) + v • (q • δ) = 0) : δ = ε := by
  have hpδ : v^2 • (p • δ) = (v*U-u*V) • ε := by
    calc
      _ = v • (x • (V • ε) + v • (p • δ)) - (x*v) • (V • ε) := by module
      _ = _ := by rw [hu, hxu]; module
  have hqδ : v^2 • (q • δ) = (-V) • ε := by
    calc
      _ = v • (y • (V • ε) + v • (q • δ)) - (y*v) • (V • ε) := by module
      _ = _ := by rw [hv, hyv, smul_zero, one_smul]; module
  rw [hp, mul_smul] at hpδ
  rw [hq, mul_smul] at hqδ
  have hcancel : Function.Injective (fun z : N => v^2 • z) := by
    obtain ⟨w, hw⟩ := hvunit.pow 2
    intro a b h
    have hh := congrArg (fun z : N => (↑w⁻¹ : B) • z) h
    rw [← hw, smul_smul, smul_smul, Units.inv_mul, one_smul, one_smul] at hh
    exact hh
  obtain ⟨a,b,hab⟩ := hcp
  calc
    δ = (a*p+b*q) • δ := by rw [hab, one_smul]
    _ = a • (p • δ) + b • (q • δ) := by module
    _ = a • (p • ε) + b • (q • ε) := by rw [hcancel hpδ, hcancel hqδ]
    _ = (a*p+b*q) • ε := by module
    _ = ε := by rw [hab, one_smul]
end OverlapAlgebra

section SheafConstruction
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
local notation "A" => ArithmeticThetaLegendreComparisonR0177.ChartRing R W
local notation "jZ" => ArithmeticThetaLegendreComparisonR0177.chartInclusion R W
local notation "cZ" => ArithmeticThetaLegendreComparisonR0177.chartScalar R W
local notation "f" => structureMap R W

abbrev zOpen : (Curve R W).Opens := jZ ''ᵁ ⊤
abbrev yOpen : (Curve R W).Opens := originChartι W ''ᵁ ⊤
abbrev oOpen : (Curve R W).Opens := overlapInclusion W ''ᵁ ⊤
abbrev zSection := (chartRingEquiv jZ).symm
abbrev ySection := (chartRingEquiv (originChartι W)).symm
abbrev oSection := (chartRingEquiv (overlapInclusion W)).symm

def zP : A := 2*yOverZ W.toProjective + cZ W.a₁*xOverZ W.toProjective + cZ W.a₃
def zQ : A := 3*xOverZ W.toProjective^2 + 2*cZ W.a₂*xOverZ W.toProjective +
  cZ W.a₄ - cZ W.a₁*yOverZ W.toProjective

def yP : OriginRing W := originU (originScalar W W.a₁) (originScalar W W.a₂)
  (originScalar W W.a₃) (originScalar W W.a₄) (originScalar W W.a₆) (xOverY W) (zOverY W)
def yQ : OriginRing W := originV (originScalar W W.a₁) (originScalar W W.a₂)
  (originScalar W W.a₄) (xOverY W) (zOverY W)

lemma actual_affine_coprime [W.IsElliptic] : IsCoprime (zP R W) (zQ R W) := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_chart_equiv R W
  have hc := affine_coefficients_coprime R W _ _ (affine_relation R W)
  have hh := hc.map φ.symm.toRingHom
  have hcs (a : R) : φ.symm (algebraMap R (AffineQuotient R W) a) = cZ a :=
    φ.symm_apply_eq.mpr (hφ a).symm
  have hxs : φ.symm (affineQ R W (X 0)) = xOverZ W.toProjective := φ.symm_apply_eq.mpr hx.symm
  have hys : φ.symm (affineQ R W (X 1)) = yOverZ W.toProjective := φ.symm_apply_eq.mpr hy.symm
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_add, map_sub, map_mul, map_pow, map_ofNat, hcs, hxs, hys, zP, zQ] using hh

lemma kaehler_invertible [W.IsElliptic] : Scheme.Modules.IsInvertible (structureMap R W).kaehler := by
  letI : SmoothOfRelativeDimension 1 f := projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
    ((structureMap R W).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1

attribute [local instance] chartAlgebra originAlgebra

lemma z_local_frame [W.IsElliptic] :
    ∃ δ : Γ((structureMap R W).kaehler, zOpen R W), Scheme.Modules.IsFrameOn δ (zOpen R W) ∧
      relativeD f (zOpen R W) (zSection R W (xOverZ W.toProjective)) = zSection R W (zP R W) • δ ∧
      relativeD f (zOpen R W) (zSection R W (yOverZ W.toProjective)) = zSection R W (zQ R W) • δ := by
  obtain ⟨e, hx, hy⟩ := actual_affine_frame R W
  obtain ⟨δ, hδ, hn⟩ := frame_on_chart f jZ (chart_structure R W) (kaehler_invertible R W) e
  exact ⟨δ, hδ, hn _ _ hx, hn _ _ hy⟩

lemma y_local_frame [W.IsElliptic] :
    ∃ ε : Γ((structureMap R W).kaehler, yOpen R W), Scheme.Modules.IsFrameOn ε (yOpen R W) ∧
      relativeD f (yOpen R W) (ySection R W (xOverY W)) = ySection R W (yP R W) • ε ∧
      relativeD f (yOpen R W) (ySection R W (zOverY W)) = ySection R W (yQ R W) • ε := by
  obtain ⟨e, hx, hy⟩ := actual_origin_frame R W
  obtain ⟨ε, hε, hn⟩ := frame_on_chart f (originChartι W) (origin_structure W)
    (kaehler_invertible R W) e
  exact ⟨ε, hε, hn _ _ hx, hn _ _ hy⟩

lemma scalar_maps_equal {S₁ S₂ S₃ : Type u} [CommRing S₁] [CommRing S₂] [CommRing S₃]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    (iA : Spec (CommRingCat.of S₁) ⟶ X) (iB : Spec (CommRingCat.of S₂) ⟶ X)
    (cA : R →+* S₁) (cB : R →+* S₂) (lA : S₁ →+* S₃) (lB : S₂ →+* S₃)
    (ha : iA ≫ g = Spec.map (CommRingCat.ofHom cA))
    (hb : iB ≫ g = Spec.map (CommRingCat.ofHom cB))
    (hl : Spec.map (CommRingCat.ofHom lA) ≫ iA = Spec.map (CommRingCat.ofHom lB) ≫ iB) :
    lA.comp cA = lB.comp cB := by
  have he : Spec.map (CommRingCat.ofHom (lA.comp cA)) =
      Spec.map (CommRingCat.ofHom (lB.comp cB)) := by
    calc
      _ = Spec.map (CommRingCat.ofHom lA) ≫ (iA ≫ g) := by
        rw [ha, ← Spec.map_comp]; rfl
      _ = Spec.map (CommRingCat.ofHom lB) ≫ (iB ≫ g) := by
        rw [← Category.assoc, hl, Category.assoc]
      _ = _ := by rw [hb, ← Spec.map_comp]; rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

lemma overlap_scalar (a : R) : fromAffine W (cZ a) = fromOrigin W (originScalar W a) := by
  have he := scalar_maps_equal R f jZ (originChartι W) cZ (originScalar W)
    (fromAffine W) (fromOrigin W) (chart_structure R W) (origin_structure W)
    ((fromAffine_inclusion W).trans (fromOrigin_inclusion W).symm)
  exact RingHom.congr_fun he a

lemma overlap_opens_eq : oOpen R W = zOpen R W ⊓ yOpen R W := by
  simp only [oOpen, zOpen, yOpen, Scheme.Hom.image_top_eq_opensRange,
    overlap_opens, inf_comm, ArithmeticThetaLegendreComparisonR0177.chartInclusion]

lemma chart_cover : zOpen R W ⊔ yOpen R W = ⊤ := by
  simpa only [zOpen, yOpen, Scheme.Hom.image_top_eq_opensRange, sup_comm,
    ArithmeticThetaLegendreComparisonR0177.chartInclusion] using projective_cover W

lemma local_frames_agree [W.IsElliptic]
    (δ : Γ((structureMap R W).kaehler, zOpen R W))
    (ε : Γ((structureMap R W).kaehler, yOpen R W))
    (hδx : relativeD f (zOpen R W) (zSection R W (xOverZ W.toProjective)) = zSection R W (zP R W) • δ)
    (hδy : relativeD f (zOpen R W) (zSection R W (yOverZ W.toProjective)) = zSection R W (zQ R W) • δ)
    (hεu : relativeD f (yOpen R W) (ySection R W (xOverY W)) = ySection R W (yP R W) • ε)
    (hεv : relativeD f (yOpen R W) (ySection R W (zOverY W)) = ySection R W (yQ R W) • ε) :
    (structureMap R W).kaehler.presheaf.map (homOfLE (inf_le_left : zOpen R W ⊓ yOpen R W ≤ zOpen R W)).op δ =
      (structureMap R W).kaehler.presheaf.map (homOfLE (inf_le_right : zOpen R W ⊓ yOpen R W ≤ yOpen R W)).op ε := by
  have hoz : oOpen R W ≤ zOpen R W := (overlap_opens_eq R W).le.trans inf_le_left
  have hoy : oOpen R W ≤ yOpen R W := (overlap_opens_eq R W).le.trans inf_le_right
  let δr := (structureMap R W).kaehler.presheaf.map (homOfLE hoz).op δ
  let εr := (structureMap R W).kaehler.presheaf.map (homOfLE hoy).op ε
  let fa : A →+* Γ(Curve R W, oOpen R W) := (oSection R W).toRingHom.comp (fromAffine W)
  let fo : OriginRing W →+* Γ(Curve R W, oOpen R W) := (oSection R W).toRingHom.comp (fromOrigin W)
  let x := fa (xOverZ W.toProjective)
  let y := fa (yOverZ W.toProjective)
  let u := fo (xOverY W)
  let v := fo (zOverY W)
  let p := fa (zP R W)
  let q := fa (zQ R W)
  let U := fo (yP R W)
  let V := fo (yQ R W)
  have hxu : x*v = u := by
    simpa only [x, v, u, fa, fo, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_mul] using congrArg (oSection R W) (overlap_x W)
  have hyv : y*v = 1 := by
    simpa only [y, v, fa, fo, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_mul, map_one] using congrArg (oSection R W) (overlap_y W)
  have cs (a : R) : fa (cZ a) = fo (originScalar W a) := congrArg (oSection R W) (overlap_scalar R W a)
  have he : v + fo (originScalar W W.a₁)*u*v + fo (originScalar W W.a₃)*v^2 =
      u^3 + fo (originScalar W W.a₂)*u^2*v + fo (originScalar W W.a₄)*u*v^2 +
      fo (originScalar W W.a₆)*v^3 := by
    simpa only [u, v, map_add, map_mul, map_pow, originAlgebra, RingHom.algebraMap_toAlgebra] using
      congrArg fo (origin_relation W)
  have hp : v*U-u*V = v^2*p := by
    simpa only [U,V,p,x,y,u,v,yP,yQ,zP,originU,originV,map_neg,map_add,map_sub,
      map_mul,map_pow,map_one,map_ofNat,cs] using
      transition_x (fo (originScalar W W.a₁)) (fo (originScalar W W.a₂))
        (fo (originScalar W W.a₃)) (fo (originScalar W W.a₄)) (fo (originScalar W W.a₆))
        x y u v hxu hyv he
  have hq : -V = v^2*q := by
    simpa only [V,q,x,y,u,v,yQ,zQ,originV,map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,cs] using
      transition_y (fo (originScalar W W.a₁)) (fo (originScalar W W.a₂))
        (fo (originScalar W W.a₄)) x y u v hxu hyv
  have hx : relativeD f (oOpen R W) x = p • δr :=
    chart_normalization_restrict f jZ (overlapInclusion W) (fromAffine W)
      (fromAffine_inclusion W).symm hoz _ _ δ hδx
  have hy : relativeD f (oOpen R W) y = q • δr :=
    chart_normalization_restrict f jZ (overlapInclusion W) (fromAffine W)
      (fromAffine_inclusion W).symm hoz _ _ δ hδy
  have hu : relativeD f (oOpen R W) u = U • εr :=
    chart_normalization_restrict f (originChartι W) (overlapInclusion W) (fromOrigin W)
      (fromOrigin_inclusion W).symm hoy _ _ ε hεu
  have hv : relativeD f (oOpen R W) v = V • εr :=
    chart_normalization_restrict f (originChartι W) (overlapInclusion W) (fromOrigin W)
      (fromOrigin_inclusion W).symm hoy _ _ ε hεv
  have hh : δr = εr := by
    apply overlap_module x y u v p q U V δr εr
      ((actual_affine_coprime R W).map fa)
      ((overlap_v_unit W).map (oSection R W).toRingHom) hxu hyv hp hq
    · have h := congrArg (relativeD f (oOpen R W)) hxu
      rwa [relativeD_mul, hx, hv, hu] at h
    · have h := congrArg (relativeD f (oOpen R W)) hyv
      rwa [relativeD_mul, hy, hv, relativeD_one] at h
  have ht := congrArg (fun z => (structureMap R W).kaehler.presheaf.map
    (eqToHom (overlap_opens_eq R W).symm).op z) hh
  simp only [δr, εr, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at ht
  convert ht using 1 <;> rfl

lemma global_frame_on_open [W.IsElliptic] :
    ∃ δ : CurveFrame R W,
      relativeD f (zOpen R W) (zSection R W (xOverZ W.toProjective)) =
        zSection R W (zP R W) • Scheme.Modules.Hom.app δ.hom (zOpen R W) (1 : Γ(Curve R W, zOpen R W)) ∧
      relativeD f (zOpen R W) (zSection R W (yOverZ W.toProjective)) =
        zSection R W (zQ R W) • Scheme.Modules.Hom.app δ.hom (zOpen R W) (1 : Γ(Curve R W, zOpen R W)) := by
  obtain ⟨δ,hδ,hδx,hδy⟩ := z_local_frame R W
  obtain ⟨ε,hε,hεu,hεv⟩ := y_local_frame R W
  obtain ⟨e,hez,hey⟩ := glue_two_frames (zOpen R W) (yOpen R W) (chart_cover R W)
    δ ε hδ hε (local_frames_agree R W δ ε hδx hδy hεu hεv)
  exact ⟨e, by rw [hez]; exact hδx, by rw [hez]; exact hδy⟩

end SheafConstruction

section NormalizationTransfer
open ArithmeticThetaPullback

lemma pullback_restrict_top {X Y : Scheme.{u}} (j : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (h : ⊤ ≤ j ⁻¹ᵁ U) (s : Γ(M, ⊤)) :
    res ((Scheme.Modules.pullback j).obj M) h
      (Scheme.Modules.pullbackLocalSection j (res M le_top s)) = pullbackGlobalSection j M s := by
  change ((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE h).op
    (Scheme.Modules.pullbackLocalSection j (M.presheaf.map (homOfLE le_top).op s)) = _
  rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change ((Scheme.Modules.pullback j).obj M).presheaf.map (𝟙 _) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma pullback_normalization {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ j ⁻¹ᵁ U) (x p : Γ(Y,U)) (δ : Γ(g.kaehler,⊤))
    (hn : relativeD g U x = p • res g.kaehler le_top δ) :
    relativeD (j ≫ g) ⊤ (j.appLE U ⊤ h x) = j.appLE U ⊤ h p •
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap
        g (j ≫ g) j (by simp)).app ⊤ (pullbackGlobalSection j g.kaehler δ) := by
  let m := ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap
    g (j ≫ g) j (by simp)
  have hh := congrArg (fun t => res (j ≫ g).kaehler h
    (m.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j t))) hn
  change res (j ≫ g).kaehler h
    ((ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap
      g (j ≫ g) j (by simp)).app _ (Scheme.Modules.pullbackLocalSection j (relativeD g U x))) = _ at hh
  rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_D,
    relativeD_res, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    res_smul, hom_res, pullback_restrict_top] at hh
  exact hh

lemma chart_app_section {B : Type u} [CommRing B] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
    (h : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤)) (b : B) :
    j.appLE (j ''ᵁ ⊤) ⊤ h ((chartRingEquiv j).symm b) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1
  have he := (chartRingEquiv j).apply_symm_apply b
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    ((j.appIso ⊤).hom ((chartRingEquiv j).symm b)) = b at he
  rw [Scheme.Hom.appIso_hom'] at he
  exact he.trans (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id b).symm

lemma normalized_of_open (δ : CurveFrame R W)
    (hn : relativeD (structureMap R W) (zOpen R W)
      (zSection R W (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective)) =
      zSection R W (zP R W) • Scheme.Modules.Hom.app δ.hom (zOpen R W)
        (1 : Γ(Curve R W,zOpen R W))) : NormalizedFrame R W δ := by
  let j := ArithmeticThetaLegendreComparisonR0177.chartInclusion R W
  have h : ⊤ ≤ j ⁻¹ᵁ (zOpen R W) := by
    change ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤)
    rw [Scheme.Hom.preimage_image_eq]
  have hn' : relativeD (structureMap R W) (zOpen R W)
      (zSection R W (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective)) =
      zSection R W (zP R W) • res (structureMap R W).kaehler (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ) := by
    rw [hn]
    congr 1
    exact (frame_section_restrict (structureMap R W) δ ⊤ (zOpen R W) le_top).symm
  have hh := pullback_normalization R (structureMap R W) j (zOpen R W) h _ _ _ hn'
  rw [chart_app_section, chart_app_section] at hh
  exact hh

lemma normalized_frame_exists [W.IsElliptic] : ∃ δ : CurveFrame R W, NormalizedFrame R W δ := by
  obtain ⟨δ,hx,hy⟩ := global_frame_on_open R W
  exact ⟨δ,normalized_of_open R W δ hx⟩

end NormalizationTransfer

section UniquenessAlgebra
open WeierstrassCurve.DrinfeldGlobal

lemma affine_quotient_nontrivial [Nontrivial R] : Nontrivial (AffineQuotient R W) := by
  letI : Nontrivial (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial}) :=
    inferInstanceAs (Nontrivial W.toAffine.CoordinateRing)
  exact (affineQuotientEquiv R W).symm.toRingHom.domain_nontrivial

lemma affineTangent_p : affineTangent R W (affineQ R W (affinePolyP R W)) =
    2*affineQ R W (affinePolyQ R W) +
      algebraMap R (AffineQuotient R W) W.a₁*affineQ R W (affinePolyP R W) := by
  have hc (a : R) : affineQ R W (C a) = algebraMap R (AffineQuotient R W) a := rfl
  simp only [affinePolyP, map_add, map_mul, map_ofNat, hc, Derivation.leibniz,
    Derivation.map_algebraMap, smul_zero, add_zero,
    affineTangent_x, affineTangent_y, smul_eq_mul]
  have htwo : affineTangent R W (2 : AffineQuotient R W) = 0 := by
    convert (affineTangent R W).map_algebraMap (2 : R) using 1; simp only [map_ofNat]
  simp only [htwo,mul_zero,add_zero]

lemma zP_ne_zero [Nontrivial R] [Algebra ℚ R] [W.IsElliptic] : zP R W ≠ 0 := by
  letI := affine_quotient_nontrivial R W
  have h2 : IsUnit (2 : AffineQuotient R W) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map
      ((algebraMap R (AffineQuotient R W)).comp (algebraMap ℚ R))
  have hp : affineQ R W (affinePolyP R W) ≠ 0 := by
    intro hz
    have hd := affineTangent_p R W
    rw [hz, map_zero, mul_zero, add_zero] at hd
    have hq : affineQ R W (affinePolyQ R W) = 0 := by
      apply h2.mul_right_injective
      simpa only [mul_zero] using hd.symm
    have hc := affine_coefficients_coprime R W _ _ (affine_relation R W)
    have hp' : 2*affineQ R W (X 1) + algebraMap R (AffineQuotient R W) W.a₁*affineQ R W (X 0) +
        algebraMap R (AffineQuotient R W) W.a₃ = 0 := by
      simpa only [affinePolyP,map_add,map_mul,map_ofNat,
        show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using hz
    have hq' : 3*affineQ R W (X 0)^2 + 2*algebraMap R (AffineQuotient R W) W.a₂*affineQ R W (X 0) +
        algebraMap R (AffineQuotient R W) W.a₄ - algebraMap R (AffineQuotient R W) W.a₁*affineQ R W (X 1) = 0 := by
      simpa only [affinePolyQ,map_add,map_sub,map_mul,map_pow,map_ofNat,
        show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using hq
    obtain ⟨a,b,hab⟩ := hc
    rw [hp',hq',mul_zero,mul_zero,zero_add] at hab
    exact zero_ne_one hab
  obtain ⟨φ,hφ,hx,hy⟩ := exists_chart_equiv R W
  intro hz
  apply hp
  have hh := congrArg φ hz
  simpa only [zP,map_add,map_mul,map_ofNat,map_zero,hφ,hx,hy,affinePolyP,
    show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using hh

lemma zOpen_nonempty [Nontrivial R] : Nonempty (zOpen R W) := by
  letI := affine_quotient_nontrivial R W
  obtain ⟨φ,hφ,hx,hy⟩ := exists_chart_equiv R W
  letI := φ.toRingHom.domain_nontrivial
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (ArithmeticThetaLegendreComparisonR0177.ChartRing R W))) := inferInstance
  refine ⟨⟨ArithmeticThetaLegendreComparisonR0177.chartInclusion R W z, ?_⟩⟩
  rw [zOpen, Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.mem_opensRange.mpr ⟨z,rfl⟩

end UniquenessAlgebra

section DifferentialFaithfulness
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull

lemma differential_on_isomorphic_sections {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (j ⁻¹ᵁ U))
    (hj : Function.Bijective (j.app U)) :
    Function.Injective ((k1 g (j ≫ g) j (by simp)).app U) := by
  letI := g.sectionsAlgebra U
  letI := (j ≫ g).sectionsAlgebra (j ⁻¹ᵁ U)
  let φ : Γ(Y,U) ≃ₐ[R] Γ(X,j ⁻¹ᵁ U) :=
    { RingEquiv.ofBijective (j.app U).hom hj with
      commutes' := by
        intro a
        exact fac_apply g (j ≫ g) j (by simp) U a }
  have he : ∀ ω : KaehlerDifferential R Γ(Y,U),
      (k1 g (j ≫ g) j (by simp)).app U (g.kaehlerToSections U ω) =
        (j ≫ g).kaehlerToSections (j ⁻¹ᵁ U)
          (GlobalNormalizedDifferential.differentialMap φ.toAlgHom ω) := by
    let lhs : KaehlerDifferential R Γ(Y,U) →+ Γ((j ≫ g).kaehler,j ⁻¹ᵁ U) :=
      (((k1 g (j ≫ g) j (by simp)).app U).hom).comp
        (g.kaehlerToSectionsₗ U).toAddMonoidHom
    let rhs : KaehlerDifferential R Γ(Y,U) →+ Γ((j ≫ g).kaehler,j ⁻¹ᵁ U) :=
      ((j ≫ g).kaehlerToSectionsₗ (j ⁻¹ᵁ U)).toAddMonoidHom.comp
        (GlobalNormalizedDifferential.differentialMap φ.toAlgHom).toAddMonoidHom
    have hh : lhs = rhs := KaehlerDifferential.addMonoidHom_ext_smul_D (fun a b => by
      change (k1 g (j ≫ g) j (by simp)).app U (g.kaehlerToSections U (a • KaehlerDifferential.D R Γ(Y,U) b)) = _
      change (k1 g (j ≫ g) j (by simp)).app U (g.kaehlerToSectionsₗ U (a • KaehlerDifferential.D R Γ(Y,U) b)) = _
      rw [map_smul, Scheme.Modules.Hom.app_smul]
      change j.app U a • (show Γ((j ≫ g).kaehler,j ⁻¹ᵁ U) from
        (k1 g (j ≫ g) j (by simp)).app U (g.kaehlerToSections U (dK g U b))) = _
      rw [k1_kaehlerToSections, k1app_dK]
      change j.app U a • (j ≫ g).kaehlerToSections (j ⁻¹ᵁ U)
        (KaehlerDifferential.D R Γ(X,j ⁻¹ᵁ U) (j.app U b)) =
        (j ≫ g).kaehlerToSections (j ⁻¹ᵁ U)
          (GlobalNormalizedDifferential.differentialMap φ.toAlgHom (a • KaehlerDifferential.D R Γ(Y,U) b))
      rw [GlobalNormalizedDifferential.differentialMap_smul, GlobalNormalizedDifferential.differentialMap_D]
      exact ((j ≫ g).kaehlerToSectionsₗ (j ⁻¹ᵁ U)).map_smul (φ a) _ |>.symm)
    exact DFunLike.congr_fun hh
  intro s t hst
  obtain ⟨a,rfl⟩ := (g.kaehlerToSections_bijective_of_isAffineOpen hU).2 s
  obtain ⟨b,rfl⟩ := (g.kaehlerToSections_bijective_of_isAffineOpen hU).2 t
  rw [he,he] at hst
  have hab := (GlobalNormalizedDifferential.differentialMap_bijective φ).1
    (((j ≫ g).kaehlerToSections_bijective_of_isAffineOpen hV).1 hst)
  exact congrArg (g.kaehlerToSections U) hab

lemma differential_restrict_global {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ j ⁻¹ᵁ U) (s : Γ(g.kaehler,⊤)) :
    res (j ≫ g).kaehler h
      ((k1 g (j ≫ g) j (by simp)).app U (res g.kaehler le_top s)) =
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap
        g (j ≫ g) j (by simp)).app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection j g.kaehler s) := by
  have he := Scheme.Modules.homEquiv_symm_app_pullbackLocalSection j
    (k1 g (j ≫ g) j (by simp)) (res g.kaehler (show U ≤ ⊤ from le_top) s)
  change (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap
    g (j ≫ g) j (by simp)).app _ (Scheme.Modules.pullbackLocalSection j
      (res g.kaehler le_top s)) = _ at he
  rw [← he, hom_res, pullback_restrict_top]

lemma differential_restrict_smul {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ j ⁻¹ᵁ U) (a : Γ(Y,U)) (s : Γ(g.kaehler,⊤)) :
    res (j ≫ g).kaehler h
      ((k1 g (j ≫ g) j (by simp)).app U (a • res g.kaehler le_top s)) =
      j.appLE U ⊤ h a •
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap
        g (j ≫ g) j (by simp)).app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection j g.kaehler s) := by
  rw [Scheme.Modules.Hom.app_smul]
  change res (j ≫ g).kaehler h (j.app U a •
    (show Γ((j ≫ g).kaehler,j ⁻¹ᵁ U) from
      (k1 g (j ≫ g) j (by simp)).app U (res g.kaehler le_top s))) = _
  rw [res_smul, differential_restrict_global]
  rfl

lemma res_injective_of_top {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (h : ⊤ ≤ U) :
    Function.Injective (res M h) := by
  haveI : IsIso (homOfLE h) := homOfLE_isIso_of_eq h (top_unique h).symm
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map (homOfLE h).op)).1

lemma normalized_frames_equal [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Algebra ℚ R] [W.IsElliptic] (δ δ' : CurveFrame R W)
    (hδ : NormalizedFrame R W δ) (hδ' : NormalizedFrame R W δ') : δ' = δ := by
  letI := (relative_curve_geometry R W).1
  letI := zOpen_nonempty R W
  let j := ArithmeticThetaLegendreComparisonR0177.chartInclusion R W
  let U := zOpen R W
  have hpre : j ⁻¹ᵁ U = ⊤ := Scheme.Hom.preimage_image_eq j ⊤
  have h : ⊤ ≤ j ⁻¹ᵁ U := hpre.ge
  have hU : IsAffineOpen U := by
    change IsAffineOpen (j ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange j
  have hV : IsAffineOpen (j ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
  have hj : Function.Bijective (j.app U) := by
    haveI : IsIso (j.app U) := j.isIso_app U (by
      change j ''ᵁ ⊤ ≤ j.opensRange
      rw [Scheme.Hom.image_top_eq_opensRange])
    exact ConcreteCategory.bijective_of_isIso _
  have hc : zSection R W (zP R W) ≠ 0 := by
    intro hz
    apply zP_ne_zero R W
    apply (zSection R W).injective
    simpa only [map_zero] using hz
  have hm : zSection R W (zP R W) • res (structureMap R W).kaehler (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ') =
      zSection R W (zP R W) • res (structureMap R W).kaehler (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ) := by
    apply differential_on_isomorphic_sections R (structureMap R W) j U hU hV hj
    apply res_injective_of_top (j ≫ structureMap R W).kaehler _ h
    rw [differential_restrict_smul, differential_restrict_smul, chart_app_section]
    exact hδ'.symm.trans hδ
  have hd : res (structureMap R W).kaehler (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ') =
      res (structureMap R W).kaehler (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ) := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app δ.inv U)).1
    have hh := congrArg (Scheme.Modules.Hom.app δ.inv U) hm
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at hh
    change zSection R W (zP R W) * (show Γ(Curve R W,U) from Scheme.Modules.Hom.app δ.inv U _) =
      zSection R W (zP R W) * (show Γ(Curve R W,U) from Scheme.Modules.Hom.app δ.inv U _) at hh
    exact @mul_left_cancel₀ Γ(Curve R W,U) _ _ _ (zSection R W (zP R W))
      (show Γ(Curve R W,U) from Scheme.Modules.Hom.app δ.inv U _)
      (show Γ(Curve R W,U) from Scheme.Modules.Hom.app δ.inv U _) hc hh
  apply Iso.ext
  apply ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unit_hom_ext
  apply frame_restrict_injective δ ⊤ U le_top
  exact hd

end DifferentialFaithfulness

end RelativeNormalizedDifferential
/-- The unique normalized frame of the actual relative differential sheaf,
whose pullback generates the Hodge sheaf on every subopen. -/
theorem relative_normalized_differential :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
      [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic],
      ∃! δ : CurveFrame R W, NormalizedFrame R W δ ∧
        ArithmeticThetaRelativeDiscriminantR0171.IsFrame
          (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W) ⊤ (hodgeGenerator R W δ) := by
  intro R _ _ _ _ _ W _
  obtain ⟨δ,hδ⟩ := RelativeNormalizedDifferential.normalized_frame_exists R W
  exact ⟨δ, ⟨hδ, RelativeNormalizedDifferential.hodge_generator_frame R W δ⟩,
    fun δ' hδ' => RelativeNormalizedDifferential.normalized_frames_equal R W δ δ' hδ hδ'.1⟩

end ArithmeticThetaGlobalFourTorsionR0190

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.hodge_generator_frame
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.origin_frame

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.affine_frame

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.actual_affine_frame
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.actual_origin_frame

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.z_local_frame
#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.y_local_frame

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.global_frame_on_open

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.normalized_frame_exists

#print axioms ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.zP_ne_zero

#print axioms ArithmeticThetaGlobalFourTorsionR0190.relative_normalized_differential
