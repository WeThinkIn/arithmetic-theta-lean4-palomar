module

public import PeriodOneRamifiedEvaluationR0248

@[expose] public section

/-! The full normalized Kato product on the original period-one cubic. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaPeriodOneNormR0248
namespace FullKatoNormProof
open ArithmeticThetaLaurentNormR0064 (w t Q fValue)
open ArithmeticThetaUnsplitExpansionR0158

variable (k : Type) [Field k] [CharZero k]

/-- The monomial factors of the full product follow the same parameter map
as its gamma factors. No coefficient or truncation is discarded. -/
lemma product_ramification (psi : Series k →+* Series k)
    (hp : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi)
    (c : ℕ) (g h : Series k) :
    psi (fValue k c 1 (HahnSeries.C (w k)) g h) =
      fValue k c 4 (HahnSeries.C (w k)) (psi g) (psi h) := by
  letI : CharZero (Coeff k) := charZero_of_injective_ringHom
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
  have hs (e : ℤ) (a : Coeff k) :
      psi (HahnSeries.single e a) = HahnSeries.single (4 * e) a := by
    rw [GammaBaseChangeNaturalityR0158.ramificationHom_eq _ 4 (by decide) psi hp]
    exact GammaBaseChangeNaturalityR0158.ramificationHom_single _ 4 (by decide) e a
  have hC (a : Coeff k) : psi (HahnSeries.C a) = HahnSeries.C a := by
    simpa only [HahnSeries.C_apply, mul_zero] using hs 0 a
  have ht : psi (t (Coeff k)) = t (Coeff k) ^ 4 := by
    simpa [t, HahnSeries.single_pow] using hs 1 1
  simp only [fValue, Q, pow_one, map_mul, map_div₀, map_zpow₀,
    map_pow, map_neg, hC, ht]

/-- Faithful descent of the entire Laurent expansion from period four. -/
lemma expansion_descent (psi : Series k →+* Series k)
    (hp : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi)
    (c : ℕ) (v : Series k) (hv : HasExpansion k 4 c 0 (psi v)) :
    HasExpansion k 1 c 0 v := by
  letI : CharZero (Coeff k) := charZero_of_injective_ringHom
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
  intro g h hg hh
  have hw := ChartEvaluationProof.w_ne_zero k
  have hg4 := gamma_base_change_naturality.2 (Coeff k) 4 (by decide) psi hp
    1 0 (w k) g (by decide) hw hg
  have hh4 := gamma_base_change_naturality.2 (Coeff k) 4 (by decide) psi hp
    1 (c * 0) (w k ^ c) h (by decide) (pow_ne_zero _ hw) hh
  apply psi.injective
  simp only [pow_zero, mul_one]
  rw [product_ramification k psi hp]
  simpa only [pow_zero, mul_one] using
    hv (psi g) (psi h) (by simpa using hg4) (by simpa using hh4)

/-- The two literal gamma limits used at the transcendental coordinate exist
and are nonzero, so the full-product assertion has actual witnesses. -/
lemma gamma_witnesses (c : ℕ) (hc : 0 < c) :
    ∃ g h : Series k,
      ArithmeticThetaLaurentNormR0064.IsGamma (Coeff k) 1 0 (w k) g ∧
      ArithmeticThetaLaurentNormR0064.IsGamma (Coeff k) 1 0 (w k ^ c) h ∧
      g ≠ 0 ∧ h ≠ 0 := by
  have hw0 := ChartEvaluationProof.w_ne_zero k
  have hw1 := ChartEvaluationProof.w_ne_one k
  have hwc0 := pow_ne_zero c hw0
  have hwc1 : w k ^ c ≠ 1 := by
    have ht := (ChartEvaluationProof.w_transcendental k).pow hc
    exact fun h => ht (h.symm ▸ isAlgebraic_one)
  obtain ⟨g, hg, _⟩ := ArithmeticThetaLaurentNormR0064.gamma_exists_unique
    (Coeff k) 1 0 (w k) (by decide) hw0
  obtain ⟨h, hh, _⟩ := ArithmeticThetaLaurentNormR0064.gamma_exists_unique
    (Coeff k) 1 0 (w k ^ c) (by decide) hwc0
  exact ⟨g, h, hg, hh,
    ArithmeticThetaLaurentNormR0064.gamma_nonzero (Coeff k) 1 0 (w k)
      (by decide) hw0 hw1 g hg,
    ArithmeticThetaLaurentNormR0064.gamma_nonzero (Coeff k) 1 0 (w k ^ c)
      (by decide) hwc0 hwc1 h hh⟩

end FullKatoNormProof

open AlgebraicGeometry
open ArithmeticThetaGeneralEllipticKatoR0168

/-- Geometry, origin law and one faithful generic-coordinate evaluation work
simultaneously for every c > 1 prime to six, over the original parameter Q. -/
theorem period_one_full_kato_norm :
    ∀ (k : Type) [Field k] [CharZero k], PeriodOneNorm k := by
  intro k _ _
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : CharZero (Coeff k) := charZero_of_injective_ringHom
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
  letI : (periodCurve k).IsElliptic :=
    (ArithmeticThetaPeriodOneR0246.period_one_geometric_comparison k).1
  letI : (ramifiedCurve k 4).IsElliptic :=
    ArithmeticThetaTateCuspsR0181.TateFullLevelMarking.elliptic k 4 (by decide) (by decide)
  have hgeom := ArithmeticThetaRelativeKatoR0169.relative_curve_geometry
    (LaurentSeries k) (periodCurve k)
  have hgeom4 := ArithmeticThetaRelativeKatoR0169.relative_curve_geometry
    (LaurentSeries k) (ramifiedCurve k 4)
  letI : IsIntegral (Curve k (periodCurve k)) := hgeom.1
  letI : IsLocallyNoetherian (Curve k (periodCurve k)) := hgeom.2.1
  letI : IsIntegral (Curve k (ramifiedCurve k 4)) := hgeom4.1
  letI : IsLocallyNoetherian (Curve k (ramifiedCurve k 4)) := hgeom4.2.1
  obtain ⟨G, hG⟩ := ArithmeticThetaPeriodOneR0246.NormalizedFrameProof.origin_law
    (LaurentSeries k) (periodCurve k)
  obtain ⟨G4, hG4⟩ := ArithmeticThetaPeriodOneR0246.NormalizedFrameProof.origin_law
    (LaurentSeries k) (ramifiedCurve k 4)
  obtain ⟨ev, hev, huev⟩ := period_one_function_field_evaluation k
  obtain ⟨ev4, hev4, _⟩ := ramified_cubic_kato_evaluation k 4 (by decide) (by decide)
  obtain ⟨ell, ⟨he, _⟩, _⟩ :=
    ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k 4 (by decide)
  obtain ⟨C⟩ := (ArithmeticThetaPeriodOneR0246.period_one_geometric_comparison k).2 ell he |>.2
  obtain ⟨psi, ⟨hp, _⟩, _⟩ :=
    ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension (Coeff k) 4 (by decide)
  obtain ⟨a, ⟨_, hsquare, htransport⟩, _⟩ :=
    period_one_ramified_evaluation k ell he C G G4 hG hG4 ev ev4 hev.1 hev4.1 psi hp
  refine ⟨inferInstance, inferInstance, G, hG, ev, ⟨hev.1, hev.2, ?_⟩, ?_⟩
  · intro c hc hcop
    obtain ⟨g, hg, hug⟩ := general_kato_existence
      (LaurentSeries k) (periodCurve k) G hG c hc hcop
    refine ⟨g, ⟨hg, ?_⟩, fun f hf => hug f hf.1⟩
    apply FullKatoNormProof.expansion_descent k psi hp c (ev g)
    have hx : ev4 (a g) = psi (ev g) := RingHom.congr_fun hsquare g
    rw [← hx]
    exact hev4.2.2 G4 hG4 c hc hcop (a g) (htransport c hc hcop g hg)
  · intro ev' hev'
    exact huev ev' ⟨hev'.1, hev'.2.1⟩

#print axioms FullKatoNormProof.gamma_witnesses
#print axioms period_one_full_kato_norm
end ArithmeticThetaPeriodOneNormR0248
