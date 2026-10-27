import UnsplitExpansionDefinitionsR0158

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaUnsplitExpansionR0158
namespace CoefficientEvaluationNaturalityR0158
open ArithmeticThetaLaurentNormR0064
open ArithmeticThetaCoefficientNormDescentR0157
variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]

private def polynomialMap (ι : k →+* l) : LaurentPolynomial k →+* LaurentPolynomial l :=
  AddMonoidAlgebra.mapRingHom ℤ ι

private lemma polynomialMap_injective (ι : k →+* l) :
    Function.Injective (polynomialMap k l ι) := by
  intro p q h
  ext n
  apply ι.injective
  exact congrArg (fun p : LaurentPolynomial l => p.coeff n) h

private def coefficientExtension (ι : k →+* l) : Coeff k →+* Coeff l :=
  IsFractionRing.lift (g := (algebraMap (LaurentPolynomial l) (Coeff l)).comp (polynomialMap k l ι))
    ((IsFractionRing.injective (LaurentPolynomial l) (Coeff l)).comp
    (polynomialMap_injective k l ι))

private lemma coefficientExtension_spec (ι : k →+* l) :
    IsCoefficientMap k l ι (coefficientExtension k l ι) := by
  constructor
  · intro a
    unfold scalar coefficientExtension
    rw [IsFractionRing.lift_algebraMap]
    change algebraMap (LaurentPolynomial l) (Coeff l)
      (AddMonoidAlgebra.mapRingHom ℤ ι (AddMonoidAlgebra.single 0 a)) = _
    rw [AddMonoidAlgebra.mapRingHom_single]
    rfl
  · unfold w coefficientExtension
    rw [IsFractionRing.lift_algebraMap]
    change algebraMap (LaurentPolynomial l) (Coeff l)
      (AddMonoidAlgebra.mapRingHom ℤ ι (AddMonoidAlgebra.single 1 1)) = _
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
    rfl

private lemma coefficient_unique (ι : k →+* l) (κ κ' : Coeff k →+* Coeff l)
    (hκ : IsCoefficientMap k l ι κ) (hκ' : IsCoefficientMap k l ι κ') : κ = κ' := by
  apply IsFractionRing.ringHom_ext (A := LaurentPolynomial k)
  suffices h : κ.comp (algebraMap (LaurentPolynomial k) (Coeff k)) =
      κ'.comp (algebraMap (LaurentPolynomial k) (Coeff k)) from RingHom.congr_fun h
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro a
    simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C, scalar] using (hκ.1 a).trans (hκ'.1 a).symm
  · simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X, w] using hκ.2.trans hκ'.2.symm

private def seriesMap (κ : Coeff k →+* Coeff l) : Series k →+* Series l where
  toFun f := f.map κ.toZeroHom
  map_zero' := HahnSeries.map_zero _
  map_one' := HahnSeries.map_one κ.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add κ.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul κ.toNonUnitalRingHom

private lemma seriesMap_power (κ : Coeff k →+* Coeff l) (b : PowerSeries (Coeff k)) :
    seriesMap k l κ (algebraMap (PowerSeries (Coeff k)) (Series k) b) =
      algebraMap (PowerSeries (Coeff l)) (Series l) (PowerSeries.map κ b) := by
  apply HahnSeries.ext
  funext e
  change κ ((algebraMap (PowerSeries (Coeff k)) (Series k) b).coeff e) = _
  by_cases he : e < 0
  · simp [PowerSeries.coeff_coe, he]
  · simp [PowerSeries.coeff_coe, he, PowerSeries.coeff_map]

private lemma laurent_coeff (κ : Coeff k →+* Coeff l)
    (ell : Series k →+* Series l) (hell : IsLaurentMap (Coeff k) (Coeff l) κ ell)
    (b : Series k) (e : ℤ) : (ell b).coeff e = κ (b.coeff e) := by
  have h : ell = seriesMap k l κ := by
    apply IsFractionRing.ringHom_ext (A := PowerSeries (Coeff k))
    intro b
    exact (hell b).trans (seriesMap_power k l κ b).symm
  rw [h]
  rfl

open ArithmeticThetaAnnularNormBridgeR0156 (baseSeries coordinate IsEvaluation)
open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaScaledTateBridgeR0046

private lemma evaluation_square (ι : k →+* l)
    (κ : Coeff k →+* Coeff l) (hκ : IsCoefficientMap k l ι κ)
    (ell : Series k →+* Series l) (hell : IsLaurentMap (Coeff k) (Coeff l) κ ell)
    (ρ : Chart k →+* Chart l) (hρ : ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ)
    (E : ChartField k →+* ChartField l) (hE : ExtendsChart k l ρ E)
    (evk : ChartField k →+* Series k) (evl : ChartField l →+* Series l)
    (hk : IsEvaluation k 1 1 evk) (hl : IsEvaluation l 1 1 evl) :
    evl.comp E = ell.comp evk := by
  have hbase (b : PowerSeries k) : ell (baseSeries k b) = baseSeries l (baseMap k l ι b) := by
    rw [baseSeries, hell]
    congr 1
    ext n
    simpa only [baseMap, PowerSeries.coeff_map, scalar,
      ArithmeticThetaAnnularNormBridgeR0156.coefficientMap, RingHom.comp_apply] using hκ.1 (PowerSeries.coeff n b)
  have hC (a : Coeff k) : ell (HahnSeries.C a) = HahnSeries.C (κ a) := by
    have h := hell (PowerSeries.C a)
    change ell (HahnSeries.ofPowerSeries ℤ (Coeff k) (PowerSeries.C a)) =
      HahnSeries.ofPowerSeries ℤ (Coeff l) (PowerSeries.map κ (PowerSeries.C a)) at h
    simpa only [baseMap, PowerSeries.map_C, HahnSeries.ofPowerSeries_C] using h
  have ht : ell (ArithmeticThetaLaurentNormR0064.t (Coeff k)) =
      ArithmeticThetaLaurentNormR0064.t (Coeff l) := by
    have h := hell PowerSeries.X
    change ell (HahnSeries.ofPowerSeries ℤ (Coeff k) PowerSeries.X) =
      HahnSeries.ofPowerSeries ℤ (Coeff l) (PowerSeries.map κ PowerSeries.X) at h
    simpa only [baseMap, PowerSeries.map_X, HahnSeries.ofPowerSeries_X,
      ArithmeticThetaLaurentNormR0064.t] using h
  have hcoord : κ (coordinate k 1 1) = coordinate l 1 1 := by
    simpa [coordinate] using hκ.2
  have hnode (b : Node k 1) :
      evl (E (chartToField k (toCompleted k 1 b))) =
      ell (evk (chartToField k (toCompleted k 1 b))) := by
    suffices h : ((evl.comp E).comp (chartToField k)).comp (toCompleted k 1) =
        ((ell.comp evk).comp (chartToField k)).comp (toCompleted k 1) from RingHom.congr_fun h b
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro b
      change evl (E (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b))) = ell (evk (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)))
      rw [hE, hρ.1, hl.1, hk.1, hbase]
    · intro i
      fin_cases i
      · change evl (E (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.cx k))) = ell (evk (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)))
        rw [hE, hρ.2.1, hl.2.1, hk.2.1, hC, hcoord]
      · change evl (E (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.cy k))) = ell (evk (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)))
        rw [hE, hρ.2.2.1, hl.2.2.1, hk.2.2.1]
        simp only [map_mul, map_inv₀, hC, hcoord, ht]
  have hchart (b : Chart k) : evl (E (chartToField k b)) = ell (evk (chartToField k b)) := by
    apply HahnSeries.ext
    funext e
    let N := (e + 1).toNat
    obtain ⟨p, hp⟩ := (completion_reductions k 1 (by omega)).2.2.2.2.2.2 N b
    have he : e < (N : ℤ) := by dsimp [N]; omega
    have h1 := hl.2.2.2 N _ (hρ.2.2.2 N _ hp) e he
    have h2 : (ell (evk (chartToField k (b - toCompleted k 1 (quotientMap k 1 p))))).coeff e = 0 := by
      rw [laurent_coeff k l κ ell hell, hk.2.2.2 N _ hp e he, map_zero]
    rw [← hE] at h1
    simp only [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1 h2
    rw [h1, h2, hnode]
  apply IsFractionRing.ringHom_ext (A := ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k)
  suffices h : (evl.comp E).comp (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _) =
      (ell.comp evk).comp (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.GenericChart k) _) from
    fun b => RingHom.congr_fun h b
  apply IsLocalization.ringHom_ext (Submonoid.powers (ArithmeticThetaAnnularTorsionPrereqR0053.tau k))
  apply RingHom.ext
  exact hchart

end CoefficientEvaluationNaturalityR0158
/-- Coefficient extension fixing the transcendental coordinate and compatibility
of the full completed-chart evaluation with coefficient base change. -/
theorem coefficient_evaluation_naturality :
∀ (k : Type) [Field k] [CharZero k] (l : Type) [Field l] [CharZero l] (ι : k →+* l), (∃! κ : ArithmeticThetaLaurentNormR0064.Coeff k →+* ArithmeticThetaLaurentNormR0064.Coeff l, ArithmeticThetaUnsplitExpansionR0158.IsCoefficientMap k l ι κ) ∧ (∀ (κ : ArithmeticThetaLaurentNormR0064.Coeff k →+* ArithmeticThetaLaurentNormR0064.Coeff l), ArithmeticThetaUnsplitExpansionR0158.IsCoefficientMap k l ι κ → ∀ (ell : ArithmeticThetaLaurentNormR0064.Series k →+* ArithmeticThetaLaurentNormR0064.Series l), ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap (ArithmeticThetaLaurentNormR0064.Coeff k) (ArithmeticThetaLaurentNormR0064.Coeff l) κ ell → ∀ (ρ : ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart l), ArithmeticThetaCoefficientNormDescentR0157.IsChartMap k l ι ρ → ∀ (E : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField l), ArithmeticThetaCoefficientNormDescentR0157.ExtendsChart k l ρ E → ∀ (evk : ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaLaurentNormR0064.Series k) (evl : ArithmeticThetaKatoAnnularR0152.ChartField l →+* ArithmeticThetaLaurentNormR0064.Series l), ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation k 1 1 evk → ArithmeticThetaAnnularNormBridgeR0156.IsEvaluation l 1 1 evl → evl.comp E = ell.comp evk) := by
  intro k _ _ l _ _ ι
  constructor
  · refine ⟨CoefficientEvaluationNaturalityR0158.coefficientExtension k l ι,
      CoefficientEvaluationNaturalityR0158.coefficientExtension_spec k l ι, ?_⟩
    intro κ hκ
    exact CoefficientEvaluationNaturalityR0158.coefficient_unique k l ι κ _ hκ
      (CoefficientEvaluationNaturalityR0158.coefficientExtension_spec k l ι)
  · intro κ hκ ell hell ρ hρ E hE evk evl hk hl
    exact CoefficientEvaluationNaturalityR0158.evaluation_square k l ι κ hκ ell hell
      ρ hρ E hE evk evl hk hl

end ArithmeticThetaUnsplitExpansionR0158

#print axioms ArithmeticThetaUnsplitExpansionR0158.coefficient_evaluation_naturality
