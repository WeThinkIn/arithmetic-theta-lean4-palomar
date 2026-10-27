import ActualKatoTaylorR0161
import ActualOriginLocalComparisonR0161
import RamifiedInitialTransportR0161

/-! The nonzero initial class of the actual normalized five-Kato function.
All auxiliary implementation lemmas are private to this module. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaKatoExistenceR0151 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

private lemma regular_of_nonnegative_order {A K : Type}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (g : K) (n : ℕ) (h : Ring.ordFrac A g = WithZero.exp (n : ℤ)) :
    ∃ a : A, algebraMap A K a = g := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hn : Ring.ordFrac A (algebraMap A K (π^n)) = WithZero.exp (n : ℤ) := by
    rw [map_pow, map_pow, Ring.ordFrac_irreducible hπ]
    simp
  obtain ⟨v, hv⟩ := Ring.associated_of_ordFrac_eq (algebraMap A K (π^n)) g (hn.trans h.symm)
  exact ⟨(v : A) * π^n, by simpa only [map_mul, Units.smul_def, Algebra.smul_def] using hv⟩

private lemma origin_regular (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (h3 : 3 ≤ r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (g : (genericScheme k M).functionField)
    (hg : IsKatoFunction k M s hs.1 G 5 g) :
    ∃ a : OriginStalk k M s hs.1,
      algebraMap (OriginStalk k M s hs.1) (genericScheme k M).functionField a = g := by
  let e := Origin k M s hs.1
  let x := e (IsLocalRing.closedPoint (LaurentSeries k))
  letI : IsClosedImmersion e :=
    genericPoint_closed
      k M hM s hs.1
  have hx : IsClosed ({x} : Set (genericScheme k M)) := by
    have heq : Set.range e = {x} := Set.range_eq_singleton fun a =>
      congrArg e (Subsingleton.elim a (IsLocalRing.closedPoint (LaurentSeries k)))
    rw [← heq]
    exact e.isClosedEmbedding.isClosed_range
  letI : SmoothOfRelativeDimension 1 (genericStructure k M) := generic_relative_one k h3 M hM s hs
  letI : IsIntegral (CategoryTheory.Limits.pullback M.p (genericBase k)) :=
    inferInstanceAs (IsIntegral (genericScheme k M))
  letI : IsDiscreteValuationRing (OriginStalk k M s hs.1) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      (genericStructure k M) x hx
  have hco : Order.coheight x = 1 := by
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (OriginStalk k M s hs.1)
    rw [ringKrullDim_stalk_eq_coheight] at hd
    exact_mod_cast hd
  have hord : Scheme.ord g x = katoOrder k M s hs.1 G 5 x := hg.1.2 x
  have hv := (Scheme.ord_eq_iff hco hg.1.1).mp hord
  change Ring.ordFrac (OriginStalk k M s hs.1) g = _ at hv
  simp only [katoOrder, show x = identityPoint k M s hs.1 from rfl, ite_true] at hv
  split_ifs at hv
  · exact regular_of_nonnegative_order g 24 (by norm_num [← WithZero.exp_eq_coe_ofAdd] at hv ⊢; exact hv)
  · exact regular_of_nonnegative_order g 25 (by norm_num [← WithZero.exp_eq_coe_ofAdd] at hv ⊢; exact hv)



/-- The exact nonzero initial class in the actual identity stalk. -/
theorem geometric_discriminant_initial :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g ∧ (∃ (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) M.X) (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k)) (σ : ArithmeticThetaOriginInitialR0161.Chart k →+* ArithmeticThetaOriginInitialR0161.Bivariate k) (Ψ : ArithmeticThetaOriginInitialR0161.ChartField k →+* ArithmeticThetaOriginInitialR0161.Iterated k) (κ : ArithmeticThetaOriginInitialR0161.OriginStalk k M s hs.1 →+* PowerSeries (LaurentSeries k)), (∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) ∧ (∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) ∧ ArithmeticThetaOriginInitialR0161.IsChartTaylor k σ ∧ ArithmeticThetaOriginInitialR0161.ExtendsTaylor k σ Ψ ∧ ArithmeticThetaOriginInitialR0161.IsOriginTaylor k M s hs.1 (Ψ.comp (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr))) κ ∧ Ψ (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) g) = ArithmeticThetaOriginInitialR0161.f5Taylor k r ∧ ArithmeticThetaOriginInitialR0161.HasDiscriminantInitial k M s hs.1 g κ) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _
  classical
  obtain ⟨g, hg, huniq⟩ := actual_kato_function_existence
    k r hr h3 T he M hM s hs G hG 5 (by decide) (by decide)
  have Hχ : ∀ j : Fin r, ∃ χj, IsChartMap k M j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k r hr h3 T M hM j
    exact ⟨χj, hj⟩
  choose χ hχ using Hχ
  have Hφ : ∀ j : Fin r, ∃ φj, IsChartFieldMap k M (χ j) φj := by
    intro j
    obtain ⟨φj, hj, _⟩ := completed_chart_field_maps k r hr h3 T M hM j (χ j) (hχ j)
    exact ⟨φj, hj.1⟩
  choose φ hφ using Hφ
  obtain ⟨σ, hσ, _⟩ := completed_chart_taylor k
  obtain ⟨Ψ, hΨ, _⟩ := (faithful_taylor_field k σ hσ).2
  obtain ⟨κ, hκ, _⟩ := actual_origin_local_comparison
    k r hr h3 he T M hM s hs χ hχ φ hφ σ hσ Ψ hΨ
  have hexp := actual_kato_taylor k r hr h3 he T M hM s hs G hG
    χ hχ φ hφ σ hσ Ψ hΨ g hg
  obtain ⟨hord, hcoeff, hnonzero⟩ := ramified_initial_transport k r hr
  obtain ⟨a, ha⟩ := origin_regular k h3 M hM s hs G g hg
  let b : OriginStalk k M s hs.1 := 5*a
  have hb : algebraMap (OriginStalk k M s hs.1) (genericScheme k M).functionField b = 5*g := by
    simp only [b, map_mul, map_ofNat, ha]
  have hbexp : HahnSeries.ofPowerSeries ℤ (LaurentSeries k) (κ b) = 5*f5Taylor k r := by
    rw [hκ.1 b, hb]
    simp only [RingHom.comp_apply, map_mul, map_ofNat, hexp]
  have hbc (i : ℕ) : PowerSeries.coeff i (κ b) = 5*(f5Taylor k r).coeff (i : ℤ) := by
    have h := congrArg (fun f : Iterated k => f.coeff (i : ℤ)) hbexp
    have hfive : (5 : Iterated k) = HahnSeries.single 0 (5 : LaurentSeries k) := by
      exact (HahnSeries.single_zero_ofNat 5).symm
    rw [hfive, HahnSeries.coeff_single_zero_mul] at h
    simpa only [LaurentSeries.coeff_coe_powerSeries] using h
  have hc24 : PowerSeries.coeff 24 (κ b) = ArithmeticThetaUnaryKatoPowerR0160.discriminant k r := by
    rw [hbc]
    norm_num only [Nat.cast_ofNat]
    rw [hcoeff]
    have h5 : (5 : LaurentSeries k) ≠ 0 := by
      have hf : (5 : LaurentSeries k) = HahnSeries.C (5 : k) := by
        exact (HahnSeries.single_zero_ofNat 5).symm
      rw [hf]
      simpa only [map_zero] using
        ((HahnSeries.C_injective (Γ := ℤ) (R := k)).ne (by norm_num : (5 : k) ≠ 0))
    field_simp
  refine ⟨g, ⟨hg, χ, φ, σ, Ψ, κ, hχ, hφ, hσ, hΨ, hκ, hexp, ?_⟩, ?_⟩
  · refine ⟨b, hb, ?_, ?_, hc24⟩
    · apply (hκ.2.2 b 24).mpr
      intro i hi
      rw [hbc, HahnSeries.coeff_eq_zero_of_lt_order (by rw [hord]; exact_mod_cast hi), mul_zero]
    · intro hm
      have hz := (hκ.2.2 b 25).mp hm 24 (by decide)
      exact hnonzero (hc24.symm.trans hz)
  · intro g' hg'
    exact huniq g' hg'.1

end ArithmeticThetaOriginInitialR0161
#print axioms ArithmeticThetaOriginInitialR0161.geometric_discriminant_initial
