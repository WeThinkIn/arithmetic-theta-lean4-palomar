import CubicModelDefinitionsR0144

/-! The cleared cubic on the actual finite node charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaCubicModelR0144
namespace FiniteChartSplitCubicR0144
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCohomologyR0131.PolygonCechKernelR0131
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaModelSymmetriesR0137

lemma polynomial_density {K S : Type*} [Field K] [CommRing S]
    (f : K →+* S) (p : Polynomial S) (s : Set K) (hs : s.Infinite)
    (hp : ∀ a ∈ s, p.eval (f a) = 0) : p = 0 := by
  classical
  nontriviality S
  suffices aux : ∀ d, ∀ p : Polynomial S, p.natDegree = d →
      ∀ s : Set K, s.Infinite → (∀ a ∈ s, p.eval (f a) = 0) → p = 0 by
    exact aux _ p rfl s hs hp
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hd s hs hp
    obtain ⟨a, ha⟩ := hs.nonempty
    by_cases hz : d = 0
    · have he := Polynomial.eq_C_of_natDegree_eq_zero (hd.trans hz)
      rw [he] at hp ⊢
      simpa using congrArg Polynomial.C (hp a ha)
    · let q := p /ₘ (Polynomial.X - Polynomial.C (f a))
      have hq : q.natDegree < d := by
        rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
          Polynomial.natDegree_X_sub_C, hd]
        omega
      have he : p = (Polynomial.X - Polynomial.C (f a)) * q := by
        have h := p.modByMonic_add_div (Polynomial.X - Polynomial.C (f a))
        rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, hp a ha, Polynomial.C_0,
          zero_add] at h
        exact h.symm
      have hqz : q = 0 := by
        apply ih q.natDegree hq q rfl (s \ {a}) (hs.sdiff (Set.finite_singleton a))
        intro b hb
        have hu : IsUnit (f b - f a) := by
          rw [← map_sub]
          exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (by simpa using hb.2))).map f
        have hh := hp b hb.1
        rw [he, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C] at hh
        exact hu.mul_left_cancel (hh.trans (mul_zero _).symm)
      rw [he, hqz, mul_zero]

lemma laurent_density {K S : Type*} [Field K] [Infinite K] [CommRing S]
    (f : K →+* S) (p : LaurentPolynomial S)
    (hp : ∀ a : Kˣ, (a : K) ≠ 1 →
      LaurentPolynomial.eval₂ (RingHom.id S) (Units.map f a) p = 0) : p = 0 := by
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow p
  have hqz : q = 0 := by
    apply polynomial_density f q ({0, 1}ᶜ : Set K)
      (Set.Finite.infinite_compl (Set.toFinite _))
    intro a ha
    have ha0 : a ≠ 0 := by simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at ha; exact ha.1
    have ha1 : a ≠ 1 := by simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at ha; exact ha.2
    let b : Kˣ := Units.mk0 a ha0
    have hh := congrArg (LaurentPolynomial.eval₂ (RingHom.id S) (Units.map f b)) hq
    simpa [LaurentPolynomial.eval₂_toLaurent, hp b ha1, b] using hh
  rw [hqz, map_zero] at hq
  exact (LaurentPolynomial.isUnit_T (R := S) (n : ℤ)).mul_right_cancel
    (hq.symm.trans (zero_mul _).symm)


variable (k : Type u) [Field k] [CharZero k]

lemma eval_right (n : ℕ) (L : B k n true ≃+* LaurentPolynomial (R k n))
    (hL : LaurentPresentation k n L) (a : kˣ) (z : A k n) :
    LaurentPolynomial.eval₂ (RingHom.id (R k n)) (markedUnit k n a)
      (rightMap L z) = markedPoint k n a z := by
  suffices he : (LaurentPolynomial.eval₂ (RingHom.id (R k n)) (markedUnit k n a)).comp
      (rightMap L) = markedPoint k n a from RingHom.congr_fun he z
  apply point_ext
  · ext c
    simp only [RingHom.comp_apply, right_base L hL, LaurentPolynomial.eval₂_C,
      RingHom.id_apply, marked_base]
  · simp only [RingHom.comp_apply, right_x L hL, LaurentPolynomial.eval₂_T,
      zpow_one, markedPoint, mkPoint_x]
  · simp only [RingHom.comp_apply, right_y L hL, map_mul,
      LaurentPolynomial.eval₂_C, RingHom.id_apply, LaurentPolynomial.eval₂_T,
      zpow_neg_one, markedPoint, mkPoint_y]

lemma right_zero (n : ℕ) (L : B k n true ≃+* LaurentPolynomial (R k n))
    (hL : LaurentPresentation k n L) (z : A k n)
    (hz : ∀ a : kˣ, (a : k) ≠ 1 → markedPoint k n a z = 0) : rightMap L z = 0 := by
  apply laurent_density ((q k n).comp PowerSeries.C)
  intro a ha
  exact (eval_right k n L hL a z).trans (hz a ha)

lemma chart_detection (n : ℕ) (z : A k n)
    (hz : ∀ a : kˣ, (a : k) ≠ 1 → markedPoint k n a z = 0)
    (hs : ∀ a : kˣ, (a : k) ≠ 1 →
      markedPoint k n a (TowerInversionR0137.swap k n z) = 0) : z = 0 := by
  classical
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  obtain ⟨E, hE, _⟩ := finite_stage_adjacent k n
  have hr := right_zero k n L hL z hz
  have hs' := right_zero k n L hL _ hs
  have hl : leftMap L E z = 0 := by
    have hh : restriction k n true (TowerInversionR0137.swap k n z) = 0 := by
      apply L.injective
      exact hs'.trans (map_zero L).symm
    have he := RingHom.congr_fun (TowerInversionR0137.edgeSwap_right hE)
      (TowerInversionR0137.swap k n z)
    have hss := RingHom.congr_fun (TowerInversionR0137.swap_sq k n) z
    simp only [RingHom.comp_apply, RingHom.id_apply] at he hss
    rw [hh, map_zero, hss] at he
    change L (E (restriction k n false z)) = 0
    exact (congrArg L he.symm).trans (map_zero L)
  obtain ⟨c, hc⟩ := exists_expansion k n z
  have hc0 : c = 0 := by
    ext j
    by_cases hj : 0 ≤ j
    · have hh := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff j) hr
      rw [hc, right_coeff L hL] at hh
      simpa [Int.toNat_of_nonpos (by omega : -j ≤ 0)] using hh
    · have hh := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff j) hl
      rw [hc, left_coeff L hL E hE] at hh
      simpa [Int.toNat_of_nonpos (by omega : j ≤ 0)] using hh
  simp [hc, hc0]


lemma series_cubic (r : ℕ) (he : Even r) (i : Fin r) (a : kˣ)
    (ha : i.val = 0 → (a : k) ≠ 1) :
    (ArithmeticThetaTateSeries.tateY r i.val (a : k))^2 =
      ∏ j : Fin 3, (ArithmeticThetaTateSeries.tateX r i.val (a : k) - rootSeries k r j) := by
  obtain ⟨m, hm⟩ := he
  have hm' : r = 2*m := by omega
  have had : ArithmeticThetaTateSeries.Admissible (2*m) i.val (a : k) :=
    ⟨by have := i.isLt; omega, by have := i.isLt; omega, Units.ne_zero a, ha⟩
  have hh := ArithmeticThetaTateIdentities.general_annular_split_cubic m i.val (a : k) had
  simpa [hm', rootSeries, Fin.prod_univ_succ, mul_assoc] using hh

def defect (r n : ℕ) (i : Fin r) : A k n :=
  numerator k true r n i ^ 2 - ∏ j : Fin 3,
    (numerator k false r n i - rootAt k r n j * equation k r n i ^ 2)

lemma marked_defect (r n : ℕ) (h3 : 3 ≤ r) (he : Even r) (i : Fin r)
    (a : kˣ) (ha : (a : k) ≠ 1) : markedPoint k n a (defect k r n i) = 0 := by
  have hx := numerator_at_marked k false r n h3 i a (fun _ => ha)
  have hy := numerator_at_marked k true r n h3 i a (fun _ => ha)
  have hc := congrArg (q k n) (series_cubic k r he i a (fun _ => ha))
  simp only [map_pow, map_prod, map_sub] at hc
  simp only [defect, map_sub, map_pow, map_prod, map_mul, hx, hy,
    rootAt, marked_base, degree, Bool.false_eq_true, ↓reduceIte]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hc ⊢
  linear_combination (markedPoint k n a (equation k r n i))^6 * hc

lemma swap_defect (r n : ℕ) (i : Fin r) :
    TowerInversionR0137.swap k n (defect k r n (Fin.rev i)) = defect k r n i := by
  simp only [defect, map_sub, map_pow, map_prod, map_mul,
    CoordinateGeometricInversionR0143.swap_numerator,
    ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141.Numerators.swap_equation,
    rootAt, TowerInversionR0137.swap_base_apply, ↓reduceIte, Bool.false_eq_true, neg_sq]

end FiniteChartSplitCubicR0144

/-- The literal degree-six cleared cubic identity holds in every finite node chart. -/
theorem finite_chart_split_cubic :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (h3 : 3 ≤ r) (he : Even r)
      (n : ℕ) (i : Fin r),
      (ArithmeticThetaAlgebraicCoordinatesR0143.numerator k true r n i)^2 =
        ∏ j : Fin 3, (ArithmeticThetaAlgebraicCoordinatesR0143.numerator k false r n i -
          ArithmeticThetaCubicModelR0144.rootAt k r n j *
            (ArithmeticThetaIdentitySectionsR0138.equation k r n i)^2) := by
  intro k _ _ r h3 he n i
  apply sub_eq_zero.mp
  apply FiniteChartSplitCubicR0144.chart_detection k n
  · exact FiniteChartSplitCubicR0144.marked_defect k r n h3 he i
  · intro a ha
    change ArithmeticThetaPolygonCohomologyR0131.markedPoint k n a
      (ArithmeticThetaModelSymmetriesR0137.TowerInversionR0137.swap k n
        (FiniteChartSplitCubicR0144.defect k r n i)) = 0
    rw [← Fin.rev_rev i, FiniteChartSplitCubicR0144.swap_defect]
    exact FiniteChartSplitCubicR0144.marked_defect k r n h3 he (Fin.rev i) a ha

end ArithmeticThetaCubicModelR0144
#print axioms ArithmeticThetaCubicModelR0144.finite_chart_split_cubic
