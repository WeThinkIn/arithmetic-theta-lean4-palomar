import CompactUnaryDefinitionsR0183

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality
open ArithmeticThetaLaurentNormR0064 ArithmeticThetaMarkedKatoValuesR0159
open ArithmeticThetaNormFiniteR0063

/-- Every finite gamma product in the fundamental period is integral. -/
lemma partial_integral (k : Type) [Field k] (r j n : ℕ) (hj : j < r) (a : k) :
    ∃ f : PowerSeries k, HahnSeries.ofPowerSeries ℤ k f = Partial k r j a n := by
  refine ⟨(∏ l ∈ Finset.range n,
    (1 - PowerSeries.C a * PowerSeries.X ^ (r*l+j))) *
    (∏ l ∈ Finset.range n,
    (1 - PowerSeries.C a⁻¹ * PowerSeries.X ^ (r*(l+1)-j))), ?_⟩
  have hle (l : ℕ) : j ≤ r*(l+1) := by nlinarith
  simp only [Partial, map_mul, map_prod, map_sub, map_one,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, Int.natCast_sub (hle _)]

/-- Uniform agreement below each cutoff retains integrality in the limit. -/
lemma gamma_integral (k : Type) [Field k] (r j : ℕ) (hj : j < r)
    (a : k) (γ : LaurentSeries k) (hγ : IsGamma k r j a γ) :
    ∃ f : PowerSeries k, HahnSeries.ofPowerSeries ℤ k f = γ := by
  have hneg (e : ℤ) (he : e < 0) : γ.coeff e = 0 := by
    obtain ⟨n, hn⟩ := hγ e
    obtain ⟨f, hf⟩ := partial_integral k r j n hj a
    rw [← hn n le_rfl e le_rfl, ← hf]
    change (f : LaurentSeries k).coeff e = 0
    simp [PowerSeries.coeff_coe, he]
  refine ⟨PowerSeries.mk (fun n => γ.coeff n), ?_⟩
  apply HahnSeries.ext
  funext e
  by_cases he : e < 0
  · rw [hneg e he]
    change ((PowerSeries.mk (fun n => γ.coeff n) : PowerSeries k) : LaurentSeries k).coeff e = 0
    simp [PowerSeries.coeff_coe, he]
  · have heq : e = (e.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    rw [heq, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

lemma gamma_integral_nonzero (k : Type) [Field k] (r j : ℕ) (hj : j < r)
    (a : k) (ha : a ≠ 0) (hne : j ≠ 0 ∨ a ≠ 1)
    (γ : LaurentSeries k) (hγ : IsGamma k r j a γ) :
    ∃ f : PowerSeries k, f ≠ 0 ∧ HahnSeries.ofPowerSeries ℤ k f = γ := by
  obtain ⟨f, hf⟩ := gamma_integral k r j hj a γ hγ
  refine ⟨f, ?_, hf⟩
  intro hz
  have hzγ : γ = 0 := by rw [← hf, hz, map_zero]
  obtain ⟨hd, ha1⟩ := (gamma_zero_locus k r j a γ (by omega) ha hγ).mp hzγ
  have hj0 := Nat.eq_zero_of_dvd_of_lt hd hj
  exact hne.elim (fun h => h hj0) (fun h => h ha1)

lemma exponent_formula (N : ℕ) : exponent N = 24*N + 144*N^2 := by
  have : (1+12*N)^2 = (24*N+144*N^2)+1 := by ring
  unfold exponent
  omega

lemma dExponent_exact (N : ℕ) (he : Even N) : 48*dExponent N = exponent N := by
  apply Nat.mul_div_cancel'
  obtain ⟨n, rfl⟩ := he
  rw [exponent_formula]
  exact ⟨n+12*n^2, by ring⟩

/-- Eight times the period times the normalized monomial exponent is a square
multiplied by K. No primitive-order condition enters this calculation. -/
lemma normalized_exponent_square (r N j : ℕ) (hr : 0 < r) (he : Even N)
    (hd : r ∣ N*j) :
    8*(r : ℤ)*((r : ℤ)*(K (1+12*N)/12) + (j : ℤ)*p (1+12*N) +
      (j : ℤ)*(shift r (1+12*N) j : ℤ) +
      (r : ℤ)*((shift r (1+12*N) j : ℤ)*((shift r (1+12*N) j : ℤ)-1)/2) +
      2*(r : ℤ)*(dExponent N : ℤ)) =
      (exponent N : ℤ)*(2*(j : ℤ)-(r : ℤ))^2 := by
  obtain ⟨q, hq⟩ := hd
  have hqz : (N : ℤ)*j = r*q := by exact_mod_cast hq
  have hs : shift r (1+12*N) j = 12*q := by
    unfold shift
    rw [Nat.add_sub_cancel_left, mul_assoc, hq,
      show 12*(r*q) = r*(12*q) by ring, Nat.mul_div_right _ hr]
  have hk : K (1+12*N)/12 = 2*(N : ℤ)+12*(N : ℤ)^2 := by
    unfold K
    push_cast
    rw [show (1+12*(N : ℤ))^2-1 = (2*(N : ℤ)+12*(N : ℤ)^2)*12 by ring,
      Int.mul_ediv_cancel]
    all_goals norm_num
  have hp : p (1+12*N) = -6*(N : ℤ)*(1+12*(N : ℤ)) := by
    unfold p triangle
    push_cast
    rw [show (1+12*(N : ℤ))*(1+12*(N : ℤ)-1) =
      (6*(N : ℤ)*(1+12*(N : ℤ)))*2 by ring, Int.mul_ediv_cancel]
    all_goals norm_num
  have hl : (12*(q : ℤ)*(12*(q : ℤ)-1))/2 = 6*(q : ℤ)*(12*(q : ℤ)-1) := by
    rw [show 12*(q : ℤ)*(12*(q : ℤ)-1) =
      (6*(q : ℤ)*(12*(q : ℤ)-1))*2 by ring, Int.mul_ediv_cancel]
    all_goals norm_num
  have hez : 48*(dExponent N : ℤ) = 24*(N : ℤ)+144*(N : ℤ)^2 := by
    exact_mod_cast (dExponent_exact N he).trans (exponent_formula N)
  rw [hs, hk, hp, exponent_formula]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  rw [hl]
  apply (mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num))
  linear_combination (r : ℤ)^2 * hez -
    144*(12*(N : ℤ)*j+2*j+12*(q : ℤ)*r-r)*hqz

lemma normalized_exponent_nonnegative (r N j : ℕ) (hr : 0 < r) (he : Even N)
    (hd : r ∣ N*j) :
    0 ≤ (r : ℤ)*(K (1+12*N)/12) + (j : ℤ)*p (1+12*N) +
      (j : ℤ)*(shift r (1+12*N) j : ℤ) +
      (r : ℤ)*((shift r (1+12*N) j : ℤ)*((shift r (1+12*N) j : ℤ)-1)/2) +
      2*(r : ℤ)*(dExponent N : ℤ) := by
  have h := normalized_exponent_square r N j hr he hd
  have hs := sq_nonneg (2*(j : ℤ)-(r : ℤ))
  have hk : 0 ≤ (exponent N : ℤ) := by positivity
  have hmul := mul_nonneg hk hs
  have hrz : 0 < (r : ℤ) := by exact_mod_cast hr
  nlinarith

/-- The discriminant has exactly its displayed monomial times an integral
Euler product with constant coefficient one. -/
lemma discriminant_factor (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) :
    ∃ E : PowerSeries k, E ≠ 0 ∧
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k r =
        t k ^ (2*r) * (HahnSeries.ofPowerSeries ℤ k E)^48 := by
  let E := PowerSeries.expand r (Nat.ne_of_gt hr)
    (PowerSeries.map (algebraMap ℚ k) ArithmeticThetaDiscriminant.P)
  refine ⟨E, ?_, ?_⟩
  · intro h
    have hc := congrArg PowerSeries.constantCoeff h
    dsimp [E] at hc
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      ArithmeticThetaDiscriminant.P_constant, map_one] at hc
    exact one_ne_zero hc
  · unfold ArithmeticThetaUnaryKatoPowerR0160.discriminant
    rw [← PowerSeries.expand_apply _ (Nat.ne_of_gt hr)]
    simp only [map_mul, map_pow, PowerSeries.map_X, PowerSeries.expand_X]
    have htX : HahnSeries.ofPowerSeries ℤ k (PowerSeries.X : PowerSeries k) = t k := by
      simpa [t] using (HahnSeries.ofPowerSeries_X_pow (Γ := ℤ) (R := k) 1)
    rw [← pow_mul, htX, Nat.mul_comm r 2]

/-- The complete normalized Siegel product is a nonzero power series for
all nonidentity torsion labels, including exponent zero and scalar one. -/
lemma siegel_normalized_integral (k : Type) [Field k] [CharZero k]
    (r N j : ℕ) (hj : j < r) (he : Even N) (hd : r ∣ N*j)
    (a : k) (ha : a ≠ 0) (hne : j ≠ 0 ∨ a ≠ 1)
    (γ : LaurentSeries k) (hγ : IsGamma k r j a γ) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        siegelPower k r (1+12*N) j a γ *
          ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ dExponent N := by
  have hr : 0 < r := by omega
  obtain ⟨F, hF, hFγ⟩ := gamma_integral_nonzero k r j hj a ha hne γ hγ
  obtain ⟨E, hE, hED⟩ := discriminant_factor k r hr
  let b : k := (-a) ^ (p (1+12*N) + (shift r (1+12*N) j : ℤ))
  let e : ℤ := (r : ℤ)*(K (1+12*N)/12) + (j : ℤ)*p (1+12*N) +
      (j : ℤ)*(shift r (1+12*N) j : ℤ) +
      (r : ℤ)*((shift r (1+12*N) j : ℤ)*((shift r (1+12*N) j : ℤ)-1)/2)
  have he0 : 0 ≤ e + 2*(r : ℤ)*(dExponent N : ℤ) :=
    normalized_exponent_nonnegative r N j hr he hd
  let n := (e + 2*(r : ℤ)*(dExponent N : ℤ)).toNat
  have hn : (n : ℤ) = e + 2*(r : ℤ)*(dExponent N : ℤ) := Int.toNat_of_nonneg he0
  refine ⟨PowerSeries.C b * PowerSeries.X^n * F^((1+12*N)^2-1) *
    E^(48*dExponent N), ?_, ?_⟩
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact (map_ne_zero_iff _ PowerSeries.C_injective).mpr
            (zpow_ne_zero _ (neg_ne_zero.mpr ha))
        · exact pow_ne_zero _ PowerSeries.X_ne_zero
      · exact pow_ne_zero _ hF
    · exact pow_ne_zero _ hE
  · change HahnSeries.ofPowerSeries ℤ k _ = _
    have ht : t k ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
    have htX : HahnSeries.ofPowerSeries ℤ k (PowerSeries.X : PowerSeries k) = t k := by
      simpa [t] using (HahnSeries.ofPowerSeries_X_pow (Γ := ℤ) (R := k) 1)
    have hb : HahnSeries.C b =
        (-HahnSeries.C a : LaurentSeries k) ^
          (p (1+12*N) + (shift r (1+12*N) j : ℤ)) := by
      dsimp [b]
      rw [map_zpow₀, map_neg]
    simp only [map_mul, map_pow, HahnSeries.ofPowerSeries_C, htX, hFγ]
    rw [hb, hED, siegelPower]
    change _ = _ * t k ^ e * γ^((1+12*N)^2-1) *
      (t k ^ (2*r) * (HahnSeries.ofPowerSeries ℤ k E)^48)^dExponent N
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have htprod : t k ^ n = t k ^ e * t k ^ (2*r*dExponent N) := by
      rw [← zpow_natCast, hn, zpow_add₀ ht, ← zpow_natCast]
      congr 2
    rw [htprod]
    ring

/-- Integrality after a positive ramification descends to the original disk.
The Laurent map is the specified extension of t ↦ t^d. -/
lemma ramified_integrality_descent (k : Type) [Field k] [CharZero k]
    (d : ℕ) (hd : 0 < d) (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell)
    (v : LaurentSeries k)
    (hv : ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = ell v) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = v := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hFv
    exact hF ((IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
      (hFv.trans (map_zero _).symm))
  have hneg (e : ℤ) (he : e < 0) : v.coeff e = 0 := by
    rw [ArithmeticThetaUnsplitExpansionR0158.GammaBaseChangeNaturalityR0158.ramificationHom_eq
      k d hd ell hell] at hFv
    have h := congrArg (fun x : LaurentSeries k => x.coeff ((d : ℤ)*e)) hFv
    rw [ArithmeticThetaUnsplitExpansionR0158.GammaBaseChangeNaturalityR0158.ramificationHom_coeff] at h
    have hde : (d : ℤ)*e < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hd) he
    change (F : LaurentSeries k).coeff ((d : ℤ)*e) = _ at h
    simpa [PowerSeries.coeff_coe, hde] using h.symm
  let f : PowerSeries k := PowerSeries.mk (fun n => v.coeff n)
  have hf : algebraMap (PowerSeries k) (LaurentSeries k) f = v := by
    apply HahnSeries.ext
    funext e
    by_cases he : e < 0
    · rw [hneg e he]
      change (f : LaurentSeries k).coeff e = 0
      simp [PowerSeries.coeff_coe, he]
    · have heq : e = (e.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
      change (HahnSeries.ofPowerSeries ℤ k f).coeff e = _
      rw [heq, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
  exact ⟨f, fun hz => hv0 (by rw [← hf, hz, map_zero]), hf⟩

open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146

/-- Reuse the unique normalized Kato function and its complete marked value;
only the integrality consumer is new. -/
lemma marked_value_integral (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (N : ℕ) (hN : 0 < N) (heN : Even N)
    (j : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M j a p)
    (hkill : G.nsmul (𝟙 _) N (pointOver k M (𝟙 _) p hp.1) = G.one (𝟙 _))
    (hne : pointOver k M (𝟙 _) p hp.1 ≠ G.one (𝟙 _))
    (g : (genericScheme k M).functionField)
    (hg : ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G (1+12*N) g)
    (v : LaurentSeries k)
    (hv : HasValue (LaurentSeries k) (genericScheme k M) (genericPoint k M p hp.1) g v) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        v * ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ dExponent N := by
  obtain ⟨hd, haN⟩ := (marked_exact_torsion k r hr h3 T he M hM s hs G hG j a p hp N).mp hkill
  have hlabel : j.val ≠ 0 ∨ (a : k) ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    have hj : j = zeroIndex r hr := Fin.ext h.1
    have ha : a = 1 := Units.ext h.2
    subst j
    subst a
    rw [← MarkedPointAddition.point_eq k h3 M hM _ _ p hp]
    exact MarkedExactTorsion.point_one k M hM h3 s hs G hG
  obtain ⟨γ, hγ, _⟩ := gamma_exists_unique k r j.val (a : k) hr (Units.ne_zero a)
  obtain ⟨g₀, hg₀, _⟩ := actual_torsion_power_value k r hr h3 he T M hM s hs G hG N hN
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    rw [show 12*N = (2*N)*6 by omega]
    exact (Nat.coprime_add_mul_right_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  obtain ⟨g₁, _, hu⟩ := ArithmeticThetaKatoExistenceR0151.actual_kato_function_existence
    k r hr h3 T he M hM s hs G hG (1+12*N) (by omega) hc6
  have hgg : g = g₀ := (hu _ hg).trans (hu _ hg₀.1).symm
  subst g
  have heq := rational_value_transport.1 (LaurentSeries k) (genericScheme k M)
    (genericPoint k M p hp.1) g₀ v (siegelPower k r (1+12*N) j.val (a : k) γ)
    hv (hg₀.2 j a p hp hd (by simpa using congrArg Units.val haN) hlabel γ hγ)
  rw [heq]
  exact siegel_normalized_integral k r N j.val j.isLt heN hd (a : k)
    (Units.ne_zero a) hlabel γ hγ

lemma torsion_of_dvd {R : Type} [CommRing R] {X V : Scheme}
    {q : X ⟶ Spec (.of R)} (G : WeierstrassProjModel.RelativeGroupLaw R q)
    (t : V ⟶ Spec (.of R)) (N r : ℕ) (hd : N ∣ r)
    (x : SchemeHomOver t q) (hx : G.nsmul t N x = G.one t) :
    G.nsmul t r x = G.one t := by
  letI := G.pointGroup t
  have hpow (n : ℕ) : G.nsmul t n x = x^n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih]; rfl
  obtain ⟨d, rfl⟩ := hd
  rw [hpow] at hx ⊢
  change x^N = 1 at hx
  change x^(N*d) = 1
  rw [pow_mul, hx, one_pow]

/-- When N divides the split period, every rational N-torsion point is one
of the actual marks; N need not be its exact order. -/
lemma split_point_integral (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (N : ℕ) (hN : 0 < N) (heN : Even N) (hd : N ∣ r)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) r)
    (x : SchemeHomOver (𝟙 _) (genericStructure k M))
    (hx : G.nsmul (𝟙 _) N x = G.one (𝟙 _)) (hne : x ≠ G.one (𝟙 _))
    (g : (genericScheme k M).functionField)
    (hg : ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G (1+12*N) g)
    (v : LaurentSeries k) (hv : HasValue (LaurentSeries k) (genericScheme k M) x.val g v) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        v * ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ dExponent N := by
  let p := MarkedPointAddition.sectionAt k h3 M hM
  have hp := MarkedPointAddition.sectionAt_spec k h3 M hM
  have hx' := torsion_of_dvd G (𝟙 _) N r hd x hx
  have hbase : extensionBase k (LaurentSeries k) = 𝟙 _ := by
    simp [extensionBase]
  have hc := split_marked_torsion_completeness k r hr h3 T he M hM s hs
    G hG ζ hζ p hp (LaurentSeries k)
  rw [hbase] at hc
  obtain ⟨ij, hij, _⟩ := (hc x).mp hx'
  have hxi : x = pointOver k M (𝟙 _) (p ij.1 (ζ^ij.2.val)) (hp _ _).1 := hij
  rw [hxi] at hx hne hv
  exact marked_value_integral k r hr h3 he T M hM s hs G hG N hN heN
    ij.1 (ζ^ij.2.val) (p _ _) (hp _ _) hx hne g hg v hv

lemma discriminant_ramification (k : Type) [Field k] [CharZero k]
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell) :
    ell (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) =
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k (r*d) := by
  unfold ArithmeticThetaUnaryKatoPowerR0160.discriminant
  rw [← PowerSeries.expand_apply r (Nat.ne_of_gt hr),
    ← PowerSeries.expand_apply (r*d) (by positivity)]
  change ell (algebraMap (PowerSeries k) (LaurentSeries k) _) = _
  rw [hell]
  change HahnSeries.ofPowerSeries ℤ k (PowerSeries.expand d _ (PowerSeries.expand r _ _)) = _
  rw [← PowerSeries.expand_mul]
  simp only [Nat.mul_comm d r]

open ArithmeticThetaGeometricNormR0150 ArithmeticThetaKatoExistenceR0151
open ArithmeticThetaKatoAnnularR0152 ArithmeticThetaRamifiedPeriodR0154
open ArithmeticThetaRamifiedPeriodR0155
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential
open ArithmeticThetaCubicModelR0144

/-- Arbitrary nonzero N-torsion values on an algebraized Tate model. The
ramified model has period r*N; the final power series is on the original disk. -/
lemma model_point_integral (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (N : ℕ) (hN : 0 < N) (heN : Even N)
    (x : SchemeHomOver (𝟙 _) (genericStructure k M))
    (hx : G.nsmul (𝟙 _) N x = G.one (𝟙 _)) (hne : x ≠ G.one (𝟙 _))
    (g : (genericScheme k M).functionField) (hg : IsKatoFunction k M s hs.1 G (1+12*N) g)
    (v : LaurentSeries k) (hv : HasValue (LaurentSeries k) (genericScheme k M) x.val g v) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        v * ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ dExponent N := by
  classical
  have hrb : 0 < r*N := Nat.mul_pos hr hN
  have h3b : 3 ≤ r*N := h3.trans (Nat.le_mul_of_pos_right r hN)
  have heb : Even (r*N) := he.mul_right N
  obtain ⟨Tb, Mb, hMb⟩ := ArithmeticThetaTateCuspsR0181.TateFullLevelMarking.model_exists k (r*N) h3b hrb
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3b Mb hMb
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k Mb hMb
  letI : IsLocallyNoetherian (genericScheme k Mb) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k Mb)
  obtain ⟨sb, hsb, _⟩ := marked_section_algebraization k (r*N) hrb h3b Tb Mb hMb (zeroIndex (r*N) hrb) 1
  obtain ⟨Gb, hGb, _⟩ := actual_generic_group_law k (r*N) hrb h3b Tb heb Mb hMb sb hsb
  have Hχ : ∀ j : Fin r, ∃ χj, IsChartMap k M j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k r hr h3 T M hM j
    exact ⟨χj, hj⟩
  choose χ hχ using Hχ
  have Hχb : ∀ j : Fin (r*N), ∃ χj, IsChartMap k Mb j χj := by
    intro j
    obtain ⟨χj, hj, _⟩ := completed_model_chart_maps k (r*N) hrb h3b Tb Mb hMb j
    exact ⟨χj, hj⟩
  choose χb hχb using Hχb
  have Hρ : ∀ q : Fin N, ∃ ρq, IsChartRamification k N hN q ρq := by
    intro q
    obtain ⟨ρq, hρq, _⟩ := completed_chart_ramification k N hN q
    exact ⟨ρq, hρq.1⟩
  choose ρ hρ using Hρ
  obtain ⟨F, hF, _⟩ := ramified_model_morphism k N hN r hr h3 hrb
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb
  obtain ⟨ell, hell, _⟩ := ramified_laurent_extension k N hN
  obtain ⟨b, hb, _⟩ := ramified_generic_base_change k N hN r hr h3 hrb
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1
  have hbase := ramified_kato_base_change k N hN r hr h3 hrb
    T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF.1 ell hell.1 b hb.1
    he heb s hs sb hsb G hG Gb hGb
  let i := Spec.map (CommRingCat.ofHom ell)
  have H := hbase.1
  let xb : SchemeHomOver (𝟙 _) (genericStructure k Mb) :=
    ⟨H.lift (i ≫ x.val) (𝟙 _) (by rw [Category.assoc, x.property, Category.comp_id, Category.id_comp]),
      H.lift_snd _ _ _⟩
  have hxb : xb.val ≫ b = i ≫ x.val := H.lift_fst _ _ _
  have hmult : Gb.schemeNsmul N ≫ b = b ≫ G.schemeNsmul N := hbase.2.2 N
  have hxbkill : Gb.nsmul (𝟙 _) N xb = Gb.one (𝟙 _) := by
    apply Subtype.ext
    apply H.hom_ext
    · rw [← comp_schemeNsmul Gb (𝟙 _) xb N, Category.assoc, hmult,
        ← Category.assoc, hxb, Category.assoc, comp_schemeNsmul G (𝟙 _) x N, hx]
      rw [hG.1, hGb.1]
      simpa only [pointOver, Category.id_comp] using hbase.2.1.symm
    · exact (Gb.nsmul (𝟙 _) N xb).property.trans (Gb.one (𝟙 _)).property.symm
  have hxbne : xb ≠ Gb.one (𝟙 _) := by
    intro hz
    have hz' := congrArg (fun y : SchemeHomOver (𝟙 _) (genericStructure k Mb) => y.val ≫ b) hz
    rw [hxb, hGb.1] at hz'
    have hiEpi : Epi i := Flat.epi_of_flat_of_surjective i
    letI := hiEpi
    apply hne
    apply Subtype.ext
    apply (cancel_epi i).mp
    rw [hG.1]
    simpa only [pointOver, Category.id_comp, hbase.2.1] using hz'
  haveI : Surjective b := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  obtain ⟨α, hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap b
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    rw [show 12*N = (2*N)*6 by omega]
    exact (Nat.coprime_add_mul_right_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  have hgb := (actual_kato_field_base_change k r hr h3 T he M hM s hs G hG
    k (r*N) hrb h3b Tb heb Mb hMb sb hsb Gb hGb ell b hbase α hα
    (1+12*N) (by omega) hc6).2 g hg
  have hvb := rational_value_transport.2 (LaurentSeries k) (LaurentSeries k) ell
    (genericScheme k M) (genericScheme k Mb) b α hα x.val xb.val hxb g v hv
  letI : NeZero (r*N : ℕ) := ⟨hrb.ne'⟩
  letI : NeZero ((r*N : ℕ) : k) := ⟨Nat.cast_ne_zero.mpr hrb.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k (r*N)
  let z : kˣ := (hζ.isUnit hrb.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hrb.ne').unit_spec
  have hout := split_point_integral k (r*N) hrb h3b heb Tb Mb hMb sb hsb Gb hGb N hN heN
    (dvd_mul_left N r) z (by simpa only [hz] using hζ) xb hxbkill hxbne (α g) hgb (ell v) hvb
  apply ramified_integrality_descent k N hN ell hell.1
  simpa only [map_mul, map_pow, discriminant_ramification k r N hr hN ell hell.1] using hout

end ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality

#print axioms ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.gamma_integral_nonzero

#print axioms ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.siegel_normalized_integral

#print axioms ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.ramified_integrality_descent

#print axioms ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.split_point_integral

#print axioms ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.model_point_integral

namespace ArithmeticThetaCompactUnaryR0183
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaGeometricNormR0150 ArithmeticThetaCubicModelR0144
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

/-- Normalized Kato values at every nonzero N-torsion point of the actual Tate
cubic, with integrality on the original, unramified disk. -/
theorem tate_torsion_normalized_integrality :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (r N : ℕ) (hr : 3 ≤ r) (heven : Even r) (hN : 0 < N) (hNeven : Even N) [(ArithmeticThetaTateCuspsR0181.TateCurve k r).IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r))] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r))] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r))] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r))] (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r)), ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r) G → ∀ (p : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Puncture k) (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r))), CategoryTheory.CategoryStruct.comp p (ArithmeticThetaRelativeKatoR0169.structureMap (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r)) = CategoryTheory.CategoryStruct.id (ArithmeticThetaTateCuspsR0181.Puncture k) → CategoryTheory.CategoryStruct.comp p (G.schemeNsmul N) = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r) → p ≠ ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r) → ∀ (g : AlgebraicGeometry.Scheme.functionField (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r))) (v : LaurentSeries k), ArithmeticThetaRelativeKatoNaturalityR0170.Normalized (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r) G (1+12*N) g → ArithmeticThetaRelativeKatoNaturalityR0170.HasValue (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k r) p g v → ∃ f : PowerSeries k, f ≠ 0 ∧ algebraMap (PowerSeries k) (LaurentSeries k) f = v * ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ (ArithmeticThetaCompactUnaryR0183.dExponent N) := by
  intro k _ _ _ r N h3 he hN heN _ _ _ _ _ G hG p hp hkill hne g v hg hv
  have hr : 0 < r := by omega
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k r h3 hr
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) 1
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI := AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k M hM
  letI : IsLocallyNoetherian (genericScheme k M) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3 M hM s hs
  obtain ⟨Gm, hGm, _⟩ := actual_generic_group_law k r hr h3 T he M hM s hs
  obtain ⟨X,Y,hX,hY,E,hE,hO,-,-⟩ := CubicComparison.model_iso_framed k r hr h3 he T M hM s hs
  have hmult := CubicComparison.model_nsmul_of_origin k h3 he M hM s hs Gm hGm
    (TateCurve k r) G hG E hE hO
  obtain ⟨α, hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap E.hom
  have hgm := OpenDiscriminantFullTateExpansionR0182.normalized_kato_to_model
    k M s hs.1 (TateCurve k r) G hG Gm E hE hO hmult α hα
    (1+12*N) (by omega) g hg
  have hEinv : E.inv ≫ genericStructure k M = structureMap (LaurentSeries k) (TateCurve k r) := by
    rw [← hE, Iso.inv_hom_id_assoc]
  let x : SchemeHomOver (𝟙 _) (genericStructure k M) :=
    ⟨p ≫ E.inv, by rw [Category.assoc, hEinv, hp]⟩
  have hxe : x.val ≫ E.hom = p := by simp [x]
  have hx : Gm.nsmul (𝟙 _) N x = Gm.one (𝟙 _) := by
    apply Subtype.ext
    apply (cancel_mono E.hom).mp
    rw [← comp_schemeNsmul Gm (𝟙 _) x N, Category.assoc, hmult N,
      ← Category.assoc, hxe, hkill, hGm.1]
    simpa only [pointOver, Category.id_comp] using hO.symm
  have hxne : x ≠ Gm.one (𝟙 _) := by
    intro hz
    apply hne
    have ht := congrArg (fun y : SchemeHomOver (𝟙 _) (genericStructure k M) => y.val ≫ E.hom) hz
    rw [hxe, hGm.1] at ht
    simpa only [pointOver, Category.id_comp, hO] using ht
  have hvst := TargetTest.relative_value_stalk (TateCurve k r) p g v hv
  have hvm := ArithmeticThetaMarkedKatoValuesR0159.rational_value_transport.2
    (LaurentSeries k) (LaurentSeries k) (RingHom.id _) (Curve (LaurentSeries k) (TateCurve k r))
    (genericScheme k M) E.hom α hα p x.val
    (by simpa only [show CommRingCat.ofHom (RingHom.id (LaurentSeries k)) = 𝟙 _ from rfl,
      Spec.map_id, Category.id_comp] using hxe) g v hvst
  exact TateTorsionNormalizedIntegrality.model_point_integral k r hr h3 he T M hM s hs
    Gm hGm N hN heN x hx hxne (α g) hgm v hvm

#print axioms tate_torsion_normalized_integrality
end ArithmeticThetaCompactUnaryR0183
