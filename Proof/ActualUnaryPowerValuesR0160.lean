module

public import UnaryKatoProductR0160

@[expose] public section

/-! Actual unary values on the algebraized marked Tate curve. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaUnaryKatoPowerR0160
namespace ActualUnaryPowerValues
open ArithmeticThetaUnaryProduct

private lemma torsion_index (d m N : ℕ) (ν : ℤ) (hm : 0 < m)
    (hem : Even m) (hmN : m ∣ N)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    24*d*m^2 ∣ N*(d*unaryA m ν) := by
  obtain ⟨n, rfl⟩ := hmN
  obtain ⟨b, hb⟩ := hem
  let L : ℤ := (n : ℤ)*((b : ℤ)+ν)
  have hbZ : (m : ℤ) = (b : ℤ)+(b : ℤ) := by exact_mod_cast hb
  have hL : 0 ≤ L := mul_nonneg (by positivity) (by omega)
  refine ⟨L.toNat, ?_⟩
  apply Int.ofNat_inj.mp
  push_cast
  rw [Int.toNat_of_nonneg hL, (unary_parameters m ν hm hν).1]
  dsimp [L]
  rw [hbZ]
  ring

end ActualUnaryPowerValues
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaUnaryProduct ArithmeticThetaLaurentNormR0064
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaMarkedKatoValuesR0159

/-- The unique normalized Kato function has all the exact unary stalk values. -/
theorem actual_unary_power_values :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (d m N : ℕ), 0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N → r = 24*d*m^2 → ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G (1+12*N) g ∧ ArithmeticThetaUnaryKatoPowerR0160.PowerValues k M d m N g := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ d m N hd hm hem hN heN hmN hrEq
  obtain ⟨g, hg, _⟩ := actual_torsion_power_value
    k r hr h3 he T M hM s hs G hG N hN
  have hc : 1 < 1+12*N := by omega
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    rw [show 12*N = (2*N)*6 by omega]
    exact (Nat.coprime_add_mul_right_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  obtain ⟨g₀, hg₀, hu⟩ := ArithmeticThetaKatoExistenceR0151.actual_kato_function_existence
    k r hr h3 T he M hM s hs G hG (1+12*N) hc hc6
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · intro ν hν
    have hj : d*unaryA m ν < r := by
      rw [hrEq, show 24*d*m^2 = d*(24*m^2) by ring]
      exact Nat.mul_lt_mul_of_pos_left (unary_parameters m ν hm hν).2 hd
    let j : Fin r := ⟨d*unaryA m ν, hj⟩
    obtain ⟨p, hp, _⟩ := marked_section_algebraization k r hr h3 T M hM j (-1)
    refine ⟨j, p, hp, rfl, ?_⟩
    obtain ⟨γ, hγ, _⟩ := gamma_exists_unique k r j.val (-1) hr (neg_ne_zero.mpr one_ne_zero)
    have hidx : r ∣ N*j.val := by
      change r ∣ N*(d*unaryA m ν)
      rw [hrEq]
      exact ActualUnaryPowerValues.torsion_index d m N ν hm hem hmN hν
    have haN : (((-1 : kˣ) : k))^N = 1 := by
      simpa using heN.neg_one_pow (α := k)
    have hne : j.val ≠ 0 ∨ (((-1 : kˣ) : k)) ≠ 1 := by
      right
      norm_num
    have hv := hg.2 j (-1) p hp hidx haN hne γ (by simpa using hγ)
    have hprod := unary_kato_product k d m N ν hd hm hem hN heN hmN hν γ
      (by simpa only [← hrEq] using hγ)
    have hD : discriminant k r ^ (((1+12*N)^2-1)/48) ≠ 0 :=
      pow_ne_zero _ (hrEq ▸ (discriminant_eta_substitution k d m hd hm).2)
    have heq : unary k d m ν ^ ((1+12*N)^2-1) /
        discriminant k r ^ (((1+12*N)^2-1)/48) =
          siegelPower k r (1+12*N) j.val (-1) γ := by
      apply (div_eq_iff hD).mpr
      simpa only [hrEq, mul_comm] using hprod
    rw [heq]
    exact hv
  · intro g' hg'
    exact (hu g' hg'.1).trans (hu g hg.1).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A characteristic-zero field and the numerical hypotheses suffice to
construct all of the geometric providers as well as their exact power values. -/
theorem actual_unary_geometric_realization (k : Type) [Field k] [CharZero k]
    (d m N : ℕ) (hd : 0 < d) (hm : 0 < m) (hem : Even m)
    (hN : 0 < N) (heN : Even N) (hmN : m ∣ N) :
    GeometricRealization k d m N := by
  let r := 24*d*m^2
  have hr : 0 < r := by dsimp [r]; positivity
  have h3 : 3 ≤ r := by
    have : 1 ≤ d*m^2 := Nat.succ_le_of_lt (by positivity)
    dsimp [r]
    nlinarith
  have he : Even r := ⟨12*d*m^2, by dsimp [r]; ring⟩
  obtain ⟨T, _⟩ := ArithmeticThetaInfinitesimalPolygonR0129.proper_flat_polygon_tower
    k r hr h3
  obtain ⟨b, hb, hbr, _⟩ := ArithmeticThetaPositiveLineR0134.compatible_formal_section_basis
    k r hr h3 T (fun _ => 1) 3 (by decide)
  have hbc : ArithmeticThetaProjectiveEffectivityR0135.CompatibleBases k T (fun _ => 1) b :=
    ⟨hb, hbr⟩
  obtain ⟨j, hj⟩ := ArithmeticThetaProjectiveEffectivityR0135.compatible_projective_embeddings
    k r hr h3 T (fun _ => 1) b hbc
  obtain ⟨M, hM, _⟩ := ArithmeticThetaProjectiveEffectivityR0135.projective_tower_effectivity
    k r hr h3 T (fun _ => 1) b hbc j hj
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k r hr h3 T M hM
    (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1
  obtain ⟨G, hG, _⟩ := ArithmeticThetaMarkedGroupLawR0146.actual_generic_group_law
    k r hr h3 T he M hM s hs
  letI : IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI : IsProper (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) :=
    ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI : LocallyOfFinitePresentation (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) :=
    ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.generic_finitePresentation k M hM
  letI : IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)
  exact ⟨r, hr, h3, he, T, M, hM, s, hs, G, hG, inferInstance, inferInstance,
    rfl, actual_unary_power_values k r hr h3 he T M hM s hs G hG
      d m N hd hm hem hN heN hmN rfl⟩

end ArithmeticThetaUnaryKatoPowerR0160
#print axioms ArithmeticThetaUnaryKatoPowerR0160.actual_unary_power_values

#print axioms ArithmeticThetaUnaryKatoPowerR0160.actual_unary_geometric_realization
