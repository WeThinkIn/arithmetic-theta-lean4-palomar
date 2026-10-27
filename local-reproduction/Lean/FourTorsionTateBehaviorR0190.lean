import GlobalFourTorsionDefinitionsR0190

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ArithmeticThetaGlobalFourTorsionR0190
namespace FourTorsionTateBehavior
open ArithmeticThetaTateSeries ArithmeticThetaTateIdentities
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCubicModelR0144

variable (k : Type) [Field k] [CharZero k]

lemma thetaAt_eq_expand (L : ℕ) (h : L / 2 ≠ 0) :
    thetaAt k L = PowerSeries.expand (L/2) h (theta k) := by
  ext n
  simp [thetaAt, PowerSeries.coeff_expand]

lemma thetaAt_unit (L : ℕ) : IsUnit (thetaAt k L) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h : PowerSeries.constantCoeff (thetaAt k L) = 1 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff, thetaAt, theta]
  rw [h]
  exact isUnit_one

lemma laurent_order_of_coeff (f : PowerSeries k) (n : ℕ)
    (hn : PowerSeries.coeff n f ≠ 0)
    (hz : ∀ i < n, PowerSeries.coeff i f = 0) :
    (algebraMap (PowerSeries k) (LaurentSeries k) f).order = (n : ℤ) := by
  let F : LaurentSeries k := algebraMap (PowerSeries k) (LaurentSeries k) f
  have hc : F.coeff n ≠ 0 := by simpa [F, LaurentSeries.coeff_coe_powerSeries] using hn
  have hf : F ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hc
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc)
  apply (HahnSeries.le_order_iff_forall hf).mpr
  intro i hi
  by_cases hi0 : i < 0
  · simpa [F, PowerSeries.coeff_coe, hi0]
  · have hi0' : 0 ≤ i := le_of_not_gt hi0
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi0'
    simpa [F, LaurentSeries.coeff_coe_powerSeries] using hz j (by omega)

lemma unit_factor_of_order (f : LaurentSeries k) (hf : f ≠ 0) (j : ℕ)
    (hj : f.order = j) :
    ∃ v : (PowerSeries k)ˣ,
      f = algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k)) := by
  have hu : IsUnit f.powerSeriesPart := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff, LaurentSeries.powerSeriesPart_coeff]
      using (HahnSeries.coeff_order_eq_zero.not.mpr hf)
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, ?_⟩
  rw [hv]
  exact (LaurentSeries.X_order_mul_powerSeriesPart hj.symm).symm

lemma rootSeries_difference_orders (m : ℕ) (hm : 0 < m) (i j : Fin 3) (hij : i ≠ j) :
    (algebraMap (PowerSeries k) (LaurentSeries k)
      (rootSeries k (4*m) i - rootSeries k (4*m) j)).order =
        if i = 0 ∨ j = 0 then 0 else (2*m : ℕ) := by
  have hc := marked_cusp_terms (k := k) m hm
  have hz := marked_cusp_vanishing (k := k) m hm
  have h20 : PowerSeries.coeff 0 (tateX (4*m) (2*m) (1:k)) = 0 := by
    simpa using hz.1 0 (by omega)
  have h30 : PowerSeries.coeff 0 (tateX (4*m) (2*m) (-1:k)) = 0 := by
    simpa using hz.2.1 0 (by omega)
  have h01 : (algebraMap (PowerSeries k) (LaurentSeries k)
      (tateX (4*m) 0 (-1:k) - tateX (4*m) (2*m) (1:k))).order = 0 := by
    apply laurent_order_of_coeff k _ 0
    · rw [map_sub, hc.1, h20]; norm_num
    · intro i hi; omega
  have h02 : (algebraMap (PowerSeries k) (LaurentSeries k)
      (tateX (4*m) 0 (-1:k) - tateX (4*m) (2*m) (-1:k))).order = 0 := by
    apply laurent_order_of_coeff k _ 0
    · rw [map_sub, hc.1, h30]; norm_num
    · intro i hi; omega
  have h12 : (algebraMap (PowerSeries k) (LaurentSeries k)
      (tateX (4*m) (2*m) (1:k) - tateX (4*m) (2*m) (-1:k))).order = (2*m : ℕ) := by
    apply laurent_order_of_coeff k _ (2*m)
    · rw [hc.2.2.2.2.2]; norm_num
    · intro i hi; simp [hz.1 i hi, hz.2.1 i hi]
  have h10 := congrArg (fun z : LaurentSeries k => z.order)
    (map_neg (algebraMap (PowerSeries k) (LaurentSeries k))
      (tateX (4*m) 0 (-1:k) - tateX (4*m) (2*m) (1:k)))
  have h20' := congrArg (fun z : LaurentSeries k => z.order)
    (map_neg (algebraMap (PowerSeries k) (LaurentSeries k))
      (tateX (4*m) 0 (-1:k) - tateX (4*m) (2*m) (-1:k)))
  have h21 := congrArg (fun z : LaurentSeries k => z.order)
    (map_neg (algebraMap (PowerSeries k) (LaurentSeries k))
      (tateX (4*m) (2*m) (1:k) - tateX (4*m) (2*m) (-1:k)))
  simp only [neg_sub, HahnSeries.order_neg, h01, h02, h12] at h10 h20' h21
  fin_cases i <;> fin_cases j <;>
    simp_all [rootSeries, show 4*m/2 = 2*m by omega]

open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaFullLevelCoverR0175
open CategoryTheory AlgebraicGeometry

lemma label_is_literal_root (L : ℕ) (E : TateLevel k L)
    (e : Fin 3 → LaurentSeries k) (he : Labels (LaurentSeries k) (TateCurve k L)
      E.law L E.marking e) (i : Fin 3) :
    ∃ j : Fin 3, e i = root k L j := by
  have h := TwoTorsionSplitCubicR0177.root_equation (he i)
  simp only [TateCurve, curve, zero_mul, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hz : (e i - root k L 0) * (e i - root k L 1) * (e i - root k L 2) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hz with hab | hc
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact ⟨0, sub_eq_zero.mp ha⟩
    · exact ⟨1, sub_eq_zero.mp hb⟩
  · exact ⟨2, sub_eq_zero.mp hc⟩

lemma rootData_coefficient_integral (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
    (E : TateLevel k L) (e : Fin 3 → LaurentSeries k) (x y g : LaurentSeries k)
    (h : RootData (LaurentSeries k) (TateCurve k L) E.law L E.marking e x y g) :
    ∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧
      2*g = algebraMap (PowerSeries k) (LaurentSeries k)
        (PowerSeries.X^j * (v : PowerSeries k)) := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 0 < m := by omega
  obtain ⟨i, hi⟩ := label_is_literal_root k (4*m) E e h.1 1
  obtain ⟨j, hj⟩ := label_is_literal_root k (4*m) E e h.1 0
  have hij : i ≠ j := by
    intro hij
    have hu := h.2.1.1 1 0 (by decide)
    rw [hi, hj, hij, sub_self] at hu
    exact not_isUnit_zero hu
  have hg : g ≠ 0 := h.2.2.2.2.1.ne_zero
  have hs : g^2 = root k (4*m) i - root k (4*m) j := by
    simpa [hi, hj] using h.2.2.2.2.2.2
  have ho := congrArg (fun z : LaurentSeries k => z.order) hs
  rw [HahnSeries.order_pow] at ho
  have hr := rootSeries_difference_orders k m hm i j hij
  rw [map_sub] at hr
  change (root k (4*m) i - root k (4*m) j).order = _ at hr
  rw [hr] at ho
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have h2 : (2 : LaurentSeries k) ≠ 0 := by norm_num
  have htwo : (2 : LaurentSeries k).order = 0 := by
    have hh : (HahnSeries.C (2:k) : LaurentSeries k).order = 0 := HahnSeries.order_C
    simpa only [map_ofNat] using hh
  have hmul : (2*g).order = g.order := by
    rw [HahnSeries.order_mul h2 hg, htwo, zero_add]
  by_cases hz : i = 0 ∨ j = 0
  · rw [if_pos hz] at ho
    have ho0 : (2*g).order = (0 : ℕ) := by rw [hmul]; simpa using ho
    obtain ⟨v, hv⟩ := unit_factor_of_order k (2*g) (mul_ne_zero h2 hg) 0 ho0
    exact ⟨v, 0, Or.inl rfl, hv⟩
  · rw [if_neg hz] at ho
    have hom : (2*g).order = (m : ℤ) := by
      rw [hmul]
      simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at ho
      omega
    obtain ⟨v, hv⟩ := unit_factor_of_order k (2*g) (mul_ne_zero h2 hg) m hom
    exact ⟨v, m, Or.inr (by omega), hv⟩

lemma literal_cleared_identity :
    yR k * (PowerSeries.expand 2 (by decide) (theta k))^2 =
      (xR k - e₁ k)^2 - (e₁ k - e₂ k)*(e₁ k - e₃ k) := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have h := (marked_root_expansion (k := k)).2
  have hy : toLaurent k (yR k) ≠ 0 := by
    exact (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr
      (marked_root_expansion (k := k)).1
  unfold ArithmeticThetaFourTorsion.rootExpression at h
  have hh := congrArg (fun z : LaurentSeries k => z * toLaurent k (yR k)) h
  field_simp [hy] at hh
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
  change toLaurent k _ = toLaurent k _
  simp only [map_mul, map_pow, map_sub]
  rw [map_pow] at hh
  exact hh.symm

lemma ramified_cleared_identity (m : ℕ) (hm : 0 < m) :
    tateY (4*m) m (1:k) * thetaAt k (4*m)^2 =
      (tateX (4*m) m (1:k) - tateX (4*m) 0 (-1:k))^2 -
        (tateX (4*m) 0 (-1:k) - tateX (4*m) (2*m) (1:k)) *
        (tateX (4*m) 0 (-1:k) - tateX (4*m) (2*m) (-1:k)) := by
  have h := congrArg (PowerSeries.expand m (Nat.ne_of_gt hm)) (literal_cleared_identity k)
  simp only [map_mul, map_pow, map_sub] at h
  have h0 := (ramified_substitution m 4 0 (-1:k) hm (by norm_num [Admissible])).1
  have h1 := ramified_substitution m 4 1 (1:k) hm (by norm_num [Admissible])
  have h2 := (ramified_substitution m 4 2 (1:k) hm (by norm_num [Admissible])).1
  have h3 := (ramified_substitution m 4 2 (-1:k) hm (by norm_num [Admissible])).1
  have ht : PowerSeries.expand m (Nat.ne_of_gt hm)
      (PowerSeries.expand 2 (by decide) (theta k)) = thetaAt k (4*m) := by
    rw [← PowerSeries.expand_mul]
    rw [thetaAt_eq_expand k (4*m) (by omega)]
    congr 2 <;> omega
  simpa only [xR, yR, e₁, e₂, e₃, ← h0, ← h1.1, ← h1.2, ← h2, ← h3,
    ht, Nat.mul_zero, Nat.mul_one, Nat.mul_comm m, Nat.zero_mul, Nat.one_mul] using h

lemma literal_coefficient_signed (m : ℕ) (hm : 0 < m) (g : LaurentSeries k)
    (hg : 2 * algebraMap (PowerSeries k) (LaurentSeries k)
      (tateY (4*m) m (1:k)) * g =
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) m (1:k)) -
        algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) 0 (-1:k)))^2 -
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) 0 (-1:k)) -
        algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) (2*m) (1:k))) *
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) 0 (-1:k)) -
        algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) (2*m) (-1:k)))) :
    2*g = algebraMap (PowerSeries k) (LaurentSeries k) (thetaAt k (4*m)^2) := by
  have hy : tateY (4*m) m (1:k) ≠ 0 := by
    intro hy
    have hc := (marked_cusp_terms (k := k) m hm).2.2.2.2.1
    rw [hy, map_zero] at hc
    exact (inv_ne_zero (by norm_num : (2:k) ≠ 0)) hc.symm
  have hyL : algebraMap (PowerSeries k) (LaurentSeries k) (tateY (4*m) m (1:k)) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr hy
  apply mul_left_cancel₀ hyL
  have hh := congrArg (algebraMap (PowerSeries k) (LaurentSeries k))
    (ramified_cleared_identity k m hm)
  simp only [map_mul, map_pow, map_sub] at hh
  rw [map_pow]
  linear_combination hg - hh

lemma realization_integral_in_own_frame (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
    (E : TateLevel k L)
    (a : Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge
      (LaurentSeries k) (TateCurve k L), ⊤))
    (ha : RealizesAlpha (LaurentSeries k) (TateCurve k L) E.law L E.marking a) :
    ∃ (δ : ArithmeticThetaGlobalFourTorsionR0190.CurveFrame (LaurentSeries k) (TateCurve k L))
      (v : (PowerSeries k)ˣ) (j : ℕ),
      NormalizedFrame (LaurentSeries k) (TateCurve k L) δ ∧
      (j = 0 ∨ j = L/4) ∧
      a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
        (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
          ArithmeticThetaGlobalFourTorsionR0190.hodgeGenerator (LaurentSeries k) (TateCurve k L) δ := by
  obtain ⟨e, x, y, g, δ, hd, hn, ha⟩ := ha
  obtain ⟨v, j, hj, hg⟩ := rootData_coefficient_integral k L hL h4 E e x y g hd
  exact ⟨δ, v, j, hn, hj, by simpa only [hg] using ha⟩

lemma coordinates_unique {K : Type} [Field K] (W : WeierstrassCurve K)
    (P : ArithmeticThetaRelativeDiscriminantR0171.Base K ⟶
      ArithmeticThetaRelativeKatoR0169.Curve K W) (x y x' y' : K)
    (h : HasCoordinates K W P x y) (h' : HasCoordinates K W P x' y') :
    x = x' ∧ y = y' := by
  exact (WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    W.toProjective).2 ⟨P, h.1⟩ ⟨P, h'.1⟩ x y x' y' h.2 h'.2 |>.mp rfl

lemma canonical_rootData_coordinates (m : ℕ) (hm : 0 < m)
    (E : TateLevel k (4*m)) (ζ : k) (hζ : IsPrimitiveRoot ζ (4*m))
    (hcan : CanonicalMarking k (4*m) ζ E)
    (e : Fin 3 → LaurentSeries k) (x y g : LaurentSeries k)
    (h : RootData (LaurentSeries k) (TateCurve k (4*m)) E.law (4*m) E.marking e x y g) :
    (∀ i, e i = root k (4*m) i) ∧
    x = algebraMap (PowerSeries k) (LaurentSeries k) (tateX (4*m) m (1:k)) ∧
    y = algebraMap (PowerSeries k) (LaurentSeries k) (tateY (4*m) m (1:k)) := by
  have hz : ζ^(2*m) = -1 :=
    (IsPrimitiveRoot.pow (by omega : 0 < 4*m) hζ (by omega : 4*m = (2*m)*2)).eq_neg_one_of_two_right
  have hx0 := hcan ⟨2*m, by omega⟩ ⟨0, by omega⟩ (Or.inl (by dsimp; omega))
  have hx1 := hcan ⟨0, by omega⟩ ⟨2*m, by omega⟩ (Or.inr (by dsimp; omega))
  have hx2 := hcan ⟨2*m, by omega⟩ ⟨2*m, by omega⟩ (Or.inl (by dsimp; omega))
  have hq := hcan ⟨0, by omega⟩ ⟨m, by omega⟩ (Or.inr (by dsimp; omega))
  simp only [coordinatePoint, hz, pow_zero, E.law.nsmul_zero,
    E.law.mul_one, E.law.one_mul] at hx0 hx1 hx2 hq
  have hd0 := h.1 0
  have hd1 := h.1 1
  have hd2 := h.1 2
  simp only [twoLabel, show 4*m/2 = 2*m by omega, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hd0 hd1 hd2
  have he0 := (coordinates_unique _ _ _ _ _ _ hd0 hx0).1
  have he1 := (coordinates_unique _ _ _ _ _ _ hd1 hx1).1
  have he2 := (coordinates_unique _ _ _ _ _ _ hd2 hx2).1
  have hqd := h.2.2.1
  simp only [quarterPoint, show 4*m/4 = m by omega] at hqd
  have heq := coordinates_unique _ _ _ _ _ _ hqd hq
  refine ⟨?_, heq⟩
  intro i
  fin_cases i
  · simpa [root, rootSeries] using he0
  · simpa [root, rootSeries, show 4*m/2 = 2*m by omega] using he1
  · simpa [root, rootSeries, show 4*m/2 = 2*m by omega] using he2

lemma canonical_rootData_signed (L : ℕ) (hL : 0 < L) (h4 : 4 ∣ L)
    (E : TateLevel k L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (hcan : CanonicalMarking k L ζ E)
    (e : Fin 3 → LaurentSeries k) (x y g : LaurentSeries k)
    (h : RootData (LaurentSeries k) (TateCurve k L) E.law L E.marking e x y g) :
    2*g = algebraMap (PowerSeries k) (LaurentSeries k) (thetaAt k L ^ 2) := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 0 < m := by omega
  obtain ⟨he, hx, hy⟩ := canonical_rootData_coordinates k m hm E ζ hζ hcan e x y g h
  apply literal_coefficient_signed k m hm g
  have hh := h.2.2.2.2.2.1
  simpa [completedY, TateCurve, curve, he, hx, hy, root, rootSeries,
    show 4*m/2 = 2*m by omega] using hh


open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull

lemma differential_square_injective {A B C : CommRingCat} (f : A ⟶ B) (g : A ⟶ C)
    (e : B ≅ C) (h : f ≫ e.hom = g) :
    Function.Injective (CommRingCat.KaehlerDifferential.map
      (show (𝟙 A) ≫ g = f ≫ e.hom by simpa using h.symm)) := by
  let hh : (𝟙 A) ≫ g = f ≫ e.hom := by simpa using h.symm
  let hi : (𝟙 A) ≫ f = g ≫ e.inv := by rw [← h]; simp
  let α := CommRingCat.KaehlerDifferential.map hh
  let β := CommRingCat.KaehlerDifferential.map hi
  have hinv : ∀ z, β (α z) = z := by
    let q : CommRingCat.KaehlerDifferential f ⟶ CommRingCat.KaehlerDifferential f :=
      ModuleCat.ofHom {
        toFun := fun z => β (α z)
        map_add' := by intros; simp
        map_smul' := by
          intro r z
          rw [α.hom.map_smul]
          change β ((e.hom.hom r) • α z) = r • β (α z)
          rw [β.hom.map_smul]
          change e.inv.hom (e.hom.hom r) • β (α z) = r • β (α z)
          exact congrArg (fun b : B => b • β (α z))
            (ConcreteCategory.congr_hom e.hom_inv_id r) }
    have hq : q = 𝟙 _ := by
      apply CommRingCat.KaehlerDifferential.ext
      intro b
      change β (α (CommRingCat.KaehlerDifferential.d b)) = _
      simp [α, β]
    intro z
    exact ConcreteCategory.congr_hom hq z
  exact Function.LeftInverse.injective hinv

lemma k1_chart_injective {F : Type} [CommRing F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (j : X ⟶ Y) (hj : j ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)))
    (U : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (j ⁻¹ᵁ U))
    [IsIso (j.app U)] : Function.Injective (k1h f g j hj U) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := (f.kaehlerToSections_bijective_of_isAffineOpen hU).surjective a
  obtain ⟨b', rfl⟩ := (f.kaehlerToSections_bijective_of_isAffineOpen hU).surjective b
  change (k1 f g j hj).app U _ = (k1 f g j hj).app U _ at hab
  rw [k1_kaehlerToSections, k1_kaehlerToSections] at hab
  change g.kaehlerToSections _ (kdMap f g j hj U a') =
    g.kaehlerToSections _ (kdMap f g j hj U b') at hab
  have hab' := (g.kaehlerToSections_bijective_of_isAffineOpen hV).injective hab
  have hfac : f.constToPresheaf.app (Opposite.op U) ≫ j.app U =
      g.constToPresheaf.app (Opposite.op (j ⁻¹ᵁ U)) := by
    simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Category.id_comp]
      using (fac f g j hj U).symm
  have hinj := differential_square_injective (f.constToPresheaf.app (Opposite.op U))
    (g.constToPresheaf.app (Opposite.op (j ⁻¹ᵁ U))) (asIso (j.app U)) hfac
  have : a' = b' := hinj hab'
  exact congrArg (f.kaehlerToSections U) this

lemma k1_restrict_top {F : Type} [CommRing F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (j : X ⟶ Y) (hj : j ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)))
    (U : Y.Opens) (h : (⊤ : X.Opens) ≤ j ⁻¹ᵁ U) (s : Γ(f.kaehler, ⊤)) :
    res g.kaehler h (k1h f g j hj U (res f.kaehler le_top s)) =
      res g.kaehler (by simp) (k1h f g j hj ⊤ s) := by
  have hh := congrArg (res g.kaehler h)
    (map_k1h f g j hj (homOfLE (show U ≤ ⊤ from le_top)).op s)
  change res g.kaehler h (res g.kaehler _ (k1h f g j hj ⊤ s)) = _ at hh
  rw [InitialHodgeSection.res_res] at hh
  exact hh.symm

lemma k1_derivative_on {F : Type} [CommRing F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (j : X ⟶ Y) (hj : j ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)))
    (U : Y.Opens) (h : (⊤ : X.Opens) ≤ j ⁻¹ᵁ U) (x : Γ(Y,U)) :
    res g.kaehler h (k1h f g j hj U (relativeD f U x)) =
      relativeD g ⊤ (j.appLE U ⊤ h x) := by
  change res g.kaehler h ((k1 f g j hj).app U (f.kaehlerToSections U (dK f U x))) = _
  rw [k1_kaehlerToSections, k1app_dK]
  exact relativeD_res g h _

lemma chart_frame_equation {F : Type} [CommRing F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (j : X ⟶ Y) (hj : j ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)))
    (U : Y.Opens) (h : (⊤ : X.Opens) ≤ j ⁻¹ᵁ U)
    (x y : Γ(Y,U)) (s : Γ(f.kaehler, ⊤))
    (hn : relativeD f U x = y • res f.kaehler le_top s) :
    relativeD g ⊤ (j.appLE U ⊤ h x) = j.appLE U ⊤ h y •
      res g.kaehler (by simp) (k1h f g j hj ⊤ s) := by
  rw [← k1_derivative_on f g j hj U h x, hn, k1h_smul,
    InitialHodgeSection.res_smul, k1_restrict_top]
  rfl

lemma chart_k1_global_injective {F B : Type} [CommRing F] [CommRing B]
    {Y : Scheme} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of F))
    (j : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j]
    [Nonempty (Spec (CommRingCat.of B))]
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    Function.Injective (fun s : Γ(f.kaehler, ⊤) =>
      res (j ≫ f).kaehler (V := ⊤) (by simp)
        (k1h f (j ≫ f) j (by simp) ⊤ s)) := by
  let U := j ''ᵁ ⊤
  have hU : IsAffineOpen U := by
    simpa only [U, Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j
  have hpre : j ⁻¹ᵁ U = ⊤ := j.preimage_image_eq ⊤
  have hV : IsAffineOpen (j ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
  letI : IsIso (j.app U) := j.isIso_app U (by simp [U])
  letI : Nonempty U := by
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of B)))
    exact ⟨⟨j z, ⟨z, trivial, rfl⟩⟩⟩
  intro a b hab
  apply frame_restrict_injective δ ⊤ U le_top
  apply k1_chart_injective f (j ≫ f) j (by simp) U hU hV
  apply (ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.res_bijective
    (j ≫ f).kaehler hpre.ge le_top).injective
  exact (k1_restrict_top f (j ≫ f) j (by simp) U hpre.ge a).trans
    (hab.trans (k1_restrict_top f (j ≫ f) j (by simp) U hpre.ge b).symm)

lemma frame_section_eq_of_chart_smul {F B : Type} [CommRing F] [CommRing B]
    {Y : Scheme} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of F))
    (j : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j]
    [Nonempty (Spec (CommRingCat.of B))]
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (a b : Γ(f.kaehler, ⊤)) (q : Γ(Spec (CommRingCat.of B), ⊤)) (hq : q ≠ 0)
    (hab : q • res (j ≫ f).kaehler (V := ⊤) (by simp) (k1h f (j ≫ f) j (by simp) ⊤ a) =
      q • res (j ≫ f).kaehler (V := ⊤) (by simp) (k1h f (j ≫ f) j (by simp) ⊤ b)) : a = b := by
  let U := j ''ᵁ ⊤
  have hpre : j ⁻¹ᵁ U = ⊤ := j.preimage_image_eq ⊤
  letI : Nonempty U := by
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of B)))
    exact ⟨⟨j z, ⟨z, trivial, rfl⟩⟩⟩
  have hU : IsAffineOpen U := by simpa [U] using isAffineOpen_opensRange j
  have hV : IsAffineOpen (j ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
  letI : IsIso (j.app U) := j.isIso_app U (by simp [U])
  let c : Γ(Y,U) := (j.appIso ⊤).inv q
  have hc : j.appLE U ⊤ hpre.ge c = q := by
    rw [← j.appIso_hom' ⊤]
    exact ConcreteCategory.congr_hom (j.appIso ⊤).inv_hom_id q
  have hc0 : c ≠ 0 := by
    intro hz
    apply hq
    rw [← hc, hz, map_zero]
  have heq : c • res f.kaehler (V := U) le_top a = c • res f.kaehler (V := U) le_top b := by
    apply k1_chart_injective f (j ≫ f) j (by simp) U hU hV
    apply (ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.res_bijective
      (j ≫ f).kaehler hpre.ge le_top).injective
    rw [k1h_smul, k1h_smul, InitialHodgeSection.res_smul, InitialHodgeSection.res_smul]
    change j.appLE U ⊤ hpre.ge c • _ = j.appLE U ⊤ hpre.ge c • _
    rw [hc, k1_restrict_top, k1_restrict_top]
    exact hab
  apply frame_restrict_injective δ ⊤ U le_top
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app δ.inv U)).injective
  have he := congrArg (Scheme.Modules.Hom.app δ.inv U) heq
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at he
  change c * (show Γ(Y,U) from Scheme.Modules.Hom.app δ.inv U _) =
    c * (show Γ(Y,U) from Scheme.Modules.Hom.app δ.inv U _) at he
  exact @mul_left_cancel₀ Γ(Y,U) _ _ _ c _ _ hc0 he

lemma differential_global_eq_k1 {F : Type} [CommRing F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (j : X ⟶ Y) (s : Γ(f.kaehler, ⊤)) :
    (differentialMap f (j ≫ f) j (by simp)).app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection j f.kaehler s) =
    res (j ≫ f).kaehler (V := ⊤) (by simp) (k1h f (j ≫ f) j (by simp) ⊤ s) := by
  change (differentialMap f (j ≫ f) j _).app (j ⁻¹ᵁ ⊤)
    (Scheme.Modules.pullbackLocalSection j s) = _
  rw [HodgeBaseChange.differentialMap, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  change k1h f (j ≫ f) j _ ⊤ s = res (j ≫ f).kaehler _ (k1h f (j ≫ f) j _ ⊤ s)
  symm
  exact InitialHodgeSection.res_self _ _

local instance tate_chart_open (L : ℕ) :
    IsOpenImmersion (ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion k L) :=
  CompactifiedCoordinateIsomorphism.chart_open k

lemma chart_coordinate_pull (L : ℕ) (z : ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k L) :
    let j := ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion k L
    j.appLE (j ''ᵁ ⊤) ⊤ (j.preimage_image_eq ⊤).ge ((chartRingEquiv j).symm z) =
      (Scheme.ΓSpecIso (CommRingCat.of (ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k L))).inv z := by
  dsimp only
  rw [← Scheme.Hom.appIso_hom']
  change (Scheme.Hom.appIso (ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion k L) ⊤).hom
    (((Scheme.Hom.appIso (ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion k L) ⊤) ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k L))).inv z) = _
  simp

lemma chart_coordinate_pull_general {B : Type} [CommRing B] {Y : Scheme}
    (j : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j] (z : B) :
    j.appLE (j ''ᵁ ⊤) ⊤ (j.preimage_image_eq ⊤).ge ((chartRingEquiv j).symm z) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv z := by
  rw [← Scheme.Hom.appIso_hom']
  change (Scheme.Hom.appIso j ⊤).hom
    (((Scheme.Hom.appIso j ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of B)).inv z) = _
  simp

lemma boundary_chart_normalized (L : ℕ)
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ) :
    NormalizedFrame (LaurentSeries k) (TateCurve k L) δ := by
  let j := ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k) (TateCurve k L)
  letI : IsOpenImmersion j := tate_chart_open k L
  let f := structureMap (LaurentSeries k) (TateCurve k L)
  let x := WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective
  let y := WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective
  have hn : relativeD f (j ''ᵁ ⊤) ((chartRingEquiv j).symm x) =
      (2 * (chartRingEquiv j).symm y) •
        res f.kaehler le_top (differentialSection (LaurentSeries k) (TateCurve k L) δ) := by
    dsimp only [ArithmeticThetaBoundaryHodgeR0182.Normalized, zOpen, zSection,
      zLeg, Iso.refl_inv] at hδ
    change relativeD f (j ''ᵁ ⊤) ((chartRingEquiv j).symm x) =
      (2 * (chartRingEquiv j).symm y) • Scheme.Modules.Hom.app δ.hom (j ''ᵁ ⊤) (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), j ''ᵁ ⊤)) at hδ
    exact hδ.trans (congrArg
      (fun s : Γ(f.kaehler, j ''ᵁ ⊤) => (2 * (chartRingEquiv j).symm y) • s)
      (frame_section_restrict f δ ⊤ (j ''ᵁ ⊤) le_top).symm)
  have h := chart_frame_equation f (j ≫ f) j (by simp) (j ''ᵁ ⊤)
    (j.preimage_image_eq ⊤).ge ((chartRingEquiv j).symm x)
    (2 * (chartRingEquiv j).symm y)
    (differentialSection (LaurentSeries k) (TateCurve k L) δ) hn
  rw [map_mul, map_ofNat, chart_coordinate_pull_general, chart_coordinate_pull_general] at h
  dsimp only [NormalizedFrame]
  erw [differential_global_eq_k1]
  have hz : (2 * y + chartScalar (LaurentSeries k) (TateCurve k L)
      (TateCurve k L).a₁ * x + chartScalar (LaurentSeries k) (TateCurve k L)
      (TateCurve k L).a₃) = 2 * y := by
    change 2 * y + chartScalar (LaurentSeries k) (TateCurve k L) 0 * x +
      chartScalar (LaurentSeries k) (TateCurve k L) 0 = _
    rw [map_zero, zero_mul, add_zero, add_zero]
  let B := ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) (TateCurve k L)
  let ρ : B →+* Γ(Spec (CommRingCat.of B), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have hc : ρ (2 * y + chartScalar (LaurentSeries k) (TateCurve k L)
      (TateCurve k L).a₁ * x + chartScalar (LaurentSeries k) (TateCurve k L)
      (TateCurve k L).a₃) = 2 * ρ y :=
    (congrArg ρ hz).trans ((map_mul ρ (2 : B) y).trans
      (congrArg (fun c : Γ(Spec (CommRingCat.of B), ⊤) => c * ρ y) (map_ofNat ρ 2)))
  exact h.trans (congrArg
    (fun c : Γ(Spec (CommRingCat.of B), ⊤) => c •
      res (j ≫ f).kaehler (V := ⊤) (by simp)
        (k1h f (j ≫ f) j (by simp) ⊤
          (differentialSection (LaurentSeries k) (TateCurve k L) δ))) hc.symm)

lemma normalized_sections_eq (L : ℕ)
    (δ ε : CurveFrame (LaurentSeries k) (TateCurve k L))
    (hδ : NormalizedFrame (LaurentSeries k) (TateCurve k L) δ)
    (hε : NormalizedFrame (LaurentSeries k) (TateCurve k L) ε)
    (χ : ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) (TateCurve k L) →+* LaurentSeries k)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective) ≠ 0) :
    differentialSection (LaurentSeries k) (TateCurve k L) δ =
      differentialSection (LaurentSeries k) (TateCurve k L) ε := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : IsIntegral (Curve (LaurentSeries k) (TateCurve k L)) :=
    CompactifiedCoordinateIsomorphism.projective_integral k (r := L)
  let B := ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) (TateCurve k L)
  letI : Nontrivial B := χ.domain_nontrivial
  let j := ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k) (TateCurve k L)
  letI : IsOpenImmersion j := tate_chart_open k L
  let f := structureMap (LaurentSeries k) (TateCurve k L)
  let x := WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective
  let y := WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective
  let q := 2 * y + chartScalar (LaurentSeries k) (TateCurve k L) (TateCurve k L).a₁ * x +
    chartScalar (LaurentSeries k) (TateCurve k L) (TateCurve k L).a₃
  have hq : q ≠ 0 := by
    have hq' : q = 2 * y := by
      change 2 * y + chartScalar (LaurentSeries k) (TateCurve k L) 0 * x +
        chartScalar (LaurentSeries k) (TateCurve k L) 0 = _
      rw [map_zero, zero_mul, add_zero, add_zero]
    rw [hq']
    intro hz
    have hz' := congrArg χ hz
    rw [map_mul, map_ofNat, map_zero] at hz'
    exact (mul_ne_zero (by norm_num : (2 : LaurentSeries k) ≠ 0) hy) hz'
  let q' := (Scheme.ΓSpecIso (CommRingCat.of B)).inv q
  have hq' : q' ≠ 0 := by
    exact (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv).injective).mpr hq
  apply frame_section_eq_of_chart_smul f j δ _ _ q' hq'
  dsimp only [NormalizedFrame] at hδ hε
  erw [differential_global_eq_k1] at hδ hε
  exact hδ.symm.trans hε

/-- Integral expansion in the frame supplied by the realization witness. -/
theorem four_torsion_tate_behavior_in_own_frame :
  ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 0 < L → 4 ∣ L →
    ∀ (E : TateLevel k L) (a : Γ(Hodge (LaurentSeries k) (TateCurve k L), ⊤)),
      RealizesAlpha (LaurentSeries k) (TateCurve k L) E.law L E.marking a →
      ∃ (δ : CurveFrame (LaurentSeries k) (TateCurve k L)) (v : (PowerSeries k)ˣ) (j : ℕ),
        NormalizedFrame (LaurentSeries k) (TateCurve k L) δ ∧
        (j = 0 ∨ j = L/4) ∧
        a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
          (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) •
          hodgeGenerator (LaurentSeries k) (TateCurve k L) δ := by
  intro k _ _ L hL h4 E a ha
  exact realization_integral_in_own_frame k L hL h4 E a ha

lemma normalized_hodge_eq (L : ℕ)
    (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L)
    (ε : CurveFrame (LaurentSeries k) (TateCurve k L))
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ)
    (hε : NormalizedFrame (LaurentSeries k) (TateCurve k L) ε)
    (χ : ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) (TateCurve k L) →+* LaurentSeries k)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective) ≠ 0) :
    hodgeGenerator (LaurentSeries k) (TateCurve k L) ε =
      ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ := by
  have hs := normalized_sections_eq k L ε δ hε (boundary_chart_normalized k L δ hδ) χ hy
  unfold hodgeGenerator
  rw [hs]
  change _ = res _ _ _
  symm
  exact InitialHodgeSection.res_self _ _

end FourTorsionTateBehavior

/-- Exact integral and signed Tate expansion in any prescribed normalized frame. -/
theorem four_torsion_tate_behavior : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 0 < L → 4 ∣ L → ∀ (E : ArithmeticThetaTateCuspsR0181.TateLevel k L) (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L), ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ → ∀ a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L) E.law L E.marking a → (∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧ a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ)) ∧ (∀ ζ : k, IsPrimitiveRoot ζ L → ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ E → a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k L ^ 2)) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ)) := by
  intro k _ _ L hL h4 E δ hδ a ha
  obtain ⟨e, x, y, g, ε, hd, hε, ha⟩ := ha
  obtain ⟨χ, hχ, hx, hy⟩ := hd.2.2.1.2
  have hy0 : y ≠ 0 := by
    have hu := hd.2.2.2.1
    simpa only [completedY, ArithmeticThetaTateCuspsR0181.TateCurve,
      ArithmeticThetaCompactifiedDifferentialR0145.curve, zero_mul, zero_add,
      mul_zero, add_zero] using hu.ne_zero
  have hg := FourTorsionTateBehavior.normalized_hodge_eq k L δ ε hδ hε χ
    (by simpa only [hy] using hy0)
  rw [hg] at ha
  constructor
  · obtain ⟨v, j, hj, hv⟩ := FourTorsionTateBehavior.rootData_coefficient_integral k L hL h4 E e x y g hd
    exact ⟨v, j, hj, by simpa only [hv] using ha⟩
  · intro ζ hζ hcan
    have hc := FourTorsionTateBehavior.canonical_rootData_signed k L hL h4 E ζ hζ hcan e x y g hd
    simpa only [hc] using ha

#print axioms four_torsion_tate_behavior
end ArithmeticThetaGlobalFourTorsionR0190
