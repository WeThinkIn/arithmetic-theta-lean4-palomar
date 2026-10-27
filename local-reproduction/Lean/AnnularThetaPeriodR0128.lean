import ThetaLimitRecoveryRootR0128
import AnnularThetaGluingDefinitionsR0128

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaAnnularThetaR0128
open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaScaledAnnularR0050

private lemma restriction_spec (k : Type u) [Field k] [CharZero k] (j : ℕ) (s : Bool) :
    IsRestriction k j s (restriction k j s) :=
  (Classical.choose_spec (completed_coordinate_restrictions k j s).exists)

private lemma nodeEquiv_coord (k : Type u) [Field k] [CharZero k] (s : Bool) :
    nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeCoord k s) =
      nodeCoord k s := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter]
  cases s <;>
    change (Ideal.quotientEquivAlgOfEq (PowerSeries k) hrel)
      (Ideal.Quotient.mk _ (MvPolynomial.X _)) = Ideal.Quotient.mk _ (MvPolynomial.X _)
  all_goals rw [Ideal.quotientEquivAlgOfEq_mk]

private lemma restriction_x (k : Type u) [Field k] [CharZero k] (j : ℕ) (s : Bool) :
    restriction k j s (cx k 1) = completeOpen k j s (ox k j s) := by
  have h := RingHom.congr_fun (restriction_spec k j s).1
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)
  change restriction k j s (cx k 1) = completeOpen k j s
    (algebraMap _ _ (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1))) at h
  rw [show nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
    ArithmeticThetaNodeCharts.x k from nodeEquiv_coord k true] at h
  exact h

private lemma restriction_y (k : Type u) [Field k] [CharZero k] (j : ℕ) (s : Bool) :
    restriction k j s (cy k 1) = completeOpen k j s (oy k j s) := by
  have h := RingHom.congr_fun (restriction_spec k j s).1
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)
  change restriction k j s (cy k 1) = completeOpen k j s
    (algebraMap _ _ (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1))) at h
  rw [show nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
    ArithmeticThetaNodeCharts.y k from nodeEquiv_coord k false] at h
  exact h

private lemma restriction_t (k : Type u) [Field k] [CharZero k] (j : ℕ) (s : Bool) :
    restriction k j s (tau k 1) = completeOpen k j s (ot k j s) := by
  exact RingHom.congr_fun (restriction_spec k j s).1
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)

private def overlapUnit (k : Type u) [Field k] [CharZero k] : (OpenHat k 0 true)ˣ :=
  Units.map (completeOpen k 0 true) (xUnit k 0)

private lemma overlapUnit_val (k : Type u) [Field k] [CharZero k] :
    (overlapUnit k : OpenHat k 0 true) = targetX k 0 := by
  rw [targetX]
  change completeOpen k 0 true (xUnit k 0) = restriction k 0 true (cx k 1)
  rw [restriction_x]
  congr 1

private lemma boundary_eq (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) :
    boundaryAdjacent k m hm =
      Classical.choose (completed_indexed_adjacent k (2*m) (lastIndex m hm).val
        (Nat.mul_pos (by decide) hm) (lastIndex m hm).isLt).exists := by
  unfold boundaryAdjacent adjacent ArithmeticThetaCorrectedGammaR0061.overlap
  dsimp only
  exact eq_of_heq (eqRec_heq_iff.mpr (HEq.refl _))

private lemma boundary_on_open (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) (a : Open k (lastIndex m hm).val false) :
    boundaryAdjacent k m hm (completeOpen k (lastIndex m hm).val false a) =
      completeOpen k 0 true (ArithmeticThetaIndexedOverlapsR0058.adjacent k (2*m)
        (lastIndex m hm).val a) := by
  have h := RingHom.congr_fun (Classical.choose_spec
    (completed_indexed_adjacent k (2*m) (lastIndex m hm).val
      (Nat.mul_pos (by decide) hm) (lastIndex m hm).isLt).exists).1 a
  rw [boundary_eq]
  exact h

private lemma boundary_t (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) :
    boundaryAdjacent k m hm (restriction k (lastIndex m hm).val false (tau k 1)) =
      targetT k 0 := by
  rw [restriction_t, boundary_on_open]
  have h := RingHom.congr_fun (indexed_adjacent_coordinates k (2*m)
    (lastIndex m hm).val (Nat.mul_pos (by decide) hm) (lastIndex m hm).isLt).1
    PowerSeries.X
  change ArithmeticThetaIndexedOverlapsR0058.adjacent k (2*m) (lastIndex m hm).val
    (ot k (lastIndex m hm).val false) = ot k 0 true at h
  rw [h]
  exact (restriction_t k 0 true).symm

private lemma boundary_x (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) :
    boundaryAdjacent k m hm (restriction k (lastIndex m hm).val false (cx k 1)) =
      targetT k 0 * (overlapUnit k : OpenHat k 0 true) := by
  rw [restriction_x, boundary_on_open]
  rw [(indexed_adjacent_coordinates k (2*m) (lastIndex m hm).val
    (Nat.mul_pos (by decide) hm) (lastIndex m hm).isLt).2.2.1, map_mul]
  rw [overlapUnit_val]
  exact congrArg₂ (· * ·) (restriction_t k 0 true).symm (restriction_x k 0 true).symm

private lemma boundary_y (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m) :
    boundaryAdjacent k m hm (restriction k (lastIndex m hm).val false (cy k 1)) =
      ((overlapUnit k)⁻¹ : (OpenHat k 0 true)ˣ) := by
  rw [restriction_y, boundary_on_open]
  rw [(indexed_adjacent_coordinates k (2*m) (lastIndex m hm).val
    (Nat.mul_pos (by decide) hm) (lastIndex m hm).isLt).2.1]
  rfl

private lemma restriction_y_unit (k : Type u) [Field k] [CharZero k] :
    restriction k 0 true (cy k 1) =
      targetT k 0 * ((overlapUnit k)⁻¹ : (OpenHat k 0 true)ˣ) := by
  have hxy : ox k 0 true * oy k 0 true = ot k 0 true := by
    change algebraMap _ _ (ArithmeticThetaNodeCharts.x k) *
      algebraMap _ _ (ArithmeticThetaNodeCharts.y k) = _
    rw [← map_mul, ArithmeticThetaNodeCharts.node_xy]
    rfl
  have h : targetX k 0 * restriction k 0 true (cy k 1) = targetT k 0 := by
    change restriction k 0 true (cx k 1) * restriction k 0 true (cy k 1) = _
    rw [restriction_x, restriction_y, ← map_mul, hxy]
    exact (restriction_t k 0 true).symm
  apply (overlapUnit k).isUnit.mul_left_cancel
  rw [overlapUnit_val, h]
  rw [← overlapUnit_val]
  simp [mul_left_comm]

private lemma term_image (k : Type u) [Field k] [CharZero k]
    {R : Type*} [CommRing R] (f : Chart k →+* R) (t : R) (U : Rˣ)
    (i : ℕ) (hi : i ≤ 1) (j : ℕ)
    (ht : f (tau k 1) = t)
    (hx : f (cx k 1) = t^i * U)
    (hy : f (cy k 1) = t^(1-i) * ↑U⁻¹) (b : ℤ) :
    f (thetaTerm k 1 1 j b) =
      t ^ (specializedExponent 1 i 1 j b).toNat * ↑(U ^ b) := by
  have he := (theta_exponent_control 1 1 j (by decide) (by decide)).1 b
  unfold thetaTerm
  rw [map_mul, map_pow, ht]
  by_cases hb : 0 ≤ b
  · rw [if_pos hb, map_pow, hx, mul_pow]
    have hnat : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
    have hp : thetaExponent 1 1 j b + (i : ℤ)*b = specializedExponent 1 i 1 j b := by
      simp [thetaExponent, specializedExponent, hb, thetaShift]
      ring
    have hexp : (thetaExponent 1 1 j b).toNat + i * b.toNat =
        (specializedExponent 1 i 1 j b).toNat := by
      rw [← hp, Int.toNat_add he (mul_nonneg (Int.natCast_nonneg _) hb),
        Int.toNat_mul, Int.toNat_natCast] <;> omega
    rw [← mul_assoc, ← pow_mul, ← pow_add, hexp]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hnat]
  · rw [if_neg hb, map_pow, hy, mul_pow]
    have hnat : ((-b).toNat : ℤ) = -b := Int.toNat_of_nonneg (by omega)
    have hp : thetaExponent 1 1 j b + ((1-i : ℕ) : ℤ)*(-b) =
        specializedExponent 1 i 1 j b := by
      have hi' : ((1-i : ℕ) : ℤ) = 1 - (i : ℤ) := by omega
      simp [thetaExponent, specializedExponent, hb, thetaShift, hi']
      ring
    have hexp : (thetaExponent 1 1 j b).toNat + (1-i) * (-b).toNat =
        (specializedExponent 1 i 1 j b).toNat := by
      rw [← hp, Int.toNat_add he (mul_nonneg (Int.natCast_nonneg _) (by omega)),
        Int.toNat_mul, Int.toNat_natCast] <;> omega
    rw [← mul_assoc, ← pow_mul, ← pow_add, hexp]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hnat, inv_zpow, zpow_neg, inv_inv]

private lemma period_term (k : Type u) [Field k] [CharZero k]
    {R : Type*} [CommRing R] (f g : Chart k →+* R) (t : R) (U : Rˣ)
    (m l : ℕ) (hl : l+1 = 2*m)
    (hft : f (tau k 1) = t) (hfx : f (cx k 1) = t * U)
    (hfy : f (cy k 1) = ↑U⁻¹)
    (hgt : g (tau k 1) = t) (hgx : g (cx k 1) = ↑U)
    (hgy : g (cy k 1) = t * ↑U⁻¹) (b : ℤ) :
    t^(shift 0 + m*m) * (U : R)^m * f (thetaTerm k 1 1 l b) =
      t^(shift l) * g (thetaTerm k 1 1 0 (b + m)) := by
  rw [term_image k f t U 1 (by decide) l hft (by simpa using hfx)
    (by simpa using hfy),
    term_image k g t U 0 (by decide) 0 hgt (by simpa using hgx)
    (by simpa using hgy)]
  have hlz : (l : ℤ)+1 = 2*(m : ℤ) := by exact_mod_cast hl
  have he : 0 ≤ specializedExponent 1 1 1 l b := by
    simp only [specializedExponent, thetaShift, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, one_mul, hlz]
    nlinarith [sq_nonneg (b+(m:ℤ)), sq_nonneg (m:ℤ)]
  have he0 : 0 ≤ specializedExponent 1 0 1 0 (b+m) := by
    simp [specializedExponent, thetaShift]
    positivity
  have hpow : shift 0 + m*m + (specializedExponent 1 1 1 l b).toNat =
      shift l + (specializedExponent 1 0 1 0 (b+m)).toNat := by
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg he,
      Int.toNat_of_nonneg he0]
    simp [shift, specializedExponent, thetaShift]
    rw [hlz]
    ring
  have hU : (U : R)^m * ↑(U^b) = ↑(U^(b+(m:ℤ))) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
    congr 2
    omega
  calc
    _ = (t^(shift 0 + m*m) * t^(specializedExponent 1 1 1 l b).toNat) *
        ((U : R)^m * ↑(U^b)) := by ring
    _ = t^(shift l + (specializedExponent 1 0 1 0 (b+m)).toNat) *
        ↑(U^(b+(m:ℤ))) := by rw [← pow_add, hpow, hU]
    _ = _ := by rw [pow_add]; ring

private lemma sum_translate {R : Type*} [AddCommMonoid R]
    (G : ℤ → R) (a b c : ℤ) :
    (∑ r ∈ Finset.Icc a b, G (r+c)) = ∑ r ∈ Finset.Icc (a+c) (b+c), G r := by
  apply Finset.sum_bij (fun r _ => r+c)
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r hr s hs h
    omega
  · intro s hs
    refine ⟨s-c, ?_, by omega⟩
    simp only [Finset.mem_Icc] at hs ⊢
    omega
  · intro r hr
    rfl

private lemma period_partial (k : Type u) [Field k] [CharZero k]
    {R : Type*} [CommRing R] (f g : Chart k →+* R) (t : R) (U : Rˣ)
    (m l : ℕ) (hl : l+1 = 2*m)
    (hft : f (tau k 1) = t) (hfx : f (cx k 1) = t * U)
    (hfy : f (cy k 1) = ↑U⁻¹)
    (hgt : g (tau k 1) = t) (hgx : g (cx k 1) = ↑U)
    (hgy : g (cy k 1) = t * ↑U⁻¹) (ν : ℤ)
    (n N : ℕ) (hN : n+3+m ≤ N)
    (htail : ∀ b : ℤ, b < -((n+3:ℕ):ℤ) ∨ ((n+3:ℕ):ℤ) < b →
      g (thetaTerm k 1 1 0 b) = 0) :
    t^(shift 0+m*m) * (U:R)^m * f (thetaPartial k 1 m 1 l ν N) =
      t^(shift l) * g (thetaPartial k 1 m 1 0 ν (N+m)) := by
  classical
  let G : ℤ → R := fun b =>
    if b % (m:ℤ) = ν % (m:ℤ) then t^(shift l) * g (thetaTerm k 1 1 0 b) else 0
  have hterm (b : ℤ) :
      t^(shift 0+m*m) * (U:R)^m *
        (if b % (m:ℤ) = ν % (m:ℤ) then f (thetaTerm k 1 1 l b) else 0) =
      G (b+m) := by
    dsimp [G]
    rw [Int.add_emod_right]
    split_ifs
    · exact period_term k f g t U m l hl hft hfx hfy hgt hgx hgy b
    · simp
  simp only [thetaPartial, map_sum, apply_ite, map_zero, Finset.mul_sum]
  simp only [mul_ite, mul_zero] at hterm
  simp only [mul_zero]
  change (∑ b ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    (if b % (m:ℤ) = ν % (m:ℤ) then
      t^(shift 0+m*m) * (U:R)^m * f (thetaTerm k 1 1 l b) else 0)) =
      ∑ b ∈ Finset.Icc (-((N+m:ℕ):ℤ)) ((N+m:ℕ):ℤ), G b
  simp_rw [hterm]
  rw [sum_translate]
  apply Finset.sum_subset
  · intro b hb
    simp only [Finset.mem_Icc, Nat.cast_add] at hb ⊢
    constructor <;> omega
  · intro b hb hb'
    have hsmall : b < -((n+3:ℕ):ℤ) := by
      simp only [Finset.mem_Icc, Nat.cast_add] at hb hb'
      omega
    simp [G, htail b (Or.inl hsmall)]

theorem annular_theta_period :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (he : Even m),
    ∀ ν : Fin m, PeriodEquation k m (NeZero.pos m)
      (thetaSection k m (NeZero.pos m) he (lastIndex m (NeZero.pos m)).val ν)
      (thetaSection k m (NeZero.pos m) he 0 ν) := by
  intro k _ _ m _ he ν
  let hm := NeZero.pos m
  let l := (lastIndex m hm).val
  have hl : l+1 = 2*m := by dsimp [l, lastIndex]; omega
  let R := OpenHat k 0 true
  let J : Ideal R := Ideal.span {targetT k 0}
  have hJ : J = (openIdeal k 0 true).map
      (algebraMap (Open k 0 true) R) := by
    change Ideal.span {restriction k 0 true (tau k 1)} = _
    rw [restriction_t]
    simp [openIdeal, Ideal.map_span, Set.image_singleton, completeOpen, R]
  let : IsAdicComplete J R := by
    rw [hJ]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr
      (AdicCompletion.isAdicComplete (show (openIdeal k 0 true).FG from
        Submodule.fg_span_singleton _))
  have hJpow (n : ℕ) : J^n = hatPower k 0 true n := by
    change (Ideal.span {restriction k 0 true (tau k 1)})^n = _
    rw [restriction_t]
    rfl
  let f : Chart k →+* R := (boundaryAdjacent k m hm).toRingHom.comp
    (restriction k l false)
  let g : Chart k →+* R := restriction k 0 true
  have hf (n : ℕ) (z : Chart k)
      (hz : z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k 1 n) :
      f z ∈ J^n := by
    rw [hJpow]
    change boundaryAdjacent k m hm (restriction k l false z) ∈ _
    rw [boundary_eq]
    exact (Classical.choose_spec (completed_indexed_adjacent k (2*m) l
      (Nat.mul_pos (by decide) hm) (lastIndex m hm).isLt).exists).2.1 n _
      ((restriction_spec k l false).2 n z hz)
  have hg (n : ℕ) (z : Chart k)
      (hz : z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k 1 n) :
      g z ∈ J^n := by
    rw [hJpow]
    exact (restriction_spec k 0 true).2 n z hz
  have hs (j : ℕ) : ThetaLimit k 1 m 1 j (ν.val:ℤ)
      (thetaSection k m hm he j ν) :=
    (Classical.choose_spec (theta_completed_limit k 1 m 1 j (ν.val:ℤ)
      (by decide) hm he (by decide))).1
  unfold PeriodEquation
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  let π := Ideal.Quotient.mk (J^n)
  let F := π.comp f
  let G := π.comp g
  let t := π (targetT k 0)
  let U := Units.map π.toMonoidHom (overlapUnit k)
  let N := n+2*(l+1)+m+4
  have hF : F (thetaSection k m hm he l ν) =
      F (thetaPartial k 1 m 1 l (ν.val:ℤ) N) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    apply hf
    exact hs l n N (by dsimp [N]; omega)
  have hG : G (thetaSection k m hm he 0 ν) =
      G (thetaPartial k 1 m 1 0 (ν.val:ℤ) (N+m)) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    apply hg
    exact hs 0 n (N+m) (by dsimp [N]; omega)
  have hft : F (tau k 1) = t := by
    change π (boundaryAdjacent k m hm (restriction k l false (tau k 1))) = _
    rw [boundary_t]
  have hfx : F (cx k 1) = t * (U : R ⧸ J^n) := by
    change π (boundaryAdjacent k m hm (restriction k l false (cx k 1))) = _
    rw [boundary_x, map_mul]
    rfl
  have hfy : F (cy k 1) = ↑U⁻¹ := by
    change π (boundaryAdjacent k m hm (restriction k l false (cy k 1))) = _
    rw [boundary_y]
    rfl
  have hgt : G (tau k 1) = t := rfl
  have hgx : G (cx k 1) = (U : R ⧸ J^n) := by
    change π (targetX k 0) = π (overlapUnit k)
    rw [overlapUnit_val]
  have hgy : G (cy k 1) = t * ↑U⁻¹ := by
    change π (restriction k 0 true (cy k 1)) = _
    rw [restriction_y_unit, map_mul]
    rfl
  have htail (b : ℤ) (hb : b < -((n+3:ℕ):ℤ) ∨ ((n+3:ℕ):ℤ) < b) :
      G (thetaTerm k 1 1 0 b) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hg
    apply theta_term_tail k 1 1 0 n (by decide) (by decide) b
    push_cast at hb ⊢
    omega
  have hp := period_partial k F G t U m l hl hft hfx hfy hgt hgx hgy
    (ν.val:ℤ) n N (by dsimp [N]; omega) htail
  simp only [map_mul, map_pow]
  change t^(shift 0+m*m) * π (targetX k 0)^m *
      F (thetaSection k m hm he l ν) =
    t^(shift l) * G (thetaSection k m hm he 0 ν)
  rw [hF, hG, ← overlapUnit_val]
  exact hp

end ArithmeticThetaAnnularThetaR0128
