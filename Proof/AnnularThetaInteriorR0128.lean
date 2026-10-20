module

public import ThetaLimitRecoveryRootR0128
public import AnnularThetaGluingDefinitionsR0128

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaAnnularThetaR0128
open ArithmeticThetaScaledAnnularR0050
open ArithmeticThetaIndexedOverlapsR0058

variable (k : Type u) [Field k] [CharZero k]

private lemma restriction_spec (j : ℕ) (side : Bool) :
    IsRestriction k j side (restriction k j side) :=
  (Classical.choose_spec (completed_coordinate_restrictions k j side).exists)

private lemma restriction_of (j : ℕ) (side : Bool)
    (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    restriction k j side (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      completeOpen k j side (openMap k j side a) :=
  RingHom.congr_fun (restriction_spec k j side).1 a

private lemma openMap_x' (j : ℕ) (side : Bool) :
    openMap k j side (ArithmeticThetaScaledTateBridgeR0046.x k 1) = ox k j side := by
  change algebraMap (Node k j) _ (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rfl

private lemma openMap_y' (j : ℕ) (side : Bool) :
    openMap k j side (ArithmeticThetaScaledTateBridgeR0046.y k 1) = oy k j side := by
  change algebraMap (Node k j) _ (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rfl

private lemma restriction_tau (j : ℕ) (side : Bool) :
    restriction k j side (tau k 1) = completeOpen k j side (ot k j side) :=
  restriction_of k j side _

private lemma restriction_x (j : ℕ) (side : Bool) :
    restriction k j side (cx k 1) = completeOpen k j side (ox k j side) := by
  rw [show cx k 1 = ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1) from rfl, restriction_of, openMap_x']

private lemma restriction_y (j : ℕ) (side : Bool) :
    restriction k j side (cy k 1) = completeOpen k j side (oy k j side) := by
  rw [show cy k 1 = ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1) from rfl, restriction_of, openMap_y']

private lemma interior_eq (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m) :
    interiorAdjacent k m hm j hj = adjacent k m hm j (Nat.lt_of_succ_lt hj) := by
  dsimp only [interiorAdjacent]
  apply eq_of_heq
  exact eqRec_heq_iff.mpr HEq.rfl

private lemma interior_of (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m)
    (a : Open k j false) :
    interiorAdjacent k m hm j hj (completeOpen k j false a) =
      completeOpen k (j+1) true (ArithmeticThetaIndexedOverlapsR0058.adjacent k (2*m) j a) := by
  have h := RingHom.congr_fun
    (Classical.choose_spec (completed_indexed_adjacent k (2*m) j
      (by omega) (by omega)).exists).1 a
  rw [interior_eq]
  exact h

private lemma interior_filtered (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m)
    (n : ℕ) (f : OpenHat k j false) (hf : f ∈ hatPower k j false n) :
    interiorAdjacent k m hm j hj f ∈ hatPower k (j+1) true n := by
  have h := (Classical.choose_spec (completed_indexed_adjacent k (2*m) j
    (by omega) (by omega)).exists).2.1 n f hf
  rw [interior_eq]
  exact h

private lemma interior_coordinates (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m) :
    interiorAdjacent k m hm j hj (restriction k j false (tau k 1)) =
      restriction k (j+1) true (tau k 1) ∧
    interiorAdjacent k m hm j hj (restriction k j false (cx k 1)) =
      restriction k (j+1) true (tau k 1) * restriction k (j+1) true (cx k 1) ∧
    restriction k (j+1) true (cy k 1) =
      restriction k (j+1) true (tau k 1) *
        interiorAdjacent k m hm j hj (restriction k j false (cy k 1)) := by
  have h := indexed_adjacent_coordinates k (2*m) j (by omega) (by omega)
  have ht := RingHom.congr_fun h.1 PowerSeries.X
  have hx := h.2.2.1
  have hy := h.2.1
  have hn : next (2*m) j = j+1 := Nat.mod_eq_of_lt hj
  rw [hn] at hx hy
  change ArithmeticThetaIndexedOverlapsR0058.adjacent k (2*m) j (ot k j false) = ot k (next (2*m) j) true at ht
  rw [hn] at ht
  simp only [restriction_tau, restriction_x, restriction_y, interior_of]
  refine ⟨congrArg (completeOpen k (j+1) true) ht, ?_, ?_⟩
  · rw [hx, map_mul]
  · rw [hy, ← map_mul]
    congr 1
    have hu : (↑(xUnit k (j+1)) : Open k (j+1) true) = ox k (j+1) true :=
      IsUnit.unit_spec _
    apply (xUnit k (j+1)).isUnit.mul_left_cancel
    have hxy : ox k (j+1) true * oy k (j+1) true = ot k (j+1) true := by
      have hn : ArithmeticThetaScaledTateBridgeR0046.x k 1 *
          ArithmeticThetaScaledTateBridgeR0046.y k 1 =
          ArithmeticThetaScaledTateBridgeR0046.t k 1 := by
        have hh : ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
            (ArithmeticThetaScaledTateBridgeR0046.relation k 1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        exact sub_eq_zero.mp hh
      have hh := congrArg (openMap k (j+1) true) hn
      simpa [map_mul, openMap_x', openMap_y', ot, openBase,
        ArithmeticThetaScaledTateBridgeR0046.t,
        ArithmeticThetaScaledTateBridgeR0046.parameter,
        ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase] using hh
    rw [hu]
    rw [hxy]
    rw [mul_left_comm, ← hu]
    simp

private lemma theta_term_interior (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m)
    (b : ℤ) :
    targetT k (j+1) ^ shift (j+1) *
        interiorAdjacent k m hm j hj (restriction k j false (thetaTerm k 1 1 j b)) =
      targetT k (j+1) ^ shift j *
        restriction k (j+1) true (thetaTerm k 1 1 (j+1) b) := by
  obtain ⟨ht, hx, hy⟩ := interior_coordinates k m hm j hj
  have he := (theta_exponent_control 1 1 j (by decide) (by decide)).1 b
  have he' := (theta_exponent_control 1 1 (j+1) (by decide) (by decide)).1 b
  change restriction k (j+1) true (tau k 1) ^ shift (j+1) * _ =
    restriction k (j+1) true (tau k 1) ^ shift j * _
  by_cases hb : 0 ≤ b
  · have hexp : shift (j+1) + (thetaExponent 1 1 j b).toNat + b.toNat =
        shift j + (thetaExponent 1 1 (j+1) b).toNat := by
      have hi : (shift (j+1) : ℤ) + thetaExponent 1 1 j b + b =
          (shift j : ℤ) + thetaExponent 1 1 (j+1) b := by
        simp only [thetaExponent, if_pos hb, shift, thetaShift, Nat.cast_add,
          Nat.cast_pow, Nat.cast_one, one_mul]
        ring
      omega
    simp only [thetaTerm, if_pos hb, map_mul, map_pow, ht, hx, mul_pow]
    simp only [← mul_assoc, ← pow_add, ← Nat.add_assoc, hexp]
  · have hexp : shift (j+1) + (thetaExponent 1 1 j b).toNat =
        shift j + (thetaExponent 1 1 (j+1) b).toNat + (-b).toNat := by
      have hi : (shift (j+1) : ℤ) + thetaExponent 1 1 j b =
          (shift j : ℤ) + thetaExponent 1 1 (j+1) b + -b := by
        simp only [thetaExponent, if_neg hb, shift, thetaShift, Nat.cast_add,
          Nat.cast_pow, Nat.cast_one, one_mul]
        ring
      omega
    simp only [thetaTerm, if_neg hb, map_mul, map_pow, ht, hy, mul_pow]
    simp only [← mul_assoc, ← pow_add, ← Nat.add_assoc, hexp]

private lemma theta_partial_interior (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m)
    (ν : ℤ) (N : ℕ) :
    targetT k (j+1) ^ shift (j+1) *
        interiorAdjacent k m hm j hj (restriction k j false (thetaPartial k 1 m 1 j ν N)) =
      targetT k (j+1) ^ shift j *
        restriction k (j+1) true (thetaPartial k 1 m 1 (j+1) ν N) := by
  classical
  simp only [thetaPartial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : b % (m : ℤ) = ν % (m : ℤ)
  · simp only [if_pos h]
    exact theta_term_interior k m hm j hj b
  · simp [h]

private lemma completion_separated {R : Type*} [CommRing R] (I : Ideal R) (hfg : I.FG)
    (f g : AdicCompletion I R)
    (h : ∀ n, f-g ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n) : f = g := by
  apply AdicCompletion.ext_evalₐ
  intro n
  have hh := h n
  rw [← ArithmeticThetaNodeCharts.completion_eval_kernel I hfg n] at hh
  change AdicCompletion.evalₐ I n (f-g) = 0 at hh
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

private lemma hat_separated (j : ℕ) (side : Bool) (f g : OpenHat k j side)
    (h : ∀ n, f-g ∈ hatPower k j side n) : f = g := by
  have hfg : (openIdeal k j side).FG := by
    unfold openIdeal
    set_option backward.isDefEq.respectTransparency true in
      exact Submodule.fg_span (by simp)
  apply completion_separated (openIdeal k j side) hfg f g
  intro n
  have hmap : (openIdeal k j side).map
      (algebraMap (Open k j side) (OpenHat k j side)) =
      Ideal.span {completeOpen k j side (ot k j side)} := by
    change (Ideal.span {ot k j side}).map
      (algebraMap (Open k j side) (OpenHat k j side)) = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [hmap]
  exact h n

theorem annular_theta_interior :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (he : Even m),
    ∀ (j : ℕ) (hj : j+1 < 2*m) (ν : Fin m),
      InteriorEquation k m (NeZero.pos m) j hj
        (thetaSection k m (NeZero.pos m) he j ν)
        (thetaSection k m (NeZero.pos m) he (j+1) ν) := by
  intro k _ _ m _ he j hj ν
  have hlim (i : ℕ) : ThetaLimit k 1 m 1 i (ν.val : ℤ)
      (thetaSection k m (NeZero.pos m) he i ν) :=
    (Classical.choose_spec (theta_completed_limit k 1 m 1 i (ν.val : ℤ)
      (by decide) (NeZero.pos m) he (by decide))).1
  unfold InteriorEquation
  apply hat_separated
  intro n
  let N := n + 2 * (j+1+1) + 1
  have hl := hlim j n N (by dsimp [N]; omega)
  have hr := hlim (j+1) n N (by dsimp [N]; omega)
  have hl' := interior_filtered k m (NeZero.pos m) j hj n _
    ((restriction_spec k j false).2 n _ hl)
  have hr' := (restriction_spec k (j+1) true).2 n _ hr
  have hl'' := (hatPower k (j+1) true n).mul_mem_left
    (targetT k (j+1) ^ shift (j+1)) hl'
  have hr'' := (hatPower k (j+1) true n).mul_mem_left
    (targetT k (j+1) ^ shift j) hr'
  have h := (hatPower k (j+1) true n).sub_mem hl'' hr''
  simp only [map_sub, mul_sub] at h
  rw [theta_partial_interior k m (NeZero.pos m) j hj] at h
  simpa only [sub_sub_sub_cancel_right] using h

end ArithmeticThetaAnnularThetaR0128
