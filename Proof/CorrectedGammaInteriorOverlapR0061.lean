module

public import CorrectedGammaDataUniqueR0061

@[expose] public section
set_option synthInstance.maxHeartbeats 200000
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

open ArithmeticThetaIndexedOverlapsR0058

variable (k : Type u) [Field k] [CharZero k]

private theorem restriction_spec (j : ℕ) (side : Bool) :
    IsRestriction k j side (restrict k j side) :=
  (Classical.choose_spec (completed_coordinate_restrictions k j side).exists)

private theorem overlap_spec (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    IsCompletedAdjacent k r j (overlap k r j hr hj) :=
  (Classical.choose_spec (completed_indexed_adjacent k r j hr hj).exists)

omit [CharZero k] in
private theorem node_equiv_coord (i : Fin 2) :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (MvPolynomial.X i)) = ArithmeticThetaNodeCharts.quotientMap k
        (MvPolynomial.X i) := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private theorem restrict_tau (j : ℕ) (side : Bool) :
    restrict k j side (tau k) = completeOpen k j side (ot k j side) := by
  have h := RingHom.congr_fun (restriction_spec k j side).1
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, ot, openBase,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase] using h

private theorem restrict_cx (j : ℕ) (side : Bool) :
    restrict k j side (cx k) = completeOpen k j side (ox k j side) := by
  have h := RingHom.congr_fun (restriction_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)
  simpa [cx, ArithmeticThetaScaledAnnularR0050.cx,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, openMap,
    ArithmeticThetaScaledTateBridgeR0046.x, ArithmeticThetaNodeCharts.x,
    node_equiv_coord, ox] using h

private theorem restrict_cy (j : ℕ) (side : Bool) :
    restrict k j side (cy k) = completeOpen k j side (oy k j side) := by
  have h := RingHom.congr_fun (restriction_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)
  simpa [cy, ArithmeticThetaScaledAnnularR0050.cy,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, openMap,
    ArithmeticThetaScaledTateBridgeR0046.y, ArithmeticThetaNodeCharts.y,
    node_equiv_coord, oy] using h

omit [CharZero k] in
private theorem open_xy (j : ℕ) :
    ox k j true * oy k j true = ot k j true := by
  have hnode : ArithmeticThetaNodeCharts.x k * ArithmeticThetaNodeCharts.y k =
      ArithmeticThetaNodeCharts.t k := by
    apply sub_eq_zero.mp
    change ArithmeticThetaNodeCharts.quotientMap k
      (ArithmeticThetaNodeCharts.relation k) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h := congrArg (algebraMap (ArithmeticThetaNodeCharts.Node k)
    (Open k j true)) hnode
  have ht : nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X) =
        ArithmeticThetaNodeCharts.t k := by
    have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
        ArithmeticThetaNodeCharts.relationIdeal k := by
      simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
        ArithmeticThetaScaledTateBridgeR0046.relation,
        ArithmeticThetaScaledTateBridgeR0046.parameter,
        ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
        ArithmeticThetaNodeCharts.parameter]
    unfold nodeEquiv ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase
      ArithmeticThetaNodeCharts.t
    change (Ideal.quotientEquivAlgOfEq _ hrel)
      (Ideal.Quotient.mk _ (MvPolynomial.C PowerSeries.X)) =
        Ideal.Quotient.mk _ (MvPolynomial.C PowerSeries.X)
    rw [Ideal.quotientEquivAlgOfEq_mk]
  change ox k j true * oy k j true =
    algebraMap (Node k j) _ (nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X))
  rw [ht]
  exact (map_mul _ _ _).symm.trans h

private theorem transported_coordinates (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    let F := (overlap k r j hr hj).toRingHom.comp (restrict k j false)
    let G := restrict k (next r j) true
    F (tau k) = G (tau k) ∧
      F (cx k) = G (tau k) * G (cx k) ∧
      G (tau k) * F (cy k) = G (cy k) := by
  dsimp
  have hcomm (a : Open k j false) :=
    RingHom.congr_fun (overlap_spec k r j hr hj).1 a
  have ht := DFunLike.congr_fun (indexed_adjacent_coordinates k r j hr hj).1
    PowerSeries.X
  change adjacent k r j (ot k j false) = ot k (next r j) true at ht
  have hx := (indexed_adjacent_coordinates k r j hr hj).2.2.1
  have hy := (indexed_adjacent_coordinates k r j hr hj).2.1
  have hu : (ArithmeticThetaIndexedOverlapsR0058.xUnit k (next r j) :
      Open k (next r j) true) = ox k (next r j) true := IsUnit.unit_spec _
  have hty : ot k (next r j) true *
      adjacent k r j (oy k j false) = oy k (next r j) true := by
    rw [hy, ← open_xy k (next r j), ← hu]
    simp [mul_assoc, mul_comm]
  simp only [restrict_tau, restrict_cx, restrict_cy]
  refine ⟨?_, ?_, ?_⟩
  · have h := hcomm (ot k j false)
    change overlap k r j hr hj (completeOpen k j false (ot k j false)) =
      completeOpen k (next r j) true (adjacent k r j (ot k j false)) at h
    rwa [ht] at h
  · have h := hcomm (ox k j false)
    change overlap k r j hr hj (completeOpen k j false (ox k j false)) =
      completeOpen k (next r j) true (adjacent k r j (ox k j false)) at h
    rwa [hx, map_mul] at h
  · rw [show overlap k r j hr hj (completeOpen k j false (oy k j false)) =
        completeOpen k (next r j) true (adjacent k r j (oy k j false)) from
          hcomm (oy k j false)]
    rw [← map_mul, hty]

private theorem full_partial_overlap (r j : ℕ) (hr : 0 < r) (hj : j < r)
    (hi : j + 1 < r) (N : ℕ) :
    overlap k r j hr hj (restrict k j false (fullPartial k r j N)) =
      restrict k (next r j) true (fullPartial k r (next r j) N) := by
  let F := (overlap k r j hr hj).toRingHom.comp (restrict k j false)
  let G := restrict k (next r j) true
  obtain ⟨ht, hx, hy⟩ := transported_coordinates k r j hr hj
  change F (tau k) = G (tau k) at ht
  change F (cx k) = G (tau k) * G (cx k) at hx
  change G (tau k) * F (cy k) = G (cy k) at hy
  have hn : next r j = j + 1 := Nat.mod_eq_of_lt hi
  have hl (l : ℕ) : F (leftFactor k r j l) = G (leftFactor k r (next r j) l) := by
    simp only [leftFactor, map_sub, map_one, map_mul, map_pow, ht, hx]
    rw [hn]
    simp only [leftExponent]
    rw [show r * l + (j + 1) = (r * l + j) + 1 by omega, pow_succ]
    ring
  have hright (l : ℕ) : F (rightFactor k r j (l + 1)) =
      G (rightFactor k r (next r j) (l + 1)) := by
    have hlarge : j + 2 ≤ r * (l + 1) := by
      have h := Nat.mul_le_mul_left r (show 1 ≤ l + 1 by omega)
      omega
    have he : rightExponent r j (l + 1) =
        rightExponent r (next r j) (l + 1) + 1 := by
      unfold rightExponent
      rw [hn]
      omega
    simp only [rightFactor, map_sub, map_one, map_mul, map_pow, ht]
    rw [he, pow_succ, mul_assoc, hy]
  change F (fullPartial k r j N) = G (fullPartial k r (next r j) N)
  simp only [fullPartial, leftPartial, rightPartial, map_mul, map_prod]
  congr 1
  · exact Finset.prod_congr rfl (fun l _ => hl l)
  · exact Finset.prod_congr rfl (fun l _ => hright l)

theorem gamma_interior_overlap :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ),
      (hr : 0 < r) → (hj : j < r) → (hinterior : j + 1 < r) →
      ∀ (v u v' u' : Chart k), IsGammaData k r j v u →
        IsGammaData k r (next r j) v' u' →
        (overlap k r j hr hj) ((restrict k j false) u) =
          (restrict k (next r j) true) u' := by
  intro k _ _ r j hr hj hi v u v' u' h h'
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨N₁, hN₁⟩ := h.2.2.1 n
  obtain ⟨N₂, hN₂⟩ := h'.2.2.1 n
  let N := max N₁ N₂
  have ha := (overlap_spec k r j hr hj).2.1 n _
    ((restriction_spec k j false).2 n _ (hN₁ N (Nat.le_max_left _ _)))
  have hb := (restriction_spec k (next r j) true).2 n _
    (hN₂ N (Nat.le_max_right _ _))
  have hdiff := (hatPower k (next r j) true n).sub_mem ha hb
  have heq := full_partial_overlap k r j hr hj hi N
  simp only [map_sub] at hdiff
  rw [heq] at hdiff
  have hdiff' : overlap k r j hr hj (restrict k j false u) -
      restrict k (next r j) true u' ∈ hatPower k (next r j) true n := by
    convert hdiff using 1
    ring
  have hker : hatPower k (next r j) true n =
      RingHom.ker (AdicCompletion.evalₐ (openIdeal k (next r j) true) n).toRingHom := by
    rw [ArithmeticThetaNodeCharts.completion_eval_kernel
      (openIdeal k (next r j) true)
      (Submodule.fg_span_singleton _) n]
    unfold hatPower openIdeal
    congr 1
    rw [Ideal.map_span]
    simp [completeOpen]
    rfl
  rw [hker] at hdiff'
  change AdicCompletion.evalₐ (openIdeal k (next r j) true) n
    (overlap k r j hr hj (restrict k j false u) - restrict k (next r j) true u') = 0
      at hdiff'
  exact sub_eq_zero.mp (by simpa only [map_sub] using hdiff')

end ArithmeticThetaCorrectedGammaR0061
