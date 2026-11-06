import IndexedFormalOverlapDefinitionsR0058

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaIndexedOverlapsR0058

open ArithmeticThetaNodeCharts

variable (k : Type u) [Field k] [CharZero k]

private lemma nodeEquiv_x : nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1) = x k := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.x ArithmeticThetaNodeCharts.x
    ArithmeticThetaScaledTateBridgeR0046.quotientMap ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal,
    ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private lemma nodeEquiv_y : nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1) = y k := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.y ArithmeticThetaNodeCharts.y
    ArithmeticThetaScaledTateBridgeR0046.quotientMap ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal,
    ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private lemma openMap_x (j : ℕ) (side : Bool) :
    openMap k j side (ArithmeticThetaScaledTateBridgeR0046.x k 1) = ox k j side := by
  change algebraMap (Node k j) _ (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [nodeEquiv_x]
  rfl

private lemma openMap_y (j : ℕ) (side : Bool) :
    openMap k j side (ArithmeticThetaScaledTateBridgeR0046.y k 1) = oy k j side := by
  change algebraMap (Node k j) _ (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [nodeEquiv_y]
  rfl

private lemma torusEquiv_false_y (j : ℕ) : torusEquiv k j false (oy k j false) = LaurentPolynomial.T 1 := by
  have he := (Classical.choose_spec (node_torus_chart_equivalences k).2).1
  have h := congrArg (fun f => f (MvPolynomial.X 1)) he
  change (Classical.choose (node_torus_chart_equivalences k).2)
      ((toYChart k) (quotientMap k (MvPolynomial.X 1))) = _
  simpa [ArithmeticThetaNodeCharts.oppositeTorusMap, RingHom.comp_apply] using h

private lemma torusEquiv_false_x (j : ℕ) : torusEquiv k j false (ox k j false) =
    LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1) := by
  have he := (Classical.choose_spec (node_torus_chart_equivalences k).2).1
  have h := congrArg (fun f => f (MvPolynomial.X 0)) he
  change (Classical.choose (node_torus_chart_equivalences k).2)
      ((toYChart k) (quotientMap k (MvPolynomial.X 0))) = _
  simpa [ArithmeticThetaNodeCharts.oppositeTorusMap, RingHom.comp_apply] using h

private lemma torusEquiv_false_C (j : ℕ) (a : Base k) :
    torusEquiv k j false (openBase k j false a) = LaurentPolynomial.C a := by
  have he := (Classical.choose_spec (node_torus_chart_equivalences k).2).1
  have h := congrArg (fun f => f (MvPolynomial.C a)) he
  change (Classical.choose (node_torus_chart_equivalences k).2)
      ((toYChart k) ((quotientMap k) (MvPolynomial.C a))) = _
  simpa [ArithmeticThetaNodeCharts.oppositeTorusMap, RingHom.comp_apply,
    openBase, openMap,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase] using h

private lemma torusEquiv_true_x (j : ℕ) :
    torusEquiv k j true (ox k j true) = LaurentPolynomial.T 1 := by
  have he := (Classical.choose_spec (node_torus_chart_equivalences k).1).1
  have h := congrArg (fun f => f (MvPolynomial.X 0)) he
  change (Classical.choose (node_torus_chart_equivalences k).1)
      ((toXChart k) (quotientMap k (MvPolynomial.X 0))) = _
  simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using h

private lemma torusEquiv_true_C (j : ℕ) (a : Base k) :
    torusEquiv k j true (openBase k j true a) = LaurentPolynomial.C a := by
  have he := (Classical.choose_spec (node_torus_chart_equivalences k).1).1
  have h := congrArg (fun f => f (MvPolynomial.C a)) he
  change (Classical.choose (node_torus_chart_equivalences k).1)
      ((toXChart k) ((quotientMap k) (MvPolynomial.C a))) = _
  simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using h

private lemma torusEquiv_true_inv (j : ℕ) :
    (torusEquiv k j true).symm (LaurentPolynomial.T (-1)) =
      ↑((xUnit k j)⁻¹) := by
  have hx := torusEquiv_true_x k j
  have hu : (xUnit k j : Open k j true) = ox k j true := IsUnit.unit_spec _
  apply (RingEquiv.symm_apply_eq (torusEquiv k j true)).2
  have hi : (↑((xUnit k j)⁻¹) : Open k j true) * (xUnit k j : Open k j true) = 1 := by
    simp
  have hmap : torusEquiv k j true (↑((xUnit k j)⁻¹) : Open k j true) *
      LaurentPolynomial.T 1 = 1 := by
    calc
      _ = torusEquiv k j true (↑((xUnit k j)⁻¹) : Open k j true) *
          torusEquiv k j true (xUnit k j : Open k j true) := by rw [hu, hx]
      _ = torusEquiv k j true
          ((↑((xUnit k j)⁻¹) : Open k j true) * (xUnit k j : Open k j true)) := by
            rw [map_mul]
      _ = 1 := by rw [hi, map_one]
  have hT : LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) =
      (1 : LaurentPolynomial (Base k)) := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  exact (LaurentPolynomial.isUnit_T (R := Base k) 1).mul_right_cancel
    (hT.trans hmap.symm)

private lemma torusEquiv_true_T (j : ℕ) :
    (torusEquiv k j true).symm (LaurentPolynomial.T 1) = ox k j true := by
  exact (RingEquiv.symm_apply_eq (torusEquiv k j true)).2
    (torusEquiv_true_x k j).symm

private lemma adjacent_y (r j : ℕ) :
    adjacent k r j (oy k j false) = ↑((xUnit k (next r j))⁻¹) := by
  simp only [adjacent, RingEquiv.trans_apply]
  rw [torusEquiv_false_y k j]
  change (torusEquiv k (next r j) true).symm
      (LaurentPolynomial.invert (LaurentPolynomial.T 1)) = _
  rw [LaurentPolynomial.invert_T]
  exact torusEquiv_true_inv k (next r j)

private lemma adjacent_x (r j : ℕ) :
    adjacent k r j (ox k j false) =
      ot k (next r j) true * ox k (next r j) true := by
  simp only [adjacent, RingEquiv.trans_apply]
  rw [torusEquiv_false_x k j, map_mul]
  change (torusEquiv k (next r j) true).symm
      (LaurentPolynomial.invert (LaurentPolynomial.C (parameter k)) *
        LaurentPolynomial.invert (LaurentPolynomial.T (-1))) = _
  rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  have hc : (torusEquiv k (next r j) true).symm
      (LaurentPolynomial.C (parameter k)) = ot k (next r j) true := by
    apply (RingEquiv.symm_apply_eq (torusEquiv k (next r j) true)).2
    exact (torusEquiv_true_C k (next r j) (parameter k)).symm
  have ht : (torusEquiv k (next r j) true).symm
      (LaurentPolynomial.T 1) = ox k (next r j) true := by
    apply (RingEquiv.symm_apply_eq (torusEquiv k (next r j) true)).2
    exact (torusEquiv_true_x k (next r j)).symm
  norm_num
  rw [hc, ht]

theorem indexed_adjacent_coordinates :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ), 0 < r → j < r →
      (adjacent k r j).toRingHom.comp (openBase k j false) =
          openBase k (next r j) true ∧
      adjacent k r j (oy k j false) =
          ↑((xUnit k (next r j))⁻¹) ∧
      adjacent k r j (ox k j false) =
          ot k (next r j) true * ox k (next r j) true ∧
      adjacent k r j (oz k j false) =
          (if j + 1 = r then ot k (next r j) true ^ r else 1) *
            oz k (next r j) true ∧
      CategoryTheory.CategoryStruct.comp (adjacentSpec k r j)
          (structureMap k j false) = structureMap k (next r j) true := by
  intro k _ _ r j hr hj
  have hy := adjacent_y k r j
  have hx := adjacent_x k r j
  have hbase :
      (adjacent k r j).toRingHom.comp (openBase k j false) =
        openBase k (next r j) true := by
    apply RingHom.ext
    intro a
    change adjacent k r j (openBase k j false a) = openBase k (next r j) true a
    simp only [adjacent, RingEquiv.trans_apply]
    rw [torusEquiv_false_C]
    change (torusEquiv k (next r j) true).symm
        (LaurentPolynomial.invert (LaurentPolynomial.C a)) = _
    rw [LaurentPolynomial.invert_C]
    apply (RingEquiv.symm_apply_eq (torusEquiv k (next r j) true)).2
    exact (torusEquiv_true_C k (next r j) a).symm
  refine ⟨hbase, hy, hx, ?_, ?_⟩
  · have hot : adjacent k r j (ot k j false) = ot k (next r j) true := by
      exact DFunLike.congr_fun hbase (PowerSeries.X)
    by_cases hboundary : j + 1 = r
    · have hnext : next r j = 0 := by
        simp [next, hboundary, hr.ne']
      simp only [oz, map_mul, map_pow, hot, hx]
      rw [hnext, ← hboundary]
      simp [pow_succ, mul_assoc]
    · have hlt : j + 1 < r := by omega
      have hnext : next r j = j + 1 := by
        simp [next, Nat.mod_eq_of_lt hlt]
      simp only [oz, map_mul, map_pow, hot, hx]
      rw [hnext]
      simp [hboundary, pow_succ, mul_assoc]
  · change CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (adjacent k r j).toRingHom))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (openBase k j false))) = _
    rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hbase]
    rfl

end ArithmeticThetaIndexedOverlapsR0058
