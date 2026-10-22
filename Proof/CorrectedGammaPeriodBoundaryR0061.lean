module

public import CorrectedGammaDataUniqueR0061
public import CorrectedGammaDefinitionsR0061

@[expose] public section
set_option synthInstance.maxHeartbeats 200000
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

private lemma restrict_spec (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (side : Bool) :
    ArithmeticThetaIndexedOverlapsR0058.IsRestriction k j side
      (restrict k j side) :=
  (Classical.choose_spec
    (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions
      k j side).exists)

private lemma overlap_spec (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    ArithmeticThetaIndexedOverlapsR0058.IsCompletedAdjacent k r j
      (overlap k r j hr hj) :=
  (Classical.choose_spec
    (ArithmeticThetaIndexedOverlapsR0058.completed_indexed_adjacent
      k r j hr hj).exists)

private lemma restrict_tau (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (side : Bool) :
    (restrict k j side) (tau k) =
      ArithmeticThetaIndexedOverlapsR0058.completeOpen k j side
        (ArithmeticThetaIndexedOverlapsR0058.ot k j side) := by
  have h := RingHom.congr_fun (restrict_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.t k 1)
  simpa [tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaIndexedOverlapsR0058.ot,
    ArithmeticThetaIndexedOverlapsR0058.openBase,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    RingHom.comp_apply] using h

private lemma nodeEquiv_x (k : Type u) [Field k] [CharZero k] :
    ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k
      (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
        ArithmeticThetaNodeCharts.x k := by
  unfold ArithmeticThetaIndexedOverlapsR0058.nodeEquiv
    ArithmeticThetaScaledTateBridgeR0046.x ArithmeticThetaNodeCharts.x
    ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal,
    ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private lemma nodeEquiv_y (k : Type u) [Field k] [CharZero k] :
    ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k
      (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
        ArithmeticThetaNodeCharts.y k := by
  unfold ArithmeticThetaIndexedOverlapsR0058.nodeEquiv
    ArithmeticThetaScaledTateBridgeR0046.y ArithmeticThetaNodeCharts.y
    ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal,
    ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private lemma restrict_cx (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (side : Bool) :
    (restrict k j side) (cx k) =
      ArithmeticThetaIndexedOverlapsR0058.completeOpen k j side
        (ArithmeticThetaIndexedOverlapsR0058.ox k j side) := by
  have h := RingHom.congr_fun (restrict_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)
  simpa [cx, ArithmeticThetaScaledAnnularR0050.cx,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    ArithmeticThetaIndexedOverlapsR0058.openMap,
    ArithmeticThetaIndexedOverlapsR0058.ox,
    nodeEquiv_x, RingHom.comp_apply] using h

private lemma restrict_cy (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (side : Bool) :
    (restrict k j side) (cy k) =
      ArithmeticThetaIndexedOverlapsR0058.completeOpen k j side
        (ArithmeticThetaIndexedOverlapsR0058.oy k j side) := by
  have h := RingHom.congr_fun (restrict_spec k j side).1
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)
  simpa [cy, ArithmeticThetaScaledAnnularR0050.cy,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    ArithmeticThetaIndexedOverlapsR0058.openMap,
    ArithmeticThetaIndexedOverlapsR0058.oy,
    nodeEquiv_y, RingHom.comp_apply] using h

private lemma overlap_complete (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) (hj : j < r)
    (z : ArithmeticThetaIndexedOverlapsR0058.Open k j false) :
    (overlap k r j hr hj)
        (ArithmeticThetaIndexedOverlapsR0058.completeOpen k j false z) =
      ArithmeticThetaIndexedOverlapsR0058.completeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j) true
        (ArithmeticThetaIndexedOverlapsR0058.adjacent k r j z) := by
  exact RingHom.congr_fun (overlap_spec k r j hr hj).1 z

private lemma boundary_next (r j : ℕ)
    (hboundary : j + 1 = r) :
    ArithmeticThetaIndexedOverlapsR0058.next r j = 0 := by
  simp [ArithmeticThetaIndexedOverlapsR0058.next, hboundary]

private lemma overlap_restrict_tau (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    (overlap k r j hr hj) ((restrict k j false) (tau k)) =
      (restrict k (ArithmeticThetaIndexedOverlapsR0058.next r j) true) (tau k) := by
  rw [restrict_tau, overlap_complete, restrict_tau]
  congr 1
  exact RingHom.congr_fun
    (ArithmeticThetaIndexedOverlapsR0058.indexed_adjacent_coordinates
      k r j hr hj).1 PowerSeries.X

private lemma overlap_restrict_cx (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    (overlap k r j hr hj) ((restrict k j false) (cx k)) =
      ArithmeticThetaIndexedOverlapsR0058.completeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j) true
        (ArithmeticThetaIndexedOverlapsR0058.ot k
          (ArithmeticThetaIndexedOverlapsR0058.next r j) true *
          ArithmeticThetaIndexedOverlapsR0058.ox k
            (ArithmeticThetaIndexedOverlapsR0058.next r j) true) := by
  rw [restrict_cx, overlap_complete]
  exact congrArg _
    (ArithmeticThetaIndexedOverlapsR0058.indexed_adjacent_coordinates
      k r j hr hj).2.2.1

private lemma overlap_restrict_cy (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    (overlap k r j hr hj) ((restrict k j false) (cy k)) =
      ArithmeticThetaIndexedOverlapsR0058.completeOpen k
        (ArithmeticThetaIndexedOverlapsR0058.next r j) true
        (↑((ArithmeticThetaIndexedOverlapsR0058.xUnit k
          (ArithmeticThetaIndexedOverlapsR0058.next r j))⁻¹)) := by
  rw [restrict_cy, overlap_complete]
  exact congrArg _
    (ArithmeticThetaIndexedOverlapsR0058.indexed_adjacent_coordinates
      k r j hr hj).2.1

private lemma prod_shift {R : Type*} [CommRing R]
    (A : ℕ → R) (N : ℕ) :
    (∏ l ∈ Finset.range N, A (l + 1)) * A 0 =
      (∏ l ∈ Finset.range N, A l) * A N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.prod_range_succ]
      calc
        ((∏ l ∈ Finset.range N, A (l + 1)) * A (N + 1)) * A 0 =
            ((∏ l ∈ Finset.range N, A (l + 1)) * A 0) * A (N + 1) := by ring
        _ = ((∏ l ∈ Finset.range N, A l) * A N) * A (N + 1) := by rw [ih]
        _ = ((∏ l ∈ Finset.range N, A l) * A N) * A (N + 1) := rfl

private lemma boundary_finite_shift {R : Type*} [CommRing R]
    (A B : ℕ → R) (c : R) (hzero : B 0 = c * A 0) (N : ℕ) :
    ((∏ l ∈ Finset.range N, A (l + 1)) *
      (∏ l ∈ Finset.range N, B l)) * B N =
      c * ((∏ l ∈ Finset.range N, A l) *
        (∏ l ∈ Finset.range N, B (l + 1))) * A N := by
  have hA := prod_shift A N
  have hB := prod_shift B N
  calc
    _ = (∏ l ∈ Finset.range N, A (l + 1)) *
        ((∏ l ∈ Finset.range N, B l) * B N) := by ring
    _ = (∏ l ∈ Finset.range N, A (l + 1)) *
        (B 0 * (∏ l ∈ Finset.range N, B (l + 1))) := by rw [← hB]; ring
    _ = c * (((∏ l ∈ Finset.range N, A (l + 1)) * A 0) *
        (∏ l ∈ Finset.range N, B (l + 1))) := by rw [hzero]; ring
    _ = c * (((∏ l ∈ Finset.range N, A l) * A N) *
        (∏ l ∈ Finset.range N, B (l + 1))) := by rw [hA]
    _ = _ := by ring

private lemma node_xy (k : Type u) [Field k] [CharZero k] :
    ArithmeticThetaNodeCharts.x k * ArithmeticThetaNodeCharts.y k =
      ArithmeticThetaNodeCharts.t k := by
  have hr : ArithmeticThetaNodeCharts.quotientMap k
      (ArithmeticThetaNodeCharts.relation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have quotient_C (a : ArithmeticThetaNodeCharts.Base k) :
      ArithmeticThetaNodeCharts.quotientMap k (MvPolynomial.C a) =
        algebraMap (ArithmeticThetaNodeCharts.Base k)
          (ArithmeticThetaNodeCharts.Node k) a := rfl
  have hxy : ArithmeticThetaNodeCharts.quotientMap k (MvPolynomial.X 0) *
      ArithmeticThetaNodeCharts.quotientMap k (MvPolynomial.X 1) =
      ArithmeticThetaNodeCharts.quotientMap k
        (MvPolynomial.C (ArithmeticThetaNodeCharts.parameter k)) := by
    apply sub_eq_zero.mp
    simpa [ArithmeticThetaNodeCharts.relation, map_sub, map_mul] using hr
  rw [quotient_C] at hxy
  simpa [ArithmeticThetaNodeCharts.x, ArithmeticThetaNodeCharts.y,
    ArithmeticThetaNodeCharts.t, ArithmeticThetaNodeCharts.parameter,
    ArithmeticThetaNodeCharts.quotientMap] using hxy

private lemma nodeEquiv_t (k : Type u) [Field k] [CharZero k] :
    ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X) =
        ArithmeticThetaNodeCharts.t k := by
  have hrel : ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal,
      ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter]
  have h := (Ideal.quotientEquivAlgOfEq
    (ArithmeticThetaNodeCharts.Base k) hrel).commutes PowerSeries.X
  simpa [ArithmeticThetaIndexedOverlapsR0058.nodeEquiv,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase,
    ArithmeticThetaNodeCharts.t, ArithmeticThetaNodeCharts.parameter] using h

private lemma open_xy (k : Type u) [Field k] [CharZero k] (j : ℕ) :
    ArithmeticThetaIndexedOverlapsR0058.ox k j true *
      ArithmeticThetaIndexedOverlapsR0058.oy k j true =
      ArithmeticThetaIndexedOverlapsR0058.ot k j true := by
  have h := congrArg
    (algebraMap (ArithmeticThetaIndexedOverlapsR0058.Node k j)
      (ArithmeticThetaIndexedOverlapsR0058.Open k j true)) (node_xy k)
  simpa [ArithmeticThetaIndexedOverlapsR0058.ox,
    ArithmeticThetaIndexedOverlapsR0058.oy,
    ArithmeticThetaIndexedOverlapsR0058.ot,
    ArithmeticThetaIndexedOverlapsR0058.openBase,
    ArithmeticThetaIndexedOverlapsR0058.openMap,
    nodeEquiv_t,
    ArithmeticThetaNodeCharts.t, ArithmeticThetaNodeCharts.parameter,
    map_mul] using h

private abbrev boundaryX (k : Type u) [Field k] [CharZero k] (j : ℕ) :
    OpenHat k j true :=
  ArithmeticThetaIndexedOverlapsR0058.completeOpen k j true
    (ArithmeticThetaIndexedOverlapsR0058.ox k j true)

private abbrev boundaryY (k : Type u) [Field k] [CharZero k] (j : ℕ) :
    OpenHat k j true :=
  ArithmeticThetaIndexedOverlapsR0058.completeOpen k j true
    (ArithmeticThetaIndexedOverlapsR0058.oy k j true)

private abbrev boundaryT (k : Type u) [Field k] [CharZero k] (j : ℕ) :
    OpenHat k j true :=
  ArithmeticThetaIndexedOverlapsR0058.completeOpen k j true
    (ArithmeticThetaIndexedOverlapsR0058.ot k j true)

private abbrev boundaryInv (k : Type u) [Field k] [CharZero k] (j : ℕ) :
    OpenHat k j true :=
  ArithmeticThetaIndexedOverlapsR0058.completeOpen k j true
    (↑((ArithmeticThetaIndexedOverlapsR0058.xUnit k j)⁻¹))

private lemma boundaryX_mul_inv (k : Type u) [Field k] [CharZero k]
    (j : ℕ) : boundaryX k j * boundaryInv k j = 1 := by
  have hu : (ArithmeticThetaIndexedOverlapsR0058.xUnit k j :
      ArithmeticThetaIndexedOverlapsR0058.Open k j true) =
      ArithmeticThetaIndexedOverlapsR0058.ox k j true := IsUnit.unit_spec _
  change ArithmeticThetaIndexedOverlapsR0058.completeOpen k j true _ *
    ArithmeticThetaIndexedOverlapsR0058.completeOpen k j true _ = 1
  rw [← map_mul, ← hu]
  simp

private lemma boundaryY_eq_T_mul_inv (k : Type u) [Field k] [CharZero k]
    (j : ℕ) : boundaryY k j = boundaryT k j * boundaryInv k j := by
  have hxy : boundaryX k j * boundaryY k j = boundaryT k j := by
    unfold boundaryX boundaryY boundaryT
    rw [← map_mul, open_xy]
  have hunit := boundaryX_mul_inv k j
  calc
    boundaryY k j = (boundaryX k j * boundaryInv k j) *
        boundaryY k j := by rw [hunit]; ring
    _ = (boundaryX k j * boundaryY k j) * boundaryInv k j := by ring
    _ = boundaryT k j * boundaryInv k j := by rw [hxy]

private lemma boundary_zero_factor (k : Type u) [Field k] [CharZero k]
    (j : ℕ) :
    1 - boundaryInv k j =
      -boundaryInv k j * (1 - boundaryX k j) := by
  have hunit := boundaryX_mul_inv k j
  calc
    1 - boundaryInv k j =
      boundaryX k j * boundaryInv k j - boundaryInv k j := by rw [hunit]
    _ = -boundaryInv k j * (1 - boundaryX k j) := by ring

private def boundaryA (k : Type u) [Field k] [CharZero k]
    (r j l : ℕ) : OpenHat k j true :=
  1 - boundaryT k j ^ (r * l) * boundaryX k j

private def boundaryB (k : Type u) [Field k] [CharZero k]
    (r j l : ℕ) : OpenHat k j true :=
  1 - boundaryT k j ^ (r * l) * boundaryInv k j

private lemma overlap_leftFactor (k : Type u) [Field k] [CharZero k]
    (r j l : ℕ) (hr : 0 < r) (hj : j < r)
    (hboundary : j + 1 = r) :
    (overlap k r j hr hj)
        ((restrict k j false) (leftFactor k r j l)) =
      boundaryA k r (ArithmeticThetaIndexedOverlapsR0058.next r j) (l + 1) := by
  have hexp : r * l + j + 1 = r * (l + 1) := by
    simp only [Nat.mul_add, mul_one]
    omega
  simp only [leftFactor, leftExponent, boundaryA, map_sub, map_one,
    map_mul, map_pow]
  rw [overlap_restrict_tau k r j hr hj, overlap_restrict_cx k r j hr hj]
  rw [map_mul]
  rw [restrict_tau k (ArithmeticThetaIndexedOverlapsR0058.next r j) true]
  change 1 - boundaryT k _ ^ (r * l + j) *
      (boundaryT k _ * boundaryX k _) =
    1 - boundaryT k _ ^ (r * (l + 1)) * boundaryX k _
  rw [← mul_assoc, ← pow_succ, hexp]

private lemma overlap_rightFactor (k : Type u) [Field k] [CharZero k]
    (r j l : ℕ) (hr : 0 < r) (hj : j < r)
    (hboundary : j + 1 = r) :
    (overlap k r j hr hj)
        ((restrict k j false) (rightFactor k r j (l + 1))) =
      boundaryB k r (ArithmeticThetaIndexedOverlapsR0058.next r j) l := by
  have hexp : r * (l + 1) - j - 1 = r * l := by
    simp only [Nat.mul_add, mul_one]
    omega
  simp only [rightFactor, rightExponent, boundaryB, map_sub, map_one,
    map_mul, map_pow]
  rw [overlap_restrict_tau k r j hr hj, overlap_restrict_cy k r j hr hj]
  rw [restrict_tau k (ArithmeticThetaIndexedOverlapsR0058.next r j) true]
  change 1 - boundaryT k _ ^ (r * (l + 1) - j - 1) * boundaryInv k _ =
    1 - boundaryT k _ ^ (r * l) * boundaryInv k _
  rw [hexp]

private lemma restrict_leftFactor_zero (k : Type u) [Field k] [CharZero k]
    (r j l : ℕ) :
    (restrict k j true) (leftFactor k r 0 l) = boundaryA k r j l := by
  simp only [leftFactor, leftExponent, boundaryA, map_sub, map_one,
    map_mul, map_pow, add_zero]
  rw [restrict_tau, restrict_cx]

private lemma restrict_rightFactor_zero (k : Type u) [Field k] [CharZero k]
    (r j l : ℕ) (hr : 0 < r) :
    (restrict k j true) (rightFactor k r 0 (l + 1)) =
      boundaryB k r j (l + 1) := by
  have hpos : 0 < r * (l + 1) := Nat.mul_pos hr (by omega)
  have hexp : r * (l + 1) - 0 - 1 + 1 = r * (l + 1) := by omega
  simp only [rightFactor, rightExponent, boundaryB, map_sub, map_one,
    map_mul, map_pow]
  rw [restrict_tau, restrict_cy]
  change 1 - boundaryT k j ^ (r * (l + 1) - 0 - 1) * boundaryY k j = _
  rw [boundaryY_eq_T_mul_inv]
  change 1 - boundaryT k j ^ (r * (l + 1) - 0 - 1) *
      (boundaryT k j * boundaryInv k j) =
    1 - boundaryT k j ^ (r * (l + 1)) * boundaryInv k j
  rw [← mul_assoc, ← pow_succ, hexp]

private lemma overlap_fullPartial (k : Type u) [Field k] [CharZero k]
    (r j N : ℕ) (hr : 0 < r) (hj : j < r)
    (hboundary : j + 1 = r) :
    (overlap k r j hr hj)
        ((restrict k j false) (fullPartial k r j N)) =
      (∏ l ∈ Finset.range N,
        boundaryA k r (ArithmeticThetaIndexedOverlapsR0058.next r j) (l + 1)) *
      (∏ l ∈ Finset.range N,
        boundaryB k r (ArithmeticThetaIndexedOverlapsR0058.next r j) l) := by
  simp only [fullPartial, leftPartial, rightPartial, map_mul, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro l _
    exact overlap_leftFactor k r j l hr hj hboundary
  · apply Finset.prod_congr rfl
    intro l _
    exact overlap_rightFactor k r j l hr hj hboundary

private lemma restrict_fullPartial_zero (k : Type u) [Field k] [CharZero k]
    (r j N : ℕ) (hr : 0 < r) :
    (restrict k j true) (fullPartial k r 0 N) =
      (∏ l ∈ Finset.range N, boundaryA k r j l) *
      (∏ l ∈ Finset.range N, boundaryB k r j (l + 1)) := by
  simp only [fullPartial, leftPartial, rightPartial, map_mul, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro l _
    exact restrict_leftFactor_zero k r j l
  · apply Finset.prod_congr rfl
    intro l _
    exact restrict_rightFactor_zero k r j l hr

private lemma finite_boundary_identity (k : Type u) [Field k] [CharZero k]
    (r j N : ℕ) (hr : 0 < r) (hj : j < r)
    (hboundary : j + 1 = r) :
    (overlap k r j hr hj)
        ((restrict k j false) (fullPartial k r j N)) *
        boundaryB k r (ArithmeticThetaIndexedOverlapsR0058.next r j) N =
      -boundaryInv k (ArithmeticThetaIndexedOverlapsR0058.next r j) *
        (restrict k (ArithmeticThetaIndexedOverlapsR0058.next r j) true)
          (fullPartial k r 0 N) *
        boundaryA k r (ArithmeticThetaIndexedOverlapsR0058.next r j) N := by
  rw [overlap_fullPartial k r j N hr hj hboundary,
    restrict_fullPartial_zero k r
      (ArithmeticThetaIndexedOverlapsR0058.next r j) N hr]
  exact boundary_finite_shift
    (boundaryA k r (ArithmeticThetaIndexedOverlapsR0058.next r j))
    (boundaryB k r (ArithmeticThetaIndexedOverlapsR0058.next r j))
    (-boundaryInv k (ArithmeticThetaIndexedOverlapsR0058.next r j))
    (by
      simpa [boundaryA, boundaryB] using
        (boundary_zero_factor k
          (ArithmeticThetaIndexedOverlapsR0058.next r j))) N

private lemma boundaryT_pow_mul_mem (k : Type u) [Field k] [CharZero k]
    (j n e : ℕ) (z : OpenHat k j true) (h : n ≤ e) :
    boundaryT k j ^ e * z ∈
      ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n := by
  rw [show e = n + (e - n) by omega, pow_add]
  rw [mul_assoc]
  change (boundaryT k j ^ n) * (boundaryT k j ^ (e - n) * z) ∈
    (Ideal.span {boundaryT k j}) ^ n
  rw [Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private lemma boundaryA_tends_one (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) :
    ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 - boundaryA k r j N ∈
        ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n := by
  intro n
  refine ⟨n, ?_⟩
  intro N hN
  have hexp : n ≤ r * N := by
    calc
      n ≤ N := hN
      _ = 1 * N := by simp
      _ ≤ r * N := Nat.mul_le_mul_right N hr
  have hmem := boundaryT_pow_mul_mem k j n (r * N) (boundaryX k j) hexp
  convert hmem using 1 <;> simp [boundaryA]

private lemma boundaryB_tends_one (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) :
    ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 - boundaryB k r j N ∈
        ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n := by
  intro n
  refine ⟨n, ?_⟩
  intro N hN
  have hexp : n ≤ r * N := by
    calc
      n ≤ N := hN
      _ = 1 * N := by simp
      _ ≤ r * N := Nat.mul_le_mul_right N hr
  have hmem := boundaryT_pow_mul_mem k j n (r * N) (boundaryInv k j) hexp
  convert hmem using 1 <;> simp [boundaryB]

private lemma restrict_converges (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (side : Bool) (s : ℕ → Chart k) (v : Chart k)
    (hv : Converges k r j s v) :
    ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (restrict k j side) v - (restrict k j side) (s N) ∈
        ArithmeticThetaIndexedOverlapsR0058.hatPower k j side n := by
  intro n
  obtain ⟨N₀, hN₀⟩ := hv n
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [← map_sub]
  exact (restrict_spec k j side).2 n (v - s N) (hN₀ N hN)

private lemma overlap_converges (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0 < r) (hj : j < r)
    (s : ℕ → Chart k) (v : Chart k)
    (hv : Converges k r j s v) :
    ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (overlap k r j hr hj) ((restrict k j false) v) -
          (overlap k r j hr hj) ((restrict k j false) (s N)) ∈
        ArithmeticThetaIndexedOverlapsR0058.hatPower k
          (ArithmeticThetaIndexedOverlapsR0058.next r j) true n := by
  intro n
  obtain ⟨N₀, hN₀⟩ := restrict_converges k r j false s v hv n
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [← map_sub]
  exact (overlap_spec k r j hr hj).2.1 n _ (hN₀ N hN)

private lemma boundary_limit_identity (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (s t A B : ℕ → OpenHat k j true)
    (a b c : OpenHat k j true)
    (hs : ∀ n, ∃ N₀, ∀ N, N₀ ≤ N →
      a - s N ∈ ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n)
    (ht : ∀ n, ∃ N₀, ∀ N, N₀ ≤ N →
      b - t N ∈ ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n)
    (hA : ∀ n, ∃ N₀, ∀ N, N₀ ≤ N →
      1 - A N ∈ ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n)
    (hB : ∀ n, ∃ N₀, ∀ N, N₀ ≤ N →
      1 - B N ∈ ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n)
    (hfin : ∀ N, s N * B N = c * t N * A N) : a = c * b := by
  let I := (ArithmeticThetaIndexedOverlapsR0058.openIdeal k j true).map
    (algebraMap (ArithmeticThetaIndexedOverlapsR0058.Open k j true)
      (OpenHat k j true))
  have hcomp : IsAdicComplete I (OpenHat k j true) := by
    exact (IsAdicComplete.map_algebraMap_iff
      (ArithmeticThetaIndexedOverlapsR0058.openIdeal k j true)
      (OpenHat k j true)).mpr
        (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))
  letI : IsHausdorff I (OpenHat k j true) := hcomp.1
  have hpow (n : ℕ) :
      ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n = I ^ n := by
    simp [I, ArithmeticThetaIndexedOverlapsR0058.hatPower,
      ArithmeticThetaIndexedOverlapsR0058.openIdeal, Ideal.map_span,
      ArithmeticThetaIndexedOverlapsR0058.completeOpen]
  apply (IsHausdorff.eq_iff_smodEq (I := I) (M := OpenHat k j true)).mpr
  intro n
  rw [SModEq.sub_mem]
  obtain ⟨Ns, hNs⟩ := hs n
  obtain ⟨Nt, hNt⟩ := ht n
  obtain ⟨Na, hNa⟩ := hA n
  obtain ⟨Nb, hNb⟩ := hB n
  let N := max (max Ns Nt) (max Na Nb)
  have hs' : a - s N ∈ I ^ n := by
    rw [← hpow]
    exact hNs N (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have ht' : b - t N ∈ I ^ n := by
    rw [← hpow]
    exact hNt N (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have hA' : 1 - A N ∈ I ^ n := by
    rw [← hpow]
    exact hNa N (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hB' : 1 - B N ∈ I ^ n := by
    rw [← hpow]
    exact hNb N (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have h₁ : (a - s N) * B N ∈ I ^ n := (I ^ n).mul_mem_right _ hs'
  have h₂ : a * (1 - B N) ∈ I ^ n := (I ^ n).mul_mem_left _ hB'
  have ht'' : t N - b ∈ I ^ n := by simpa only [neg_sub] using (I ^ n).neg_mem ht'
  have hA'' : A N - 1 ∈ I ^ n := by simpa only [neg_sub] using (I ^ n).neg_mem hA'
  have h₃ : c * ((t N - b) * A N) ∈ I ^ n :=
    (I ^ n).mul_mem_left _ ((I ^ n).mul_mem_right _ ht'')
  have h₄ : c * (b * (A N - 1)) ∈ I ^ n :=
    (I ^ n).mul_mem_left _ ((I ^ n).mul_mem_left _ hA'')
  have heq : a - c * b = (a - s N) * B N + a * (1 - B N) +
      c * ((t N - b) * A N) + c * (b * (A N - 1)) := by
    calc
      a - c * b = (a - s N * B N) + (c * t N * A N - c * b) := by
        rw [← hfin N]
        ring
      _ = _ := by ring
  rw [heq]
  simpa [smul_eq_mul, Ideal.mul_top] using
    (I ^ n).add_mem ((I ^ n).add_mem ((I ^ n).add_mem h₁ h₂) h₃) h₄

theorem gamma_period_boundary :
    ∀ (k : Type u) [Field k] [CharZero k] (r j : ℕ),
      (hr : 0 < r) → (hj : j < r) → (hboundary : j + 1 = r) →
      ∀ (v u v' u' : Chart k), IsGammaData k r j v u →
        IsGammaData k r (ArithmeticThetaIndexedOverlapsR0058.next r j) v' u' →
        (overlap k r j hr hj) ((restrict k j false) u) =
          -(ArithmeticThetaIndexedOverlapsR0058.completeOpen k
              (ArithmeticThetaIndexedOverlapsR0058.next r j) true
              (↑((xUnit k (ArithmeticThetaIndexedOverlapsR0058.next r j))⁻¹))) *
            (restrict k (ArithmeticThetaIndexedOverlapsR0058.next r j) true) u' := by
  intro k _ _ r j hr hj hboundary v u v' u' hdata hdata'
  have hs := overlap_converges k r j hr hj (fullPartial k r j) u hdata.2.2.1
  have ht := restrict_converges k r
    (ArithmeticThetaIndexedOverlapsR0058.next r j) true
    (fullPartial k r 0) u' (by simpa [boundary_next r j hboundary] using hdata'.2.2.1)
  exact boundary_limit_identity k
    (ArithmeticThetaIndexedOverlapsR0058.next r j)
    (fun N => (overlap k r j hr hj)
      ((restrict k j false) (fullPartial k r j N)))
    (fun N => (restrict k (ArithmeticThetaIndexedOverlapsR0058.next r j) true)
      (fullPartial k r 0 N))
    (boundaryA k r (ArithmeticThetaIndexedOverlapsR0058.next r j))
    (boundaryB k r (ArithmeticThetaIndexedOverlapsR0058.next r j))
    ((overlap k r j hr hj) ((restrict k j false) u))
    ((restrict k (ArithmeticThetaIndexedOverlapsR0058.next r j) true) u')
    (-boundaryInv k (ArithmeticThetaIndexedOverlapsR0058.next r j))
    hs ht
    (boundaryA_tends_one k r _ hr)
    (boundaryB_tends_one k r _ hr)
    (fun N => finite_boundary_identity k r j N hr hj hboundary)

end ArithmeticThetaCorrectedGammaR0061
