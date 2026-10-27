import GenericRestrictionProvidersR0065
import GenericAdjacentProvidersR0065

/-! Powered period translation in the actual completed coordinate open. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
universe u
namespace ArithmeticThetaGenericOverlapR0065.Boundary
open ArithmeticThetaCorrectedGammaR0061
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

private lemma finite_shift {R : Type*} [CommRing R]
    (A B : ℕ → R) (w : R) (c M : ℕ) (hc : 0 < c)
    (hzero : B 0 = w * A 0) :
    (∏ l ∈ Finset.range (M + c), A (l + c)) *
      ((∏ l ∈ Finset.range (c - 1), A (c - 1 - l)) *
        (∏ l ∈ Finset.range (M + 1), B l)) =
    w * ((∏ l ∈ Finset.range M, A l) *
      (∏ l ∈ Finset.range M, B (l + 1))) *
      (∏ l ∈ Finset.range (2*c), A (M + l)) := by
  have href : (∏ l ∈ Finset.range (c - 1), A (c - 1 - l)) =
      ∏ l ∈ Finset.range (c - 1), A (l + 1) := by
    rw [← Finset.prod_range_reflect (fun l => A (l + 1)) (c - 1)]
    apply Finset.prod_congr rfl
    intro l hl
    congr 1
    have := Finset.mem_range.mp hl
    omega
  have hjoin : (∏ l ∈ Finset.range (c - 1), A (l + 1)) *
      (∏ l ∈ Finset.range (M + c), A (l + c)) =
      ∏ l ∈ Finset.range (M + 2*c - 1), A (l + 1) := by
    rw [show M + 2*c - 1 = (c - 1) + (M + c) by omega,
      Finset.prod_range_add (fun l => A (l + 1)) (c - 1) (M + c)]
    congr 1
    apply Finset.prod_congr rfl
    intro l _
    congr 1
    omega
  have hall : (∏ l ∈ Finset.range (M + 2*c - 1), A (l + 1)) * A 0 =
      (∏ l ∈ Finset.range M, A l) *
        (∏ l ∈ Finset.range (2*c), A (M + l)) := by
    rw [← Finset.prod_range_succ', show M + 2*c - 1 + 1 = M + 2*c by omega,
      Finset.prod_range_add]
  rw [href, Finset.prod_range_succ' B, hzero]
  calc
    _ = w * (((∏ l ∈ Finset.range (c-1), A (l+1)) *
        (∏ l ∈ Finset.range (M+c), A (l+c))) * A 0) *
        (∏ l ∈ Finset.range M, B (l+1)) := by ring
    _ = _ := by rw [hjoin, hall]; ring

private def pa (k : Type u) [Field k] [CharZero k] (r c j l : ℕ) :
    OpenHat k j true := 1 - boundaryT k j ^ (r*l) * boundaryX k j ^ c
private def pb (k : Type u) [Field k] [CharZero k] (r c j l : ℕ) :
    OpenHat k j true := 1 - boundaryT k j ^ (r*l) * boundaryInv k j ^ c

private lemma powered_zero (k : Type u) [Field k] [CharZero k] (r c j : ℕ) :
    pb k r c j 0 = -boundaryInv k j ^ c * pa k r c j 0 := by
  have h : boundaryX k j ^ c * boundaryInv k j ^ c = 1 := by
    rw [← mul_pow, boundaryX_mul_inv, one_pow]
  simp only [pa, pb, mul_zero, pow_zero, one_mul]
  linear_combination -h

private lemma normalized_left (k : Type u) [Field k] [CharZero k]
    (c j l : ℕ) (hr : 0 < 2*c) (hj : j < 2*c) (hb : j+1 = 2*c) :
    (overlap k (2*c) j hr hj) ((restrict k j false)
      (1 - ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^
        ArithmeticThetaAnnularTorsionPrereqR0053.leftExponent (2*c) c j l *
        ArithmeticThetaAnnularTorsionPrereqR0053.cx k ^ c)) =
      pa k (2*c) c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) (l+c) := by
  simp only [map_sub, map_one, map_mul, map_pow]
  change 1 - (overlap k (2*c) j hr hj) ((restrict k j false) (tau k)) ^
    (2*c*l+c*j) * ((overlap k (2*c) j hr hj) ((restrict k j false) (cx k))) ^ c = _
  rw [overlap_restrict_tau, overlap_restrict_cx, restrict_tau, map_mul, mul_pow]
  change 1 - boundaryT k _ ^ (2*c*l+c*j) *
    (boundaryT k _ ^ c * boundaryX k _ ^ c) = _
  rw [← mul_assoc, ← pow_add]
  have he : 2*c*l+c*j+c = 2*c*(l+c) := by nlinarith [congrArg (c * ·) hb]
  rw [he]
  rfl

private lemma normalized_right_early (k : Type u) [Field k] [CharZero k]
    (c j l : ℕ) (hc : 0 < c) (hr : 0 < 2*c) (hj : j < 2*c)
    (hb : j+1 = 2*c) (hl : l < c-1) :
    (overlap k (2*c) j hr hj) ((restrict k j false)
      (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedRight k (2*c) c j l)) =
      pa k (2*c) c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) (c-1-l) := by
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
  have hbZ : (j : ℤ)+1 = 2*c := by exact_mod_cast hb
  have hlZ : (l : ℤ)+1 < c := by omega
  have he : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l =
      (2*c : ℤ) * ((l : ℤ)+1-c) := by
    simp only [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent, Nat.cast_mul,
      Nat.cast_ofNat]
    rw [hbZ]
    ring
  have hneg : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l < 0 := by
    rw [he]
    exact mul_neg_of_pos_of_neg (by omega) (by omega)
  have heq : (-ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l -
      (c : ℤ)).toNat + c = 2*c*(c-1-l) := by
    rw [he]
    have hlN : ((c-1-l : ℕ) : ℤ) = (c : ℤ)-1-l := by omega
    have hnonneg : 0 ≤ -(2*(c : ℤ)*((l : ℤ)+1-c)) - c := by
      have : (l : ℤ)+1-c ≤ -1 := by omega
      nlinarith
    apply Int.natCast_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg hnonneg, hlN]
    ring
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.normalizedRight, if_pos hneg,
    map_sub, map_one, map_mul, map_pow]
  change 1 - (overlap k (2*c) j hr hj) ((restrict k j false) (tau k)) ^ _ *
    ((overlap k (2*c) j hr hj) ((restrict k j false) (cx k))) ^ c = _
  rw [overlap_restrict_tau, overlap_restrict_cx, restrict_tau, map_mul, mul_pow]
  change 1 - boundaryT k _ ^ _ * (boundaryT k _ ^ c * boundaryX k _ ^ c) = _
  rw [← mul_assoc, ← pow_add, heq]
  rfl

private lemma normalized_right_late (k : Type u) [Field k] [CharZero k]
    (c j l : ℕ) (hc : 0 < c) (hr : 0 < 2*c) (hj : j < 2*c)
    (hb : j+1 = 2*c) :
    (overlap k (2*c) j hr hj) ((restrict k j false)
      (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedRight k (2*c) c j (c-1+l))) =
      pb k (2*c) c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) l := by
  have hbZ : (j : ℤ)+1 = 2*c := by exact_mod_cast hb
  have he : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j (c-1+l) =
      (2*c*l : ℕ) := by
    simp only [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add]
    rw [show ((c-1 : ℕ) : ℤ) = (c : ℤ)-1 by omega, hbZ]
    ring
  have hn : ¬ ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j (c-1+l) < 0 := by
    rw [he]; omega
  rw [ArithmeticThetaAnnularTorsionPrereqR0053.normalizedRight, if_neg hn, he]
  simp only [Int.toNat_natCast, map_sub, map_one, map_mul, map_pow]
  change 1 - (overlap k (2*c) j hr hj) ((restrict k j false) (tau k)) ^ _ *
    ((overlap k (2*c) j hr hj) ((restrict k j false) (cy k))) ^ c = _
  rw [overlap_restrict_tau, overlap_restrict_cy, restrict_tau]
  rfl

private lemma normalized_zero (k : Type u) [Field k] [CharZero k]
    (c j N : ℕ) (hc : 0 < c) :
    restrict k j true (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c 0 N) =
    (∏ l ∈ Finset.range N, pa k (2*c) c j l) *
      (∏ l ∈ Finset.range N, pb k (2*c) c j (l+1)) := by
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial,
    ArithmeticThetaAnnularTorsionPrereqR0053.normalizedFactor, map_prod, map_mul,
    Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro l _
    simp only [ArithmeticThetaAnnularTorsionPrereqR0053.leftExponent, mul_zero, add_zero,
      map_sub, map_one, map_mul, map_pow]
    change 1 - restrict k j true (tau k) ^ (2*c*l) * restrict k j true (cx k) ^ c = _
    rw [restrict_tau, restrict_cx]
    rfl
  · apply Finset.prod_congr rfl
    intro l _
    have he : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c 0 l =
        ((2*c*(l+1)-c : ℕ) : ℤ) := by
      have hle : c ≤ 2*c*(l+1) := by nlinarith
      simp [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent, Nat.cast_sub hle]
    have hn : ¬ ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c 0 l < 0 := by
      rw [he]; omega
    rw [ArithmeticThetaAnnularTorsionPrereqR0053.normalizedRight, if_neg hn, he]
    simp only [Int.toNat_natCast,
      map_sub, map_one, map_mul, map_pow]
    change 1 - restrict k j true (tau k) ^ (2*c*(l+1)-c) * restrict k j true (cy k) ^ c = _
    rw [restrict_tau, restrict_cy]
    change 1 - boundaryT k j ^ (2*c*(l+1)-c) * boundaryY k j ^ c = _
    rw [boundaryY_eq_T_mul_inv, mul_pow, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (by nlinarith : c ≤ 2*c*(l+1))]
    rfl

private lemma normalized_finite_boundary (k : Type u) [Field k] [CharZero k]
    (c j M : ℕ) (hc : 0 < c) (hr : 0 < 2*c) (hj : j < 2*c) (hb : j+1=2*c) :
    overlap k (2*c) j hr hj (restrict k j false
      (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c j (M+c))) =
    -boundaryInv k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) ^ c *
      restrict k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true
        (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c 0 M) *
      (∏ l ∈ Finset.range (2*c),
        pa k (2*c) c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) (M+l)) := by
  rw [normalized_zero k c _ M hc]
  simp only [ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial,
    ArithmeticThetaAnnularTorsionPrereqR0053.normalizedFactor, map_prod, map_mul,
    Finset.prod_mul_distrib]
  have hleft := fun l => normalized_left k c j l hr hj hb
  simp_rw [hleft]
  have hright : (∏ l ∈ Finset.range (M+c), overlap k (2*c) j hr hj
      (restrict k j false (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedRight k (2*c) c j l))) =
    (∏ l ∈ Finset.range (c-1), pa k (2*c) c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) (c-1-l)) *
    (∏ l ∈ Finset.range (M+1), pb k (2*c) c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) l) := by
    rw [show M+c = (c-1)+(M+1) by omega, Finset.prod_range_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro l hl
      exact normalized_right_early k c j l hc hr hj hb (Finset.mem_range.mp hl)
    · apply Finset.prod_congr rfl
      intro l _
      exact normalized_right_late k c j l hc hr hj hb
  rw [hright]
  exact finite_shift _ _ _ c M hc (powered_zero k _ c _)

private def normValue (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hj : j < 2*c) : Chart k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.horizontal k (2*c) c j *
    Classical.choose (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_unit_limit
      k (2*c) c j (by omega) hc (by simp) hcop hj)

private lemma normValue_converges (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6) (hj : j < 2*c) :
    Converges k (2*c) j
      (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c j)
      (normValue k c j hc hcop hj) := by
  intro n
  refine ⟨ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j n, ?_⟩
  intro N hN
  exact ((Classical.choose_spec (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_unit_limit
    k (2*c) c j (by omega) hc (by simp) hcop hj)).1.2 n N hN).2
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


private lemma pa_tail_one (k : Type u) [Field k] [CharZero k]
    (c j n M q : ℕ) (hc : 0 < c) (hM : n ≤ M) :
    1 - (∏ l ∈ Finset.range q, pa k (2*c) c j (M+l)) ∈
      ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.prod_range_succ]
    have ha : 1 - pa k (2*c) c j (M+q) ∈
        ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n := by
      simp only [pa, sub_sub_cancel]
      exact boundaryT_pow_mul_mem k j n _ _ (by nlinarith)
    have hh := (ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n).add_mem ih
      ((ArithmeticThetaIndexedOverlapsR0058.hatPower k j true n).mul_mem_left
        (∏ l ∈ Finset.range q, pa k (2*c) c j (M+l)) ha)
    convert hh using 1 <;> ring

private lemma normalized_boundary (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hr : 0 < 2*c) (hj : j < 2*c) (hb : j+1=2*c) :
    overlap k (2*c) j hr hj (restrict k j false (normValue k c j hc hcop hj)) =
      -boundaryInv k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) ^ c *
      restrict k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true
        (normValue k c 0 hc hcop hr) := by
  have hs := overlap_converges k (2*c) j hr hj _ _ (normValue_converges k c j hc hcop hj)
  have ht := restrict_converges k (2*c) (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true
    _ _ (normValue_converges k c 0 hc hcop hr)
  apply boundary_limit_identity k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j)
    (fun M => overlap k (2*c) j hr hj (restrict k j false
      (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c j (M+c))))
    (fun M => restrict k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true
      (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c 0 M))
    (fun M => ∏ l ∈ Finset.range (2*c), pa k (2*c) c
      (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) (M+l)) (fun _ => 1)
  · intro n
    obtain ⟨N, hN⟩ := hs n
    exact ⟨N, fun M hM => hN (M+c) (by omega)⟩
  · exact ht
  · intro n
    exact ⟨n, fun M hM => pa_tail_one k c _ n M (2*c) (by omega) hM⟩
  · intro n
    exact ⟨0, fun _ _ => by simp⟩
  · intro M
    simpa using normalized_finite_boundary k c j M (by omega) hr hj hb
private lemma chart_domain (k : Type u) [Field k] [CharZero k] :
    IsDomain (Chart k) :=
  (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by omega)).1

private lemma chart_tau_ne_zero (k : Type u) [Field k] [CharZero k] :
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
  have h := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions k 1
    (by omega)).2.2.2.2.1
  simpa [ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t,
    ArithmeticThetaScaledTateBridgeR0046.parameter] using h

private lemma generic_injective (k : Type u) [Field k] [CharZero k] :
    Function.Injective (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k) := by
  letI : IsDomain (Chart k) := chart_domain k
  exact IsLocalization.injective (GenericChart k)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chart_tau_ne_zero k))


private lemma generic_filtration_separated (k : Type u) [Field k] [CharZero k]
    (z : GenericChart k) (hz : ∀ n : ℕ, ∃ f : Chart k,
      f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n ∧ z = ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f) : z = 0 := by
  letI : IsAdicComplete
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k))) (Chart k) := by
    exact (IsAdicComplete.map_algebraMap_iff
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k)).mpr inferInstance
  letI : IsHausdorff
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k))) (Chart k) := hcomp.1
  have hpow (n : ℕ) : ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n =
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k))) ^ n := by
    simp [ArithmeticThetaAnnularTorsionPrereqR0053.filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]
  obtain ⟨a, _, ha⟩ := hz 0
  have hamem (n : ℕ) : a ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n := by
    obtain ⟨f, hf, hz_eq⟩ := hz n
    have heq : a = f := generic_injective k (ha.symm.trans hz_eq)
    exact heq ▸ hf
  have ha0 : a = 0 := by
    apply (IsHausdorff.eq_iff_smodEq
      (I := (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (ArithmeticThetaAnnularTorsionPrereqR0053.Node k) (Chart k))) (M := Chart k)).mpr
    intro n
    rw [SModEq.sub_mem]
    simpa [hpow, smul_eq_mul, Ideal.mul_top] using hamem n
  simpa [ha0] using ha


private lemma powered_eq_normalized (k : Type u) [Field k] [CharZero k]
    (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
    (hζ : IsPrimitiveRoot ζ c) (hj : j < 2*c) :
    powered k c j ζ hc hcop hζ hj =
      ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j
        (ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0) *
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (normValue k c j hc hcop hj) := by
  let C := ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j
    (ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0)
  have hclear := ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_clearing
    k (2*c) c j (by omega) hc (by simp) hcop hj
  have hu : IsUnit C := (hclear.2.1 _).2
  obtain ⟨D, hD⟩ := hu.exists_right_inv
  have hspec := (Classical.choose_spec
    (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_local_divisor
      k (2*c) c j ζ (by omega) hc (by simp) hcop hζ hj)).1.1
  change ∀ n N, ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j n ≤ N →
    ∃ f, f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n ∧
      powered k c j ζ hc hcop hζ hj - ArithmeticThetaAnnularTorsionPrereqR0053.literalPartial k (2*c) c j N =
        ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j N *
          ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f at hspec
  have heq : D * (powered k c j ζ hc hcop hζ hj - C *
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (normValue k c j hc hcop hj)) = 0 := by
    apply generic_filtration_separated k
    intro n
    let N := ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j n
    obtain ⟨f, hf, he⟩ := hspec n N (le_refl _)
    have hn := ((Classical.choose_spec
      (ArithmeticThetaAnnularTorsionPrereqR0053.powered_gamma_unit_limit
        k (2*c) c j (by omega) hc (by simp) hcop hj)).1.2 n N (le_refl _)).2
    change normValue k c j hc hcop hj -
      ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c j N ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n at hn
    have hC : ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j N = C := by
      apply hclear.2.2 N _ _ (le_refl _)
      simp only [N, ArithmeticThetaAnnularTorsionPrereqR0053.cutoff]
      omega
    rw [(hclear.2.1 N).1, hC] at he
    refine ⟨f - (normValue k c j hc hcop hj -
      ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c j N),
      (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).sub_mem hf hn, ?_⟩
    simp only [map_sub]
    calc
      _ = D * (C * (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k f -
          (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (normValue k c j hc hcop hj) -
            ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
              (ArithmeticThetaAnnularTorsionPrereqR0053.normalizedPartial k (2*c) c j N)))) := by
        congr 1
        linear_combination he
      _ = _ := by rw [← mul_assoc, mul_comm D C, hD, one_mul]
  apply sub_eq_zero.mp
  calc
    _ = (C * D) * (powered k c j ζ hc hcop hζ hj - C *
        ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k (normValue k c j hc hcop hj)) := by
      rw [hD, one_mul]
    _ = 0 := by rw [mul_assoc, heq, mul_zero]

private lemma clearing_zero (k : Type u) [Field k] [CharZero k] (c N : ℕ) :
    ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c 0 N = 1 := by
  apply Finset.prod_eq_one
  intro l _
  have hn : ¬ ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c 0 l < 0 := by
    simp only [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]
    nlinarith [mul_nonneg (Int.natCast_nonneg c) (Int.natCast_nonneg l)]
  simp only [if_neg hn]

private lemma clearing_truncate (k : Type u) [Field k] [CharZero k]
    (c j N : ℕ) (hc : 0 < c) (hb : j+1=2*c) (hN : c-1 ≤ N) :
    ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j N =
      ∏ l ∈ Finset.range (c-1),
        -(ArithmeticThetaAnnularTorsionPrereqR0053.tpower k
          (ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l) *
          ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
            (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) ^ c) := by
  have hbZ : (j : ℤ)+1=2*c := by exact_mod_cast hb
  have he (l : ℕ) : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l =
      (2*c : ℤ)*((l : ℤ)+1-c) := by
    simp only [ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent, Nat.cast_mul, Nat.cast_ofNat]
    rw [hbZ]; ring
  have hcut : ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j N =
      ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j (c-1) := by
    unfold ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial
    apply Finset.eventually_constant_prod (N := c-1) _ hN
    intro l hl
    have hn : ¬ ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l < 0 := by
      rw [he]
      have : (0 : ℤ) ≤ (l : ℤ)+1-c := by omega
      exact not_lt_of_ge (mul_nonneg (by positivity) this)
    rw [if_neg hn]
  rw [hcut]
  apply Finset.prod_congr rfl
  intro l hl
  have hn : ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j l < 0 := by
    rw [he]
    have := Finset.mem_range.mp hl
    exact mul_neg_of_pos_of_neg (by exact_mod_cast (by omega : 0<2*c)) (by omega)
  rw [if_pos hn]

private lemma reverse_sum (c : ℕ) (hc : 0<c) :
    (∑ l ∈ Finset.range (c-1), (c-1-l)) = c*(c-1)/2 := by
  have href : (∑ l ∈ Finset.range (c-1), (c-1-l)) =
      ∑ l ∈ Finset.range (c-1), (l+1) := by
    rw [← Finset.sum_range_reflect (fun l => l+1) (c-1)]
    apply Finset.sum_congr rfl
    intro l hl
    have := Finset.mem_range.mp hl
    omega
  rw [href]
  have hs := Finset.sum_range_succ' (fun l : ℕ => l) (c-1)
  simpa [Nat.sub_add_cancel hc, Finset.sum_range_id] using hs.symm

private lemma tpower_cancel (k : Type u) [Field k] [CharZero k]
    (e : ℤ) (n : ℕ) (he : e + (n : ℤ) = 0) :
    ArithmeticThetaAnnularTorsionPrereqR0053.tpower k e *
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ n = 1 := by
  have ht : (ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k : GenericChart k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) := IsUnit.unit_spec _
  rw [← ht]
  change (↑(ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k ^ e) : GenericChart k) *
    (↑(ArithmeticThetaAnnularTorsionPrereqR0053.parameterUnit k) : GenericChart k) ^ n = 1
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul, ← zpow_add, he]
  simp

private lemma clearing_monomial (k : Type u) [Field k] [CharZero k]
    {R : Type*} [CommRing R] (F : GenericChart k →+* R)
    (X Y T : R) (hxy : X*Y=1)
    (hy : F (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = Y)
    (ht : F (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = T)
    (c j N : ℕ) (hc : 0<c) (hb : j+1=2*c) (hN : c-1≤N) :
    F (ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j N) *
      X ^ (c*(c-1)) * T ^ (2*c*(c*(c-1)/2)) = (-1 : R) ^ (c-1) := by
  let e := ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent (2*c) c j
  let a (l : ℕ) := F (-(ArithmeticThetaAnnularTorsionPrereqR0053.tpower k (e l) *
      ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
        (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) ^ c))
  have hf (l : ℕ) (hl : l ∈ Finset.range (c-1)) :
      a l * (X^c * T^(2*c*(c-1-l))) = -1 := by
    have he : e l + ((2*c*(c-1-l) : ℕ) : ℤ) = 0 := by
      have hbZ : (j : ℤ)+1=2*c := by exact_mod_cast hb
      have hl' := Finset.mem_range.mp hl
      dsimp [e, ArithmeticThetaAnnularTorsionPrereqR0053.rightExponent]
      push_cast
      rw [hbZ, show ((c-1-l : ℕ) : ℤ) = (c : ℤ)-1-l by omega]
      ring
    have ht' := congrArg F (tpower_cancel k (e l) (2*c*(c-1-l)) he)
    simp only [map_mul, map_pow, map_one, ht] at ht'
    have hx' : X^c * Y^c=1 := by rw [← mul_pow, hxy, one_pow]
    dsimp [a]
    simp only [map_neg, map_mul, map_pow, hy]
    calc
      _ = -(F (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k (e l)) *
        T ^ (2*c*(c-1-l))) * (X^c * Y^c) := by ring
      _ = -1 := by rw [ht', hx', mul_one]
  have hprod := Finset.prod_congr rfl hf
  have hexp : (∏ l ∈ Finset.range (c-1), X^c * T^(2*c*(c-1-l))) =
      X^(c*(c-1)) * T^(2*c*(c*(c-1)/2)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← pow_mul, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, reverse_sum c hc]
  rw [clearing_truncate k c j N hc hb hN, map_prod]
  change (∏ l ∈ Finset.range (c-1), a l) * X^(c*(c-1)) *
    T^(2*c*(c*(c-1)/2)) = _
  rw [mul_assoc, ← hexp, ← Finset.prod_mul_distrib, hprod]
  simp

private lemma restriction_apply (k : Type u) [Field k] [CharZero k]
    (j : ℕ) (side : Bool) (R : GenericChart k →+* GenericOpen k j side)
    (hR : IsGenericRestriction k j side R) (a : Chart k) :
    R (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k a) =
      includeOpen k j side (restrict k j side a) := RingHom.congr_fun hR a

private lemma adjacent_apply (k : Type u) [Field k] [CharZero k]
    (r j : ℕ) (hr : 0<r) (hj : j<r)
    (R : GenericChart k →+* GenericOpen k j false)
    (E : GenericOpen k j false ≃+* GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next r j) true)
    (hR : IsGenericRestriction k j false R) (hE : IsGenericAdjacent k r j hr hj E)
    (a : Chart k) :
    E (R (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k a)) =
      includeOpen k (ArithmeticThetaIndexedOverlapsR0058.next r j) true
        (overlap k r j hr hj (restrict k j false a)) := by
  rw [restriction_apply k j false R hR]
  exact RingHom.congr_fun hE _

end ArithmeticThetaGenericOverlapR0065.Boundary
namespace ArithmeticThetaGenericOverlapR0065
open Boundary

/-- The literal powered gamma obeys the denominator-cleared period law. -/
theorem powered_period_boundary :
    ∀ (k : Type u) [Field k] [CharZero k]
      (c j : ℕ) (ζ : k) (hc : 1 < c) (hcop : Nat.Coprime c 6)
      (hζ : IsPrimitiveRoot ζ c) (hr : 0 < 2*c) (hj : j < 2*c)
      (hn : (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) < 2*c), j + 1 = 2*c →
      ∀ (RX : ArithmeticThetaGenericOverlapR0065.GenericChart k →+* ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true)
        (RY : ArithmeticThetaGenericOverlapR0065.GenericChart k →+* ArithmeticThetaGenericOverlapR0065.GenericOpen k j false)
        (E : ArithmeticThetaGenericOverlapR0065.GenericOpen k j false ≃+* ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true),
        ArithmeticThetaGenericOverlapR0065.IsGenericRestriction k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true RX →
        ArithmeticThetaGenericOverlapR0065.IsGenericRestriction k j false RY →
        ArithmeticThetaGenericOverlapR0065.IsGenericAdjacent k (2*c) j hr hj E →
        E (RY (ArithmeticThetaGenericOverlapR0065.powered k c j ζ hc hcop hζ hj)) *
          ArithmeticThetaGenericOverlapR0065.openX k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true ^ (c^2) *
          ArithmeticThetaGenericOverlapR0065.openT k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true ^ (2*c*(c*(c-1)/2)) =
          (-1 : ArithmeticThetaGenericOverlapR0065.GenericOpen k (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) true) ^ c * RX (ArithmeticThetaGenericOverlapR0065.powered k c (ArithmeticThetaIndexedOverlapsR0058.next (2*c) j) ζ hc hcop hζ hn) := by
  intro k _ _ c j ζ hc hcop hζ hr hj hn hb RX RY E hRX hRY hE
  let i := ArithmeticThetaIndexedOverlapsR0058.next (2*c) j
  let G := includeOpen k i true
  let F := E.toRingHom.comp RY
  let X := openX k i true
  let T := openT k i true
  let I := G (boundaryInv k i)
  let V := G (ArithmeticThetaCorrectedGammaR0061.restrict k i true
    (normValue k c 0 hc hcop hr))
  let C := F (ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c j
    (ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c j 0))
  have hX : G (boundaryX k i) = X := rfl
  have hT : G (boundaryT k i) = T := rfl
  have hXI : X*I=1 := by
    rw [← hX]
    exact (map_mul G _ _).symm.trans ((congrArg G (boundaryX_mul_inv k i)).trans (map_one G))
  have hcy : F (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) = I := by
    dsimp [F]
    rw [adjacent_apply k (2*c) j hr hj RY E hRY hE]
    change G (ArithmeticThetaCorrectedGammaR0061.overlap k (2*c) j hr hj
      (ArithmeticThetaCorrectedGammaR0061.restrict k j false
        (ArithmeticThetaCorrectedGammaR0061.cy k))) = _
    rw [overlap_restrict_cy]
  have ht : F (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k
      (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = T := by
    dsimp [F]
    rw [adjacent_apply k (2*c) j hr hj RY E hRY hE]
    change G (ArithmeticThetaCorrectedGammaR0061.overlap k (2*c) j hr hj
      (ArithmeticThetaCorrectedGammaR0061.restrict k j false
        (ArithmeticThetaCorrectedGammaR0061.tau k))) = _
    rw [overlap_restrict_tau, restrict_tau]
    rfl
  have hC : C * X^(c*(c-1)) * T^(2*c*(c*(c-1)/2)) = (-1)^(c-1) := by
    exact clearing_monomial k F X I T hXI hcy ht c j _ (by omega) hb (by
      simp only [ArithmeticThetaAnnularTorsionPrereqR0053.cutoff]; omega)
  have hp : E (RY (powered k c j ζ hc hcop hζ hj)) = C * (-(I^c) * V) := by
    rw [powered_eq_normalized, map_mul, map_mul,
      adjacent_apply k (2*c) j hr hj RY E hRY hE,
      normalized_boundary k c j hc hcop hr hj hb, map_mul, map_neg, map_pow]
    rfl
  have hi : i = 0 := boundary_next (2*c) j hb
  have hp0 : RX (powered k c i ζ hc hcop hζ hn) = V := by
    rw [powered_eq_normalized]
    have hclear : ArithmeticThetaAnnularTorsionPrereqR0053.clearingPartial k (2*c) c i
        (ArithmeticThetaAnnularTorsionPrereqR0053.cutoff c i 0) = 1 := by
      rw [hi]; exact clearing_zero k c _
    rw [hclear, one_mul, restriction_apply k i true RX hRX]
    dsimp [V, G]
    congr 2
    simp only [hi]
  change E (RY (powered k c j ζ hc hcop hζ hj)) * X^(c^2) *
    T^(2*c*(c*(c-1)/2)) = (-1)^c * RX (powered k c i ζ hc hcop hζ hn)
  rw [hp, hp0]
  have hexp : c^2=c*(c-1)+c := by nlinarith [Nat.sub_add_cancel (by omega : 1≤c)]
  have hpow : X^c * I^c=1 := by rw [← mul_pow, hXI, one_pow]
  rw [hexp, pow_add]
  calc
    _ = -(C * X^(c*(c-1)) * T^(2*c*(c*(c-1)/2))) * (X^c*I^c) * V := by ring
    _ = -((-1)^(c-1)) * V := by rw [hC, hpow, mul_one]
    _ = (-1)^c * V := by
      congr 1
      have hs := pow_succ (-1 : GenericOpen k i true) (c-1)
      rw [Nat.sub_add_cancel (by omega : 1≤c)] at hs
      simpa using hs.symm
end ArithmeticThetaGenericOverlapR0065
