import IdentityThetaSectionsDefinitionsR0138
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.TorsionFree
/-! Literal completed theta numerators for the single identity equation.
The proof first combines the full theta and gamma overlap identities without
inverting horizontal factors, then transports the result through the frozen
completion comparisons. Approximation also proves every truncation equation.
All implementation names are private or in this module's own namespace. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138.ThetaNumeratorCompatibility
namespace Uniform
open ArithmeticThetaAnnularThetaR0128 ArithmeticThetaIndexedOverlapsR0058
variable (k : Type u) [Field k] [CharZero k]
private lemma restriction_base (j : ℕ) (s : Bool) (w : PowerSeries k) :
    restriction k j s (ArithmeticThetaAnnularTorsionPrereqR0053.base k w) =
      completeOpen k j s (openBase k j s w) :=
  RingHom.congr_fun (Classical.choose_spec
    (completed_coordinate_restrictions k j s).exists).1
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k w)

private lemma interior_base (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m)
    (w : PowerSeries k) :
    interiorAdjacent k m hm j hj
      (restriction k j false (ArithmeticThetaAnnularTorsionPrereqR0053.base k w)) =
    restriction k (j+1) true (ArithmeticThetaAnnularTorsionPrereqR0053.base k w) := by
  have he : interiorAdjacent k m hm j hj = adjacent k m hm j (by omega) := by
    dsimp only [interiorAdjacent]
    apply eq_of_heq
    exact eqRec_heq_iff.mpr HEq.rfl
  rw [restriction_base, restriction_base, he]
  have h := RingHom.congr_fun (Classical.choose_spec
    (completed_indexed_adjacent k (2*m) j (by omega) (by omega)).exists).1
    (openBase k j false w)
  change adjacent k m hm j (by omega) _ = _ at h
  apply h.trans
  exact congrArg (completeOpen k (j+1) true)
    (RingHom.congr_fun (indexed_adjacent_coordinates k (2*m) j (by omega) (by omega)).1 w)

private lemma boundary_base (m : ℕ) (hm : 0 < m) (w : PowerSeries k) :
    boundaryAdjacent k m hm
      (restriction k (lastIndex m hm).val false (ArithmeticThetaAnnularTorsionPrereqR0053.base k w)) =
    restriction k 0 true (ArithmeticThetaAnnularTorsionPrereqR0053.base k w) := by
  have he : boundaryAdjacent k m hm = adjacent k m hm (lastIndex m hm).val
      (lastIndex m hm).isLt := by
    dsimp only [boundaryAdjacent]
    apply eq_of_heq
    exact eqRec_heq_iff.mpr HEq.rfl
  rw [restriction_base, restriction_base, he]
  have h := RingHom.congr_fun (Classical.choose_spec
    (completed_indexed_adjacent k (2*m) (lastIndex m hm).val (by omega)
      (lastIndex m hm).isLt).exists).1 (openBase k (lastIndex m hm).val false w)
  change adjacent k m hm (lastIndex m hm).val (lastIndex m hm).isLt _ = _ at h
  apply h.trans
  exact congrArg (completeOpen k 0 true)
    (RingHom.congr_fun (indexed_adjacent_coordinates k (2*m) (lastIndex m hm).val
      (by omega) (lastIndex m hm).isLt).1 w)

set_option backward.isDefEq.respectTransparency true in
private lemma target_regular (j : ℕ) (n : ℕ) :
    Function.Injective (fun x : OpenHat k j true => targetT k j ^ n * x) := by
  letI : IsDomain (Open k j true) :=
    Function.Injective.isDomain (torusEquiv k j true).toRingHom (torusEquiv k j true).injective
  letI : IsNoetherianRing (ArithmeticThetaNodeCharts.Torus k) :=
    IsLocalization.isNoetherianRing
      (Submonoid.powers (Polynomial.X : Polynomial (PowerSeries k))) _ inferInstance
  letI : IsNoetherianRing (Open k j true) :=
    isNoetherianRing_of_ringEquiv (ArithmeticThetaNodeCharts.Torus k)
      (torusEquiv k j true).symm
  have ht : ot k j true ≠ 0 := by
    intro hzero
    have he := (Classical.choose_spec
      (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1).1
    have h := congrArg (fun f => f (MvPolynomial.C (PowerSeries.X : PowerSeries k))) he
    have hv : torusEquiv k j true (ot k j true) = LaurentPolynomial.C PowerSeries.X := by
      change (Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1)
        ((ArithmeticThetaNodeCharts.toXChart k)
          ((ArithmeticThetaNodeCharts.quotientMap k) (MvPolynomial.C PowerSeries.X))) = _
      simpa [ArithmeticThetaNodeCharts.torusMap, RingHom.comp_apply] using h
    rw [hzero, map_zero] at hv
    have hh := congrArg (fun p : LaurentPolynomial (PowerSeries k) => p.coeff 0) hv
    exact (PowerSeries.X_ne_zero (R := k)) (by simpa using hh.symm)
  have hr := Module.Flat.isSMulRegular_of_isRegular
    (M := OpenHat k j true) (IsRegular.of_ne_zero (pow_ne_zero n ht))
  have he : targetT k j = completeOpen k j true (ot k j true) :=
    restriction_base k j true PowerSeries.X
  simpa only [IsSMulRegular, he, ← map_pow, completeOpen, Algebra.smul_def] using hr

private lemma shift_le (m j : ℕ) (hj : j < 2*m) : shift j ≤ commonShift m := by
  dsimp [shift, ArithmeticThetaScaledAnnularR0050.thetaShift, commonShift]
  nlinarith

private lemma normalize_equation {R : Type*} [CommRing R] (t x y : R)
    (C a b : ℕ) (ha : a ≤ C) (hb : b ≤ C)
    (hc : Function.Injective (fun z : R => t^(a+b)*z))
    (h : t^b*x = t^a*y) : t^(C-a)*x = t^(C-b)*y := by
  apply hc
  have he := congrArg (fun z => t^C*z) h
  simp only [← mul_assoc, ← pow_add] at he ⊢
  rw [show a+b+(C-a) = C+b by omega, show a+b+(C-b) = C+a by omega]
  exact he

theorem uniform_compatible (m : ℕ) [NeZero m] (he : Even m)
    (w : Fin m → PowerSeries k) :
    UniformCompatible k m (NeZero.pos m) (uniformSection k m (NeZero.pos m) he w) := by
  classical
  have hi (j : ℕ) (hj : j+1 < 2*m) :
      InteriorEquation k m (NeZero.pos m) j hj
        (combine k m (NeZero.pos m) he j w)
        (combine k m (NeZero.pos m) he (j+1) w) := by
    unfold InteriorEquation combine
    simp only [map_sum, map_mul, interior_base, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    have h := annular_theta_interior k m he j hj ν
    unfold InteriorEquation at h
    rw [mul_left_comm, h, mul_left_comm]
  have hp : PeriodEquation k m (NeZero.pos m)
      (combine k m (NeZero.pos m) he (lastIndex m (NeZero.pos m)).val w)
      (combine k m (NeZero.pos m) he 0 w) := by
    unfold PeriodEquation combine
    simp only [map_sum, map_mul, boundary_base, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    have h := annular_theta_period k m he ν
    unfold PeriodEquation at h
    rw [mul_left_comm, h, mul_left_comm]
  have hit (j : ℕ) (hj : j+1 < 2*m) :
      interiorAdjacent k m (NeZero.pos m) j hj
        (restriction k j false (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) =
      targetT k (j+1) := interior_base k m (NeZero.pos m) j hj PowerSeries.X
  have hbt : boundaryAdjacent k m (NeZero.pos m)
      (restriction k (lastIndex m (NeZero.pos m)).val false
        (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)) = targetT k 0 :=
    boundary_base k m (NeZero.pos m) PowerSeries.X
  constructor
  · intro j hj
    simp only [uniformSection, map_mul, map_pow, hit]
    exact normalize_equation _ _ _ (commonShift m) (shift j.val) (shift (j.val+1))
      (shift_le m j.val j.isLt) (shift_le m (j.val+1) hj)
      (target_regular k (j.val+1) _) (hi j.val hj)
  · simp only [uniformSection, map_mul, map_pow, hbt]
    have h := normalize_equation (targetT k 0)
      (targetT k 0 ^ (m*m) * targetX k 0 ^ m *
        boundaryAdjacent k m (NeZero.pos m)
          (restriction k (lastIndex m (NeZero.pos m)).val false
            (combine k m (NeZero.pos m) he (lastIndex m (NeZero.pos m)).val w)))
      (restriction k 0 true (combine k m (NeZero.pos m) he 0 w))
      (commonShift m) (shift (lastIndex m (NeZero.pos m)).val) (shift 0)
      (shift_le m _ (lastIndex m (NeZero.pos m)).isLt)
      (shift_le m 0 (by have := NeZero.pos m; omega)) (target_regular k 0 _) ?_
    · convert h using 1 <;> dsimp only [firstIndex, targetT] <;> ring
    · simpa only [PeriodEquation, pow_add, mul_assoc] using hp

end Uniform
namespace Gamma
open ArithmeticThetaCorrectedGammaR0061 ArithmeticThetaIndexedOverlapsR0058
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

theorem transported_coordinates (r j : ℕ) (hr : 0 < r) (hj : j < r) :
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

end Gamma

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaCorrectedGammaR0061
open ArithmeticThetaAnnularThetaR0128
variable (k : Type u) [Field k] [CharZero k]

private theorem tail_data (r : ℕ) (hr : 0 < r) (i : Fin r) :
    IsGammaData k r i.val (gammaTail k r hr i)
      (ArithmeticThetaCorrectedGammaR0061.horizontal k r i.val * gammaTail k r hr i) := by
  have hv := Classical.choose_spec (gamma_tail_exists k r i.val hr i.isLt)
  have hvv : (gammaTail k r hr i : Hat k) =
      Classical.choose (gamma_tail_exists k r i.val hr i.isLt) := IsUnit.unit_spec _
  rw [hvv]
  refine ⟨hv.1, hv.2, ?_, rfl⟩
  intro n
  obtain ⟨N₀, hN₀⟩ := hv.2 n
  refine ⟨N₀+1, ?_⟩
  intro N hN
  rw [gamma_finite_factorization k r i.val N hr i.isLt (by omega), ← mul_sub]
  exact (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).mul_mem_left _
    (hN₀ N (by omega))

private lemma clear_units {R : Type*} [CommRing R] (a b A B : R) (u v : Rˣ) (m : ℕ)
    (h : A * (b * v)^m = B * (a * u)^m) :
    (A * (↑u⁻¹ : R)^m) * b^m = (B * (↑v⁻¹ : R)^m) * a^m := by
  apply (u^m * v^m).isUnit.mul_left_cancel
  change ((u : R)^m * (v : R)^m) * _ = ((u : R)^m * (v : R)^m) * _
  calc
    _ = (A * (b * v)^m) * ((u : R) * ↑u⁻¹)^m := by simp only [mul_pow]; ring
    _ = (B * (a * u)^m) * ((v : R) * ↑v⁻¹)^m := by simp only [Units.mul_inv, one_pow, mul_one]; exact h
    _ = _ := by simp only [mul_pow]; ring

private def weighted (m : ℕ) (hm : 0 < m) (he : Even m)
    (w : Fin m → PowerSeries k) (i : Fin (2*m)) : Hat k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (i.val * (m/2)) *
    ArithmeticThetaAnnularTorsionPrereqR0053.cx k ^ (m/2) *
    uniformSection k m hm he w i

private lemma completed_cross (m : ℕ) (hm : 0 < m) (he : Even m)
    (w : Fin m → PowerSeries k) (i : Fin (2*m)) :
    let j := ArithmeticThetaInfinitesimalPolygonR0129.next (2*m) (by omega) i
    let F : Hat k →+* HatOpen k true := (overlap k (2*m) i.val (by omega) i.isLt).toRingHom.comp (restrict k i.val false)
    let G : Hat k →+* HatOpen k true := restrict k j.val true
    F (weighted k m hm he w i) *
      (G (ArithmeticThetaCorrectedGammaR0061.horizontal k (2*m) j.val * gammaTail k (2*m) (by omega) j))^m =
    G (weighted k m hm he w j) *
      (F (ArithmeticThetaCorrectedGammaR0061.horizontal k (2*m) i.val * gammaTail k (2*m) (by omega) i))^m := by
  classical
  letI : NeZero m := ⟨by omega⟩
  dsimp only
  let j := ArithmeticThetaInfinitesimalPolygonR0129.next (2*m) (by omega) i
  let F : Hat k →+* HatOpen k true := (overlap k (2*m) i.val (by omega) i.isLt).toRingHom.comp (restrict k i.val false)
  let G : Hat k →+* HatOpen k true := restrict k j.val true
  have ht := (Gamma.transported_coordinates k (2*m) i.val (by omega) i.isLt).1
  have hx := (Gamma.transported_coordinates k (2*m) i.val (by omega) i.isLt).2.1
  change F (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = G (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) at ht
  change F (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
    G (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) * G (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) at hx
  have hc := Uniform.uniform_compatible k m he w
  by_cases hi : i.val+1 < 2*m
  · have hj : j.val = i.val+1 := Nat.mod_eq_of_lt hi
    have hs : F (uniformSection k m hm he w i) = G (uniformSection k m hm he w j) := by
      have hh := hc.1 i hi
      have ha : interiorAdjacent k m hm i.val hi = overlap k (2*m) i.val (by omega) i.isLt := by
        dsimp only [interiorAdjacent, ArithmeticThetaAnnularThetaR0128.adjacent]
        apply eq_of_heq
        exact eqRec_heq_iff.mpr HEq.rfl
      rw [ha] at hh
      have hjf : j = ⟨i.val+1,hi⟩ := Fin.ext hj
      dsimp only [F, G, RingHom.comp_apply]
      change overlap k (2*m) i.val _ _ (restrict k i.val false _) = restrict k j.val true _
      rw [hjf]
      exact hh
    have hw : F (weighted k m hm he w i) = G (weighted k m hm he w j) := by
      simp only [weighted, map_mul, map_pow, ht, hx, hs]
      rw [hj, Nat.add_mul, one_mul, pow_add, mul_pow]
      ring
    have hg := gamma_interior_overlap k (2*m) i.val (by omega) i.isLt hi
      _ _ _ _ (tail_data k (2*m) (by omega) i) (tail_data k (2*m) (by omega) j)
    change F _ = G _ at hg
    change F _ * (G _)^m = G _ * (F _)^m
    rw [hw, hg]
  · have hib : i.val+1 = 2*m := by omega
    have hj : j = firstIndex m hm := by apply Fin.ext; simp [j, ArithmeticThetaInfinitesimalPolygonR0129.next, firstIndex, hib]
    have hil : i = lastIndex m hm := by apply Fin.ext; simp only [lastIndex]; omega
    have hs : G (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)^(m*m) *
        G (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)^m * F (uniformSection k m hm he w i) =
        G (uniformSection k m hm he w j) := by
      have hh := hc.2
      have ha : boundaryAdjacent k m hm = overlap k (2*m) (lastIndex m hm).val (by omega) (lastIndex m hm).isLt := by
        dsimp only [boundaryAdjacent, ArithmeticThetaAnnularThetaR0128.adjacent]
        apply eq_of_heq
        exact eqRec_heq_iff.mpr HEq.rfl
      rw [ha] at hh
      change G _ ^ (m*m) * G _ ^ m * F _ = G _
      dsimp only [F, G, RingHom.comp_apply]
      rw [hj, hil]
      exact hh
    have hmul : (i.val+1)*(m/2) = m*m := by
      rw [hib, Nat.mul_assoc, Nat.mul_comm m (m/2), ← Nat.mul_assoc,
        Nat.mul_div_cancel' (even_iff_two_dvd.mp he)]
    have hw : G (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)^m *
        F (weighted k m hm he w i) = G (weighted k m hm he w j) := by
      simp only [weighted, map_mul, map_pow, ht, hx, mul_pow]
      have h0 : j.val = 0 := by rw [hj]; rfl
      rw [h0, zero_mul, pow_zero, one_mul]
      calc
        _ = G (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)^(m/2) *
          (G (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)^(m*m) *
          G (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)^m * F (uniformSection k m hm he w i)) := by
            rw [← hmul, Nat.add_mul, one_mul, pow_add]; ring
        _ = _ := by rw [hs]
    have hg := gamma_period_boundary k (2*m) i.val (by omega) i.isLt hib
      _ _ _ _ (tail_data k (2*m) (by omega) i) (tail_data k (2*m) (by omega) j)
    let X := G (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)
    let Y : HatOpen k true := completeOpen k j.val true (↑((ArithmeticThetaIndexedOverlapsR0058.xUnit k j.val)⁻¹))
    have hxy : X * Y = 1 := by
      have hh : restrict k j.val true (ArithmeticThetaCorrectedGammaR0061.cx k) *
          completeOpen k j.val true (↑((ArithmeticThetaIndexedOverlapsR0058.xUnit k j.val)⁻¹)) = 1 := by
        rw [Gamma.restrict_cx, ← map_mul]
        have hu : (↑(ArithmeticThetaIndexedOverlapsR0058.xUnit k j.val) : Open k j.val true) = ox k j.val true := IsUnit.unit_spec _
        rw [← hu, Units.mul_inv, map_one]
      exact hh
    change F _ = -Y * G _ at hg
    change F _ * (G _)^m = G _ * (F _)^m
    rw [hg, mul_pow, he.neg_pow, ← hw]
    calc
      _ = (X * Y)^m * (F (weighted k m hm he w i) * (G _)^m) := by rw [hxy, one_pow, one_mul]
      _ = _ := by rw [mul_pow]; ring


private lemma completed_numerator_overlap (m : ℕ) (hm : 0 < m) (he : Even m)
    (w : Fin m → PowerSeries k) (i : Fin (2*m)) :
    let j := ArithmeticThetaInfinitesimalPolygonR0129.next (2*m) (by omega) i
    let F : Hat k →+* HatOpen k true := (overlap k (2*m) i.val (by omega) i.isLt).toRingHom.comp (restrict k i.val false)
    let G : Hat k →+* HatOpen k true := restrict k j.val true
    F (thetaNumerator k m hm he w i) * (G (ArithmeticThetaCorrectedGammaR0061.horizontal k (2*m) j.val))^m =
    G (thetaNumerator k m hm he w j) * (F (ArithmeticThetaCorrectedGammaR0061.horizontal k (2*m) i.val))^m := by
  dsimp only
  let j := ArithmeticThetaInfinitesimalPolygonR0129.next (2*m) (by omega) i
  let F : Hat k →+* HatOpen k true := (overlap k (2*m) i.val (by omega) i.isLt).toRingHom.comp (restrict k i.val false)
  let G : Hat k →+* HatOpen k true := restrict k j.val true
  have h := completed_cross k m hm he w i
  have hh := clear_units
    (F (ArithmeticThetaCorrectedGammaR0061.horizontal k (2*m) i.val))
    (G (ArithmeticThetaCorrectedGammaR0061.horizontal k (2*m) j.val))
    (F (weighted k m hm he w i)) (G (weighted k m hm he w j))
    (Units.map F (gammaTail k (2*m) (by omega) i))
    (Units.map G (gammaTail k (2*m) (by omega) j)) m
    (by simp only [map_mul] at h; exact h)
  simp only [thetaNumerator, weighted, map_mul, map_pow, Units.coe_map_inv] at hh ⊢
  exact hh

private def openReduction (n : ℕ) (s : Bool) : HatOpen k s →+* B k n s :=
  (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) s).toRingHom.comp
    (trunc (HatOpen k s) (completeOpen k 0 s (openParameter k s)) n)

private lemma reduction_of (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1 a

private lemma openReduction_of (n : ℕ) (s : Bool) (a : RawOpen k s) :
    openReduction k n s (completeOpen k 0 s a) = trunc _ (openParameter k s) n a :=
  RingHom.congr_fun ((Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).2.1 s) a

private lemma filtration_eq (n : ℕ) :
    ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n =
      (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})^n := by
  simp [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
    ArithmeticThetaScaledTateBridgeR0046.completedPower,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private lemma reduction_approx (n : ℕ) (z : Hat k) :
    ∃ a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k,
      z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a ∈
        ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (completedReduction k n z)
  refine ⟨(nodeEquiv k).symm a, ?_⟩
  have hh : completedReduction k n z = completedReduction k n
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k ((nodeEquiv k).symm a)) := by
    rw [reduction_of, RingEquiv.apply_symm_apply]
    exact ha.symm
  have hh' := (Classical.choose (finite_stage_completion_comparison k n)).injective hh
  rw [filtration_eq]
  exact Ideal.Quotient.eq.mp hh'

private lemma reduction_kills (n : ℕ) (z : Hat k)
    (hz : z ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1)) :
    completedReduction k n z = 0 := by
  change (Classical.choose (finite_stage_completion_comparison k n)) (trunc _ _ n z) = 0
  rw [filtration_eq] at hz
  rw [show trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]

private lemma reduction_natural (n N : ℕ) (h : n ≤ N) (z : Hat k) :
    truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h (completedReduction k N z) =
      completedReduction k n z := by
  obtain ⟨a, ha⟩ := reduction_approx k N z
  have hn : z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right h 1) ha
  have hN := reduction_kills k N _ ha
  have hn' := reduction_kills k n _ hn
  rw [map_sub, sub_eq_zero] at hN hn'
  rw [hN, hn', reduction_of, reduction_of]
  rfl

private lemma restrict_index (j : ℕ) (s : Bool) : restrict k j s = restrict k 0 s := by
  apply (completed_coordinate_restrictions k 0 s).unique
  · exact (Classical.choose_spec (completed_coordinate_restrictions k j s).exists)
  · exact (Classical.choose_spec (completed_coordinate_restrictions k 0 s).exists)

private lemma reduction_restrict (n j : ℕ) (s : Bool) (z : Hat k) :
    openReduction k n s (restrict k j s z) =
      ArithmeticThetaInfinitesimalPolygonR0129.restriction k n s (completedReduction k n z) := by
  rw [restrict_index]
  have hr : restrict k 0 s = Classical.choose (completed_coordinate_restrictions k 0 s) :=
    (completed_coordinate_restrictions k 0 s).unique
      (Classical.choose_spec (completed_coordinate_restrictions k 0 s).exists)
      (Classical.choose_spec (completed_coordinate_restrictions k 0 s)).1
  rw [hr]
  exact (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).2.2 s z

private lemma openReduction_kills (n : ℕ) (s : Bool) (z : HatOpen k s)
    (hz : z ∈ hatPower k 0 s (n+1)) : openReduction k n s z = 0 := by
  have ht : ot k 0 s = openParameter k s := by
    change algebraMap _ _ (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
    congr 1
  change (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) s) (trunc _ _ n z) = 0
  rw [show trunc _ _ n z = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [hatPower, ht] using hz), map_zero]

private lemma openReduction_approx (n : ℕ) (s : Bool) (z : HatOpen k s) :
    ∃ a : RawOpen k s, openReduction k n s z = openReduction k n s (completeOpen k 0 s a) ∧
      z - completeOpen k 0 s a ∈ hatPower k 0 s (n+1) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (openReduction k n s z)
  have hh : openReduction k n s z = openReduction k n s (completeOpen k 0 s a) := by
    rw [openReduction_of]; exact ha.symm
  refine ⟨a, hh, ?_⟩
  have hh' := (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) s).injective hh
  have hm := Ideal.Quotient.eq.mp hh'
  have ht : ot k 0 s = openParameter k s := by
    change algebraMap _ _ (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
    congr 1
  simpa only [hatPower, ht] using hm

private lemma reduction_overlap (n r j : ℕ) (hr : 0 < r) (hj : j < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E) (z : HatOpen k false) :
    openReduction k n true (overlap k r j hr hj z) = E (openReduction k n false z) := by
  obtain ⟨a, ha, hm⟩ := openReduction_approx k n false z
  have hspec := Classical.choose_spec (completed_indexed_adjacent k r j hr hj).exists
  have hz := openReduction_kills k n true _ (hspec.2.1 (n+1) _ hm)
  rw [map_sub, map_sub, sub_eq_zero] at hz
  let O : HatOpen k false ≃+* HatOpen k true := overlap k r j hr hj
  change openReduction k n true (O z) = openReduction k n true (O (completeOpen k 0 false a)) at hz
  change openReduction k n true (O z) = E (openReduction k n false z)
  rw [hz, ha]
  have hc := RingHom.congr_fun hspec.1 a
  change overlap k r j hr hj (completeOpen k 0 false a) = completeOpen k 0 true (rawAdjacent k a) at hc
  change O (completeOpen k 0 false a) = completeOpen k 0 true (rawAdjacent k a) at hc
  rw [hc, openReduction_of, openReduction_of]
  exact (RingHom.congr_fun hE a).symm

private lemma reduction_horizontal (n r : ℕ) (i : Fin r) :
    completedReduction k n (ArithmeticThetaCorrectedGammaR0061.horizontal k r i.val) =
      equation k r n i := by
  have hx : completedReduction k n (ArithmeticThetaCorrectedGammaR0061.cx k) = coordX k n := by
    change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
    rw [reduction_of]
    change trunc _ _ n (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0))) = _
    rw [Gamma.node_equiv_coord]
    rfl
  have hy : completedReduction k n (ArithmeticThetaCorrectedGammaR0061.cy k) = coordY k n := by
    change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
    rw [reduction_of]
    change trunc _ _ n (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 1))) = _
    rw [Gamma.node_equiv_coord]
    rfl
  unfold ArithmeticThetaCorrectedGammaR0061.horizontal equation
  split_ifs <;> simp only [map_mul, map_sub, map_one, hx, hy]

end ArithmeticThetaIdentitySectionsR0138.ThetaNumeratorCompatibility

namespace ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaInfinitesimalPolygonR0129
open ThetaNumeratorCompatibility

theorem theta_numerator_compatibility :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m),
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)),
    ∀ w : Fin m → PowerSeries k,
    (∀ n : ℕ, Compatible k (2*m) n (Nat.mul_pos (by decide) hm) (T.overlap n) m (finiteNumerator k m hm he w n)) ∧
    (∀ (n N : ℕ) (h : n ≤ N) (i : Fin (2*m)),
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
        (finiteNumerator k m hm he w N i) = finiteNumerator k m hm he w n i) := by
  intro k _ _ m hm he T w
  constructor
  · intro n i
    have hh := congrArg (openReduction k n true) (completed_numerator_overlap k m hm he w i)
    let F : Hat k →+* HatOpen k true :=
      (ArithmeticThetaCorrectedGammaR0061.overlap k (2*m) i.val (by omega) i.isLt).toRingHom.comp
        (ArithmeticThetaCorrectedGammaR0061.restrict k i.val false)
    have hF (z : Hat k) : openReduction k n true (F z) =
        T.overlap n (restriction k n false (completedReduction k n z)) :=
      (reduction_overlap k n (2*m) i.val (by omega) i.isLt (T.overlap n) (T.overlap_spec n) _).trans
        (congrArg (T.overlap n) (reduction_restrict k n i.val false z))
    let G : Hat k →+* HatOpen k true := ArithmeticThetaCorrectedGammaR0061.restrict k (next (2*m) (by omega) i).val true
    have hG (z : Hat k) : openReduction k n true (G z) =
        restriction k n true (completedReduction k n z) := reduction_restrict k n _ true z
    simp only [map_mul, map_pow] at hh
    change openReduction k n true (F _) * openReduction k n true (G _) ^ m =
      openReduction k n true (G _) * openReduction k n true (F _) ^ m at hh
    rw [hF, hF, hG, hG, reduction_horizontal, reduction_horizontal] at hh
    exact hh
  · intro n N h i
    exact reduction_natural k n N h _

end ArithmeticThetaIdentitySectionsR0138
