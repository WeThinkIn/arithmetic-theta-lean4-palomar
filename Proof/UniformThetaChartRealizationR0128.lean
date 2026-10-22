module

public import AnnularThetaInteriorR0128
public import AnnularThetaPeriodR0128
public import CompletedChartThetaIndependenceR0128
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.TorsionFree
public import AllSolutionsAnnularEvaluationR0119

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! A common vertical denominator and faithful uniform completed theta charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaAnnularThetaR0128
open ArithmeticThetaSchrodingerR0119
open ArithmeticThetaIndexedOverlapsR0058

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

private lemma mono_add (a b : ℤ) : monomial k (a+b) = monomial k a * monomial k b := by
  simp [monomial, HahnSeries.single_mul_single]

private lemma mono_ne (a : ℤ) : monomial k a ≠ 0 := by
  simp [monomial]

private lemma clear_denominators (m : ℕ) (v : Fin m → K k) :
    ∃ (b : ℕ) (w : Fin m → PowerSeries k),
      ∀ ν, HahnSeries.ofPowerSeries ℤ k (w ν) = monomial k (b : ℤ) * v ν := by
  classical
  let b := Finset.univ.sup (fun ν : Fin m => (-(v ν).order).toNat)
  have hb (ν : Fin m) : 0 ≤ (b : ℤ) + (v ν).order := by
    have h := Finset.le_sup (f := fun ν : Fin m => (-(v ν).order).toNat)
      (Finset.mem_univ ν)
    dsimp [b]
    omega
  refine ⟨b, fun ν => PowerSeries.X ^ ((b : ℤ) + (v ν).order).toNat *
    (v ν).powerSeriesPart, ?_⟩
  intro ν
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, LaurentSeries.ofPowerSeries_powerSeriesPart]
  change monomial k _ * (monomial k _ * v ν) = _
  rw [← mul_assoc, ← mono_add]
  congr 2
  rw [Int.toNat_of_nonneg (hb ν)]
  omega

private lemma normalize_equation {R : Type*} [CommRing R] (t x y : R)
    (C a b : ℕ) (ha : a ≤ C) (hb : b ≤ C)
    (hc : Function.Injective (fun z : R => t^(a+b)*z))
    (h : t^b*x = t^a*y) : t^(C-a)*x = t^(C-b)*y := by
  apply hc
  have he := congrArg (fun z => t^C*z) h
  simp only [← mul_assoc, ← pow_add] at he ⊢
  rw [show a+b+(C-a) = C+b by omega, show a+b+(C-b) = C+a by omega]
  exact he

private lemma uniform_compatible (m : ℕ) [NeZero m] (he : Even m)
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

private lemma uniform_evaluation (m : ℕ) [NeZero m] (he : Even m)
    (b : ℕ) (v : Fin m → K k) (w : Fin m → PowerSeries k)
    (hw : ∀ ν, HahnSeries.ofPowerSeries ℤ k (w ν) = monomial k (b : ℤ) * v ν)
    (j : Fin (2*m)) (a : kˣ) :
    HahnSeries.ofPowerSeries ℤ k
      (specialize k a (uniformSection k m (NeZero.pos m) he w j)) =
    monomial k ((b + commonShift m : ℕ) : ℤ) *
      evaluate k (synth k m v) (j.val : ℤ) a := by
  have ht : specialize k a (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      PowerSeries.X :=
    (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) (a : k) a.ne_zero).1
  simp only [uniformSection, map_mul, map_pow, ht]
  rw [combine_full_series]
  rw [← map_pow, HahnSeries.ofPowerSeries_X_pow]
  rw [(all_solutions_annular_evaluation k m he).2.1]
  simp only [Finset.mul_sum, hw]
  apply Finset.sum_congr rfl
  intro ν _
  have hexp : ((commonShift m - shift j.val : ℕ) : ℤ) + (b : ℤ) + (shift j.val : ℤ) =
      ((b + commonShift m : ℕ) : ℤ) := by
    have := shift_le m j.val j.isLt
    omega
  change monomial k _ * (_ * (monomial k _ * _)) = _
  calc
    _ = (monomial k ((commonShift m - shift j.val : ℕ) : ℤ) *
        monomial k (b : ℤ) * monomial k (shift j.val : ℤ)) *
        (v ν * evaluate k (theta k m ν) (j.val : ℤ) a) := by ring
    _ = _ := by rw [← mono_add, ← mono_add, hexp]

private lemma uniform_zero (m : ℕ) [NeZero m] (he : Even m)
    (w : Fin m → PowerSeries k) (j : Fin (2*m)) :
    uniformSection k m (NeZero.pos m) he w j = 0 ↔ w = 0 := by
  letI : IsDomain (Chart k) :=
    (ArithmeticThetaScaledAnnularR0050.completed_node_normal_domain k 1 (by decide)).1
  have ht : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
    intro hz
    have h := (ArithmeticThetaScaledAnnularR0050.specialization_coordinates k 1 0
      (by decide) (by decide) (1 : k) one_ne_zero).1
    change specialize k (1 : kˣ) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) =
      PowerSeries.X at h
    rw [hz, map_zero] at h
    exact PowerSeries.X_ne_zero h.symm
  have h0 : combine k m (NeZero.pos m) he j.val 0 = 0 := by simp [combine]
  rw [uniformSection, mul_eq_zero, or_iff_right (pow_ne_zero _ ht)]
  exact ⟨fun h => completed_chart_theta_independence k m he j.val (h.trans h0.symm),
    fun h => h ▸ h0⟩


/-- Uniform realization of every Laurent coefficient vector, including zero. -/
theorem uniform_theta_chart_realization :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (he : Even m), ∀ v : Fin m → ArithmeticThetaSchrodingerR0119.K k, ∃ (b : ℕ) (w : Fin m → PowerSeries k), (∀ ν : Fin m, (HahnSeries.ofPowerSeries ℤ k) (w ν) = ArithmeticThetaSchrodingerR0119.monomial k (b : ℤ) * v ν) ∧ ArithmeticThetaAnnularThetaR0128.UniformCompatible k m (NeZero.pos m) (ArithmeticThetaAnnularThetaR0128.uniformSection k m (NeZero.pos m) he w) ∧ (∀ (j : Fin (2*m)) (a : kˣ), (HahnSeries.ofPowerSeries ℤ k) (ArithmeticThetaAnnularThetaR0128.specialize k a (ArithmeticThetaAnnularThetaR0128.uniformSection k m (NeZero.pos m) he w j)) = ArithmeticThetaSchrodingerR0119.monomial k ((b + ArithmeticThetaAnnularThetaR0128.commonShift m : ℕ) : ℤ) * ArithmeticThetaSchrodingerR0119.evaluate k (ArithmeticThetaSchrodingerR0119.synth k m v) (j.val : ℤ) a) ∧ (∀ j : Fin (2*m), ArithmeticThetaAnnularThetaR0128.uniformSection k m (NeZero.pos m) he w j = 0 ↔ v = 0) := by
  intro k _ _ m _ he v
  obtain ⟨b, w, hw⟩ := clear_denominators k m v
  refine ⟨b, w, hw, uniform_compatible k m he w,
    uniform_evaluation k m he b v w hw, ?_⟩
  intro j
  rw [uniform_zero]
  constructor
  · intro hz
    funext ν
    have h := hw ν
    rw [hz] at h
    simpa only [Pi.zero_apply, map_zero, eq_comm, mul_eq_zero,
      or_iff_right (mono_ne k (b : ℤ))] using h
  · intro hz
    funext ν
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [hw, hz]
    simp

end ArithmeticThetaAnnularThetaR0128
