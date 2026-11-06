import AlgebraicTateCoordinatesDefinitionsR0143

/-! Compatibility of the literal odd Tate numerator. All auxiliary ring
identities are confined to this module's namespace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u v

namespace ArithmeticThetaAlgebraicCoordinatesR0143
namespace TateYNumeratorSystemR0143
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138

section RingIdentities
variable {S : Type v} [CommRing S]

def geom (n : ℕ) (z : S) : S := ∑ a ∈ Finset.range (n+1), z^a
def rat (n : ℕ) (z : S) : S := z * (1+z) * geom n z ^ 3
def eqn (r i : ℕ) (x y : S) : S :=
  (if i = 0 then 1-x else 1) * (if i+1 = r then 1-y else 1)
def core (r n i : ℕ) (t x y : S) : S :=
  (if i = 0 then x*(1+x) else eqn r i x y ^ 3 * rat n (t^i*x)) +
  eqn r i x y ^ 3 * ∑ a ∈ Finset.range (n+1), rat n (t^(r*(a+1)+i)*x) -
  ∑ a ∈ Finset.range (n+1),
    if a = 0 ∧ i+1 = r then y*(1+y)
    else eqn r i x y ^ 3 * rat n (t^(r*(a+1)-i-1)*y)

lemma pow_vanish {t : S} {n a : ℕ} (ht : t^(n+1) = 0) (ha : n < a) :
    t^a = 0 := by
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (show n+1 ≤ a by omega)
  rw [hb, pow_add, ht, zero_mul]

lemma monomial_nilpotent {t : S} {n d : ℕ} (ht : t^(n+1) = 0)
    (hd : 0 < d) (z : S) : (t^d*z)^(n+1) = 0 := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm d, pow_mul, ht, zero_pow hd.ne', zero_mul]

lemma geom_stable {n N : ℕ} (h : n ≤ N) {z : S} (hz : z^(n+1) = 0) :
    geom N z = geom n z := by
  unfold geom
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro a ha han
  exact pow_vanish hz (by simp only [Finset.mem_range] at han; omega)

lemma rat_stable {n N : ℕ} (h : n ≤ N) {z : S} (hz : z^(n+1) = 0) :
    rat N z = rat n z := by rw [rat, rat, geom_stable h hz]

@[simp] lemma rat_zero (n : ℕ) : rat n (0 : S) = 0 := by simp [rat]

lemma geom_inverse {n : ℕ} {z : S} (hz : z^(n+1) = 0) :
    (1-z)*geom n z = 1 := by
  have h := geom_sum_mul z (n+1)
  dsimp [geom]
  rw [hz] at h
  linear_combination -h

lemma rat_cleared {n : ℕ} {z : S} (hz : z^(n+1) = 0) :
    (1-z)^3 * rat n z = z*(1+z) := by
  have h := congrArg (fun a : S => a^3) (geom_inverse hz)
  dsimp [rat]
  calc
    _ = z*(1+z)*((1-z)*geom n z)^3 := by ring
    _ = _ := by rw [geom_inverse hz]; ring

lemma core_stable {r n N i : ℕ} (hr : 0 < r) (hi : i < r)
    (h : n ≤ N) {t : S} (ht : t^(n+1) = 0) (x y : S) :
    core r N i t x y = core r n i t x y := by
  have htarg (d : ℕ) (hd : 0 < d) (z : S) :
      rat N (t^d*z) = rat n (t^d*z) := rat_stable h (monomial_nilpotent ht hd z)
  have hp (a : ℕ) : 0 < r*(a+1)+i := by nlinarith
  have hn (a : ℕ) (ha : ¬(a = 0 ∧ i+1 = r)) : 0 < r*(a+1)-i-1 := by
    by_cases haz : a = 0
    · subst a
      have hne : i+1 ≠ r := fun he => ha ⟨rfl, he⟩
      simp only [Nat.zero_add, mul_one]
      omega
    · have : r ≤ r*a := Nat.le_mul_of_pos_right r (by omega)
      rw [Nat.mul_add, mul_one]; omega
  have hpTail (a : ℕ) (ha : n < a) : rat n (t^(r*(a+1)+i)*x) = 0 := by
    have : a+1 ≤ r*(a+1) := Nat.le_mul_of_pos_left _ hr
    rw [pow_vanish ht (by omega), zero_mul, rat_zero]
  have hnTail (a : ℕ) (ha : n < a) :
      (if a = 0 ∧ i+1 = r then y*(1+y)
       else eqn r i x y ^ 3 * rat n (t^(r*(a+1)-i-1)*y)) = 0 := by
    have haz : a ≠ 0 := by omega
    simp only [haz, false_and, ite_false]
    have : a ≤ r*a := Nat.le_mul_of_pos_left _ hr
    have he : n < r*(a+1)-i-1 := by rw [Nat.mul_add, mul_one]; omega
    rw [pow_vanish ht he, zero_mul, rat_zero, mul_zero]
  unfold core
  congr 1
  · congr 1
    · split_ifs with hi0
      · rfl
      · rw [htarg i (by omega) x]
    · congr 1
      calc
        _ = ∑ a ∈ Finset.range (N+1), rat n (t^(r*(a+1)+i)*x) := by
          apply Finset.sum_congr rfl; intro a ha; exact htarg _ (hp a) x
        _ = _ := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro a ha han
          exact hpTail a (by simp only [Finset.mem_range] at han; omega)
  · calc
      _ = ∑ a ∈ Finset.range (N+1),
          if a = 0 ∧ i+1 = r then y*(1+y)
          else eqn r i x y ^ 3 * rat n (t^(r*(a+1)-i-1)*y) := by
        apply Finset.sum_congr rfl
        intro a ha
        split_ifs with he
        · rfl
        · rw [htarg _ (hn a he) y]
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro a ha han
        exact hnTail a (by simp only [Finset.mem_range] at han; omega)

def series (r n i : ℕ) (t x y : S) : S :=
  rat n (t^i*x) + ∑ a ∈ Finset.range (n+1), rat n (t^(r*(a+1)+i)*x) -
    ∑ a ∈ Finset.range (n+1), rat n (t^(r*(a+1)-i-1)*y)

lemma core_regular {r n i : ℕ} (hr : 3 ≤ r) (x y t : S)
    (hx : i = 0 → x^(n+1) = 0) (hy : i+1 = r → y^(n+1) = 0) :
    core r n i t x y = eqn r i x y ^ 3 * series r n i t x y := by
  have hf : (if i = 0 then x*(1+x) else eqn r i x y ^ 3 * rat n (t^i*x)) =
      eqn r i x y ^ 3 * rat n (t^i*x) := by
    split_ifs with hi
    · subst i
      have hne : ¬ (0+1 = r) := by omega
      simp only [eqn, ite_true, hne, ite_false, mul_one, pow_zero, one_mul]
      exact (rat_cleared (hx rfl)).symm
    · rfl
  have hn (a : ℕ) :
      (if a = 0 ∧ i+1 = r then y*(1+y)
      else eqn r i x y ^ 3 * rat n (t^(r*(a+1)-i-1)*y)) =
      eqn r i x y ^ 3 * rat n (t^(r*(a+1)-i-1)*y) := by
    split_ifs with ha
    · obtain ⟨rfl, hi⟩ := ha
      have hne : i ≠ 0 := by omega
      have he : r*(0+1)-i-1 = 0 := by omega
      simp only [eqn, hne, ite_false, hi, ite_true, one_mul, he, pow_zero]
      exact (rat_cleared (hy hi)).symm
    · rfl
  simp only [core, hf, hn]
  simp only [series, mul_sub, mul_add, Finset.mul_sum]

lemma series_step {r n i : ℕ} (hi : i+1 < r) (t x y : S) :
    series r n i t (t*x) y = series r n (i+1) t x (t*y) := by
  have hp (a : ℕ) : r*(a+1)+(i+1) = (r*(a+1)+i)+1 := by omega
  have hn (a : ℕ) : r*(a+1)-i-1 = (r*(a+1)-(i+1)-1)+1 := by
    have : r ≤ r*(a+1) := Nat.le_mul_of_pos_right r (by omega)
    omega
  unfold series
  simp only [hp, hn, pow_succ, mul_assoc]

lemma core_step {r n i : ℕ} (hr : 3 ≤ r) (hi : i+1 < r)
    {t : S} (ht : t^(n+1) = 0) (x y : S) :
    core r n i t (t*x) y * eqn r (i+1) x (t*y)^3 =
      core r n (i+1) t x (t*y) * eqn r i (t*x) y ^3 := by
  have hn (z : S) : (t*z)^(n+1) = 0 := by rw [mul_pow, ht, zero_mul]
  rw [core_regular hr (t*x) y t (fun _ => hn x) (by omega),
    core_regular hr x (t*y) t (by omega) (fun _ => hn y), series_step hi]
  ring


def tails (r n : ℕ) (t z : S) : S :=
  ∑ a ∈ Finset.range (n+1), rat n (t^(r*(a+1))*z)

lemma tail_last_zero {r n : ℕ} (hr : 0 < r) {t : S} (ht : t^(n+1) = 0) (z : S) :
    rat n (t^(r*(n+1))*z) = 0 := by
  have : n+1 ≤ r*(n+1) := Nat.le_mul_of_pos_left _ hr
  rw [pow_vanish ht (by omega), zero_mul, rat_zero]

lemma tail_short {r n : ℕ} (hr : 0 < r) {t : S} (ht : t^(n+1) = 0) (z : S) :
    (∑ a ∈ Finset.range n, rat n (t^(r*(a+1))*z)) = tails r n t z := by
  rw [tails, Finset.sum_range_succ, tail_last_zero hr ht, add_zero]

lemma tail_shift {r n : ℕ} (hr : 0 < r) {t : S} (ht : t^(n+1) = 0) (z : S) :
    rat n (t^r*z) + (∑ a ∈ Finset.range (n+1), rat n (t^(r*(a+2))*z)) =
      tails r n t z := by
  have hz : rat n (t^(r*((n+1)+1))*z) = 0 := by
    have : n+2 ≤ r*(n+2) := Nat.le_mul_of_pos_left _ hr
    simp only [Nat.add_assoc, Nat.reduceAdd] at *
    rw [pow_vanish ht (by omega), zero_mul, rat_zero]
  have h := Finset.sum_range_succ' (fun a => rat n (t^(r*(a+1))*z)) (n+1)
  rw [Finset.sum_range_succ, hz, add_zero] at h
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, mul_one] at h
  exact (add_comm _ _).trans h.symm

lemma core_period_left {r n : ℕ} (hr : 3 ≤ r) {t : S} (ht : t^(n+1) = 0)
    (x y : S) :
    core r n (r-1) t (t*x) y =
      (1-y)^3 * (tails r n t x - tails r n t y) - y*(1+y) := by
  have hr0 : 0 < r := by omega
  have hi0 : r-1 ≠ 0 := by omega
  have hi : r-1+1 = r := by omega
  have he : eqn r (r-1) (t*x) y = 1-y := by simp [eqn, hi0, hi]
  have hp (a : ℕ) : r*(a+1)+(r-1)+1 = r*(a+2) := by
    simp only [Nat.mul_add, mul_one]; omega
  have hn (a : ℕ) : r*((a+1)+1)-(r-1)-1 = r*(a+1) := by
    rw [Nat.mul_add, mul_one]; omega
  have hsum : (∑ a ∈ Finset.range (n+1),
      if a = 0 ∧ (r-1)+1 = r then y*(1+y)
      else (1-y)^3 * rat n (t^(r*(a+1)-(r-1)-1)*y)) =
      y*(1+y) + (1-y)^3 * tails r n t y := by
    rw [Finset.sum_range_succ']
    simp only [hi, and_true, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false, hn, ite_true]
    rw [← Finset.mul_sum, tail_short hr0 ht]
    ring
  unfold core
  rw [if_neg hi0, he, hsum]
  have hx : t^(r-1)*(t*x) = t^r*x := by rw [← mul_assoc, ← pow_succ, hi]
  have hpx (a : ℕ) : t^(r*(a+1)+(r-1))*(t*x) = t^(r*(a+2))*x := by
    rw [← mul_assoc, ← pow_succ, hp]
  simp only [hx, hpx]
  have hs := tail_shift hr0 ht x
  linear_combination (1-y)^3 * hs

lemma core_period_right {r n : ℕ} (hr : 3 ≤ r) (t x y : S) :
    core r n 0 t x (t*y) =
      x*(1+x) + (1-x)^3 * (tails r n t x - tails r n t y) := by
  have hne : ¬(0+1 = r) := by omega
  have he : eqn r 0 x (t*y) = 1-x := by simp [eqn, hne]
  have hn (a : ℕ) : r*(a+1)-0-1+1 = r*(a+1) := by
    have : r ≤ r*(a+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hny (a : ℕ) : t^(r*(a+1)-0-1)*(t*y) = t^(r*(a+1))*y := by
    rw [← mul_assoc, ← pow_succ, hn]
  simp only [core, ite_true, he, hne, and_false, ite_false, Nat.add_zero, hny]
  rw [← Finset.mul_sum]
  change x*(1+x) + (1-x)^3 * tails r n t x - (1-x)^3 * tails r n t y = _
  ring

lemma inversion_cleared (x y : S) (hxy : x*y = 1) :
    -(y*(1+y))*(1-x)^3 = x*(1+x)*(1-y)^3 := by
  have he : 1-y = -y*(1-x) := by linear_combination -hxy
  have hn : x*(1+x)*y^3 = y*(1+y) := by
    linear_combination (x*y^2+y^2+y)*hxy
  rw [he]
  calc
    _ = -(x*(1+x)*y^3)*(1-x)^3 := by rw [hn]
    _ = _ := by ring

lemma core_period {r n : ℕ} (hr : 3 ≤ r) {t : S} (ht : t^(n+1) = 0)
    (x y : S) (hxy : x*y = 1) :
    core r n (r-1) t (t*x) y * eqn r 0 x (t*y)^3 =
      core r n 0 t x (t*y) * eqn r (r-1) (t*x) y ^3 := by
  rw [core_period_left hr ht, core_period_right hr]
  have hi0 : r-1 ≠ 0 := by omega
  have hi : r-1+1 = r := by omega
  have hne : ¬(0+1 = r) := by omega
  simp only [eqn, ite_true, hne, ite_false, hi0, hi, mul_one, one_mul]
  linear_combination inversion_cleared x y hxy


lemma map_geom {U : Type*} [CommRing U] (f : S →+* U) (n : ℕ) (z : S) :
    f (geom n z) = geom n (f z) := by simp [geom]
lemma map_rat {U : Type*} [CommRing U] (f : S →+* U) (n : ℕ) (z : S) :
    f (rat n z) = rat n (f z) := by simp [rat, map_geom]
lemma map_eqn {U : Type*} [CommRing U] (f : S →+* U) (r i : ℕ) (x y : S) :
    f (eqn r i x y) = eqn r i (f x) (f y) := by
  unfold eqn; split_ifs <;> simp
lemma map_core {U : Type*} [CommRing U] (f : S →+* U) (r n i : ℕ) (t x y : S) :
    f (core r n i t x y) = core r n i (f t) (f x) (f y) := by
  simp only [core, map_add, map_sub, map_mul, map_pow, map_sum, map_eqn,
    map_rat, map_one, apply_ite]


end RingIdentities
section ConcreteReduction
variable (k : Type u) [Field k] [CharZero k]

lemma numerator_core (r n : ℕ) (i : Fin r) :
    numerator k true r n i =
      base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹)) *
        core r n i.val (tau k n) (coordX k n) (coordY k n) := by
  rfl

lemma tau_nilpotent (n : ℕ) : tau k n ^ (n+1) = 0 := by
  rw [tau, ← map_pow, parameter_pow, map_zero]

lemma numerator_reduction (r : ℕ) (hr : 0 < r) (n N : ℕ) (h : n ≤ N) (i : Fin r) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (numerator k true r N i) = numerator k true r n i := by
  rw [numerator_core, map_mul, map_core, numerator_core]
  have hx : truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (coordX k N) = coordX k n := rfl
  have hy : truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (coordY k N) = coordY k n := rfl
  have ht : truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (tau k N) = tau k n := rfl
  have hc : truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n N h (base k N (trunc (PowerSeries k) PowerSeries.X N
        (PowerSeries.C (2 : k)⁻¹))) =
      base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹)) := rfl
  rw [hx, hy, ht, hc, core_stable hr i.isLt h (tau_nilpotent k n)]

lemma equation_eq_core (r n : ℕ) (i : Fin r) :
    equation k r n i = eqn r i.val (coordX k n) (coordY k n) := rfl

lemma compatible_stage (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E) :
    Compatible k r n hr E (degree true) (numerator k true r n) := by
  let L : A k n →+* B k n true := E.toRingHom.comp (restriction k n false)
  let R' : A k n →+* B k n true := restriction k n true
  let t := R' (tau k n)
  let x := R' (coordX k n)
  let y := L (coordY k n)
  have hb (c : R k n) : L (base k n c) = R' (base k n c) :=
    RingHom.congr_fun (adjacent_base hE) c
  have hlt : L (tau k n) = t := hb _
  have hxy : x*y = 1 := by
    dsimp [x, y, L, R']
    rw [mul_comm]
    exact adjacent_y_mul_x hE
  have hlxy : L (coordX k n) * y = t := by
    change L (coordX k n) * L (coordY k n) = t
    rw [← map_mul, coordX_mul_coordY]
    exact hb _
  have hrxy : x * R' (coordY k n) = t := by
    change R' (coordX k n) * R' (coordY k n) = t
    rw [← map_mul, coordX_mul_coordY]
    rfl
  have hlx : L (coordX k n) = t*x := by
    linear_combination x*hlxy - L (coordX k n)*hxy
  have hry : R' (coordY k n) = t*y := by
    linear_combination y*hrxy - R' (coordY k n)*hxy
  have ht : t^(n+1) = 0 := by
    change R' (tau k n) ^ (n+1) = 0
    rw [← map_pow, tau_nilpotent, map_zero]
  intro i
  have hc : core r n i.val t (t*x) y * eqn r (next r hr i).val x (t*y)^3 =
      core r n (next r hr i).val t x (t*y) * eqn r i.val (t*x) y ^3 := by
    by_cases hi : i.val+1 = r
    · have hi' : i.val = r-1 := by omega
      have hj : (next r hr i).val = 0 := by simp [next, hi]
      rw [hi', hj]
      exact core_period h3 ht x y hxy
    · have hil : i.val+1 < r := by have := i.isLt; omega
      have hj : (next r hr i).val = i.val+1 := Nat.mod_eq_of_lt hil
      rw [hj]
      exact core_step h3 hil ht x y
  change L (numerator k true r n i) * R' (equation k r n (next r hr i))^3 =
    R' (numerator k true r n (next r hr i)) * L (equation k r n i)^3
  simp only [numerator_core, map_mul, map_core, equation_eq_core, map_eqn,
    hb, hlt, hlx, hry]
  change (R' (base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹))) *
      core r n i.val t (t*x) y) * eqn r (next r hr i).val x (t*y)^3 =
    (R' (base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹))) *
      core r n (next r hr i).val t x (t*y)) * eqn r i.val (t*x) y ^3
  simpa only [mul_assoc] using congrArg
    (fun z => R' (base k n (trunc (PowerSeries k) PowerSeries.X n
      (PowerSeries.C (2 : k)⁻¹))) * z) hc

end ConcreteReduction

end TateYNumeratorSystemR0143

/-- The literal odd Tate numerators glue on every overlap and reduce at every thickness. -/
theorem tate_y_numerator_system :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
      CompatibleSystem k true T := by
  intro k _ _ r hr h3 T
  exact ⟨fun n => TateYNumeratorSystemR0143.compatible_stage k r n hr h3
    (T.overlap n) (T.overlap_spec n),
    fun n N h i => TateYNumeratorSystemR0143.numerator_reduction k r hr n N h i⟩

end ArithmeticThetaAlgebraicCoordinatesR0143
