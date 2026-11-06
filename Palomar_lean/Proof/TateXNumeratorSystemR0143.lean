module

public import AlgebraicTateCoordinatesDefinitionsR0143

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Compatibility of the literal finite Tate X numerators. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
universe u

namespace ArithmeticThetaAlgebraicCoordinatesR0143
namespace TateXNumeratorSystemR0143
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138

variable (k : Type u) [Field k] [CharZero k]

lemma tau_pow (n : ℕ) : tau k n ^ (n+1) = 0 := by
  rw [tau, ← map_pow, parameter_pow, map_zero]

lemma tau_pow_zero (n a : ℕ) (ha : n+1 ≤ a) : tau k n ^ a = 0 :=
  pow_eq_zero_of_le ha (tau_pow k n)

lemma monomial_nilpotent (n e : ℕ) (he : 0 < e) (v : A k n) :
    (tau k n ^ e * v) ^ (n+1) = 0 := by
  rw [mul_pow, ← pow_mul, tau_pow_zero k n (e * (n+1)) (by nlinarith), zero_mul]

lemma sum_stable {S : Type*} [AddCommMonoid S] (f : ℕ → S)
    (n N : ℕ) (h : n ≤ N) (hz : ∀ a, n+1 ≤ a → f a = 0) :
    ∑ a ∈ Finset.range (N+1), f a = ∑ a ∈ Finset.range (n+1), f a := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
  intro a _ ha
  exact hz a (by simpa using ha)

lemma geometric_stable (n N : ℕ) (h : n ≤ N) (v : A k n)
    (hv : v ^ (n+1) = 0) :
    ∑ a ∈ Finset.range (N+1), v^a = geometric k n v := by
  exact sum_stable _ n N h (fun a ha => pow_eq_zero_of_le ha hv)

abbrev reduction (n N : ℕ) (h : n ≤ N) : A k N →+* A k n :=
  truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h

@[simp] lemma reduce_tau (n N : ℕ) (h : n ≤ N) :
    reduction k n N h (tau k N) = tau k n := rfl

@[simp] lemma reduce_x (n N : ℕ) (h : n ≤ N) :
    reduction k n N h (coordX k N) = coordX k n := rfl

@[simp] lemma reduce_y (n N : ℕ) (h : n ≤ N) :
    reduction k n N h (coordY k N) = coordY k n := rfl

@[simp] lemma reduce_equation (r n N : ℕ) (h : n ≤ N) (i : Fin r) :
    reduction k n N h (equation k r N i) = equation k r n i := by
  unfold equation
  split_ifs <;> simp

lemma reduce_geometric (n N : ℕ) (h : n ≤ N) (v : A k N)
    (hv : (reduction k n N h v) ^ (n+1) = 0) :
    reduction k n N h (geometric k N v) =
      geometric k n (reduction k n N h v) := by
  simpa only [geometric, map_sum, map_pow] using
    geometric_stable k n N h (reduction k n N h v) hv

lemma reduce_term (n N : ℕ) (h : n ≤ N) (e : ℕ) (he : 0 < e)
    (v : A k N) :
    reduction k n N h (term k false N (tau k N ^ e * v)) =
      term k false n (tau k n ^ e * reduction k n N h v) := by
  have hv : (reduction k n N h (tau k N ^ e * v)) ^ (n+1) = 0 := by
    simpa using monomial_nilpotent k n e he (reduction k n N h v)
  simp [term, reduce_geometric k n N h _ hv]

lemma term_zero (n : ℕ) : term k false n 0 = 0 := by simp [term]

lemma term_tail_zero (n e : ℕ) (he : n+1 ≤ e) (v : A k n) :
    term k false n (tau k n ^ e * v) = 0 := by
  rw [tau_pow_zero k n e he, zero_mul, term_zero]

lemma reduce_first (r n N : ℕ) (h : n ≤ N) (i : Fin r) :
    reduction k n N h
      (if i.val = 0 then coordX k N else
        equation k r N i ^ 2 * term k false N (tau k N ^ i.val * coordX k N)) =
      (if i.val = 0 then coordX k n else
        equation k r n i ^ 2 * term k false n (tau k n ^ i.val * coordX k n)) := by
  split_ifs with hi
  · exact reduce_x k n N h
  · rw [map_mul, map_pow, reduce_equation,
      reduce_term k n N h i.val (by omega), reduce_x]

lemma reduce_positive (r n N : ℕ) (hr : 0 < r) (h : n ≤ N) (i : Fin r) :
    reduction k n N h
      (∑ a ∈ Finset.range (N+1),
        term k false N (tau k N ^ (r*(a+1)+i.val) * coordX k N)) =
      ∑ a ∈ Finset.range (n+1),
        term k false n (tau k n ^ (r*(a+1)+i.val) * coordX k n) := by
  simp only [map_sum]
  have he (a : ℕ) : 0 < r*(a+1)+i.val := by nlinarith
  simp only [reduce_term k n N h _ (he _), reduce_x]
  apply sum_stable _ n N h
  intro a ha
  apply term_tail_zero
  nlinarith

lemma negative_exponent (r a : ℕ) (_hr : 0 < r) (i : Fin r)
    (ha : ¬ (a = 0 ∧ i.val+1 = r)) : 0 < r*(a+1)-i.val-1 := by
  have hi := i.isLt
  by_cases hzero : a = 0
  · subst a
    simp only [Nat.zero_add, mul_one]
    omega
  · have ha1 : 1 ≤ a := by omega
    have hm : r ≤ r*a := by simpa using Nat.mul_le_mul_left r ha1
    rw [Nat.mul_add, mul_one]
    omega

lemma reduce_negative (r n N : ℕ) (hr : 0 < r) (h : n ≤ N) (i : Fin r) :
    reduction k n N h
      (∑ a ∈ Finset.range (N+1),
        if a = 0 ∧ i.val+1 = r then coordY k N else
          equation k r N i ^ 2 *
            term k false N (tau k N ^ (r*(a+1)-i.val-1) * coordY k N)) =
      ∑ a ∈ Finset.range (n+1),
        if a = 0 ∧ i.val+1 = r then coordY k n else
          equation k r n i ^ 2 *
            term k false n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n) := by
  rw [map_sum]
  have he (a : ℕ) :
      reduction k n N h
        (if a = 0 ∧ i.val+1 = r then coordY k N else
          equation k r N i ^ 2 *
            term k false N (tau k N ^ (r*(a+1)-i.val-1) * coordY k N)) =
        (if a = 0 ∧ i.val+1 = r then coordY k n else
          equation k r n i ^ 2 *
            term k false n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n)) := by
    split_ifs with ha
    · exact reduce_y k n N h
    · rw [map_mul, map_pow, reduce_equation,
        reduce_term k n N h _ (negative_exponent r a hr i ha), reduce_y]
  simp only [he]
  apply sum_stable _ n N h
  intro a ha
  rw [if_neg (by omega)]
  have hi := i.isLt
  have hex : n+1 ≤ r*(a+1)-i.val-1 := by
    have hm : a ≤ r*a := by simpa using Nat.mul_le_mul_right a hr
    rw [Nat.mul_add, mul_one]
    omega
  rw [term_tail_zero k n _ hex, mul_zero]

lemma reduce_correction (r n N : ℕ) (hr : 0 < r) (h : n ≤ N) :
    reduction k n N h
      (∑ a ∈ Finset.range (N+1),
        (a+1 : ℕ) * tau k N ^ (r*(a+1)) * geometric k N (tau k N ^ (r*(a+1)))) =
      ∑ a ∈ Finset.range (n+1),
        (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1))) := by
  have hv (a : ℕ) :
      (reduction k n N h (tau k N ^ (r*(a+1)))) ^ (n+1) = 0 := by
    simp only [map_pow, reduce_tau, ← pow_mul]
    apply tau_pow_zero
    have he : 1 ≤ r*(a+1) := Nat.mul_pos hr (by omega)
    simpa using Nat.mul_le_mul_right (n+1) he
  simp only [map_sum, map_mul, map_natCast, map_pow, reduce_tau,
    reduce_geometric k n N h _ (hv _)]
  apply sum_stable _ n N h
  intro a ha
  rw [tau_pow_zero k n (r*(a+1)) (by nlinarith), mul_zero, zero_mul]

/-- Every thickness reduction of the frozen literal X numerator. -/
lemma numerator_reduction (r n N : ℕ) (hr : 0 < r) (h : n ≤ N) (i : Fin r) :
    reduction k n N h (numerator k false r N i) = numerator k false r n i := by
  simp only [numerator, Bool.false_eq_true, ↓reduceIte, degree, mul_one]
  rw [map_sub, map_add, map_add, reduce_first, map_mul, map_pow, reduce_equation,
    reduce_positive k r n N hr h i, reduce_negative k r n N hr h i,
    map_mul, map_mul, map_ofNat, map_pow, reduce_equation,
    reduce_correction k r n N hr h]

section RingPolynomials
variable {S : Type*} [CommRing S]

def gsum (n : ℕ) (v : S) : S := ∑ a ∈ Finset.range (n+1), v^a
def xterm (n : ℕ) (v : S) : S := v * gsum n v ^ 2
def eqn (r j : ℕ) (x y : S) : S :=
  (if j = 0 then 1-x else 1) * (if j+1 = r then 1-y else 1)
def correction (r n : ℕ) (t : S) : S :=
  ∑ a ∈ Finset.range (n+1), (a+1 : ℕ) * t^(r*(a+1)) * gsum n (t^(r*(a+1)))
def raw (r n j : ℕ) (t x y : S) : S :=
  (if j = 0 then x else eqn r j x y ^ 2 * xterm n (t^j*x)) +
  eqn r j x y ^ 2 * (∑ a ∈ Finset.range (n+1), xterm n (t^(r*(a+1)+j)*x)) +
  (∑ a ∈ Finset.range (n+1), if a = 0 ∧ j+1 = r then y else
    eqn r j x y ^ 2 * xterm n (t^(r*(a+1)-j-1)*y)) -
  2 * eqn r j x y ^ 2 * correction r n t

def full (r n j : ℕ) (t x y : S) : S :=
  xterm n (t^j*x) +
  (∑ a ∈ Finset.range (n+1), xterm n (t^(r*(a+1)+j)*x)) +
  (∑ a ∈ Finset.range (n+1), xterm n (t^(r*(a+1)-j-1)*y)) -
  2 * correction r n t

lemma nilpotent_monomial (n e : ℕ) (t v : S) (ht : t^(n+1) = 0) (he : 0 < e) :
    (t^e*v)^(n+1) = 0 := by
  rw [mul_pow, ← pow_mul,
    pow_eq_zero_of_le (show n+1 ≤ e*(n+1) by nlinarith) ht, zero_mul]

lemma clear_xterm (n : ℕ) (v : S) (hv : v^(n+1) = 0) :
    (1-v)^2 * xterm n v = v := by
  have hg : gsum n v * (1-v) = 1 := by
    simpa [gsum, hv] using geom_sum_mul_neg v (n+1)
  calc
    _ = v * (gsum n v * (1-v))^2 := by unfold xterm; ring
    _ = v := by rw [hg]; ring

lemma raw_regular (r n j : ℕ) (h3 : 3 ≤ r) (hj : j < r) (t x y : S)
    (hx : j = 0 → x^(n+1) = 0) (hy : j+1 = r → y^(n+1) = 0) :
    raw r n j t x y = eqn r j x y ^ 2 * full r n j t x y := by
  have hf : (if j = 0 then x else eqn r j x y ^ 2 * xterm n (t^j*x)) =
      eqn r j x y ^ 2 * xterm n (t^j*x) := by
    split_ifs with hz
    · subst j
      simp only [eqn, ↓reduceIte, show ¬ (0+1 = r) by omega, mul_one, pow_zero, one_mul]
      exact (clear_xterm n x (hx rfl)).symm
    · rfl
  have hn (a : ℕ) :
      (if a = 0 ∧ j+1 = r then y else
        eqn r j x y ^ 2 * xterm n (t^(r*(a+1)-j-1)*y)) =
        eqn r j x y ^ 2 * xterm n (t^(r*(a+1)-j-1)*y) := by
    split_ifs with ha
    · obtain ⟨rfl, hlast⟩ := ha
      have hzero : j ≠ 0 := by omega
      simp only [eqn, hzero, ↓reduceIte, hlast, one_mul,
        Nat.zero_add, mul_one, show r-j-1 = 0 by omega, pow_zero]
      exact (clear_xterm n y (hy hlast)).symm
    · rfl
  simp only [raw, hf, hn, ← Finset.mul_sum, full]
  ring

lemma full_interior (r n j : ℕ) (hj : j+1 < r) (t x y : S) :
    full r n j t (t*x) y = full r n (j+1) t x (t*y) := by
  have hf : t^j*(t*x) = t^(j+1)*x := by rw [pow_succ]; ring
  have hp (a : ℕ) : t^(r*(a+1)+j)*(t*x) = t^(r*(a+1)+(j+1))*x := by
    rw [show r*(a+1)+(j+1) = (r*(a+1)+j)+1 by omega, pow_succ]; ring
  have hn (a : ℕ) : t^(r*(a+1)-j-1)*y = t^(r*(a+1)-(j+1)-1)*(t*y) := by
    have hm : r ≤ r*(a+1) := by nlinarith
    rw [show r*(a+1)-j-1 = (r*(a+1)-(j+1)-1)+1 by omega, pow_succ]; ring
  simp only [full, hf, hp, hn]

lemma raw_interior (r n j : ℕ) (h3 : 3 ≤ r) (hj : j+1 < r)
    (t x y : S) (ht : t^(n+1) = 0) :
    raw r n j t (t*x) y * eqn r (j+1) x (t*y)^2 =
      raw r n (j+1) t x (t*y) * eqn r j (t*x) y ^ 2 := by
  have hx : (t*x)^(n+1) = 0 := by rw [mul_pow, ht, zero_mul]
  have hy : (t*y)^(n+1) = 0 := by rw [mul_pow, ht, zero_mul]
  rw [raw_regular r n j h3 (by omega) t (t*x) y (fun _ => hx) (by omega),
    raw_regular r n (j+1) h3 hj t x (t*y) (by omega) (fun _ => hy),
    full_interior r n j hj]
  ring

def tail (r n : ℕ) (t v : S) : S :=
  ∑ a ∈ Finset.range (n+1), xterm n (t^(r*(a+1))*v)

lemma tail_endpoint (r n : ℕ) (hr : 0 < r) (t v : S) (ht : t^(n+1) = 0) :
    xterm n (t^(r*(n+1))*v) = 0 := by
  have hm : n+1 ≤ r*(n+1) := by simpa using Nat.mul_le_mul_right (n+1) hr
  simp [pow_eq_zero_of_le hm ht, xterm]

lemma tail_shift (r n : ℕ) (hr : 0 < r) (t v : S) (ht : t^(n+1) = 0) :
    xterm n (t^r*v) +
      (∑ a ∈ Finset.range (n+1), xterm n (t^(r*(a+2))*v)) = tail r n t v := by
  let f : ℕ → S := fun a => xterm n (t^(r*(a+1))*v)
  have hz : f (n+1) = 0 := by
    have hm : n+1 ≤ r*((n+1)+1) := by nlinarith
    simp [f, pow_eq_zero_of_le hm ht, xterm]
  have h₁ := Finset.sum_range_succ f (n+1)
  have h₂ := Finset.sum_range_succ' f (n+1)
  have hh : f 0 + (∑ a ∈ Finset.range (n+1), f (a+1)) =
      ∑ a ∈ Finset.range (n+1), f a := by
    rw [hz, add_zero] at h₁
    rw [h₂] at h₁
    simpa [add_comm] using h₁
  simpa [f, tail, Nat.add_assoc] using hh

lemma exceptional_tail (r n : ℕ) (hr : 0 < r) (t v H : S) (ht : t^(n+1) = 0) :
    (∑ a ∈ Finset.range (n+1), if a = 0 then v else H * xterm n (t^(r*a)*v)) =
      v + H * tail r n t v := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    ]
  rw [← Finset.mul_sum]
  have he : tail r n t v = ∑ a ∈ Finset.range n, xterm n (t^(r*(a+1))*v) := by
    rw [tail, Finset.sum_range_succ, tail_endpoint r n hr t v ht, add_zero]
  rw [he]
  ring

lemma raw_boundary_left (r n : ℕ) (h3 : 3 ≤ r) (t x y : S) (ht : t^(n+1) = 0) :
    raw r n (r-1) t (t*x) y =
      y + (1-y)^2 * (tail r n t x + tail r n t y - 2 * correction r n t) := by
  have hr : 0 < r := by omega
  have he : eqn r (r-1) (t*x) y = 1-y := by simp [eqn, show r-1 ≠ 0 by omega, Nat.sub_add_cancel hr]
  have hf : t^(r-1)*(t*x) = t^r*x := by
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  have hp (a : ℕ) : t^(r*(a+1)+(r-1))*(t*x) = t^(r*(a+2))*x := by
    rw [← mul_assoc, ← pow_succ]
    congr 2
    have hh : r-1+1 = r := Nat.sub_add_cancel hr
    nlinarith
  have hn (a : ℕ) : r*(a+1)-(r-1)-1 = r*a := by
    rw [Nat.mul_add, mul_one]
    omega
  simp only [raw, he, show r-1 ≠ 0 by omega, ↓reduceIte,
    Nat.sub_add_cancel hr, and_true, hf, hp, hn]
  rw [exceptional_tail r n hr t y ((1-y)^2) ht]
  have hs := tail_shift r n hr t x ht
  linear_combination (1-y)^2 * hs

lemma raw_boundary_right (r n : ℕ) (h3 : 3 ≤ r) (t x y : S) :
    raw r n 0 t x (t*y) =
      x + (1-x)^2 * (tail r n t x + tail r n t y - 2 * correction r n t) := by
  have he : eqn r 0 x (t*y) = 1-x := by simp [eqn, show 1 ≠ r by omega]
  have hn (a : ℕ) : t^(r*(a+1)-0-1)*(t*y) = t^(r*(a+1))*y := by
    rw [Nat.sub_zero, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by nlinarith : 1 ≤ r*(a+1))]
  simp only [raw, he, ↓reduceIte, Nat.zero_add, show ¬ (1 = r) by omega,
    and_false, Nat.add_zero, hn, ← Finset.mul_sum, tail]
  ring

lemma raw_boundary (r n : ℕ) (h3 : 3 ≤ r) (t x y : S)
    (ht : t^(n+1) = 0) (hxy : y*x = 1) :
    raw r n (r-1) t (t*x) y * eqn r 0 x (t*y)^2 =
      raw r n 0 t x (t*y) * eqn r (r-1) (t*x) y ^ 2 := by
  rw [raw_boundary_left r n h3 t x y ht, raw_boundary_right r n h3 t x y]
  have hl : eqn r (r-1) (t*x) y = 1-y := by
    simp [eqn, show r-1 ≠ 0 by omega, Nat.sub_add_cancel (show 1 ≤ r by omega)]
  have hr : eqn r 0 x (t*y) = 1-x := by simp [eqn, show 1 ≠ r by omega]
  rw [hl, hr]
  linear_combination (x-y) * hxy

end RingPolynomials

lemma map_numerator {S : Type*} [CommRing S] (r n : ℕ) (f : A k n →+* S) (i : Fin r) :
    f (numerator k false r n i) =
      raw r n i.val (f (tau k n)) (f (coordX k n)) (f (coordY k n)) := by
  classical
  have he : f (equation k r n i) = eqn r i.val (f (coordX k n)) (f (coordY k n)) := by
    unfold equation eqn
    split_ifs <;> simp
  have hm (v : A k n) : f (term k false n v) = xterm n (f v) := by
    simp [term, degree, geometric, xterm, gsum, map_sum]
  have hi (p : Prop) [Decidable p] (a b : A k n) :
      f (if p then a else b) = if p then f a else f b := by split_ifs <;> rfl
  simp only [numerator, degree, Bool.false_eq_true, ↓reduceIte, mul_one,
    map_add, map_sub, map_mul, map_pow, map_sum, map_natCast,
    map_ofNat, hi, he, hm, raw, correction, geometric, gsum]

lemma map_equation {S : Type*} [CommRing S] (r n : ℕ) (f : A k n →+* S)
    (i : Fin r) : f (equation k r n i) = eqn r i.val (f (coordX k n)) (f (coordY k n)) := by
  unfold equation eqn
  split_ifs <;> simp

/-- Compatibility uses the specified geometric adjacent map, including its cyclic edge. -/
lemma numerator_overlap (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E) :
    Compatible k r n hr E 2 (numerator k false r n) := by
  let L : A k n →+* B k n true := E.toRingHom.comp (restriction k n false)
  let R : A k n →+* B k n true := restriction k n true
  let t := R (tau k n)
  let x := R (coordX k n)
  let y := L (coordY k n)
  have ht : t^(n+1) = 0 := by
    dsimp [t]
    rw [← map_pow, tau_pow, map_zero]
  have hbase : L (tau k n) = t :=
    RingHom.congr_fun (adjacent_base hE) (parameter k n)
  have hxy : y*x = 1 := adjacent_y_mul_x hE
  have hl : L (coordX k n) * y = t := by
    dsimp only [y]
    rw [← map_mul, coordX_mul_coordY]
    exact hbase
  have hrp : x * R (coordY k n) = t := by
    dsimp only [x, t, tau]
    rw [← map_mul, coordX_mul_coordY]
  have hx : L (coordX k n) = t*x := by
    calc
      _ = L (coordX k n) * (y*x) := by rw [hxy, mul_one]
      _ = (L (coordX k n)*y)*x := by ring
      _ = t*x := by rw [hl]
  have hy : R (coordY k n) = t*y := by
    calc
      _ = (y*x)*R (coordY k n) := by rw [hxy, one_mul]
      _ = (x*R (coordY k n))*y := by ring
      _ = t*y := by rw [hrp]
  intro i
  change L (numerator k false r n i) * R (equation k r n (next r hr i))^2 =
    R (numerator k false r n (next r hr i)) * L (equation k r n i)^2
  rw [map_numerator, map_numerator, map_equation, map_equation, hbase, hx, hy]
  change raw r n i.val t (t*x) y * eqn r (next r hr i).val x (t*y)^2 =
    raw r n (next r hr i).val t x (t*y) * eqn r i.val (t*x) y ^ 2
  by_cases hi : i.val+1 = r
  · have hn : (next r hr i).val = 0 := by simp [next, hi]
    rw [hn, show i.val = r-1 by omega]
    exact raw_boundary r n h3 t x y ht hxy
  · have hj : i.val+1 < r := by omega
    have hn : (next r hr i).val = i.val+1 := Nat.mod_eq_of_lt hj
    rw [hn]
    exact raw_interior r n i.val h3 hj t x y ht

end TateXNumeratorSystemR0143

/-- The literal X coordinate supplies all chart and thickness equations. -/
theorem tate_x_numerator_system :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r)
      (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
      ArithmeticThetaAlgebraicCoordinatesR0143.CompatibleSystem k false T := by
  intro k _ _ r hr h3 T
  constructor
  · intro n
    exact TateXNumeratorSystemR0143.numerator_overlap k r n hr h3
      (T.overlap n) (T.overlap_spec n)
  · intro n N h i
    exact TateXNumeratorSystemR0143.numerator_reduction k r n N hr h i

end ArithmeticThetaAlgebraicCoordinatesR0143
