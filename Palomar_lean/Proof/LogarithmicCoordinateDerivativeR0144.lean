module

public import CubicModelDefinitionsR0144
public import TateXNumeratorSystemR0143

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCubicModelR0144
namespace LogarithmicCoordinateDerivativeR0144
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143

section GeneralLift
variable {S : Type*} [CommRing S] [Algebra ℤ S]
local instance : Module Sᵐᵒᵖ S := Semiring.toOppositeModule

def secondDeriv (f : S →+* TrivSqZeroExt S S) (hf : ∀ z, (f z).fst = z) :
    Derivation ℤ S S where
  toFun z := (f z).snd
  map_add' a b := by simp only [map_add, TrivSqZeroExt.snd_add]
  map_smul' a b := by
    simp [Algebra.smul_def, hf]
  map_one_eq_zero' := by
    change (f 1).snd = 0
    rw [map_one]; rfl
  leibniz' a b := by
    change (f (a*b)).snd = a * (f b).snd + b * (f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hf, hf]
    change a * (f b).snd + (f a).snd * b = _
    rw [mul_comm (f a).snd b]

def derivLift (D : Derivation ℤ S S) : S →+* TrivSqZeroExt S S where
  toFun a := ⟨a, D a⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [D.leibniz, smul_eq_mul, mul_comm]
end GeneralLift

section General
variable {S : Type*} [CommRing S] [Algebra ℤ S] (D : Derivation ℤ S S)
lemma geometric_derivative (n : ℕ) (v : S) (hv : v^(n+1)=0) :
    D (∑ a ∈ Finset.range (n+1), v^a) =
      D v * (∑ a ∈ Finset.range (n+1), v^a)^2 := by
  let g := ∑ a ∈ Finset.range (n+1), v^a
  have hg : g*(1-v)=1 := by simpa [g, hv] using geom_sum_mul_neg v (n+1)
  have hd : D g * (1-v) - g * D v = 0 := by
    have hh := congrArg D hg
    simpa [D.leibniz, smul_eq_mul, mul_comm, mul_sub, sub_eq_add_neg] using hh
  change D g = D v * g^2
  linear_combination g * hd - D g * hg

lemma rational_derivative (n : ℕ) (v s : S) (hv : v^(n+1)=0)
    (hd : D v = s*v) :
    D (v*(∑ a ∈ Finset.range (n+1), v^a)^2) =
      s*(v*(1+v)*(∑ a ∈ Finset.range (n+1), v^a)^3) := by
  let g := ∑ a ∈ Finset.range (n+1), v^a
  have hg : g*(1-v)=1 := by simpa [g, hv] using geom_sum_mul_neg v (n+1)
  have hDg : D g = D v*g^2 := geometric_derivative D n v hv
  simp only [D.leibniz, D.leibniz_pow, smul_eq_mul, show 2-1=1 by decide,
    pow_one, Nat.cast_ofNat, nsmul_eq_mul]
  change v * (2 * (g * D g)) + g^2 * D v = s*(v*(1+v)*g^3)
  rw [hDg, hd]
  linear_combination -s*v*g^2*hg

lemma clear_derivative (h f : S) :
    h*D (h^2*f)-2*(h^2*f)*D h = h^3*D f := by
  simp only [D.leibniz, D.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  norm_num
  ring
def cleared (h : S) : S →+ S where
  toFun f := h * D f - 2*f*D h
  map_zero' := by simp
  map_add' a b := by simp only [map_add]; ring

lemma cleared_apply (h f : S) : cleared D h f = h*D f-2*f*D h := rfl
lemma cleared_square (h f : S) : cleared D h (h^2*f) = h^3*D f :=
  clear_derivative D h f

end General

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

local instance : Module (A k n)ᵐᵒᵖ (A k n) := Semiring.toOppositeModule

abbrev Dual := TrivSqZeroExt (A k n) (A k n)

def lift : A k n →+* Dual k n :=
  mkPoint ((TrivSqZeroExt.inlHom _ _).comp (base k n))
    ⟨coordX k n, coordX k n⟩ ⟨coordY k n, -coordY k n⟩ (by
      ext <;> simp [coordX_mul_coordY])

@[simp] lemma lift_x : lift k n (coordX k n) = ⟨coordX k n, coordX k n⟩ :=
  mkPoint_x _ _ _ _
@[simp] lemma lift_y : lift k n (coordY k n) = ⟨coordY k n, -coordY k n⟩ :=
  mkPoint_y _ _ _ _
@[simp] lemma lift_base (c : R k n) :
    lift k n (base k n c) = TrivSqZeroExt.inl (base k n c) :=
by
  have h := mkPoint_base ((TrivSqZeroExt.inlHom (A k n) (A k n)).comp (base k n))
    (⟨coordX k n, coordX k n⟩ : Dual k n)
    (⟨coordY k n, -coordY k n⟩ : Dual k n)
    (by ext <;> simp [coordX_mul_coordY])
  exact RingHom.congr_fun h c


lemma lift_fst (z : A k n) : (lift k n z).fst = z := by
  have h : (TrivSqZeroExt.fstHom ℤ (A k n) (A k n)).toRingHom.comp (lift k n) =
      RingHom.id _ := by
    apply point_ext
    · ext c; simp
    · simp
    · simp
  exact RingHom.congr_fun h z

def deriv : Derivation ℤ (A k n) (A k n) :=
  secondDeriv (lift k n) (lift_fst k n)

@[simp] lemma deriv_base (c : R k n) : deriv k n (base k n c) = 0 := by
  change (lift k n (base k n c)).snd = 0
  simp
@[simp] lemma deriv_x : deriv k n (coordX k n) = coordX k n := by
  change (lift k n (coordX k n)).snd = _
  simp
@[simp] lemma deriv_y : deriv k n (coordY k n) = -coordY k n := by
  change (lift k n (coordY k n)).snd = _
  simp

variable {k n}
lemma deriv_unique (D : Derivation ℤ (A k n) (A k n))
    (hb : ∀ c, D (base k n c) = 0)
    (hx : D (coordX k n) = coordX k n)
    (hy : D (coordY k n) = -coordY k n) : D = deriv k n := by
  have h : derivLift D = lift k n := by
    apply point_ext
    · ext c <;> simp [derivLift, hb]
    · simp [derivLift, hx]
    · simp [derivLift, hy]
  ext z
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun h z)

variable (k n)

@[simp] lemma deriv_tau : deriv k n (tau k n) = 0 := deriv_base k n _

lemma deriv_pow_zero (v : A k n) (hv : deriv k n v = 0) (a : ℕ) :
    deriv k n (v^a) = 0 := by
  simp [Derivation.leibniz_pow, hv]

lemma deriv_monomial_x (a : ℕ) :
    deriv k n (tau k n ^ a * coordX k n) = tau k n ^ a * coordX k n := by
  simp [Derivation.leibniz, smul_eq_mul]
lemma deriv_monomial_y (a : ℕ) :
    deriv k n (tau k n ^ a * coordY k n) = -(tau k n ^ a * coordY k n) := by
  simp [Derivation.leibniz, smul_eq_mul]

lemma deriv_term_x (a : ℕ) (ha : 0 < a) :
    deriv k n (term k false n (tau k n^a * coordX k n)) =
      term k true n (tau k n^a * coordX k n) := by
  simpa [term, degree, geometric] using rational_derivative (deriv k n) n
    (tau k n^a * coordX k n) 1
    (TateXNumeratorSystemR0143.monomial_nilpotent k n a ha _) (by simp)
lemma deriv_term_y (a : ℕ) (ha : 0 < a) :
    deriv k n (term k false n (tau k n^a * coordY k n)) =
      -term k true n (tau k n^a * coordY k n) := by
  simpa [term, degree, geometric] using rational_derivative (deriv k n) n
    (tau k n^a * coordY k n) (-1)
    (TateXNumeratorSystemR0143.monomial_nilpotent k n a ha _) (by simp)

lemma deriv_correction (r : ℕ) :
    deriv k n (∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1)))) = 0 := by
  simp [geometric, map_sum, Derivation.leibniz, smul_eq_mul]


lemma half_cancel :
    2 * base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹)) = 1 := by
  let f := (base k n).comp ((trunc (PowerSeries k) PowerSeries.X n).comp PowerSeries.C)
  have h : f (2 * (2 : k)⁻¹) = 1 := by rw [mul_inv_cancel₀ (by norm_num), map_one]
  simpa only [map_mul, map_ofNat, map_one, f, RingHom.comp_apply, PowerSeries.C_inv] using h

lemma numerator_derivative (r : ℕ) (hr : 3 ≤ r) (i : Fin r) :
    equation k r n i * deriv k n (numerator k false r n i) -
      2 * numerator k false r n i * deriv k n (equation k r n i) =
        2 * numerator k true r n i := by
  let h := equation k r n i
  let D := deriv k n
  let L := cleared D h
  have hsq (f : A k n) : L (h^2*f) = h^3*D f := cleared_square D h f
  have hfirst : L (if i.val = 0 then coordX k n else
      h^2 * term k false n (tau k n ^ i.val * coordX k n)) =
      if i.val = 0 then coordX k n * (1+coordX k n) else
      h^3 * term k true n (tau k n ^ i.val * coordX k n) := by
    split_ifs with hi
    · have hi' : i.val+1 ≠ r := by omega
      have hh : h = 1-coordX k n := by
        simp [h, equation, hi, show 1 ≠ r by omega]
      simp only [L, cleared_apply, hh, D, map_sub, Derivation.map_one_eq_zero, deriv_x]
      ring
    · rw [hsq, deriv_term_x k n _ (by omega)]
  have hpos : L (h^2 * ∑ a ∈ Finset.range (n+1),
      term k false n (tau k n ^ (r*(a+1)+i.val) * coordX k n)) =
      h^3 * ∑ a ∈ Finset.range (n+1),
      term k true n (tau k n ^ (r*(a+1)+i.val) * coordX k n) := by
    rw [hsq]
    simp only [D, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    exact deriv_term_x k n _ (by have hp : 0 < r*(a+1) := Nat.mul_pos (by omega) (by omega); omega)
  have hneg : L (∑ a ∈ Finset.range (n+1),
      if a = 0 ∧ i.val+1 = r then coordY k n else
      h^2 * term k false n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n)) =
      -(∑ a ∈ Finset.range (n+1),
      if a = 0 ∧ i.val+1 = r then coordY k n * (1+coordY k n) else
      h^3 * term k true n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n)) := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with hai
    · have hi : i.val ≠ 0 := by omega
      have hh : h = 1-coordY k n := by simp [h, equation, hi, hai.2]
      simp only [L, cleared_apply, hh, D, map_sub, Derivation.map_one_eq_zero, deriv_y]
      ring
    · rw [hsq, deriv_term_y k n _ (by
        have hil := i.isLt
        have hp : r*(a+1) = r*a+r := by ring
        by_cases ha0 : a=0
        · subst a; omega
        · have : r ≤ r*a := Nat.le_mul_of_pos_right r (by omega)
          omega)]
      ring
  have hcorr : L (2*h^2 * ∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1)))) = 0 := by
    rw [show 2*h^2 * (∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1)))) =
      h^2 * (2 * (∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1))))) by ring,
      hsq]
    change h^3 * deriv k n (2 * _) = 0
    rw [Derivation.leibniz, deriv_correction]
    have htwo : deriv k n 2 = 0 := by
      have hh := (deriv k n).map_add 1 1
      simpa only [one_add_one_eq_two, Derivation.map_one_eq_zero, add_zero] using hh
    simp [htwo]
  change L (numerator k false r n i) = _
  have heven : numerator k false r n i =
    (if i.val=0 then coordX k n else h^2*term k false n (tau k n^i.val*coordX k n)) +
    h^2*(∑ a ∈ Finset.range (n+1), term k false n (tau k n^(r*(a+1)+i.val)*coordX k n)) +
    (∑ a ∈ Finset.range (n+1), if a=0 ∧ i.val+1=r then coordY k n else
      h^2*term k false n (tau k n^(r*(a+1)-i.val-1)*coordY k n)) -
    2*h^2*(∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ)*tau k n^(r*(a+1))*geometric k n (tau k n^(r*(a+1)))) := by
    simp [numerator, degree, h]
  rw [heven, map_sub, map_add, map_add, hfirst, hpos, hneg, hcorr, sub_zero]
  simp only [numerator, degree, if_true]
  rw [← mul_assoc, half_cancel, one_mul]
  simp only [h, sub_eq_add_neg]


end LogarithmicCoordinateDerivativeR0144

/-- The unique logarithmic derivation relative to the actual truncated base,
with the full literal coordinate identity on every finite polygon chart. -/
theorem logarithmic_coordinate_derivative :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ n : ℕ,
      ArithmeticThetaCubicModelR0144.LogarithmicDerivative k n := by
  intro k _ _ n
  let D := LogarithmicCoordinateDerivativeR0144.deriv k n
  refine ⟨D, ⟨LogarithmicCoordinateDerivativeR0144.deriv_base k n,
    LogarithmicCoordinateDerivativeR0144.deriv_x k n,
    LogarithmicCoordinateDerivativeR0144.deriv_y k n, ?_⟩, ?_⟩
  · exact LogarithmicCoordinateDerivativeR0144.numerator_derivative k n
  · intro E hE
    exact LogarithmicCoordinateDerivativeR0144.deriv_unique E hE.1 hE.2.1 hE.2.2.1

end ArithmeticThetaCubicModelR0144

#print axioms ArithmeticThetaCubicModelR0144.logarithmic_coordinate_derivative
