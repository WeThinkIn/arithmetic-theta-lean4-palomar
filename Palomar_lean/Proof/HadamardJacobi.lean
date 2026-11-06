module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ArithmeticThetaHadamard

abbrev Vec := Fin 4 → ℤ

def matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

def hadamard (x : Vec) : Vec :=
  ![x 0 + x 1 + x 2 + x 3,
    x 0 + x 1 - x 2 - x 3,
    x 0 - x 1 + x 2 - x 3,
    x 0 - x 1 - x 2 + x 3]

def coordinateSum (x : Vec) : ℤ := x 0 + x 1 + x 2 + x 3
def squareNorm (x : Vec) : ℤ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2
def OddIntegral (x : Vec) : Prop := coordinateSum x % 2 = 1
def AllOdd (y : Vec) : Prop := ∀ i, y i % 2 = 1
def Half (e : ℤ) (y : Vec) : Prop := AllOdd y ∧ coordinateSum y % 4 = e
def inverse (y : Vec) : Vec := fun i => hadamard y i / 4
def reflect (y : Vec) : Vec := ![-y 0, y 1, y 2, y 3]

end ArithmeticThetaHadamard

namespace ArithmeticThetaHadamard

abbrev IntegralShell (m : ℕ) (e : ℤ) :=
  {x : Vec // coordinateSum x % 2 = e ∧ 4 * squareNorm x = (m : ℤ)}
abbrev HalfShell (m : ℕ) (e : ℤ) :=
  {y : Vec // Half e y ∧ squareNorm y = (m : ℤ)}
abbrev OddShell (m : ℕ) :=
  {y : Vec // AllOdd y ∧ squareNorm y = (m : ℤ)}

end ArithmeticThetaHadamard

namespace ArithmeticThetaHadamard

noncomputable def a : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ)} : ℤ))
noncomputable def b : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 0} : ℤ) -
  (Nat.card {r : ℤ // 4 * r ^ 2 = (m : ℤ) ∧ r % 2 = 1} : ℤ))
noncomputable def c : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card {r : ℤ // (2 * r + 1) ^ 2 = (m : ℤ)} : ℤ))
noncomputable def paritySeries (e : ℤ) : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card (IntegralShell m e) : ℤ))
noncomputable def allOddSeries : PowerSeries ℤ := PowerSeries.mk (fun m =>
  (Nat.card (OddShell m) : ℤ))

end ArithmeticThetaHadamard


namespace ArithmeticThetaHadamard

theorem matrix_mulVec (x : Vec) : matrix.mulVec x = hadamard x := by
  ext i
  fin_cases i <;> simp [matrix, hadamard, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem hadamard_twice (x : Vec) : hadamard (hadamard x) = fun i => 4 * x i := by
  ext i
  fin_cases i <;> simp [hadamard] <;> ring

theorem hadamard_norm (x : Vec) : squareNorm (hadamard x) = 4 * squareNorm x := by
  simp [squareNorm, hadamard]
  ring

theorem hadamard_half (x : Vec) (hx : OddIntegral x) : Half 0 (hadamard x) := by
  dsimp [OddIntegral, coordinateSum] at hx
  constructor
  · intro i
    fin_cases i <;> simp [hadamard] <;> omega
  · simp [coordinateSum, hadamard]
    omega

theorem half_hadamard_divisible (y : Vec) (hy : Half 0 y) :
    ∀ i, hadamard y i % 4 = 0 := by
  have h0 := hy.1 0
  have h1 := hy.1 1
  have h2 := hy.1 2
  have h3 := hy.1 3
  have hs := hy.2
  dsimp [coordinateSum] at hs
  intro i
  fin_cases i <;> simp [hadamard] <;> omega

theorem inverse_odd (y : Vec) (hy : Half 0 y) : OddIntegral (inverse y) := by
  have h0 := half_hadamard_divisible y hy 0
  have h1 := half_hadamard_divisible y hy 1
  have h2 := half_hadamard_divisible y hy 2
  have h3 := half_hadamard_divisible y hy 3
  have ho := hy.1 0
  simp [hadamard] at h0 h1 h2 h3
  simp [OddIntegral, coordinateSum, inverse, hadamard]
  omega

theorem inverse_hadamard (x : Vec) : inverse (hadamard x) = x := by
  ext i
  change hadamard (hadamard x) i / 4 = x i
  rw [hadamard_twice]
  simp

theorem hadamard_inverse (y : Vec) (hy : Half 0 y) : hadamard (inverse y) = y := by
  have h0 := half_hadamard_divisible y hy 0
  have h1 := half_hadamard_divisible y hy 1
  have h2 := half_hadamard_divisible y hy 2
  have h3 := half_hadamard_divisible y hy 3
  simp [hadamard] at h0 h1 h2 h3
  ext i
  fin_cases i <;> simp [hadamard, inverse] <;> omega

def oddHalfEquiv : {x : Vec // OddIntegral x} ≃ {y : Vec // Half 0 y} where
  toFun x := ⟨hadamard x, hadamard_half x x.property⟩
  invFun y := ⟨inverse y, inverse_odd y y.property⟩
  left_inv x := Subtype.ext (inverse_hadamard x)
  right_inv y := Subtype.ext (hadamard_inverse y y.property)

theorem reflect_twice (y : Vec) : reflect (reflect y) = y := by
  ext i
  fin_cases i <;> simp [reflect]

theorem reflect_norm (y : Vec) : squareNorm (reflect y) = squareNorm y := by
  simp [reflect, squareNorm]

theorem reflect_half (y : Vec) (e : ℤ) (he : e = 0 ∨ e = 2) (hy : Half e y) :
    Half (2 - e) (reflect y) := by
  have ho := hy.1 0
  have hs := hy.2
  constructor
  · intro i
    have hi := hy.1 i
    fin_cases i <;> simp [reflect] at * <;> omega
  · dsimp [coordinateSum] at hs
    simp [coordinateSum, reflect]
    rcases he with he | he <;> omega

def halfReflectionEquiv : {y : Vec // Half 0 y} ≃ {y : Vec // Half 2 y} where
  toFun y := ⟨reflect y, by simpa using reflect_half y 0 (Or.inl rfl) y.property⟩
  invFun y := ⟨reflect y, by simpa using reflect_half y 2 (Or.inr rfl) y.property⟩
  left_inv y := Subtype.ext (reflect_twice y)
  right_inv y := Subtype.ext (reflect_twice y)

theorem half_partition (y : Vec) (hy : AllOdd y) : Half 0 y ∨ Half 2 y := by
  have h0 := hy 0
  have h1 := hy 1
  have h2 := hy 2
  have h3 := hy 3
  have hs : coordinateSum y % 4 = 0 ∨ coordinateSum y % 4 = 2 := by
    dsimp [coordinateSum]
    omega
  rcases hs with hs | hs
  · exact Or.inl ⟨hy, hs⟩
  · exact Or.inr ⟨hy, hs⟩

theorem squareNorm_nonneg (x : Vec) : 0 ≤ squareNorm x := by
  dsimp [squareNorm]
  positivity

theorem half_offset_parity (r : Vec) (e : ℤ) :
    Half (2 * e) (fun i => 2 * r i + 1) ↔ coordinateSum r % 2 = e := by
  have ha : AllOdd (fun i => 2 * r i + 1) := by
    intro i
    change (2 * r i + 1) % 2 = 1
    omega
  simp only [Half, ha, true_and, coordinateSum]
  omega

theorem rational_half_norm (x : Vec) :
    (∑ i : Fin 4, ((hadamard x i : ℚ) / 2) ^ 2) =
      ∑ i : Fin 4, (x i : ℚ) ^ 2 := by
  simp [hadamard, Fin.sum_univ_succ]
  ring

theorem hadamard_matrix_identities :
    (∀ x : Vec, matrix.mulVec x = hadamard x) ∧
    (∀ x : Vec, hadamard (hadamard x) = fun i => 4 * x i) ∧
    (∀ x : Vec, squareNorm (hadamard x) = 4 * squareNorm x) :=
  ⟨matrix_mulVec, hadamard_twice, hadamard_norm⟩

theorem integral_half_correspondence :
    ∃ e : {x : Vec // OddIntegral x} ≃ {y : Vec // Half 0 y},
      (∀ x, (e x).val = hadamard x.val ∧
        squareNorm (e x).val = 4 * squareNorm x.val) ∧
      ∀ y, (e.symm y).val = inverse y.val := by
  refine ⟨oddHalfEquiv, ?_, ?_⟩
  · intro x
    exact ⟨rfl, hadamard_norm x.val⟩
  · intro y
    rfl

theorem half_reflection_correspondence :
    ∃ e : {y : Vec // Half 0 y} ≃ {y : Vec // Half 2 y},
      (∀ y, (e y).val = reflect y.val ∧
        squareNorm (e y).val = squareNorm y.val) ∧
      ∀ y, (e.symm y).val = reflect y.val := by
  refine ⟨halfReflectionEquiv, ?_, ?_⟩
  · intro y
    exact ⟨rfl, reflect_norm y.val⟩
  · intro y
    rfl

end ArithmeticThetaHadamard

namespace ArithmeticThetaHadamard

theorem coordinate_bound (x : Vec) (m : ℕ) (hm : squareNorm x ≤ (m : ℤ)) :
    ∀ i, -(m : ℤ) ≤ x i ∧ x i ≤ (m : ℤ) := by
  have h0 := sq_nonneg (x 0)
  have h1 := sq_nonneg (x 1)
  have h2 := sq_nonneg (x 2)
  have h3 := sq_nonneg (x 3)
  dsimp [squareNorm] at hm
  intro i
  have hi : (x i) ^ 2 ≤ (m : ℤ) := by
    fin_cases i <;> dsimp at * <;> nlinarith
  constructor
  · by_contra hn
    have hh : x i ≤ -(m : ℤ) - 1 := by omega
    nlinarith
  · by_contra hn
    have hh : (m : ℤ) + 1 ≤ x i := by omega
    nlinarith

theorem bounded_vectors_finite (m : ℕ) : Set.Finite {x : Vec | squareNorm x ≤ (m : ℤ)} := by
  apply (Set.Finite.pi (fun _ : Fin 4 => Set.finite_Icc (-(m : ℤ)) (m : ℤ))).subset
  intro x hx i _
  exact coordinate_bound x m hx i

instance integralShell_finite (m : ℕ) (e : ℤ) : Finite (IntegralShell m e) := by
  apply Set.Finite.to_subtype
  apply (bounded_vectors_finite m).subset
  intro x hx
  have h := squareNorm_nonneg x
  change squareNorm x ≤ (m : ℤ)
  have hx2 : 4 * squareNorm x = (m : ℤ) := hx.2
  omega

instance halfShell_finite (m : ℕ) (e : ℤ) : Finite (HalfShell m e) := by
  apply Set.Finite.to_subtype
  apply (bounded_vectors_finite m).subset
  intro y hy
  exact le_of_eq hy.2

instance oddShell_finite (m : ℕ) : Finite (OddShell m) := by
  apply Set.Finite.to_subtype
  apply (bounded_vectors_finite m).subset
  intro y hy
  exact le_of_eq hy.2

def oddHalfShellEquiv (m : ℕ) : IntegralShell m 1 ≃ HalfShell m 0 where
  toFun x := ⟨hadamard x, hadamard_half x x.property.1, by
    rw [hadamard_norm]
    exact x.property.2⟩
  invFun y := ⟨inverse y, inverse_odd y y.property.1, by
    have h := hadamard_norm (inverse y)
    rw [hadamard_inverse y y.property.1, y.property.2] at h
    exact h.symm⟩
  left_inv x := Subtype.ext (inverse_hadamard x)
  right_inv y := Subtype.ext (hadamard_inverse y y.property.1)

def halfShellReflectionEquiv (m : ℕ) : HalfShell m 0 ≃ HalfShell m 2 where
  toFun y := ⟨reflect y, by simpa using reflect_half y 0 (Or.inl rfl) y.property.1,
    by rw [reflect_norm]; exact y.property.2⟩
  invFun y := ⟨reflect y, by simpa using reflect_half y 2 (Or.inr rfl) y.property.1,
    by rw [reflect_norm]; exact y.property.2⟩
  left_inv y := Subtype.ext (reflect_twice y)
  right_inv y := Subtype.ext (reflect_twice y)

def oddShellSplit (m : ℕ) : OddShell m ≃ HalfShell m 0 ⊕ HalfShell m 2 where
  toFun y := if h : coordinateSum y % 4 = 0 then
    Sum.inl ⟨y, ⟨y.property.1, h⟩, y.property.2⟩
    else Sum.inr ⟨y, by
      rcases half_partition y y.property.1 with hp | hp
      · exact (h hp.2).elim
      · exact hp, y.property.2⟩
  invFun y := match y with
    | Sum.inl z => ⟨z, z.property.1.1, z.property.2⟩
    | Sum.inr z => ⟨z, z.property.1.1, z.property.2⟩
  left_inv y := by
    by_cases h : coordinateSum y % 4 = 0 <;> simp [h]
  right_inv y := by
    rcases y with y | y
    · simp only [y.property.1.2, ↓reduceDIte]
    · have hn : coordinateSum y % 4 ≠ 0 := by rw [y.property.1.2]; decide
      simp only [hn, ↓reduceDIte]

theorem count_odd_shell (m : ℕ) :
    Nat.card (OddShell m) = 2 * Nat.card (IntegralShell m 1) := by
  rw [Nat.card_congr (oddShellSplit m), Nat.card_sum]
  have h0 := Nat.card_congr (oddHalfShellEquiv m)
  have h2 := Nat.card_congr (halfShellReflectionEquiv m)
  omega

end ArithmeticThetaHadamard

namespace ArithmeticThetaHadamard

theorem exponent_nonnegative (r : ℤ) : 0 ≤ 4 * r ^ 2 ∧ 0 ≤ (2 * r + 1) ^ 2 := by
  constructor <;> positivity

theorem integer_sign (r : ℤ) : (-1 : ℚ) ^ r = if r % 2 = 0 then 1 else -1 := by
  simp only [neg_one_zpow_eq_ite, even_iff_two_dvd, Int.dvd_iff_emod_eq_zero]

theorem unary_fibers_finite (m : ℕ) :
    Set.Finite {r : ℤ | 4 * r ^ 2 = (m : ℤ)} ∧
    Set.Finite {r : ℤ | (2 * r + 1) ^ 2 = (m : ℤ)} := by
  constructor
  · apply (Set.finite_Icc (-(m : ℤ)) (m : ℤ)).subset
    intro r hr
    change 4 * r ^ 2 = (m : ℤ) at hr
    constructor
    · by_contra hn
      have hh : r ≤ -(m : ℤ) - 1 := by omega
      nlinarith
    · by_contra hn
      have hh : (m : ℤ) + 1 ≤ r := by omega
      nlinarith
  · apply (Set.finite_Icc (-(m : ℤ) - 1) ((m : ℤ) + 1)).subset
    intro r hr
    change (2 * r + 1) ^ 2 = (m : ℤ) at hr
    constructor
    · by_contra hn
      have hh : r ≤ -(m : ℤ) - 2 := by omega
      nlinarith
    · by_contra hn
      have hh : (m : ℤ) + 2 ≤ r := by omega
      nlinarith

theorem allOddSeries_eq : allOddSeries = paritySeries 1 + paritySeries 1 := by
  ext m
  simp only [allOddSeries, paritySeries, PowerSeries.coeff_mk, map_add]
  have h := count_odd_shell m
  exact_mod_cast (show Nat.card (OddShell m) =
    Nat.card (IntegralShell m 1) + Nat.card (IntegralShell m 1) by omega)

theorem shell_series_identity : paritySeries 0 + paritySeries 1 =
    (paritySeries 0 - paritySeries 1) + allOddSeries := by
  rw [allOddSeries_eq]
  ring

end ArithmeticThetaHadamard

namespace ArithmeticThetaHadamard

theorem coefficient_finiteness (m : ℕ) :
    Set.Finite {r : ℤ | 4 * r ^ 2 = (m : ℤ)} ∧
    Set.Finite {r : ℤ | (2 * r + 1) ^ 2 = (m : ℤ)} ∧
    Finite (IntegralShell m 0) ∧ Finite (IntegralShell m 1) ∧
    Finite (HalfShell m 0) ∧ Finite (HalfShell m 2) ∧ Finite (OddShell m) :=
  ⟨(unary_fibers_finite m).1, (unary_fibers_finite m).2,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end ArithmeticThetaHadamard


namespace ArithmeticThetaHadamard

open scoped BigOperators

theorem coeff_pow_congr (F G : PowerSeries ℤ) (n k : ℕ)
    (h : ∀ d ≤ n, PowerSeries.coeff d F = PowerSeries.coeff d G) :
    ∀ d ≤ n, PowerSeries.coeff d (F^k) = PowerSeries.coeff d (G^k) := by
  induction k with
  | zero => intro d hd; rfl
  | succ k ih =>
    intro d hd
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [ih p.1 (by omega), h p.2 (by omega)]

theorem card_subtype_eq_sum {α β : Type*} [Fintype β] (f : β → α)
    (hf : Function.Injective f) (P : α → Prop) [DecidablePred P]
    (hcover : ∀ a, P a → ∃ b, f b=a) :
    (Nat.card {a : α // P a} : ℤ) = ∑ b : β, if P (f b) then 1 else 0 := by
  classical
  let g : {b : β // P (f b)} → {a : α // P a} := fun b => ⟨f b.1,b.2⟩
  have hg : Function.Bijective g := by
    constructor
    · intro b c h
      apply Subtype.ext
      exact hf (congrArg Subtype.val h)
    · intro a
      obtain ⟨b,hb⟩ := hcover a.1 a.2
      refine ⟨⟨b, ?_⟩, ?_⟩
      · simpa only [hb] using a.2
      · apply Subtype.ext
        exact hb
  rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp

abbrev Box (n : ℕ) := {r : ℤ // r ∈ Finset.Icc (-(n : ℤ)-1) ((n : ℤ)+1)}

def boxVector (n : ℕ) (x : Fin 4 → Box n) : Vec := fun i => (x i).1

theorem boxVector_injective (n : ℕ) : Function.Injective (boxVector n) := by
  intro x y h
  funext i
  apply Subtype.ext
  exact congrFun h i

theorem integral_fiber_bound (n d : ℕ) (r : ℤ) (hd : d≤n)
    (hr : 4*r^2=(d : ℤ)) : r ∈ Finset.Icc (-(n : ℤ)-1) ((n : ℤ)+1) := by
  simp only [Finset.mem_Icc]
  constructor <;> nlinarith [sq_nonneg (r+1), sq_nonneg (r-1)]

theorem odd_fiber_bound (n d : ℕ) (r : ℤ) (hd : d≤n)
    (hr : (2*r+1)^2=(d : ℤ)) : r ∈ Finset.Icc (-(n : ℤ)-1) ((n : ℤ)+1) := by
  simp only [Finset.mem_Icc]
  constructor <;> nlinarith [sq_nonneg r]

noncomputable def finiteUnary (n : ℕ) (f : ℤ → ℕ) (w : ℤ → ℤ) : PowerSeries ℤ :=
  ∑ r : Box n, PowerSeries.monomial (f r.1) (w r.1)

theorem finiteUnary_coeff (n d : ℕ) (f : ℤ → ℕ) (w : ℤ → ℤ) :
    PowerSeries.coeff d (finiteUnary n f w) =
      ∑ r : Box n, if f r.1=d then w r.1 else 0 := by
  simp [finiteUnary, PowerSeries.coeff_monomial, eq_comm]

theorem finiteUnary_fourth_coeff (n d : ℕ) (f : ℤ → ℕ) (w : ℤ → ℤ) :
    PowerSeries.coeff d ((finiteUnary n f w)^4) =
      ∑ x : Fin 4 → Box n, if (∑ i : Fin 4, f (x i).1)=d then
        (∏ i : Fin 4, w (x i).1) else 0 := by
  unfold finiteUnary
  rw [Fintype.sum_pow]
  simp only [PowerSeries.prod_monomial, map_sum, PowerSeries.coeff_monomial, eq_comm]

def integralExponent (r : ℤ) : ℕ := (4*r^2).toNat
def oddExponent (r : ℤ) : ℕ := ((2*r+1)^2).toNat
def paritySign (r : ℤ) : ℤ := if r%2=0 then 1 else -1

theorem integralExponent_cast (r : ℤ) : (integralExponent r : ℤ)=4*r^2 :=
  Int.toNat_of_nonneg (by positivity)
theorem oddExponent_cast (r : ℤ) : (oddExponent r : ℤ)=(2*r+1)^2 :=
  Int.toNat_of_nonneg (by positivity)

theorem integralExponent_eq (r : ℤ) (d : ℕ) : integralExponent r=d ↔ 4*r^2=(d : ℤ) := by
  rw [← integralExponent_cast]
  exact Nat.cast_inj.symm

theorem oddExponent_eq (r : ℤ) (d : ℕ) : oddExponent r=d ↔ (2*r+1)^2=(d : ℤ) := by
  rw [← oddExponent_cast]
  exact Nat.cast_inj.symm

theorem a_finite_coeff (n d : ℕ) (hd : d≤n) :
    PowerSeries.coeff d a = PowerSeries.coeff d (finiteUnary n integralExponent (fun _ => 1)) := by
  rw [a, PowerSeries.coeff_mk, finiteUnary_coeff]
  simp only [integralExponent_eq]
  apply card_subtype_eq_sum (fun r : Box n => r.1) Subtype.val_injective
  intro r hr
  exact ⟨⟨r,integral_fiber_bound n d r hd hr⟩,rfl⟩

theorem b_finite_coeff (n d : ℕ) (hd : d≤n) :
    PowerSeries.coeff d b = PowerSeries.coeff d (finiteUnary n integralExponent paritySign) := by
  rw [b, PowerSeries.coeff_mk, finiteUnary_coeff]
  have hc (e : ℤ) : (Nat.card {r : ℤ // 4*r^2=(d : ℤ) ∧ r%2=e} : ℤ) =
      ∑ r : Box n, if 4*r.1^2=(d : ℤ) ∧ r.1%2=e then 1 else 0 := by
    apply card_subtype_eq_sum (fun r : Box n => r.1) Subtype.val_injective
    intro r hr
    exact ⟨⟨r,integral_fiber_bound n d r hd hr.1⟩,rfl⟩
  rw [hc 0,hc 1,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hs : 4*r.1^2=(d : ℤ)
  · by_cases he : r.1%2=0
    · simp [integralExponent_eq, paritySign, hs,he]
    · have ho : r.1%2=1 := by omega
      simp [integralExponent_eq, paritySign, hs,ho]
  · simp [integralExponent_eq, hs]

theorem c_finite_coeff (n d : ℕ) (hd : d≤n) :
    PowerSeries.coeff d c = PowerSeries.coeff d (finiteUnary n oddExponent (fun _ => 1)) := by
  rw [c, PowerSeries.coeff_mk, finiteUnary_coeff]
  simp only [oddExponent_eq]
  apply card_subtype_eq_sum (fun r : Box n => r.1) Subtype.val_injective
  intro r hr
  exact ⟨⟨r,odd_fiber_bound n d r hd hr⟩,rfl⟩

theorem integral_exponent_sum (n : ℕ) (x : Fin 4 → Box n) :
    ((∑ i : Fin 4, integralExponent (x i).1) : ℤ)=4*squareNorm (boxVector n x) := by
  simp only [integralExponent_cast]
  simp [Fin.sum_univ_succ, squareNorm, boxVector]
  ring

theorem paritySign_add (r s : ℤ) : paritySign (r+s)=paritySign r*paritySign s := by
  unfold paritySign
  by_cases hr : r%2=0 <;> by_cases hs : s%2=0
  · have hh : (r+s)%2=0 := by omega
    simp [hr,hs,hh]
  · have hh : (r+s)%2≠0 := by omega
    simp [hr,hs,hh]
  · have hh : (r+s)%2≠0 := by omega
    simp [hr,hs,hh]
  · have hh : (r+s)%2=0 := by omega
    simp [hr,hs,hh]

theorem paritySign_product (n : ℕ) (x : Fin 4 → Box n) :
    (∏ i : Fin 4, paritySign (x i).1) = paritySign (coordinateSum (boxVector n x)) := by
  simp [Fin.prod_univ_succ, coordinateSum, boxVector, paritySign_add, mul_assoc]

theorem integral_shell_box_cover (n : ℕ) (e : ℤ) (y : Vec)
    (hy : coordinateSum y%2=e ∧ 4*squareNorm y=(n : ℤ)) :
    ∃ x : Fin 4 → Box n, boxVector n x=y := by
  have hn : squareNorm y≤(n : ℤ) := by
    have hs := squareNorm_nonneg y
    omega
  have hb := coordinate_bound y n hn
  refine ⟨fun i => ⟨y i, ?_⟩, rfl⟩
  simp only [Finset.mem_Icc]
  have hi := hb i
  omega

theorem integral_shell_card_sum (n : ℕ) (e : ℤ) :
    (Nat.card (IntegralShell n e) : ℤ) =
      ∑ x : Fin 4 → Box n,
        if coordinateSum (boxVector n x)%2=e ∧ 4*squareNorm (boxVector n x)=(n : ℤ)
        then 1 else 0 := by
  apply card_subtype_eq_sum (boxVector n) (boxVector_injective n)
  exact integral_shell_box_cover n e

theorem a_fourth_power : a^4=paritySeries 0+paritySeries 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pow_congr a (finiteUnary n integralExponent (fun _ => 1)) n 4
    (fun d hd => a_finite_coeff n d hd) n le_rfl, finiteUnary_fourth_coeff]
  simp only [paritySeries, map_add, PowerSeries.coeff_mk, Finset.prod_const_one]
  rw [integral_shell_card_sum n 0, integral_shell_card_sum n 1, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : (∑ i : Fin 4, integralExponent (x i).1)=n ↔
      4*squareNorm (boxVector n x)=(n : ℤ) := by
    rw [← integral_exponent_sum]
    exact Nat.cast_inj.symm
  simp only [hexp]
  by_cases hn : 4*squareNorm (boxVector n x)=(n : ℤ)
  · by_cases he : coordinateSum (boxVector n x)%2=0
    · simp [hn,he]
    · have ho : coordinateSum (boxVector n x)%2=1 := by omega
      simp [hn,ho]
  · simp [hn]

theorem b_fourth_power : b^4=paritySeries 0-paritySeries 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pow_congr b (finiteUnary n integralExponent paritySign) n 4
    (fun d hd => b_finite_coeff n d hd) n le_rfl, finiteUnary_fourth_coeff]
  simp only [paritySeries, map_sub, PowerSeries.coeff_mk]
  rw [integral_shell_card_sum n 0, integral_shell_card_sum n 1, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : (∑ i : Fin 4, integralExponent (x i).1)=n ↔
      4*squareNorm (boxVector n x)=(n : ℤ) := by
    rw [← integral_exponent_sum]
    exact Nat.cast_inj.symm
  simp only [hexp, paritySign_product]
  by_cases hn : 4*squareNorm (boxVector n x)=(n : ℤ)
  · by_cases he : coordinateSum (boxVector n x)%2=0
    · simp [paritySign,hn,he]
    · have ho : coordinateSum (boxVector n x)%2=1 := by omega
      simp [paritySign,hn,ho]
  · simp [hn]

def oddBoxVector (n : ℕ) (x : Fin 4 → Box n) : Vec := fun i => 2*(x i).1+1

theorem oddBoxVector_injective (n : ℕ) : Function.Injective (oddBoxVector n) := by
  intro x y h
  funext i
  apply Subtype.ext
  have hi := congrFun h i
  change 2*(x i).1+1=2*(y i).1+1 at hi
  omega

theorem oddBoxVector_odd (n : ℕ) (x : Fin 4 → Box n) : AllOdd (oddBoxVector n x) := by
  intro i
  change (2*(x i).1+1)%2=1
  omega

theorem odd_shell_box_cover (n : ℕ) (y : Vec)
    (hy : AllOdd y ∧ squareNorm y=(n : ℤ)) :
    ∃ x : Fin 4 → Box n, oddBoxVector n x=y := by
  have hb := coordinate_bound y n (by omega)
  have hi (i : Fin 4) : (y i-1)/2 ∈ Finset.Icc (-(n : ℤ)-1) ((n : ℤ)+1) := by
    simp only [Finset.mem_Icc]
    have hbi := hb i
    omega
  refine ⟨fun i => ⟨(y i-1)/2,hi i⟩, ?_⟩
  funext i
  have ho := hy.1 i
  change 2*((y i-1)/2)+1=y i
  omega

theorem odd_shell_card_sum (n : ℕ) :
    (Nat.card (OddShell n) : ℤ) =
      ∑ x : Fin 4 → Box n, if squareNorm (oddBoxVector n x)=(n : ℤ) then 1 else 0 := by
  classical
  have h := card_subtype_eq_sum (oddBoxVector n) (oddBoxVector_injective n)
    (fun y => AllOdd y ∧ squareNorm y=(n : ℤ)) (odd_shell_box_cover n)
  simpa only [oddBoxVector_odd, true_and] using h

theorem odd_exponent_sum (n : ℕ) (x : Fin 4 → Box n) :
    ((∑ i : Fin 4, oddExponent (x i).1) : ℤ)=squareNorm (oddBoxVector n x) := by
  simp only [oddExponent_cast]
  simp [Fin.sum_univ_succ, squareNorm, oddBoxVector, add_assoc]

theorem c_fourth_power : c^4=allOddSeries := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pow_congr c (finiteUnary n oddExponent (fun _ => 1)) n 4
    (fun d hd => c_finite_coeff n d hd) n le_rfl, finiteUnary_fourth_coeff]
  simp only [allOddSeries, PowerSeries.coeff_mk, Finset.prod_const_one]
  rw [odd_shell_card_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : (∑ i : Fin 4, oddExponent (x i).1)=n ↔
      squareNorm (oddBoxVector n x)=(n : ℤ) := by
    rw [← odd_exponent_sum]
    exact Nat.cast_inj.symm
  simp only [hexp]

theorem jacobi_formal : a^4=b^4+c^4 := by
  rw [a_fourth_power, b_fourth_power, c_fourth_power]
  exact shell_series_identity

end ArithmeticThetaHadamard

#print axioms ArithmeticThetaHadamard.a_fourth_power
#print axioms ArithmeticThetaHadamard.b_fourth_power
#print axioms ArithmeticThetaHadamard.c_fourth_power
#print axioms ArithmeticThetaHadamard.jacobi_formal
