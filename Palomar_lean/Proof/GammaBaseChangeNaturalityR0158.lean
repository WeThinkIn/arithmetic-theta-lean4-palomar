module

public import CoefficientNormDescentDefinitionsR0157
public import LaurentNormDefinitionsR0064
public import RamifiedPeriodDefinitionsR0154

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaUnsplitExpansionR0158
namespace GammaBaseChangeNaturalityR0158
open ArithmeticThetaLaurentNormR0064

variable (k l : Type) [Field k] [Field l]

def coefficientHom (ι : k →+* l) : LaurentSeries k →+* LaurentSeries l where
  toFun f := f.map ι
  map_zero' := HahnSeries.map_zero ι.toZeroHom
  map_one' := HahnSeries.map_one ι.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add ι.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul ι.toNonUnitalRingHom

lemma coefficientHom_base (ι : k →+* l) (b : PowerSeries k) :
    coefficientHom k l ι (algebraMap (PowerSeries k) (LaurentSeries k) b) =
      algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι b) := by
  ext e
  change ι ((b : LaurentSeries k).coeff e) = ((PowerSeries.map ι b : PowerSeries l) : LaurentSeries l).coeff e
  simp only [PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

lemma coefficientHom_eq [CharZero k] [CharZero l] (ι : k →+* l)
    (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell) :
    ell = coefficientHom k l ι := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro b
  exact (hell b).trans (coefficientHom_base k l ι b).symm

lemma coefficientHom_single (ι : k →+* l) (e : ℤ) (a : k) :
    coefficientHom k l ι (HahnSeries.single e a) = HahnSeries.single e (ι a) :=
  HahnSeries.map_single ι.toZeroHom

lemma coefficientHom_partial (ι : k →+* l) (r m N : ℕ) (a : k) :
    coefficientHom k l ι (Partial k r m a N) = Partial l r m (ι a) N := by
  simp only [Partial, map_mul, map_prod, map_sub, map_one, HahnSeries.C_apply,
    coefficientHom_single, map_inv₀]

lemma coefficient_gamma [CharZero k] [CharZero l] (ι : k →+* l)
    (ell : LaurentSeries k →+* LaurentSeries l)
    (hell : ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell)
    (r m : ℕ) (a : k) (g : LaurentSeries k) (hg : IsGamma k r m a g) :
    IsGamma l r m (ι a) (ell g) := by
  rw [coefficientHom_eq k l ι ell hell]
  intro n
  obtain ⟨N₀, hN₀⟩ := hg n
  refine ⟨N₀, fun N hN e he => ?_⟩
  rw [← coefficientHom_partial k l ι r m N a]
  exact congrArg ι (hN₀ N hN e he)

variable (d : ℕ) (hd : 0 < d)

def scale : ℤ →+ ℤ where
  toFun e := (d : ℤ) * e
  map_zero' := mul_zero _
  map_add' := mul_add _

include hd in
lemma scale_injective : Function.Injective (scale d) := by
  intro a b h
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hd)) h

include hd in
lemma scale_order (a b : ℤ) : scale d a ≤ scale d b ↔ a ≤ b :=
  mul_le_mul_iff_right₀ (by exact_mod_cast hd)

def ramificationHom : LaurentSeries k →+* LaurentSeries k :=
  HahnSeries.embDomainRingHom (scale d) (scale_injective d hd) (scale_order d hd)

lemma ramificationHom_coeff (f : LaurentSeries k) (e : ℤ) :
    (ramificationHom k d hd f).coeff ((d : ℤ) * e) = f.coeff e :=
  HahnSeries.embDomain_coeff

lemma ramificationHom_coeff_zero (f : LaurentSeries k) (e : ℤ)
    (he : ¬ (d : ℤ) ∣ e) : (ramificationHom k d hd f).coeff e = 0 := by
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨a, ha⟩
  exact he ⟨a, ha.symm⟩

lemma ramificationHom_base (b : PowerSeries k) :
    ramificationHom k d hd (algebraMap (PowerSeries k) (LaurentSeries k) b) =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.expand d (Nat.ne_of_gt hd) b) := by
  ext e
  by_cases he : (d : ℤ) ∣ e
  · obtain ⟨z, rfl⟩ := he
    rw [ramificationHom_coeff]
    change (b : LaurentSeries k).coeff z =
      ((PowerSeries.expand d (Nat.ne_of_gt hd) b : PowerSeries k) : LaurentSeries k).coeff ((d : ℤ) * z)
    by_cases hz : z < 0
    · rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe, if_pos hz,
        if_pos (mul_neg_of_pos_of_neg (by exact_mod_cast hd) hz)]
    · have hz' : 0 ≤ z := le_of_not_gt hz
      lift z to ℕ using hz'
      simp only [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries]
      rw [PowerSeries.coeff_expand_mul]
  · rw [ramificationHom_coeff_zero k d hd _ e he]
    change 0 = ((PowerSeries.expand d (Nat.ne_of_gt hd) b : PowerSeries k) : LaurentSeries k).coeff e
    rw [PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · symm
      apply PowerSeries.coeff_expand_of_not_dvd
      intro h
      apply he
      have he0 : 0 ≤ e := le_of_not_gt hneg
      rw [Int.eq_natAbs_of_nonneg he0]
      exact_mod_cast h

lemma ramificationHom_eq [CharZero k] (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell) :
    ell = ramificationHom k d hd := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro b
  exact (hell b).trans (ramificationHom_base k d hd b).symm

lemma ramificationHom_single (e : ℤ) (a : k) :
    ramificationHom k d hd (HahnSeries.single e a) =
      HahnSeries.single ((d : ℤ) * e) a := HahnSeries.embDomain_single

lemma ramificationHom_partial (r m N : ℕ) (a : k) :
    ramificationHom k d hd (Partial k r m a N) = Partial k (r*d) (m*d) a N := by
  simp only [Partial, map_mul, map_prod, map_sub, map_one, HahnSeries.C_apply,
    ramificationHom_single, mul_zero]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro i hi <;>
    congr 3 <;> push_cast <;> ring

lemma ramification_gamma [CharZero k] (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell)
    (r m : ℕ) (a : k) (g : LaurentSeries k) (hg : IsGamma k r m a g) :
    IsGamma k (r*d) (m*d) a (ell g) := by
  rw [ramificationHom_eq k d hd ell hell]
  intro n
  obtain ⟨N₀, hN₀⟩ := hg (max n 0)
  refine ⟨N₀, fun N hN e he => ?_⟩
  rw [← ramificationHom_partial k d hd r m N a]
  by_cases hdiv : (d : ℤ) ∣ e
  · obtain ⟨z, rfl⟩ := hdiv
    rw [ramificationHom_coeff, ramificationHom_coeff]
    apply hN₀ N hN z
    have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hn : n ≤ max n 0 := le_max_left _ _
    have hzero : (0 : ℤ) ≤ max n 0 := le_max_right _ _
    by_cases hz : z ≤ 0
    · exact hz.trans hzero
    · nlinarith
  · rw [ramificationHom_coeff_zero k d hd _ e hdiv,
      ramificationHom_coeff_zero k d hd _ e hdiv]

end GammaBaseChangeNaturalityR0158


/-- Full Laurent gamma limits commute with coefficient extension and positive ramification. -/
theorem gamma_base_change_naturality :
    (∀ (k : Type) [Field k] [CharZero k] (l : Type) [Field l] [CharZero l] (ι : k →+* l) (ell : LaurentSeries k →+* LaurentSeries l), ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι ell → ∀ (r m : ℕ) (a : k) (g : LaurentSeries k), 0 < r → a ≠ 0 → ArithmeticThetaLaurentNormR0064.IsGamma k r m a g → ArithmeticThetaLaurentNormR0064.IsGamma l r m (ι a) (ell g)) ∧ (∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d) (ell : LaurentSeries k →+* LaurentSeries k), ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell → ∀ (r m : ℕ) (a : k) (g : LaurentSeries k), 0 < r → a ≠ 0 → ArithmeticThetaLaurentNormR0064.IsGamma k r m a g → ArithmeticThetaLaurentNormR0064.IsGamma k (r*d) (m*d) a (ell g)) := by
  constructor
  · intro k _ _ l _ _ ι ell hell r m a g _hr _ha hg
    exact GammaBaseChangeNaturalityR0158.coefficient_gamma k l ι ell hell r m a g hg
  · intro k _ _ d hd ell hell r m a g _hr _ha hg
    exact GammaBaseChangeNaturalityR0158.ramification_gamma k d hd ell hell r m a g hg

end ArithmeticThetaUnsplitExpansionR0158

#print axioms ArithmeticThetaUnsplitExpansionR0158.gamma_base_change_naturality
