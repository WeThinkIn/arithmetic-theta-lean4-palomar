import Rank16Definitions
import HadamardJacobi


namespace ArithmeticThetaRank16

theorem rational_norm (n : ℕ) (y : Vec n) :
    (∑ i, ((y i : ℚ)/2)^2)/2=(normNumerator n y : ℚ)/8 := by
  simp only [normNumerator, Int.cast_sum, Int.cast_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem norm_nonnegative (n : ℕ) (y : Vec n) : 0≤normNumerator n y := by
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (y i))

theorem coordinate_square_le (n : ℕ) (y : Vec n) (i : Fin n) :
    y i^2≤normNumerator n y := by
  exact Finset.single_le_sum (fun j hj => sq_nonneg (y j)) (Finset.mem_univ i)

theorem coordinate_bound (n m : ℕ) (y : Vec n) (hy : normNumerator n y≤(m : ℤ)) :
    ∀ i, -(m : ℤ)≤y i ∧ y i≤(m : ℤ) := by
  intro i
  have hi := (coordinate_square_le n y i).trans hy
  constructor
  · by_contra h
    have hh : y i≤-(m : ℤ)-1 := by omega
    nlinarith
  · by_contra h
    have hh : (m : ℤ)+1≤y i := by omega
    nlinarith

theorem bounded_vectors_finite (n m : ℕ) :
    Set.Finite {y : Vec n | normNumerator n y≤(m : ℤ)} := by
  apply (Set.Finite.pi (fun _ : Fin n => Set.finite_Icc (-(m : ℤ)) (m : ℤ))).subset
  intro y hy i hi
  exact coordinate_bound n m y hy i

instance normShell_finite (n m : ℕ) : Finite (NormShell n m) := by
  apply Set.Finite.to_subtype
  apply (bounded_vectors_finite n m).subset
  intro y hy
  exact le_of_eq hy.2

instance sumNormShell_finite (m : ℕ) : Finite (SumNormShell m) := by
  apply Set.Finite.to_subtype
  apply ((bounded_vectors_finite 8 m).prod (bounded_vectors_finite 8 m)).subset
  intro y hy
  have h1 := norm_nonnegative 8 y.1
  have h2 := norm_nonnegative 8 y.2
  constructor <;> change normNumerator 8 _≤(m : ℤ) <;> linarith [hy.2.2]

theorem shell_finiteness (n m : ℕ) : Finite (NormShell n m) ∧ Finite (SumNormShell m) :=
  ⟨inferInstance,inferInstance⟩

theorem square_mod_two (r : ℤ) : r^2%2=r%2 := by
  rw [pow_two, Int.mul_emod]
  by_cases h : r%2=0
  · simp [h]
  · have h1 : r%2=1 := by omega
    simp [h1]

theorem odd_square_mod_eight (r : ℤ) (hr : r%2=1) : r^2%8=1 := by
  have hlo : 0≤r%8 := Int.emod_nonneg r (by norm_num)
  have hhi : r%8<8 := Int.emod_lt_of_pos r (by norm_num)
  interval_cases h : r%8 <;> norm_num [pow_two, Int.mul_emod, h] <;> omega

theorem norm_divisible_eight (n : ℕ) (hn : 8∣n) (y : Vec n)
    (hy : DPlusDoubled n y) : (8 : ℤ)∣normNumerator n y := by
  rcases hy.1 with he|ho
  · let x : Vec n := fun i => y i/2
    have hx (i : Fin n) : y i=2*x i := by
      have h := he i
      dsimp [x]
      omega
    have hsum : (∑ i, y i)=2*∑ i,x i := by simp only [hx, Finset.mul_sum]
    have heven : (∑ i,x i)%2=0 := by
      have hh := hy.2
      rw [hsum] at hh
      omega
    have hsq : normNumerator n x%2=0 := by
      rw [normNumerator, Finset.sum_int_mod]
      simp_rw [square_mod_two]
      rw [← Finset.sum_int_mod]
      exact heven
    have hnorm : normNumerator n y=4*normNumerator n x := by
      simp only [normNumerator, hx, mul_pow, Finset.mul_sum]
      norm_num
    obtain ⟨k,hk⟩ := Int.dvd_of_emod_eq_zero hsq
    refine ⟨k, ?_⟩
    rw [hnorm,hk]
    ring
  · have hs : normNumerator n y%8=(n : ℤ)%8 := by
      rw [normNumerator, Finset.sum_int_mod]
      simp_rw [odd_square_mod_eight _ (ho _)]
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    apply Int.dvd_of_emod_eq_zero
    rw [hs]
    have hcast : (8 : ℤ)∣(n : ℤ) := by exact_mod_cast hn
    exact Int.emod_eq_zero_of_dvd hcast

end ArithmeticThetaRank16


namespace ArithmeticThetaRank16

open ArithmeticThetaHadamard (Box integralExponent oddExponent paritySign finiteUnary)

abbrev VBox (n m : ℕ) := Fin n → Box m

def integralCoordinates (n : ℕ) (x : Vec n) : Vec n := fun i => 2*x i
def halfCoordinates (n : ℕ) (x : Vec n) : Vec n := fun i => 2*x i+1

def forgetBox (n m : ℕ) (x : VBox n m) : Vec n := fun i => (x i).1

abbrev IntegralParityShell (n m : ℕ) (e : ℤ) :=
  {x : Vec n // (∑ i,x i)%2=e ∧ 4*normNumerator n x=(m : ℤ)}
abbrev HalfParityShell (n m : ℕ) (e : ℤ) :=
  {x : Vec n // (∑ i,x i)%2=e ∧ normNumerator n (halfCoordinates n x)=(m : ℤ)}

noncomputable def integralParitySeries (n : ℕ) (e : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (IntegralParityShell n m e) : ℤ))
noncomputable def halfParitySeries (n : ℕ) (e : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (Nat.card (HalfParityShell n m e) : ℤ))

theorem finiteUnary_power_coeff (n m d : ℕ) (f : ℤ → ℕ) (w : ℤ → ℤ) :
    PowerSeries.coeff d ((finiteUnary m f w)^n) =
      ∑ x : VBox n m, if (∑ i : Fin n,f (x i).1)=d then
        (∏ i : Fin n,w (x i).1) else 0 := by
  unfold finiteUnary
  rw [Fintype.sum_pow]
  simp only [PowerSeries.prod_monomial, map_sum, PowerSeries.coeff_monomial, eq_comm]

theorem forgetBox_injective (n m : ℕ) : Function.Injective (forgetBox n m) := by
  intro x y h
  funext i
  apply Subtype.ext
  exact congrFun h i

theorem integral_exponent_sum (n m : ℕ) (x : VBox n m) :
    ((∑ i : Fin n,integralExponent (x i).1) : ℤ)=4*normNumerator n (forgetBox n m x) := by
  simp [ArithmeticThetaHadamard.integralExponent_cast, normNumerator, forgetBox, Finset.mul_sum]

theorem half_exponent_sum (n m : ℕ) (x : VBox n m) :
    ((∑ i : Fin n,oddExponent (x i).1) : ℤ)=normNumerator n (halfCoordinates n (forgetBox n m x)) := by
  simp [ArithmeticThetaHadamard.oddExponent_cast, normNumerator, halfCoordinates, forgetBox]

theorem paritySign_sum {ι : Type*} (s : Finset ι) (x : ι → ℤ) :
    (∏ i ∈ s,paritySign (x i))=paritySign (∑ i ∈ s,x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [paritySign]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi,
      ArithmeticThetaHadamard.paritySign_add, ih]

theorem integral_param_cover (n m : ℕ) (e : ℤ) (y : Vec n)
    (hy : (∑ i,y i)%2=e ∧ 4*normNumerator n y=(m : ℤ)) :
    ∃ x : VBox n m, forgetBox n m x=y := by
  have hn := norm_nonnegative n y
  have hb := coordinate_bound n m y (by omega)
  refine ⟨fun i => ⟨y i, ?_⟩,rfl⟩
  simp only [Finset.mem_Icc]
  have hi := hb i
  omega

theorem half_param_cover (n m : ℕ) (y : Vec n)
    (hy : normNumerator n (halfCoordinates n y)=(m : ℤ)) :
    ∃ x : VBox n m, forgetBox n m x=y := by
  have hb := coordinate_bound n m (halfCoordinates n y) (by omega)
  refine ⟨fun i => ⟨y i, ?_⟩,rfl⟩
  simp only [Finset.mem_Icc]
  have hi := hb i
  change -(m : ℤ)≤2*y i+1 ∧ 2*y i+1≤(m : ℤ) at hi
  omega

theorem integral_param_card (n m : ℕ) (e : ℤ) :
    (Nat.card (IntegralParityShell n m e) : ℤ)=
      ∑ x : VBox n m, if (∑ i,(x i).1)%2=e ∧
        4*normNumerator n (forgetBox n m x)=(m : ℤ) then 1 else 0 := by
  apply ArithmeticThetaHadamard.card_subtype_eq_sum (forgetBox n m) (forgetBox_injective n m)
  exact integral_param_cover n m e

theorem half_param_card (n m : ℕ) (e : ℤ) :
    (Nat.card (HalfParityShell n m e) : ℤ)=
      ∑ x : VBox n m, if (∑ i,(x i).1)%2=e ∧
        normNumerator n (halfCoordinates n (forgetBox n m x))=(m : ℤ) then 1 else 0 := by
  apply ArithmeticThetaHadamard.card_subtype_eq_sum (forgetBox n m) (forgetBox_injective n m)
  intro y hy
  exact half_param_cover n m y hy.2

theorem a_power (n : ℕ) : ArithmeticThetaHadamard.a^n=integralParitySeries n 0+integralParitySeries n 1 := by
  apply PowerSeries.ext
  intro m
  rw [ArithmeticThetaHadamard.coeff_pow_congr _ (finiteUnary m integralExponent (fun _ => 1)) m n
    (fun d hd => ArithmeticThetaHadamard.a_finite_coeff m d hd) m le_rfl, finiteUnary_power_coeff]
  simp only [integralParitySeries, map_add, PowerSeries.coeff_mk, Finset.prod_const_one]
  rw [integral_param_card,integral_param_card,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : (∑ i : Fin n,integralExponent (x i).1)=m ↔
      4*normNumerator n (forgetBox n m x)=(m : ℤ) := by
    rw [← integral_exponent_sum]
    rw [← Nat.cast_sum]
    exact (Nat.cast_inj (R := ℤ)).symm
  simp only [hexp]
  by_cases he : (∑ i,(x i).1)%2=0
  · simp [he]
  · have ho : (∑ i,(x i).1)%2=1 := by omega
    simp [ho]

theorem b_power (n : ℕ) : ArithmeticThetaHadamard.b^n=integralParitySeries n 0-integralParitySeries n 1 := by
  apply PowerSeries.ext
  intro m
  rw [ArithmeticThetaHadamard.coeff_pow_congr _ (finiteUnary m integralExponent paritySign) m n
    (fun d hd => ArithmeticThetaHadamard.b_finite_coeff m d hd) m le_rfl, finiteUnary_power_coeff]
  simp only [integralParitySeries, map_sub, PowerSeries.coeff_mk]
  rw [integral_param_card,integral_param_card,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : (∑ i : Fin n,integralExponent (x i).1)=m ↔
      4*normNumerator n (forgetBox n m x)=(m : ℤ) := by
    rw [← integral_exponent_sum]
    rw [← Nat.cast_sum]
    exact (Nat.cast_inj (R := ℤ)).symm
  simp only [hexp,paritySign_sum]
  by_cases he : (∑ i,(x i).1)%2=0
  · simp [paritySign,he]
  · have ho : (∑ i,(x i).1)%2=1 := by omega
    by_cases hnorm : 4*normNumerator n (forgetBox n m x)=(m : ℤ) <;> simp [paritySign,ho,hnorm]

theorem c_power (n : ℕ) : ArithmeticThetaHadamard.c^n=halfParitySeries n 0+halfParitySeries n 1 := by
  apply PowerSeries.ext
  intro m
  rw [ArithmeticThetaHadamard.coeff_pow_congr _ (finiteUnary m oddExponent (fun _ => 1)) m n
    (fun d hd => ArithmeticThetaHadamard.c_finite_coeff m d hd) m le_rfl, finiteUnary_power_coeff]
  simp only [halfParitySeries, map_add, PowerSeries.coeff_mk, Finset.prod_const_one]
  rw [half_param_card,half_param_card,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : (∑ i : Fin n,oddExponent (x i).1)=m ↔
      normNumerator n (halfCoordinates n (forgetBox n m x))=(m : ℤ) := by
    rw [← half_exponent_sum]
    rw [← Nat.cast_sum]
    exact (Nat.cast_inj (R := ℤ)).symm
  simp only [hexp]
  by_cases he : (∑ i,(x i).1)%2=0
  · simp [he]
  · have ho : (∑ i,(x i).1)%2=1 := by omega
    simp [ho]

end ArithmeticThetaRank16


namespace ArithmeticThetaRank16

theorem integralCoordinates_norm (n : ℕ) (x : Vec n) :
    normNumerator n (integralCoordinates n x)=4*normNumerator n x := by
  simp [normNumerator, integralCoordinates, mul_pow, Finset.mul_sum]

theorem integralCoordinates_membership (n : ℕ) (x : Vec n) :
    DPlusDoubled n (integralCoordinates n x) ↔ (∑ i,x i)%2=0 := by
  have hp : ∀ i, integralCoordinates n x i%2=0 := by intro i; dsimp [integralCoordinates]; omega
  have hs : (∑ i,integralCoordinates n x i)=2*∑ i,x i := by simp [integralCoordinates, Finset.mul_sum]
  constructor
  · intro h
    have hh := h.2
    rw [hs] at hh
    omega
  · intro h
    refine ⟨Or.inl hp,?_⟩
    rw [hs]
    omega

theorem halfCoordinates_membership (n : ℕ) (hn : (n : ℤ)%4=0) (x : Vec n) :
    DPlusDoubled n (halfCoordinates n x) ↔ (∑ i,x i)%2=0 := by
  have hp : ∀ i, halfCoordinates n x i%2=1 := by intro i; dsimp [halfCoordinates]; omega
  have hs : (∑ i,halfCoordinates n x i)=2*(∑ i,x i)+n := by
    simp [halfCoordinates, Finset.sum_add_distrib, Finset.mul_sum]
  constructor
  · intro h
    have hh := h.2
    rw [hs] at hh
    omega
  · intro h
    refine ⟨Or.inr hp,?_⟩
    rw [hs]
    omega

def parameterCoordinates (n m : ℕ) : VBox n m ⊕ VBox n m → Vec n :=
  Sum.elim (fun x => integralCoordinates n (forgetBox n m x))
    (fun x => halfCoordinates n (forgetBox n m x))

theorem parameterCoordinates_injective (n m : ℕ) (hn : 0<n) :
    Function.Injective (parameterCoordinates n m) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      apply congrArg Sum.inl
      funext i
      apply Subtype.ext
      have hi := congrFun h i
      change 2*(x i).1=2*(y i).1 at hi
      omega
    | inr y =>
      have hi := congrFun h ⟨0,hn⟩
      change 2*(x ⟨0,hn⟩).1=2*(y ⟨0,hn⟩).1+1 at hi
      omega
  | inr x =>
    cases y with
    | inl y =>
      have hi := congrFun h ⟨0,hn⟩
      change 2*(x ⟨0,hn⟩).1+1=2*(y ⟨0,hn⟩).1 at hi
      omega
    | inr y =>
      apply congrArg Sum.inr
      funext i
      apply Subtype.ext
      have hi := congrFun h i
      change 2*(x i).1+1=2*(y i).1+1 at hi
      omega

theorem parameterCoordinates_cover (n m : ℕ) (y : Vec n)
    (hy : DPlusDoubled n y ∧ normNumerator n y=(m : ℤ)) :
    ∃ x : VBox n m ⊕ VBox n m, parameterCoordinates n m x=y := by
  have hb := coordinate_bound n m y (by omega)
  rcases hy.1.1 with he|ho
  · have hbox (i : Fin n) : y i/2 ∈ Finset.Icc (-(m : ℤ)-1) ((m : ℤ)+1) := by
      simp only [Finset.mem_Icc]
      have hi := hb i
      omega
    refine ⟨Sum.inl (fun i => ⟨y i/2,hbox i⟩), ?_⟩
    funext i
    have hi := he i
    change 2*(y i/2)=y i
    omega
  · have hbox (i : Fin n) : (y i-1)/2 ∈ Finset.Icc (-(m : ℤ)-1) ((m : ℤ)+1) := by
      simp only [Finset.mem_Icc]
      have hi := hb i
      omega
    refine ⟨Sum.inr (fun i => ⟨(y i-1)/2,hbox i⟩), ?_⟩
    funext i
    have hi := ho i
    change 2*((y i-1)/2)+1=y i
    omega

theorem normSeries_split (n : ℕ) (hn : 0<n) (hn4 : (n : ℤ)%4=0) :
    normSeries n=integralParitySeries n 0+halfParitySeries n 0 := by
  classical
  apply PowerSeries.ext
  intro m
  simp only [normSeries,integralParitySeries,halfParitySeries,map_add,PowerSeries.coeff_mk]
  have hc := ArithmeticThetaHadamard.card_subtype_eq_sum (parameterCoordinates n m)
    (parameterCoordinates_injective n m hn)
    (fun y => DPlusDoubled n y ∧ normNumerator n y=(m : ℤ))
    (parameterCoordinates_cover n m)
  rw [hc, Fintype.sum_sum_type, integral_param_card, half_param_card]
  simp only [parameterCoordinates,Sum.elim_inl,Sum.elim_inr,
    integralCoordinates_membership,halfCoordinates_membership n hn4,integralCoordinates_norm,forgetBox]

def halfFlip (n : ℕ) (x : Vec (n+1)) : Vec (n+1) :=
  Fin.cons (-x 0-1) (fun i => x i.succ)

theorem halfFlip_twice (n : ℕ) (x : Vec (n+1)) : halfFlip n (halfFlip n x)=x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [halfFlip]
  · simp [halfFlip]

theorem halfFlip_sum (n : ℕ) (x : Vec (n+1)) :
    (∑ i,halfFlip n x i)=(∑ i,x i)-2*x 0-1 := by
  simp [halfFlip,Fin.sum_univ_succ]
  ring

theorem halfFlip_norm (n : ℕ) (x : Vec (n+1)) :
    normNumerator (n+1) (halfCoordinates (n+1) (halfFlip n x))=
      normNumerator (n+1) (halfCoordinates (n+1) x) := by
  simp [normNumerator,halfCoordinates,halfFlip,Fin.sum_univ_succ]
  ring

def halfParityEquiv (n m : ℕ) : HalfParityShell (n+1) m 0 ≃ HalfParityShell (n+1) m 1 where
  toFun x := ⟨halfFlip n x.1, by
    constructor
    · rw [halfFlip_sum]
      have h := x.2.1
      omega
    · rw [halfFlip_norm]
      exact x.2.2⟩
  invFun x := ⟨halfFlip n x.1, by
    constructor
    · rw [halfFlip_sum]
      have h := x.2.1
      omega
    · rw [halfFlip_norm]
      exact x.2.2⟩
  left_inv x := Subtype.ext (halfFlip_twice n x.1)
  right_inv x := Subtype.ext (halfFlip_twice n x.1)

theorem halfParitySeries_eq (n : ℕ) (hn : 0<n) : halfParitySeries n 0=halfParitySeries n 1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  apply PowerSeries.ext
  intro m
  simp only [halfParitySeries,PowerSeries.coeff_mk]
  exact_mod_cast Nat.card_congr (halfParityEquiv k m)

theorem parity_selection (n : ℕ) (hn : 0<n) (h8 : 8∣n) :
    (2 : PowerSeries ℤ)*normSeries n=
      ArithmeticThetaHadamard.a^n+ArithmeticThetaHadamard.b^n+ArithmeticThetaHadamard.c^n := by
  have hn4 : (n : ℤ)%4=0 := by
    have hh : (4 : ℕ)∣n := dvd_trans (by norm_num : 4∣8) h8
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast hh)
  rw [normSeries_split n hn hn4,a_power,b_power,c_power,← halfParitySeries_eq n hn]
  ring

end ArithmeticThetaRank16


namespace ArithmeticThetaRank16

noncomputable def finiteLattice (n m : ℕ) : PowerSeries ℤ := by
  classical
  exact ∑ x : VBox n m, PowerSeries.monomial
    (normNumerator n (forgetBox n m x)).toNat
    (if DPlusDoubled n (forgetBox n m x) then 1 else 0)

theorem norm_toNat_cast (n : ℕ) (x : Vec n) :
    ((normNumerator n x).toNat : ℤ)=normNumerator n x :=
  Int.toNat_of_nonneg (norm_nonnegative n x)

theorem norm_toNat_eq (n d : ℕ) (x : Vec n) :
    (normNumerator n x).toNat=d ↔ normNumerator n x=(d : ℤ) := by
  rw [← norm_toNat_cast]
  exact (Nat.cast_inj (R := ℤ)).symm

theorem lattice_box_cover (n m d : ℕ) (hd : d ≤ m) (y : Vec n)
    (hy : DPlusDoubled n y ∧ normNumerator n y=(d : ℤ)) :
    ∃ x : VBox n m, forgetBox n m x=y := by
  have hb := coordinate_bound n m y (by omega)
  refine ⟨fun i => ⟨y i,?_⟩,rfl⟩
  simp only [Finset.mem_Icc]
  have hi := hb i
  omega

theorem finiteLattice_coeff (n m d : ℕ) (hd : d ≤ m) :
    PowerSeries.coeff d (normSeries n)=PowerSeries.coeff d (finiteLattice n m) := by
  classical
  simp only [normSeries,finiteLattice,PowerSeries.coeff_mk,map_sum,PowerSeries.coeff_monomial]
  rw [ArithmeticThetaHadamard.card_subtype_eq_sum (forgetBox n m) (forgetBox_injective n m)
    (fun y => DPlusDoubled n y ∧ normNumerator n y=(d : ℤ)) (lattice_box_cover n m d hd)]
  apply Finset.sum_congr rfl
  intro x hx
  have hexp : d=(normNumerator n (forgetBox n m x)).toNat ↔
      normNumerator n (forgetBox n m x)=(d : ℤ) := by
    rw [eq_comm,norm_toNat_eq]
  simp only [hexp]
  by_cases he : normNumerator n (forgetBox n m x)=(d : ℤ) <;> simp [he]

def pairCoordinates (m : ℕ) (x : Fin 2 → VBox 8 m) : Vec 8 × Vec 8 :=
  (forgetBox 8 m (x 0),forgetBox 8 m (x 1))

theorem pairCoordinates_injective (m : ℕ) : Function.Injective (pairCoordinates m) := by
  intro x y h
  funext i
  apply forgetBox_injective 8 m
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem pairCoordinates_cover (m : ℕ) (y : Vec 8 × Vec 8)
    (hy : DPlusDoubled 8 y.1 ∧ DPlusDoubled 8 y.2 ∧
      normNumerator 8 y.1+normNumerator 8 y.2=(m : ℤ)) :
    ∃ x : Fin 2 → VBox 8 m, pairCoordinates m x=y := by
  have h1 := norm_nonnegative 8 y.1
  have h2 := norm_nonnegative 8 y.2
  have hb1 := coordinate_bound 8 m y.1 (by omega)
  have hb2 := coordinate_bound 8 m y.2 (by omega)
  let x1 : VBox 8 m := fun i => ⟨y.1 i, by have h:=hb1 i; simp only [Finset.mem_Icc]; omega⟩
  let x2 : VBox 8 m := fun i => ⟨y.2 i, by have h:=hb2 i; simp only [Finset.mem_Icc]; omega⟩
  exact ⟨![x1,x2],rfl⟩

theorem orthogonal_product : sumNormSeries=normSeries 8^2 := by
  classical
  apply PowerSeries.ext
  intro m
  rw [ArithmeticThetaHadamard.coeff_pow_congr _ (finiteLattice 8 m) m 2
    (fun d hd => finiteLattice_coeff 8 m d hd) m le_rfl]
  simp only [sumNormSeries,PowerSeries.coeff_mk,finiteLattice]
  rw [Fintype.sum_pow]
  simp only [PowerSeries.prod_monomial,map_sum,PowerSeries.coeff_monomial]
  rw [ArithmeticThetaHadamard.card_subtype_eq_sum (pairCoordinates m) (pairCoordinates_injective m)
    (fun y : Vec 8 × Vec 8 => DPlusDoubled 8 y.1 ∧ DPlusDoubled 8 y.2 ∧
      normNumerator 8 y.1+normNumerator 8 y.2=(m : ℤ)) (pairCoordinates_cover m)]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Fin.sum_univ_two,Fin.prod_univ_two,pairCoordinates]
  have he : m=(normNumerator 8 (forgetBox 8 m (x 0))).toNat+
      (normNumerator 8 (forgetBox 8 m (x 1))).toNat ↔
      normNumerator 8 (forgetBox 8 m (x 0))+normNumerator 8 (forgetBox 8 m (x 1))=(m : ℤ) := by
    rw [← norm_toNat_cast 8 (forgetBox 8 m (x 0)),← norm_toNat_cast 8 (forgetBox 8 m (x 1))]
    omega
  simp only [he]
  by_cases h1 : DPlusDoubled 8 (forgetBox 8 m (x 0)) <;>
    by_cases h2 : DPlusDoubled 8 (forgetBox 8 m (x 1)) <;> simp [h1,h2]

end ArithmeticThetaRank16


namespace ArithmeticThetaRank16

theorem norm_identity : sumNormSeries=normSeries 16 := by
  rw [orthogonal_product]
  have h8 := parity_selection 8 (by norm_num) (by norm_num)
  have h16 := parity_selection 16 (by norm_num) (by norm_num)
  let a := ArithmeticThetaHadamard.a
  let b := ArithmeticThetaHadamard.b
  let c := ArithmeticThetaHadamard.c
  have h4 : a^4=b^4+c^4 := ArithmeticThetaHadamard.jacobi_formal
  have ha8 : a^8=(b^4+c^4)^2 := by
    calc a^8=(a^4)^2 := by ring
         _=(b^4+c^4)^2 := by rw [h4]
  have ha16 : a^16=(b^4+c^4)^4 := by
    calc a^16=(a^4)^4 := by ring
         _=(b^4+c^4)^4 := by rw [h4]
  have hpoly : (a^8+b^8+c^8)^2=2*(a^16+b^16+c^16) := by
    rw [ha8,ha16]
    ring
  have hfour : (4 : PowerSeries ℤ)≠0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    norm_num [map_ofNat] at hh
  apply mul_left_cancel₀ hfour
  calc (4 : PowerSeries ℤ)*normSeries 8^2=(2*normSeries 8)^2 := by ring
       _=(a^8+b^8+c^8)^2 := by rw [h8]
       _=2*(a^16+b^16+c^16) := hpoly
       _=4*normSeries 16 := by rw [← h16]; ring

theorem expand_norm (n : ℕ) (hn : 8∣n) :
    PowerSeries.expand 8 (by decide) (theta n)=normSeries n := by
  apply PowerSeries.ext
  intro m
  by_cases hm : 8∣m
  · obtain ⟨k,rfl⟩ := hm
    rw [PowerSeries.coeff_expand_mul]
    simp only [theta,normSeries,PowerSeries.coeff_mk]
  · rw [PowerSeries.coeff_expand_of_not_dvd 8 (by decide) _ hm]
    simp only [normSeries,PowerSeries.coeff_mk]
    have hempty : IsEmpty (NormShell n m) := ⟨fun y => by
      have hd := norm_divisible_eight n hn y.1 y.2.1
      rw [y.2.2] at hd
      exact hm (by exact_mod_cast hd)⟩
    simp

theorem expand_sum : PowerSeries.expand 8 (by decide) sumTheta=sumNormSeries := by
  apply PowerSeries.ext
  intro m
  by_cases hm : 8∣m
  · obtain ⟨k,rfl⟩ := hm
    rw [PowerSeries.coeff_expand_mul]
    simp only [sumTheta,sumNormSeries,PowerSeries.coeff_mk]
  · rw [PowerSeries.coeff_expand_of_not_dvd 8 (by decide) _ hm]
    simp only [sumNormSeries,PowerSeries.coeff_mk]
    have hempty : IsEmpty (SumNormShell m) := ⟨fun y => by
      have h1 := norm_divisible_eight 8 (by norm_num) y.1.1 y.2.1
      have h2 := norm_divisible_eight 8 (by norm_num) y.1.2 y.2.2.1
      have hd := dvd_add h1 h2
      rw [y.2.2.2] at hd
      exact hm (by exact_mod_cast hd)⟩
    simp

theorem expand_actual :
    (∀ n : ℕ, 8∣n → PowerSeries.expand 8 (by decide) (theta n)=normSeries n) ∧
      PowerSeries.expand 8 (by decide) sumTheta=sumNormSeries := ⟨expand_norm,expand_sum⟩

theorem expand_eight_injective :
    Function.Injective (PowerSeries.expand 8 (by decide) : PowerSeries ℤ → PowerSeries ℤ) := by
  intro F G h
  apply PowerSeries.ext
  intro m
  have hc := congrArg (PowerSeries.coeff (8*m)) h
  simpa only [PowerSeries.coeff_expand_mul] using hc

theorem integral_identity : sumTheta=theta 16 := by
  apply expand_eight_injective
  rw [expand_sum,expand_norm 16 (by norm_num),norm_identity]

theorem norm_eq_zero (n : ℕ) (y : Vec n) : normNumerator n y=0 ↔ y=0 := by
  constructor
  · intro h
    funext i
    have hi := coordinate_square_le n y i
    rw [h] at hi
    have hs : y i^2=0 := le_antisymm hi (sq_nonneg (y i))
    exact sq_eq_zero_iff.mp hs
  · rintro rfl
    simp [normNumerator]

theorem theta_constant_one : PowerSeries.coeff 0 (theta 16)=1 := by
  simp only [theta,PowerSeries.coeff_mk,mul_zero]
  let : Unique (NormShell 16 0) :=
    { default := ⟨0,by simp [DPlusDoubled,normNumerator]⟩
      uniq := fun y => Subtype.ext ((norm_eq_zero 16 y.1).mp y.2.2) }
  simp

theorem two_column_kernel (v : Fin 2 → ℂ) :
    (∑ i,v i • columns i)=0 ↔ ∃ t : ℂ,v=![t,-t] := by
  have hc0 : PowerSeries.coeff 0 (columns 0)=1 := by
    simp [columns,PowerSeries.coeff_map,integral_identity,theta_constant_one]
  have hc1 : PowerSeries.coeff 0 (columns 1)=1 := by
    simp [columns,PowerSeries.coeff_map,theta_constant_one]
  constructor
  · intro h
    have hc : v 0+v 1=0 := by
      have hh := congrArg (PowerSeries.coeff 0) h
      simpa only [Fin.sum_univ_two,map_add,map_smul,hc0,hc1,smul_eq_mul,mul_one,map_zero] using hh
    have hv : v 1= -v 0 := by linear_combination hc
    refine ⟨v 0,?_⟩
    funext i
    fin_cases i
    · rfl
    · exact hv
  · rintro ⟨t,rfl⟩
    simp [Fin.sum_univ_two,columns,integral_identity]

end ArithmeticThetaRank16
