module

public import Mathlib

@[expose] public section
universe u
noncomputable section
namespace ArithmeticThetaArithmeticRamificationR0096
open PowerSeries

/-- Extract the coefficients in a single residue class modulo `L`. -/
private def residueSeries {k : Type u} [Field k] (L i : ℕ) :
    PowerSeries k →ₗ[k] PowerSeries k where
  toFun f := mk fun m => coeff (L * m + i) f
  map_add' f g := by ext m; simp
  map_smul' a f := by ext m; simp

/-- Synthesize a target series using the actual homomorphism on each residue component. -/
private def regroupMap {k : Type u} [Field k] (L : ℕ)
    (φ : PowerSeries k →ₐ[k] PowerSeries k) : PowerSeries k →ₗ[k] PowerSeries k where
  toFun f := ∑ i : Fin L, φ (residueSeries L i.val f) * X ^ i.val
  map_add' f g := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a f := by simp [map_smul, Finset.smul_sum]

/-- The synthesis map preserves vanishing of all coefficients through a given degree.
The proof uses divisibility by powers of `X`, so no continuity assumption is needed. -/
private theorem regroupMap_coeff_zero {k : Type u} [Field k] (L : ℕ) (hL : 0 < L)
    (φ : PowerSeries k →ₐ[k] PowerSeries k) (horder : (φ X).order = (L : ℕ∞))
    (f : PowerSeries k) (n : ℕ) (hf : ∀ j ≤ n, coeff j f = 0) :
    coeff n (regroupMap L φ f) = 0 := by
  classical
  change coeff n (∑ i : Fin L, φ (residueSeries L i.val f) * X ^ i.val) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_mul_X_pow']
  split_ifs with hi
  · let m := (n - i.val) / L + 1
    have hd : X ^ m ∣ residueSeries L i.val f := by
      apply X_pow_dvd_iff.mpr
      intro j hj
      change coeff j (mk fun t => coeff (L * t + i.val) f) = 0
      rw [coeff_mk]
      apply hf
      have hj' : j ≤ (n - i.val) / L := by omega
      have hm := Nat.mul_div_le (n - i.val) L
      have hmul := Nat.mul_le_mul_left L hj'
      omega
    obtain ⟨q, hq⟩ := hd
    rw [hq, map_mul, map_pow]
    apply coeff_of_lt_order
    rw [order_mul, order_pow, horder]
    have hm : n - i.val < L * m := by
      dsimp [m]
      have := Nat.mod_lt (n - i.val) hL
      have := Nat.div_add_mod (n - i.val) L
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    have hcast : ((n - i.val : ℕ) : ℕ∞) < (L * m : ℕ) := by exact_mod_cast hm
    have he : m • (L : ℕ∞) = (L * m : ℕ) := by simp [nsmul_eq_mul, Nat.cast_mul, mul_comm]
    rw [he]
    exact lt_of_lt_of_le hcast (le_add_right le_rfl)
  · rfl

/-- A monomial belongs to exactly one residue component. -/
private theorem residueSeries_X_pow {k : Type u} [Field k] (L : ℕ) (hL : 0 < L)
    (i : Fin L) (n : ℕ) :
    residueSeries L i.val (X ^ n : PowerSeries k) =
      if i.val = n % L then X ^ (n / L) else 0 := by
  ext m
  by_cases hi : i.val = n % L
  · rw [if_pos hi]
    simp only [residueSeries, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, coeff_X_pow]
    congr 1
    apply propext
    constructor
    · intro h
      have := congrArg (fun t => t / L) h
      simpa [Nat.mul_add_div hL, Nat.div_eq_of_lt i.isLt] using this
    · intro h
      subst m
      simpa [hi] using Nat.div_add_mod n L
  · rw [if_neg hi]
    simp only [residueSeries, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, coeff_X_pow, map_zero]
    rw [if_neg]
    intro h
    apply hi
    have := congrArg (fun t => t % L) h
    simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt] using this

/-- The synthesis map sends the `n`th monomial to a series of order `n`. -/
private theorem regroupMap_X_pow {k : Type u} [Field k] (L : ℕ) (hL : 0 < L)
    (φ : PowerSeries k →ₐ[k] PowerSeries k) (n : ℕ) :
    regroupMap L φ (X ^ n) = (φ X) ^ (n / L) * X ^ (n % L) := by
  classical
  change (∑ i : Fin L, φ (residueSeries L i.val (X ^ n)) * X ^ i.val) = _
  rw [Finset.sum_eq_single (⟨n % L, Nat.mod_lt n hL⟩ : Fin L)]
  · rw [residueSeries_X_pow L hL ⟨n % L, Nat.mod_lt n hL⟩ n]
    simp [map_pow]
  · intro i _ hi
    have hi' : i.val ≠ n % L := by intro h; exact hi (Fin.ext h)
    simp [residueSeries_X_pow L hL, hi']
  · simp


/-- Solve a triangular coefficient system successively, dividing by its diagonal entries. -/
private def inverseCoeffs {k : Type u} [Field k]
    (F : PowerSeries k →ₗ[k] PowerSeries k) (b : PowerSeries k) (n : ℕ) : k :=
  (coeff n b - coeff n (F (mk fun j => if _h : j < n then inverseCoeffs F b j else 0))) /
    coeff n (F (X ^ n))
termination_by n

/-- A filtration-preserving linear operator on series with nonzero diagonal is bijective. -/
private theorem triangular_bijective {k : Type u} [Field k]
    (F : PowerSeries k →ₗ[k] PowerSeries k)
    (hzero : ∀ (f : PowerSeries k) (n : ℕ),
      (∀ j ≤ n, coeff j f = 0) → coeff n (F f) = 0)
    (hdiag : ∀ n, coeff n (F (X ^ n)) ≠ 0) : Function.Bijective F := by
  classical
  have hcongr (n : ℕ) (f g : PowerSeries k)
      (h : ∀ j ≤ n, coeff j f = coeff j g) : coeff n (F f) = coeff n (F g) := by
    have hz := hzero (f - g) n (by intro j hj; simp [h j hj])
    simpa [map_sub, sub_eq_zero] using hz
  have hstep (n : ℕ) (f : PowerSeries k) :
      coeff n (F f) = coeff n (F (mk fun j => if j < n then coeff j f else 0)) +
        coeff n f * coeff n (F (X ^ n)) := by
    calc
      _ = coeff n (F ((mk fun j => if j < n then coeff j f else 0) +
          coeff n f • (X ^ n))) := by
        apply hcongr
        intro j hj
        simp only [map_add, coeff_mk, coeff_smul, coeff_X_pow, smul_eq_mul]
        by_cases hlt : j < n
        · simp [hlt, Nat.ne_of_lt hlt]
        · have he : j = n := by omega
          subst j
          simp
      _ = _ := by simp [map_add, map_smul, smul_eq_mul]
  constructor
  · intro f g hfg
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hp : (mk fun j => if j < n then coeff j f else 0) =
          (mk fun j => if j < n then coeff j g else 0) := by
        ext j
        simp only [coeff_mk]
        split_ifs with hj
        · exact ih j hj
        · rfl
      have he := congrArg (coeff n) hfg
      rw [hstep n f, hstep n g, hp] at he
      exact (mul_right_cancel₀ (hdiag n)) (add_left_cancel he)
  · intro b
    refine ⟨mk (inverseCoeffs F b), ?_⟩
    ext n
    rw [hstep, coeff_mk]
    simp only [coeff_mk]
    rw [inverseCoeffs]
    rw [div_mul_cancel₀ _ (hdiag n)]
    exact add_sub_cancel _ _

/-- Positive finite ramification order makes the synthesis operator invertible. -/
private theorem regroupMap_bijective {k : Type u} [Field k] (L : ℕ) (hL : 0 < L)
    (φ : PowerSeries k →ₐ[k] PowerSeries k) (horder : (φ X).order = (L : ℕ∞)) :
    Function.Bijective (regroupMap L φ) := by
  apply triangular_bijective _ (regroupMap_coeff_zero L hL φ horder)
  intro n
  rw [regroupMap_X_pow L hL]
  apply (order_eq_nat.mp ?_).1
  rw [order_mul, order_pow, order_X_pow, horder]
  simp only [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add]
  congr 1
  simpa [Nat.mul_comm] using Nat.div_add_mod n L

/-- Interleaving a finite family of series is inverse to taking residue components. -/
private theorem residueSeries_assemble {k : Type u} [Field k] (L : ℕ) (hL : 0 < L)
    (a : Fin L → PowerSeries k) (i : Fin L) :
    residueSeries L i.val (mk fun n => coeff (n / L) (a ⟨n % L, Nat.mod_lt n hL⟩)) = a i := by
  ext m
  simp only [residueSeries, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk]
  have hd : (L * m + i.val) / L = m := by
    simp [Nat.mul_add_div hL, Nat.div_eq_of_lt i.isLt]
  have hm : (⟨(L * m + i.val) % L, Nat.mod_lt _ hL⟩ : Fin L) = i := by
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  rw [hd, hm]

/-- The monomials below the ramification order form a basis for the scalar action
induced by the given algebra homomorphism, over any field. -/
theorem ramified_monomial_basis :
    ∀ (k : Type u) [Field k] (L : ℕ) (hL : 0 < L)
      (φ : PowerSeries k →ₐ[k] PowerSeries k),
      (φ PowerSeries.X).order = (L : ℕ∞) →
      ∃ b : @Module.Basis (Fin L) (PowerSeries k) (PowerSeries k) _ _
        (@Algebra.toModule (PowerSeries k) (PowerSeries k) _ _
          φ.toRingHom.toAlgebra),
        ∀ i : Fin L, b i = PowerSeries.X ^ (i : ℕ) := by
  intro k _ L hL φ horder
  classical
  have hbij := regroupMap_bijective L hL φ horder
  let cuspAlgebra : Algebra (PowerSeries k) (PowerSeries k) := φ.toRingHom.toAlgebra
  let cuspModule : Module (PowerSeries k) (PowerSeries k) :=
    @Algebra.toModule _ _ _ _ cuspAlgebra
  let := cuspModule
  let : SMul (PowerSeries k) (PowerSeries k) := cuspModule.toDistribMulAction.toMulAction.toSMul
  have hs (a b : PowerSeries k) : a • b = φ a * b := rfl
  have hli : LinearIndependent (PowerSeries k)
      (fun i : Fin L => (PowerSeries.X : PowerSeries k) ^ i.val) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    let f : PowerSeries k := mk fun n => coeff (n / L) (a ⟨n % L, Nat.mod_lt n hL⟩)
    have hf (j : Fin L) : residueSeries L j.val f = a j :=
      residueSeries_assemble L hL a j
    have hF : regroupMap L φ f = 0 := by
      change (∑ j : Fin L, φ (residueSeries L j.val f) * X ^ j.val) = 0
      simpa only [hf, hs] using ha
    have hz : f = 0 := hbij.1 (by simpa only [map_zero] using hF)
    have he := congrArg (residueSeries L i.val) hz
    simpa only [hf, map_zero] using he
  have hsp : ⊤ ≤ Submodule.span (PowerSeries k)
      (Set.range fun i : Fin L => (PowerSeries.X : PowerSeries k) ^ i.val) := by
    intro f _
    obtain ⟨a, rfl⟩ := hbij.2 f
    change (∑ i : Fin L, φ (residueSeries L i.val a) * X ^ i.val) ∈ _
    apply Submodule.sum_mem
    intro i _
    rw [← hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, Module.Basis.mk_apply hli hsp⟩

end ArithmeticThetaArithmeticRamificationR0096
