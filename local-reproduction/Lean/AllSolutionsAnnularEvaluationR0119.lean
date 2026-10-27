import ThetaRecurrenceBasisR0119
import ThetaAnnularConvergenceR0119

/-! Evaluation of the complete recurrence space in the native Laurent-series topology. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119

lemma annularTerms_synth (k : Type u) [Field k] (m : ℕ)
    (v : Fin m → K k) (j : ℤ) (x : kˣ) (r : ℤ) :
    annularTerms k (synth k m v) j x r =
      ∑ ν : Fin m, v ν * annularTerms k (theta k m ν) j x r := by
  simp [annularTerms, synth, Finset.sum_apply, Finset.sum_mul, mul_assoc]

lemma synth_annular_hasSum (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (hm : Even m) (v : Fin m → K k) (j : ℤ) (x : kˣ) :
    HasSum (annularTerms k (synth k m v) j x)
      (∑ ν : Fin m, v ν * evaluate k (theta k m ν) j x) := by
  have hfun : annularTerms k (synth k m v) j x =
      fun r => ∑ ν : Fin m, v ν * annularTerms k (theta k m ν) j x r :=
    funext (annularTerms_synth k m v j x)
  rw [hfun]
  exact hasSum_sum (s := Finset.univ) (fun ν _ =>
    ((theta_annular_convergence k m hm ν j x).2.hasSum.mul_left (v ν)))

/-- At the identity substitution each coefficient is precisely a residue-shell indicator. -/
lemma theta_identity_coeff (k : Type u) [Field k] (m : ℕ) (ν : Fin m) (r n : ℤ) :
    (annularTerms k (theta k m ν) 0 (1 : kˣ) r).coeff n =
      if Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2 = n then 1 else 0 := by
  classical
  rw [theta_annular_term]
  by_cases h : Int.ModEq (m : ℤ) r (ν.val : ℤ)
  · simp [h, HahnSeries.coeff_single, eq_comm]
  · simp [h]

/-- Coefficientwise evaluation counts every integer in the accepted finite unary shell. -/
lemma theta_identity_hasSum (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (hm : Even m) (ν : Fin m) :
    HasSum (annularTerms k (theta k m ν) 0 (1 : kˣ))
      ((HahnSeries.ofPowerSeries ℤ k) (unary k m ν)) := by
  classical
  have hs := (theta_annular_convergence k m hm ν 0 (1 : kˣ)).2.hasSum
  have heq : evaluate k (theta k m ν) 0 (1 : kˣ) =
      (HahnSeries.ofPowerSeries ℤ k) (unary k m ν) := by
    apply HahnSeries.ext
    funext n
    let : UniformSpace k := ⊥
    let c : K k →+ k :=
      { toFun := fun f => f.coeff n
        map_zero' := by simp
        map_add' := by intros; simp }
    have hc := hs.map c (LaurentSeries.uniformContinuous_coeff n).continuous
    change HasSum (fun r => (annularTerms k (theta k m ν) 0 (1 : kˣ) r).coeff n)
      ((evaluate k (theta k m ν) 0 (1 : kˣ)).coeff n) at hc
    simp_rw [theta_identity_coeff] at hc
    by_cases hn : 0 ≤ n
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, unary, PowerSeries.coeff_mk]
      let S : Set ℤ := {r | Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2 = (a : ℤ)}
      have hS : S.Finite := by
        simpa [S] using ArithmeticThetaCosets.unary_shell_finite m 1 (ν.val : ℤ) (by decide) a
      have hcount : HasSum (fun r : ℤ => if r ∈ S then (1 : k) else 0)
          (Nat.card S : k) := by
        have h := hasSum_sum_of_ne_finset_zero (L := .unconditional ℤ) (s := hS.toFinset)
          (f := fun r : ℤ => if r ∈ S then (1 : k) else 0) (by
            intro r hr
            simp only [Set.Finite.mem_toFinset] at hr
            simp [hr])
        have hsum : (∑ r ∈ hS.toFinset, if r ∈ S then (1 : k) else 0) =
            (Nat.card S : k) := by
          calc
            _ = ∑ _r ∈ hS.toFinset, (1 : k) := by
              apply Finset.sum_congr rfl
              intro r hr
              simp only [Set.Finite.mem_toFinset] at hr
              simp [hr]
            _ = _ := by simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hS]
        exact hsum ▸ h
      exact hc.unique hcount
    · have hn' : n < 0 := lt_of_not_ge hn
      have hz : ∀ r : ℤ, ¬ (Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2 = n) := by
        intro r hr
        nlinarith [sq_nonneg r, hr.2]
      have hc0 : (evaluate k (theta k m ν) 0 (1 : kˣ)).coeff n = 0 := by
        apply hc.unique
        simpa only [hz, if_false] using (hasSum_zero (β := ℤ) (α := k))
      rw [hc0, HahnSeries.ofPowerSeries_apply]
      symm
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a, ha⟩
      change (a : ℤ) = n at ha
      omega
  exact heq ▸ hs

/-- All solutions converge, finite synthesis commutes with evaluation, and the
identity evaluation is the embedded complete residue-count power series. -/
theorem all_solutions_annular_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m], Even m →
      (∀ (f : Coefficients k), f ∈ Solutions k m → ∀ (j : ℤ) (x : kˣ),
        Summable (annularTerms k f j x)) ∧
      (∀ (v : Fin m → K k) (j : ℤ) (x : kˣ),
        evaluate k (synth k m v) j x =
          ∑ ν : Fin m, v ν * evaluate k (theta k m ν) j x) ∧
      (∀ ν : Fin m, HasSum (annularTerms k (theta k m ν) 0 (1 : kˣ))
        ((HahnSeries.ofPowerSeries ℤ k) (unary k m ν))) := by
  intro k _ _ m _ hm
  refine ⟨?_, ?_, theta_identity_hasSum k m hm⟩
  · intro f hf j x
    obtain ⟨E, hE, _, _⟩ := theta_recurrence_basis k m hm
    obtain ⟨v, hv⟩ := E.surjective ⟨f, hf⟩
    have he : synth k m v = f := (hE v).symm.trans (congrArg Subtype.val hv)
    rw [← he]
    exact (synth_annular_hasSum k m hm v j x).summable
  · intro v j x
    exact (synth_annular_hasSum k m hm v j x).tsum_eq

end ArithmeticThetaSchrodingerR0119
