import ThetaEigenspaceRigidityR0119

/-! The formal synthesis intertwiner and the common-scalar comparison theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119

private lemma next_prev (m : ℕ) [NeZero m] (ν : Fin m) : next m (prev m ν) = ν := by
  apply Fin.ext
  simp only [next, prev]
  rw [Nat.mod_add_mod]
  have hm : 0 < m := NeZero.pos m
  have he : ν.val + m - 1 + 1 = ν.val + m := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt ν.isLt]

private lemma prev_next (m : ℕ) [NeZero m] (ν : Fin m) : prev m (next m ν) = ν := by
  apply Fin.ext
  simp only [next, prev]
  have hm : 1 ≤ m := NeZero.one_le
  have hν : ν.val < m := ν.isLt
  by_cases h : ν.val + 1 < m
  · rw [Nat.mod_eq_of_lt h]
    have he : ν.val + 1 + m - 1 = ν.val + m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hν]
  · have he : ν.val + 1 = m := by omega
    rw [he]
    simp only [Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (show m-1 < m by omega)]
    omega

private def synthesisMap (k : Type u) [Field k] (m : ℕ) [NeZero m] :
    (Fin m → K k) →ₗ[K k] Coefficients k :=
  (Solutions k m).subtype.comp (recurrenceEquiv k m).toLinearMap

private lemma synthesis_apply (k : Type u) [Field k] (m : ℕ) [NeZero m]
    (v : Fin m → K k) : synthesisMap k m v = synth k m v := rfl

private lemma synthesis_injective (k : Type u) [Field k] (m : ℕ) [NeZero m] :
    Function.Injective (synthesisMap k m) := by
  intro v w h
  apply (recurrenceEquiv k m).injective
  exact Subtype.ext h

private lemma synthesis_A (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (hm : Even m)
    (ζ : k) (hζ : IsPrimitiveRoot ζ m) (v : Fin m → K k) :
    synthesisMap k m (standardA k m ζ v) =
      A k ζ (synthesisMap k m v) := by
  simp only [synthesis_apply]
  funext r
  simp only [synth, standardA, A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  have he := congrFun ((theta_operator_laws k m hm ζ hζ).1 ν).1 r
  change scalar k (ζ ^ r) * theta k m ν r =
    scalar k (ζ ^ ν.val) * theta k m ν r at he
  calc
    _ = v ν * (scalar k (ζ ^ ν.val) * theta k m ν r) := by ring
    _ = v ν * (scalar k (ζ ^ r) * theta k m ν r) := by rw [he]
    _ = _ := by ring

private lemma synthesis_B (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (hm : Even m)
    (ζ : k) (hζ : IsPrimitiveRoot ζ m) (v : Fin m → K k) :
    synthesisMap k m (standardB k m v) =
      B k (synthesisMap k m v) := by
  let e : Fin m ≃ Fin m :=
    { toFun := next m
      invFun := prev m
      left_inv := prev_next m
      right_inv := next_prev m }
  simp only [synthesis_apply]
  funext r
  simp only [synth, standardB, B, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ ν : Fin m, v (prev m ν) * theta k m ν r) =
        ∑ ν : Fin m, v (prev m (next m ν)) * theta k m (next m ν) r :=
      (e.sum_comp (fun μ => v (prev m μ) * theta k m μ r)).symm
    _ = ∑ ν : Fin m, v ν * theta k m (next m ν) r := by simp only [prev_next]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      have he := congrFun ((theta_operator_laws k m hm ζ hζ).1 ν).2 r
      change monomial k (2*r-1) * theta k m ν (r-1) = theta k m (next m ν) r at he
      rw [← he]
      ring

private lemma synthesis_intertwines (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (hm : Even m) (ζ : k) (hζ : IsPrimitiveRoot ζ m) :
    Intertwines k m ζ (synthesisMap k m) := by
  refine ⟨synthesis_injective k m, ?_, ?_, ?_⟩
  · intro v
    exact synth_mem_solutions k m v
  · exact synthesis_A k m hm ζ hζ
  · exact synthesis_B k m hm ζ hζ

theorem schrodinger_common_scalar :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m], Even m →
      ∀ ζ : k, IsPrimitiveRoot ζ m →
      (∃ F : (Fin m → K k) →ₗ[K k] (Coefficients k),
        Intertwines k m ζ F ∧
          ∀ v : Fin m → K k, F v = synth k m v) ∧
      (∀ F : (Fin m → K k) →ₗ[K k] (Coefficients k),
        Intertwines k m ζ F →
          ∃! c : K k, c ≠ 0 ∧
            ∀ v : Fin m → K k, F v = c • synth k m v) := by
  intro k _ _ m _ hm ζ hζ
  constructor
  · refine ⟨synthesisMap k m, synthesis_intertwines k m hm ζ hζ, ?_⟩
    intro v
    rfl
  · intro F hF
    rcases hF with ⟨hFinj, hFsol, hFA, hFB⟩
    have hdelta_eigen (ν : Fin m) :
        standardA k m ζ (delta k m ν) =
          scalar k (ζ ^ ν.val) • delta k m ν := by
      funext μ
      by_cases h : μ = ν
      · subst h
        simp [standardA, delta]
      · simp [standardA, delta, h]
    have hFdelta_ex (ν : Fin m) :
        ∃! d : K k, F (delta k m ν) = d • theta k m ν := by
      have he := hFA (delta k m ν)
      have he' : A k ζ (F (delta k m ν)) =
          scalar k (ζ ^ ν.val) • F (delta k m ν) := by
        rw [← he, hdelta_eigen ν]
        exact F.map_smul _ _
      have hfsol := hFsol (delta k m ν)
      have hr := (theta_eigenspace_rigidity k m hm ζ hζ ν (F (delta k m ν)) hfsol)
      exact hr.mp he'
    let d : Fin m → K k := fun ν => Classical.choose (hFdelta_ex ν)
    have hd (ν : Fin m) : F (delta k m ν) = d ν • theta k m ν :=
      Classical.choose_spec (hFdelta_ex ν) |>.1
    let c : K k := d 0
    have htheta_injective (ν : Fin m) :
        Function.Injective (fun a : K k => a • theta k m ν) := by
      intro a b hab
      have he := congrFun hab (ν.val : ℤ)
      change a * theta k m ν (ν.val : ℤ) = b * theta k m ν (ν.val : ℤ) at he
      have hn : theta k m ν (ν.val : ℤ) ≠ 0 := by
        simp [theta, monomial, HahnSeries.single_eq_zero_iff]
      exact mul_right_cancel₀ hn he
    have hstdB (ν : Fin m) :
        standardB k m (delta k m ν) = delta k m (next m ν) := by
      funext μ
      by_cases hμ : μ = next m ν
      · subst hμ
        simp [standardB, delta, prev_next]
      · have hp : prev m μ ≠ ν := by
          intro hp
          apply hμ
          have := congrArg (next m) hp
          simpa [next_prev] using this
        simp [standardB, delta, hμ, hp]
    have hB_smul (a : K k) (f : Coefficients k) :
        B k (a • f) = a • B k f := by
      funext r
      simp only [B, Pi.smul_apply, smul_eq_mul]
      ring
    have hrel (ν : Fin m) : d (next m ν) = d ν := by
      have hb := hFB (delta k m ν)
      rw [hstdB ν, hd ν, hB_smul] at hb
      rw [hd (next m ν)] at hb
      rw [(theta_operator_laws k m hm ζ hζ).1 ν |>.2] at hb
      exact htheta_injective (next m ν) hb
    have hiter_next : ∀ n : ℕ,
        ((next m)^[n] (0 : Fin m)).val = n % m := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          change (((next m)^[n] (0 : Fin m)).val + 1) % m = (n+1)%m
          rw [ih, Nat.mod_add_mod]
    have hwalk : ∀ n : ℕ, d ((next m)^[n] (0 : Fin m)) = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          exact (hrel _).trans ih
    have hdc (ν : Fin m) : d ν = c := by
      have hi := hiter_next ν.val
      have hv : ((next m)^[ν.val] (0 : Fin m)) = ν := by
        apply Fin.ext
        simp [hi, Nat.mod_eq_of_lt ν.isLt]
      rw [← hv]
      exact hwalk ν.val
    have hFdelta_all (ν : Fin m) : F (delta k m ν) = c • theta k m ν := by
      rw [hd ν, hdc ν]
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hzero : F (delta k m (0 : Fin m)) = 0 := by
        rw [hFdelta_all]
        simp [hc0]
      have hzero' : F (delta k m (0 : Fin m)) = F 0 := by simpa using hzero
      have : (delta k m (0 : Fin m)) = 0 := hFinj hzero'
      have hval := congrFun this (0 : Fin m)
      simp [delta] at hval
    have hdelta_expand (v : Fin m → K k) :
        v = ∑ ν : Fin m, v ν • delta k m ν := by
      funext μ
      simp [delta, Finset.sum_apply]
    have hall (v : Fin m → K k) : F v = c • synth k m v := by
      conv_lhs => rw [hdelta_expand v, map_sum]
      simp only [map_smul, hFdelta_all]
      simp only [synth, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      exact smul_comm (v ν) c (theta k m ν)
    refine ⟨c, ⟨hc_ne, hall⟩, ?_⟩
    intro a ha
    have hs : synth k m (delta k m (0 : Fin m)) = theta k m 0 := by
      classical
      simp [synth, delta]
    apply htheta_injective (0 : Fin m)
    change a • theta k m 0 = c • theta k m 0
    rw [← hFdelta_all, ha.2, hs]

end ArithmeticThetaSchrodingerR0119
