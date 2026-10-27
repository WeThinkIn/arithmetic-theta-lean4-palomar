import ThetaRecurrenceBasisR0119
import ThetaOperatorLawsR0119

/-! Each specified A eigenspace in the full bilateral recurrence space is
exactly its literal theta line, with a unique Laurent-series scalar. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119

private lemma theta_scalar_injective (k : Type u) [Field k] (m : ℕ) (ν : Fin m) :
    Function.Injective (fun c : K k => c • theta k m ν) := by
  intro c d h
  have he := congrFun h (ν.val : ℤ)
  have hn : monomial k ((ν.val : ℤ)^2) ≠ 0 := by
    simp [monomial, HahnSeries.single_eq_zero_iff]
  have hm : theta k m ν (ν.val : ℤ) = monomial k ((ν.val : ℤ)^2) := by
    simp [theta, Int.ModEq.refl]
  change c * theta k m ν (ν.val : ℤ) = d * theta k m ν (ν.val : ℤ) at he
  rw [hm] at he
  exact mul_right_cancel₀ hn he

/-- The eigencondition singles out one literal theta line in the entire
recurrence space. The unique scalar can be zero. -/
theorem theta_eigenspace_rigidity :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m], Even m →
      ∀ ζ : k, IsPrimitiveRoot ζ m → ∀ (ν : Fin m) (f : Coefficients k),
      f ∈ Solutions k m →
      (A k ζ f = scalar k (ζ ^ ν.val) • f ↔
        ∃! c : K k, f = c • theta k m ν) := by
  intro k _ _ m _ hm ζ hζ ν f hf
  constructor
  · intro heigen
    let v := recurrenceCoordinates k m ⟨f, hf⟩
    have hv (μ : Fin m) (hne : μ ≠ ν) : v μ = 0 := by
      have hcoeff := congrFun heigen (μ.val : ℤ)
      change scalar k (ζ ^ (μ.val : ℤ)) * f μ.val =
        scalar k (ζ ^ ν.val) * f μ.val at hcoeff
      rw [zpow_natCast] at hcoeff
      have hfzero : f μ.val = 0 := by
        by_contra hn
        have hs := mul_right_cancel₀ hn hcoeff
        have hp : ζ ^ μ.val = ζ ^ ν.val := HahnSeries.single_injective 0 hs
        exact hne (Fin.ext (hζ.pow_inj μ.isLt ν.isLt hp))
      change monomial k (-((μ.val : ℤ)^2)) * f μ.val = 0
      rw [hfzero, mul_zero]
    have hrepr : f = v ν • theta k m ν := by
      calc
        f = synth k m v := (synth_recurrenceCoordinates k m ⟨f, hf⟩).symm
        _ = v ν • theta k m ν := by
          classical
          apply Finset.sum_eq_single ν
          · intro μ _ hne
            rw [hv μ hne, zero_smul]
          · simp
    refine ⟨v ν, hrepr, ?_⟩
    intro c hc
    exact theta_scalar_injective k m ν (hc.symm.trans hrepr)
  · rintro ⟨c, rfl, _⟩
    have htheta := ((theta_operator_laws k m hm ζ hζ).1 ν).1
    funext r
    have he := congrFun htheta r
    change scalar k (ζ ^ r) * theta k m ν r =
      scalar k (ζ ^ ν.val) * theta k m ν r at he
    change scalar k (ζ ^ r) * (c * theta k m ν r) =
      scalar k (ζ ^ ν.val) * (c * theta k m ν r)
    calc
      _ = c * (scalar k (ζ ^ r) * theta k m ν r) := by ring
      _ = c * (scalar k (ζ ^ ν.val) * theta k m ν r) := by rw [he]
      _ = _ := by ring

end ArithmeticThetaSchrodingerR0119
