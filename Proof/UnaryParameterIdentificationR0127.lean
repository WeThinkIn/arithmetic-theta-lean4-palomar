module

public import OrthogonalConsumerDefinitionsR0127

@[expose] public section

/-! Complete coefficient identification under the parameter substitution t = s^w. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaOrthogonalConsumerR0127

/-- The coefficients in the weighted series count finite sets of integers. -/
lemma scaledUnary_shell_finite (m w : ℕ) (hw : w ≠ 0) (ν : ℤ) (b : ℕ) :
    Set.Finite {r : ℤ | Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r^2 = (b : ℤ)} :=
  ArithmeticThetaCosets.unary_shell_finite m w ν (Nat.pos_of_ne_zero hw) b

/-- Changing the residue representative and cancelling the positive weight
identifies the entire shell at a divisible exponent. -/
def scaledUnary_shell_equiv (m w : ℕ) (hw : w ≠ 0) (ν μ : ℤ)
    (hν : Int.ModEq (m : ℤ) ν μ) (b : ℕ) :
    {r : ℤ // Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r^2 = ((w*b : ℕ) : ℤ)} ≃
    {r : ℤ // Int.ModEq (m : ℤ) r μ ∧ r^2 = (b : ℤ)} := by
  have hwZ : (w : ℤ) ≠ 0 := by exact_mod_cast hw
  refine Equiv.subtypeEquivRight (fun r => ?_)
  constructor
  · rintro ⟨hr, he⟩
    refine ⟨hr.trans hν, ?_⟩
    apply mul_left_cancel₀ hwZ
    simpa only [Nat.cast_mul] using he
  · rintro ⟨hr, he⟩
    exact ⟨hr.trans hν.symm, by simp only [he, Nat.cast_mul]⟩

/-- Every weighted exponent is a multiple of its weight, including exponent zero. -/
lemma scaledUnary_shell_empty (m w : ℕ) (ν : ℤ) (b : ℕ) (hb : ¬ w ∣ b) :
    IsEmpty {r : ℤ // Int.ModEq (m : ℤ) r ν ∧ (w : ℤ) * r^2 = (b : ℤ)} := by
  refine ⟨fun r => hb ?_⟩
  refine ⟨r.val.natAbs^2, ?_⟩
  apply Int.ofNat_inj.mp
  exact r.property.2.symm.trans (ArithmeticThetaCosets.energy_cast w r.val).symm

/-- The old weighted integer series is exactly the downstream unary series
with its parameter expanded by the positive weight. -/
theorem unary_parameter_identification :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m]
      (w : ℕ) (hw : w ≠ 0) (ν : ℤ) (a : Fin m),
      Int.ModEq (m : ℤ) ν (a.val : ℤ) →
      PowerSeries.map (Int.castRingHom k) (scaledUnary m w ν) =
        PowerSeries.expand w hw (ArithmeticThetaSchrodingerR0119.unary k m a) := by
  intro k _ _ m _ w hw ν a hν
  classical
  apply PowerSeries.ext
  intro b
  by_cases hb : w ∣ b
  · obtain ⟨c, rfl⟩ := hb
    rw [PowerSeries.coeff_map, PowerSeries.coeff_expand_mul]
    simp only [scaledUnary, ArithmeticThetaSchrodingerR0119.unary,
      PowerSeries.coeff_mk, map_natCast]
    exact congrArg (fun n : ℕ => (n : k))
      (Nat.card_congr (scaledUnary_shell_equiv m w hw ν (a.val : ℤ) hν c))
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_expand_of_not_dvd w hw _ hb]
    have := scaledUnary_shell_empty m w ν b hb
    simp [scaledUnary]

end ArithmeticThetaOrthogonalConsumerR0127
