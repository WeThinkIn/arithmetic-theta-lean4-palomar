import PairingAlternatingPerfectR0118
import PairingFieldNaturalityR0118

/-! The full marking character with its phase given by the actual
moved-divisor pairing. Accepted geometric providers and the accepted finite
character calculation are reused without changing their definitions. -/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118

/-- Construct geometric local data independently of the marking, and identify
the full character and determinant-one invariance with the actual pairing. -/
theorem geometric_four_character :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∃ D : LocalData k e,
    ∀ b : ArithmeticThetaMarkingR0115.Marking k e,
    ArithmeticThetaMarkingR0115.IsBasis k e b →
    IsPrimitiveRoot (pairing k e D (b 0) (b 1)) 4 ∧
    (∀ M : ArithmeticThetaFourTorsion.Mat4,
      ArithmeticThetaFourTorsion.PreservesEven M →
      ArithmeticThetaMarkingR0115.root k e (ArithmeticThetaMarkingR0115.act k e b M) =
        pairing k e D (b 0) (b 1) ^
          (ArithmeticThetaFourTorsion.characterExponent M).val *
        ArithmeticThetaMarkingR0115.root k e b) ∧
    (∀ M : ArithmeticThetaFourTorsion.Mat4, M.det = 1 →
      pairing k e D (ArithmeticThetaMarkingR0115.act k e b M 0)
        (ArithmeticThetaMarkingR0115.act k e b M 1) = pairing k e D (b 0) (b 1)) := by
  intro k _ _ _ e he
  obtain ⟨T, hT, _⟩ := ArithmeticThetaReciprocityR0116.function_field_translations k e he
  obtain ⟨h, hh, _⟩ := ArithmeticThetaMillerR0114.infinity_branch k e
  obtain ⟨E, hE, _⟩ :=
    ArithmeticThetaMillerR0114.infinity_function_field_embedding k e he h hh
  let D : LocalData k e := ⟨T, h, E, hT, hh, hE⟩
  refine ⟨D, ?_⟩
  intro b hb
  have hp := pairing_alternating_perfect k e he D b hb
  refine ⟨hp.1, ?_, ?_⟩
  · intro M hM
    rw [marking_pairing_identification k e he D b hb]
    exact ArithmeticThetaMarkingR0115.full_marking_character k e he b hb M hM
  · intro M hM
    have hd := hp.2.2.2 (fun i => M i 0) (fun i => M i 1)
    change pairing k e D (ArithmeticThetaMarkingR0115.act k e b M 0)
      (ArithmeticThetaMarkingR0115.act k e b M 1) =
      pairing k e D (b 0) (b 1) ^ (M 0 0 * M 1 1 - M 1 0 * M 0 1).val at hd
    have hm : M 0 0 * M 1 1 - M 1 0 * M 0 1 = (1 : ZMod 4) := by
      simpa only [Matrix.det_fin_two, mul_comm] using hM
    simpa only [hm, show (1 : ZMod 4).val = 1 from rfl, pow_one] using hd

end ArithmeticThetaGeometricPairingR0118
