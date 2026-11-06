module

public import MillerPhaseMarkingInvariantR0115

@[expose] public section

/-! The exact character law for the literal root and intrinsic Miller phase.
The phase is never identified with a geometric Weil pairing in this module. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open ArithmeticThetaFourTorsion

private lemma phase_pow_add {k : Type u} [Field k] {z : k}
    (hz : IsPrimitiveRoot z 4) (a b : ZMod 4) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  have hm : z ^ ((a.val + b.val) % 4) = z ^ (a.val + b.val) := by
    simpa only [← hz.eq_orderOf] using pow_mod_orderOf z (a.val + b.val)
  rw [ZMod.val_add, hm, pow_add]

private lemma phase_pow_three {k : Type u} [Field k] {z : k}
    (hz : IsPrimitiveRoot z 4) : z ^ 3 = z⁻¹ := by
  have hn : z ≠ 0 := (hz.isUnit (by decide)).ne_zero
  calc
    z ^ 3 = (z ^ 3 * z) * z⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
    _ = z⁻¹ := by rw [← pow_succ, hz.pow_eq_one, one_mul]

/-- Every even-characteristic marking transforms the explicit root by the
accepted finite exponent, evaluated at the intrinsic normalized Miller phase. -/
theorem full_marking_character :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ b : Marking k e, IsBasis k e b →
    ∀ M : Mat4, PreservesEven M →
    root k e (act k e b M) =
      phase k e b ^ (characterExponent M).val * root k e b := by
  intro k _ _ _ e he b hb M hM
  have hc := (even_stabilizer_generated M).mp hM
  have hall : ∀ b : Marking k e, IsBasis k e b →
      root k e (act k e b M) =
        phase k e b ^ (characterExponent M).val * root k e b := by
    induction hc using Submonoid.closure_induction with
    | mem x hx =>
      intro b hb
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · obtain ⟨_, hp, hs⟩ := generator_s_miller_phase k e he b hb
        rw [finite_character_laws.2.2.2.2.1]
        have hv : (-1 : ZMod 4).val = 3 := by decide
        rw [hv, phase_pow_three hp]
        exact hs
      · obtain rfl := Set.mem_singleton_iff.mp hx
        rw [finite_character_laws.2.2.2.2.2.1]
        simpa using generator_t2_root k e he b hb
    | one =>
      intro b hb
      rw [act_one, finite_character_laws.2.2.2.1]
      simp
    | mul x y hx hy ihx ihy =>
      intro b hb
      have px := (even_stabilizer_generated x).mpr hx
      have py := (even_stabilizer_generated y).mpr hy
      have hbx := basis_act b hb x px.1
      have hp := (generator_s_miller_phase k e he b hb).2.1
      rw [← act_mul b hb.1, ihy py _ hbx,
        miller_phase_marking_invariant k e he b hb x px, ihx px _ hb,
        (finite_character_laws.2.2.2.2.2.2 x y px py).2, phase_pow_add hp]
      ring
  exact hall b hb

end ArithmeticThetaMarkingR0115
