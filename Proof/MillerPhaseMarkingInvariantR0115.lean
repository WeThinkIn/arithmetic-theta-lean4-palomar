module

public import GeneratorSMillerPhaseR0115
public import GeneratorT2RootR0115

@[expose] public section

/-! Invariance of the actual normalized Miller evaluation phase under the
    even-characteristic stabilizer. No pairing law is assumed. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open WeierstrassCurve.Affine ArithmeticThetaFourTorsion

private lemma pointX_neg {k : Type u} [Field k] [DecidableEq k]
    (e : Fin 3 → k) (P : (Curve k e).Point) :
    pointX k e (-P) = pointX k e P := by
  cases P <;> rfl

private lemma pointY_neg {k : Type u} [Field k] [DecidableEq k]
    (e : Fin 3 → k) (P : (Curve k e).Point) :
    pointY k e (-P) = -pointY k e P := by
  cases P with
  | zero => change (0 : k) = -0; simp
  | some x y h =>
    change (Curve k e).negY x y = -y
    simp [negY, Curve, ArithmeticThetaMillerR0114.Curve, splitCurve]

private lemma root_double_S {k : Type u} [Field k] [DecidableEq k]
    (e : Fin 3 → k) (b : Marking k e) (hb : ∀ i, 4 • b i = 0) :
    root k e (act k e (act k e b generatorS) generatorS) = -root k e b := by
  have hS := act_four_torsion b hb generatorS
  unfold root
  rw [labels_generatorS e _ hS, labels_generatorS e b hb,
    act_generatorS e _ hS, act_generatorS e b hb]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, pointX_neg, pointY_neg]
  simp only [rootExpression, mul_neg, div_neg]
  rfl

/-- The S-action preserves the phase, using its primitive fourth-root property. -/
lemma phase_generatorS {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (he : Function.Injective e) (b : Marking k e)
    (hb : IsBasis k e b) :
    phase k e (act k e b generatorS) = phase k e b := by
  have hbS := basis_act b hb generatorS finite_character_laws.2.1.1
  obtain ⟨_, hp, hrootS⟩ := generator_s_miller_phase k e he b hb
  have hsq : (phase k e b)^2 = -1 :=
    (hp.pow_of_dvd (by decide : (2 : ℕ) ≠ 0) (by decide)).eq_neg_one_of_two_right
  have hnonzero := (basis_coordinate_geometry k e he b hb).2.2.2.2.1
  rw [(generator_s_miller_phase k e he _ hbS).1, root_double_S e b hb.1,
    hrootS]
  have hz : phase k e b ≠ 0 := by
    intro h
    simp [h] at hsq
  field_simp
  linear_combination -hsq

/-- T² leaves all doubled labels fixed; its S-successor uses the unchanged -P. -/
private lemma root_T2_S {k : Type u} [Field k] [DecidableEq k]
    (e : Fin 3 → k) (b : Marking k e) (hb : ∀ i, 4 • b i = 0) :
    root k e (act k e (act k e b generatorT2) generatorS) =
      root k e (act k e b generatorS) := by
  have hact : act k e b generatorT2 = ![b 0, 2 • b 0 + b 1] := by
    funext j
    have hv1 : (1 : ZMod 4).val = 1 := by decide
    have hv2 : (2 : ZMod 4).val = 2 := by decide
    fin_cases j <;> simp [act, generatorT2, hv1, hv2]
  have h20 : 2 • (2 • b 0) = 0 := by
    rw [← mul_nsmul]
    exact hb 0
  have hl : labels k e (act k e b generatorT2) = labels k e b := by
    rw [hact]
    funext j
    fin_cases j <;> simp [labels, h20]
  unfold root
  rw [labels_generatorS e _ (act_four_torsion b hb generatorT2), hl,
    labels_generatorS e b hb, act_generatorS e _ (act_four_torsion b hb generatorT2),
    act_generatorS e b hb, hact]
  rfl

/-- The T²-action preserves the phase by the actual two-torsion translation law. -/
lemma phase_generatorT2 {k : Type u} [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (he : Function.Injective e) (b : Marking k e)
    (hb : IsBasis k e b) :
    phase k e (act k e b generatorT2) = phase k e b := by
  have hbT := basis_act b hb generatorT2 finite_character_laws.2.2.1.1
  rw [(generator_s_miller_phase k e he _ hbT).1,
    generator_t2_root k e he b hb, root_T2_S e b hb.1,
    (generator_s_miller_phase k e he b hb).1]

/-- Invariance for every determinant-one marking preserving the even characteristic. -/
theorem miller_phase_marking_invariant :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ b : Marking k e, IsBasis k e b →
    ∀ M : Mat4, PreservesEven M → phase k e (act k e b M) = phase k e b := by
  intro k _ _ _ e he b hb M hM
  have hc := (even_stabilizer_generated M).mp hM
  have hall : ∀ b : Marking k e, IsBasis k e b →
      phase k e (act k e b M) = phase k e b := by
    induction hc using Submonoid.closure_induction with
    | mem x hx =>
      intro b hb
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact phase_generatorS e he b hb
      · obtain rfl := Set.mem_singleton_iff.mp hx
        exact phase_generatorT2 e he b hb
    | one => intro b hb; rw [act_one]
    | mul x y hx hy ihx ihy =>
      intro b hb
      have hbx := basis_act b hb x ((even_stabilizer_generated x).mpr hx).1
      rw [← act_mul b hb.1, ihy ((even_stabilizer_generated y).mpr hy) _ hbx,
        ihx ((even_stabilizer_generated x).mpr hx) _ hb]
  exact hall b hb

end ArithmeticThetaMarkingR0115
