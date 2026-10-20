module

public import PairingBilinearityR0118
public import MarkingPairingIdentificationR0118
import all MovedSupportMillerPairingR0116

@[expose] public section

/-! Alternation from local leading coefficients, and perfection and the
oriented determinant formula for the actual moved-divisor pairing. -/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118
open ArithmeticThetaReciprocityR0116

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

/-- The diagonal constant is one: negation has sign +1 at orders ±4. -/
private lemma closed_moved_diagonal [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Z : (Curve k e).Point) (hP : 4 • P = 0)
    (hZ : GoodShift k e P P Z) : movedValue k e D P P Z = 1 := by
  by_cases hp : P = 0
  · subst P
    exact moved_zero_left k e he D 0 Z (by simp) hZ
  let f := fourFunction k e P
  let T := D.translations
  let E := D.embedding
  let n := curveNegation k e he
  let F := (T P f / f) * (n f / n (T P f))
  have hf : f ≠ 0 := (four_function_provider k e he D P hP).1
  have ht : T P f ≠ 0 := by simpa using (T P).injective.ne hf
  have hnt : n (T P f) ≠ 0 := by simpa using n.injective.ne ht
  have ho : ∀ A, pointOrder k e T E F A = 0 :=
    fun A => general_moved_quotient_order_zero k e he T D.translations_spec
      D.branch E D.branch_spec D.embedding_spec P P A hP hP
  have hc := acceptedOrderZeroConstant k e he T D.translations_spec D.branch E
    D.branch_spec D.embedding_spec F ho
  have hfo : pointOrder k e T E f 0 = -4 := by
    simpa [order, f, Ne.symm hp] using (four_function_provider k e he D P hP).2.1 0
  have hto : pointOrder k e T E (T P f) 0 = 4 := by
    rw [(principal_divisor_support k e he T D.translations_spec D.branch E
      D.branch_spec D.embedding_spec f hf).2]
    simpa [order, f, hp] using (four_function_provider k e he D P hP).2.1 P
  have hnf : localLeading k e T E (n f) 0 = localLeading k e T E f 0 := by
    rw [localLeading_curveNegation k e he T D.translations_spec D.branch E
      D.branch_spec D.embedding_spec, neg_zero, hfo]
    norm_num
  have hntf : localLeading k e T E (n (T P f)) 0 =
      localLeading k e T E (T P f) 0 := by
    rw [localLeading_curveNegation k e he T D.translations_spec D.branch E
      D.branch_spec D.embedding_spec, neg_zero, hto]
    norm_num
  have hv : localValue k e T E F 0 = 1 := by
    have hl : localLeading k e T E F 0 = localValue k e T E F 0 := by
      unfold localLeading localValue
      rw [HahnSeries.leadingCoeff_eq]
      change (expansion k e T E 0 F).coeff (pointOrder k e T E F 0) = _
      rw [ho]
    rw [← hl]
    dsimp [F]
    rw [localLeading_mul, localLeading_div k e T E 0 _ _ hf,
      localLeading_div k e T E 0 _ _ hnt, hnf, hntf]
    rw [div_mul_div_cancel₀ (localLeading_ne_zero k e T E 0 hf),
      div_self (localLeading_ne_zero k e T E 0 ht)]
  rw [hv] at hc
  exact general_moved_pairing_of_function_field_identity k e he T D.translations_spec
    D.branch E D.branch_spec D.embedding_spec P P Z hP hP hZ 1 hc

/-- Arithmetic descent uses the coefficient-induced expansion map. -/
private lemma moved_diagonal (he : Function.Injective e) (D : LocalData k e)
    (P Z : (Curve k e).Point) (hP : 4 • P = 0) (hZ : GoodShift k e P P Z) :
    movedValue k e D P P Z = 1 := by
  let K := AlgebraicClosure k
  let : DecidableEq K := Classical.decEq K
  let c : k →+* K := algebraMap k K
  let eK : Fin 3 → K := c ∘ e
  let b := ArithmeticThetaMarkingR0115.fieldMap e c
  let hK := PowerSeries.map c D.branch
  have heK : Function.Injective eK := c.injective.comp he
  have hhK : ArithmeticThetaMillerR0114.branchEquation K eK hK :=
    branchEquation_baseChange k e K D.branch D.branch_spec
  obtain ⟨T', hT', _⟩ := function_field_translations K eK heK
  obtain ⟨E', hE', _⟩ := ArithmeticThetaMillerR0114.infinity_function_field_embedding
    K eK heK hK hhK
  let D' : LocalData K eK := ⟨T', hK, E', hT', hhK, hE'⟩
  apply c.injective
  rw [map_one, show c (movedValue k e D P P Z) =
      movedValue K eK D' (b P) (b P) (b Z) from
    movedValue_baseChange k e he K D D' rfl P P Z]
  exact closed_moved_diagonal K eK heK D' (b P) (b Z)
    (by rw [← map_nsmul, hP, map_zero]) (goodShift_baseChange k e K P P Z hZ)

lemma pairing_diagonal (he : Function.Injective e) (D : LocalData k e)
    (b : ArithmeticThetaMarkingR0115.Marking k e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis k e b)
    (P : (Curve k e).Point) (hP : 4 • P = 0) : pairing k e D P P = 1 := by
  obtain ⟨z, hz⟩ := (all_four_miller_provider k e he D).2 b hb P P hP hP
  rw [← ((pairing_shift_independence k e he D b hb P P hP hP).1 _ hz).2.2.2.2]
  exact moved_diagonal k e he D P _ hP hz

omit [CharZero k] in
private lemma torsion_nsmul (P : (Curve k e).Point) (hP : 4 • P = 0) (n : ℕ) :
    4 • (n • P) = 0 := by rw [smul_comm, hP, smul_zero]

private lemma pairing_nsmul (he : Function.Injective e) (D : LocalData k e)
    (b : ArithmeticThetaMarkingR0115.Marking k e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis k e b)
    (P Q : (Curve k e).Point) (hP : 4 • P = 0) (hQ : 4 • Q = 0) (n : ℕ) :
    pairing k e D (n • P) Q = pairing k e D P Q ^ n ∧
    pairing k e D P (n • Q) = pairing k e D P Q ^ n := by
  have hn (X Y : (Curve k e).Point) (hX : 4 • X = 0) (hY : 4 • Y = 0) :
      pairing k e D X Y ≠ 0 := by
    intro hz
    have hp := (pairing_shift_independence k e he D b hb X Y hX hY).2.1
    rw [hz, zero_pow (by decide)] at hp
    exact zero_ne_one hp
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero]
    constructor
    · apply mul_left_cancel₀ (hn 0 Q (by simp) hQ)
      simpa using (pairing_bilinearity k e he D b hb 0 0 Q (by simp) (by simp) hQ).1.symm
    · apply mul_left_cancel₀ (hn P 0 hP (by simp))
      simpa using (pairing_bilinearity k e he D b hb P 0 0 hP (by simp) (by simp)).2.symm
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul,
      (pairing_bilinearity k e he D b hb (n • P) P Q
        (torsion_nsmul k e P hP n) hP hQ).1,
      (pairing_bilinearity k e he D b hb P (n • Q) Q
        hP (torsion_nsmul k e Q hQ n) hQ).2, ih.1, ih.2, pow_succ]
    exact ⟨rfl, rfl⟩

omit [CharZero k] [DecidableEq k] in
private lemma root_pow_add {z : k} (hz : IsPrimitiveRoot z 4) (a c : ZMod 4) :
    z ^ (a + c).val = z ^ a.val * z ^ c.val := by
  have hm : z ^ ((a.val + c.val) % 4) = z ^ (a.val + c.val) := by
    simpa only [← hz.eq_orderOf] using pow_mod_orderOf z (a.val + c.val)
  rw [ZMod.val_add, hm, pow_add]

omit [CharZero k] [DecidableEq k] in
private lemma root_pow_mul {z : k} (hz : IsPrimitiveRoot z 4) (a c : ZMod 4) :
    z ^ (a * c).val = (z ^ a.val) ^ c.val := by
  have hm : z ^ ((a.val * c.val) % 4) = z ^ (a.val * c.val) := by
    simpa only [← hz.eq_orderOf] using pow_mod_orderOf z (a.val * c.val)
  rw [ZMod.val_mul, hm, pow_mul]

omit [CharZero k] [DecidableEq k] in
private lemma root_pow_sub {z : k} (hz : IsPrimitiveRoot z 4) (a c : ZMod 4) :
    z ^ (a - c).val = z ^ a.val * (z ^ c.val)⁻¹ := by
  have hn : z ^ c.val ≠ 0 := pow_ne_zero _ (hz.isUnit (by decide)).ne_zero
  apply mul_right_cancel₀ hn
  rw [← root_pow_add k hz, sub_add_cancel]
  rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]

lemma pairing_coordinates (he : Function.Injective e) (D : LocalData k e)
    (b : ArithmeticThetaMarkingR0115.Marking k e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis k e b)
    (a c : Fin 2 → ZMod 4) :
    pairing k e D (ArithmeticThetaMarkingR0115.coordinates k e b a)
      (ArithmeticThetaMarkingR0115.coordinates k e b c) =
      pairing k e D (b 0) (b 1) ^ (a 0 * c 1 - a 1 * c 0).val := by
  let z := pairing k e D (b 0) (b 1)
  have hz : IsPrimitiveRoot z 4 := by
    dsimp [z]
    rw [marking_pairing_identification k e he D b hb]
    exact (ArithmeticThetaMarkingR0115.generator_s_miller_phase k e he b hb).2.1
  have h00 := pairing_diagonal k e he D b hb (b 0) (hb.1 0)
  have h11 := pairing_diagonal k e he D b hb (b 1) (hb.1 1)
  have hsum : 4 • (b 0 + b 1) = 0 := by rw [nsmul_add, hb.1 0, hb.1 1, add_zero]
  have hswap : z * pairing k e D (b 1) (b 0) = 1 := by
    have h := pairing_diagonal k e he D b hb (b 0 + b 1) hsum
    rw [(pairing_bilinearity k e he D b hb (b 0) (b 1) (b 0 + b 1)
      (hb.1 0) (hb.1 1) hsum).1,
      (pairing_bilinearity k e he D b hb (b 0) (b 0) (b 1)
        (hb.1 0) (hb.1 0) (hb.1 1)).2,
      (pairing_bilinearity k e he D b hb (b 1) (b 0) (b 1)
        (hb.1 1) (hb.1 0) (hb.1 1)).2, h00, h11, one_mul, mul_one] at h
    exact h
  have hrev : pairing k e D (b 1) (b 0) = z⁻¹ := by
    apply mul_left_cancel₀ (hz.isUnit (by decide)).ne_zero
    rw [hswap, mul_inv_cancel₀ (hz.isUnit (by decide)).ne_zero]
  have ht (v : Fin 2 → ZMod 4) :
      4 • ArithmeticThetaMarkingR0115.coordinates k e b v = 0 := by
    simp only [ArithmeticThetaMarkingR0115.coordinates, nsmul_add,
      torsion_nsmul k e _ (hb.1 0), torsion_nsmul k e _ (hb.1 1), add_zero]
  have heval (i : Fin 2) :
      pairing k e D (b i) (ArithmeticThetaMarkingR0115.coordinates k e b c) =
        pairing k e D (b i) (b 0) ^ (c 0).val *
        pairing k e D (b i) (b 1) ^ (c 1).val := by
    rw [ArithmeticThetaMarkingR0115.coordinates,
      (pairing_bilinearity k e he D b hb (b i) ((c 0).val • b 0) ((c 1).val • b 1)
        (hb.1 i) (torsion_nsmul k e _ (hb.1 0) _) (torsion_nsmul k e _ (hb.1 1) _)).2,
      (pairing_nsmul k e he D b hb (b i) (b 0) (hb.1 i) (hb.1 0) _).2,
      (pairing_nsmul k e he D b hb (b i) (b 1) (hb.1 i) (hb.1 1) _).2]
  rw [show ArithmeticThetaMarkingR0115.coordinates k e b a =
      (a 0).val • b 0 + (a 1).val • b 1 from rfl,
    (pairing_bilinearity k e he D b hb ((a 0).val • b 0) ((a 1).val • b 1)
      (ArithmeticThetaMarkingR0115.coordinates k e b c)
      (torsion_nsmul k e _ (hb.1 0) _) (torsion_nsmul k e _ (hb.1 1) _) (ht c)).1,
    (pairing_nsmul k e he D b hb (b 0) _ (hb.1 0) (ht c) _).1,
    (pairing_nsmul k e he D b hb (b 1) _ (hb.1 1) (ht c) _).1,
    heval 0, heval 1, h00, h11, hrev]
  simp only [one_pow, one_mul, mul_one, inv_pow]
  change (z ^ (c 1).val) ^ (a 0).val * ((z ^ (c 0).val) ^ (a 1).val)⁻¹ = _
  rw [← root_pow_mul k hz, ← root_pow_mul k hz, ← root_pow_sub k hz]
  congr 2
  ring

/-- The unchanged geometric pairing is primitive on a full basis, alternating,
nondegenerate on every rational four-torsion point, and has the oriented
coordinate determinant rule as a theorem. -/
theorem pairing_alternating_perfect :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ D : LocalData k e,
    ∀ b : ArithmeticThetaMarkingR0115.Marking k e,
    ArithmeticThetaMarkingR0115.IsBasis k e b →
    IsPrimitiveRoot (pairing k e D (b 0) (b 1)) 4 ∧
    (∀ P : (Curve k e).Point, 4 • P = 0 → pairing k e D P P = 1) ∧
    (∀ P : (Curve k e).Point, 4 • P = 0 →
      (∀ Q : (Curve k e).Point, 4 • Q = 0 → pairing k e D P Q = 1) → P = 0) ∧
    (∀ a c : Fin 2 → ZMod 4,
      pairing k e D (ArithmeticThetaMarkingR0115.coordinates k e b a)
        (ArithmeticThetaMarkingR0115.coordinates k e b c) =
      pairing k e D (b 0) (b 1) ^ (a 0 * c 1 - a 1 * c 0).val) := by
  intro k _ _ _ e he D b hb
  have hz : IsPrimitiveRoot (pairing k e D (b 0) (b 1)) 4 := by
    rw [marking_pairing_identification k e he D b hb]
    exact (ArithmeticThetaMarkingR0115.generator_s_miller_phase k e he b hb).2.1
  refine ⟨hz, pairing_diagonal k e he D b hb, ?_, pairing_coordinates k e he D b hb⟩
  intro P hP hrad
  obtain ⟨a, ha⟩ := hb.2.2 P hP
  have hval (t : ZMod 4) (ht : pairing k e D (b 0) (b 1) ^ t.val = 1) : t = 0 := by
    apply (ZMod.val_eq_zero t).mp
    exact hz.pow_inj (ZMod.val_lt t) (by decide) (by simpa using ht)
  have h0 : a 0 = 0 := by
    apply hval
    have h := pairing_coordinates k e he D b hb a ![0, 1]
    have hc : ArithmeticThetaMarkingR0115.coordinates k e b ![0, 1] = b 1 := by
      simp [ArithmeticThetaMarkingR0115.coordinates, show (1 : ZMod 4).val = 1 from rfl]
    rw [ha, hc, hrad _ (hb.1 1)] at h
    simpa using h.symm
  have h1 : a 1 = 0 := by
    have h : -a 1 = 0 := by
      apply hval
      have h := pairing_coordinates k e he D b hb a ![1, 0]
      have hc : ArithmeticThetaMarkingR0115.coordinates k e b ![1, 0] = b 0 := by
        simp [ArithmeticThetaMarkingR0115.coordinates, show (1 : ZMod 4).val = 1 from rfl]
      rw [ha, hc, hrad _ (hb.1 0)] at h
      simpa using h.symm
    exact neg_eq_zero.mp h
  rw [← ha, ArithmeticThetaMarkingR0115.coordinates, h0, h1]
  simp

end ArithmeticThetaGeometricPairingR0118
