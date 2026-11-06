module

public import MarkingCharacterDefinitionsR0115
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import IndependentHalvesFourBasisR0114

@[expose] public section

/-! The right action on actual four-torsion markings. -/
noncomputable section
universe u
namespace ArithmeticThetaMarkingR0115
open ArithmeticThetaFourTorsion

private lemma val_add_smul {G : Type*} [AddCommGroup G] (P : G)
    (hP : 4 • P = 0) (a b : ZMod 4) :
    (a + b).val • P = a.val • P + b.val • P := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul _ hP, add_nsmul]

private lemma val_mul_smul {G : Type*} [AddCommGroup G] (P : G)
    (hP : 4 • P = 0) (a b : ZMod 4) :
    (a * b).val • P = a.val • (b.val • P) := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul _ hP, mul_nsmul, smul_comm]

variable {k : Type u} [Field k] [DecidableEq k] {e : Fin 3 → k}

/-- Four-torsion is preserved by every matrix, without a determinant hypothesis. -/
lemma act_four_torsion (b : Marking k e) (hb : ∀ i, 4 • b i = 0) (M : Mat4) :
    ∀ i, 4 • act k e b M i = 0 := by
  intro i
  simp only [act, nsmul_add, smul_comm 4, hb, nsmul_zero, add_zero]

/-- Coefficients transform by the usual matrix action on column vectors. -/
lemma coordinates_act (b : Marking k e) (hb : ∀ i, 4 • b i = 0)
    (M : Mat4) (z : Fin 2 → ZMod 4) :
    coordinates k e (act k e b M) z = coordinates k e b (M.mulVec z) := by
  simp only [coordinates, act, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [val_add_smul _ (hb 0), val_add_smul _ (hb 1)]
  simp only [val_mul_smul _ (hb 0), val_mul_smul _ (hb 1), nsmul_add]
  simp only [smul_comm (z 0).val, smul_comm (z 1).val]
  abel

lemma act_one (b : Marking k e) : act k e b 1 = b := by
  have hv : (1 : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by decide)
  funext i
  fin_cases i <;> simp [act, Matrix.one_apply, hv]

lemma act_mul (b : Marking k e) (hb : ∀ i, 4 • b i = 0) (M N : Mat4) :
    act k e (act k e b M) N = act k e b (M * N) := by
  funext i
  change coordinates k e (act k e b M) (fun j => N j i) = _
  rw [coordinates_act b hb]
  rfl

lemma basis_of_independent_halves [CharZero k] (he : Function.Injective e)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    IsBasis k e ![P, Q] := by
  have h := ArithmeticThetaMillerR0114.independent_halves_four_basis k e he P Q hP hQ
  have h4P : 4 • P = 0 := by
    rcases hP with ⟨hP, hd⟩
    rw [show 4 = 2 * 2 from rfl, mul_nsmul, hd, two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [WeierstrassCurve.Affine.negY, ArithmeticThetaMillerR0114.Curve,
      splitCurve]
  have h4Q : 4 • Q = 0 := by
    rcases hQ with ⟨hQ, hd⟩
    rw [show 4 = 2 * 2 from rfl, mul_nsmul, hd, two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [WeierstrassCurve.Affine.negY, ArithmeticThetaMillerR0114.Curve,
      splitCurve]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using h4P
    · simpa using h4Q
  · intro z w hzw
    have ht : 4 • coordinates k e ![P,Q] z = 0 := by
      simp [coordinates, smul_comm 4, h4P, h4Q]
    obtain ⟨v, hv, hu⟩ := (h _).mp ht
    exact (hu z (by simp [coordinates])).trans
      (hu w (by simpa [coordinates] using hzw.symm)).symm
  · intro T hT
    obtain ⟨z, hz, _⟩ := (h T).mp hT
    exact ⟨z, by simpa [coordinates] using hz⟩

lemma basis_act (b : Marking k e) (hb : IsBasis k e b) (M : Mat4)
    (hM : M.det = 1) : IsBasis k e (act k e b M) := by
  have hl : M.adjugate * M = 1 := by rw [Matrix.adjugate_mul, hM, one_smul]
  have hr : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hM, one_smul]
  refine ⟨act_four_torsion b hb.1 M, ?_, ?_⟩
  · intro z w hzw
    rw [coordinates_act b hb.1, coordinates_act b hb.1] at hzw
    have hzw' := congrArg (fun v => M.adjugate.mulVec v) (hb.2.1 hzw)
    simpa only [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec] using hzw'
  · intro T hT
    obtain ⟨z, hz⟩ := hb.2.2 T hT
    refine ⟨M.adjugate.mulVec z, ?_⟩
    rw [coordinates_act b hb.1, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec, hz]

/-- Full-four bases and the exact right action laws for the actual point group. -/
theorem basis_right_action :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e →
    (∀ P Q : (Curve k e).Point,
      ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P →
      ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q → IsBasis k e ![P, Q]) ∧
    (∀ b : Marking k e, IsBasis k e b → act k e b 1 = b ∧
      (∀ M N : Mat4, act k e (act k e b M) N = act k e b (M * N)) ∧
      (∀ M : Mat4, M.det = 1 → IsBasis k e (act k e b M))) := by
  intro k _ _ _ e he
  refine ⟨fun P Q hP hQ => basis_of_independent_halves he P Q hP hQ, ?_⟩
  intro b hb
  exact ⟨act_one b, act_mul b hb.1, basis_act b hb⟩

end ArithmeticThetaMarkingR0115
