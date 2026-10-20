module

public import SchemeFourCharacterDefinitionsR0215
public import RelativeMarkingActionR0211

@[expose] public section

/-! Right column action on full markings of the original scheme family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemeFourMarkingActionR0215
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaRelativeFourCharacterR0211.RelativeMarkingActionR0211
open ArithmeticThetaFourTorsion

variable {S : Scheme.{u}} (E : Family S)

/-- The group structure uses precisely the family's given operations. -/
@[instance_reducible]
def pointGroup {T : Scheme.{u}} (t : T ⟶ S) : CommGroup (SchemeHomOver t E.p) where
  mul := E.law.mul t
  one := E.law.one t
  inv := E.law.inv t
  mul_assoc := E.law.mul_assoc t
  one_mul := E.law.one_mul t
  mul_one := E.law.mul_one t
  inv_mul_cancel := E.law.inv_mul_cancel t
  mul_comm := E.law.mul_comm t

lemma multiple_pow {T : Scheme.{u}} (t : T ⟶ S)
    (n : ℕ) (x : SchemeHomOver t E.p) :
    letI := pointGroup E t
    multiple E t n x = x ^ n := by
  letI := pointGroup E t
  induction n with
  | zero => rfl
  | succ n ih =>
    change E.law.mul t (multiple E t n x) x = x ^ (n+1)
    rw [ih]
    rfl

lemma fullLevel_ext (M N : FullLevel E 4) (hx : M.x = N.x) (hy : M.y = N.y) :
    M = N := by
  cases M
  cases N
  cases hx
  cases hy
  rfl

end SchemeFourMarkingActionR0215
open SchemeFourMarkingActionR0215
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaRelativeFourCharacterR0211.RelativeMarkingActionR0211
open ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaCharacter
open ArithmeticThetaFourTorsion

/-- The source right action, including preservation of the actual even point. -/
theorem scheme_four_marking_action :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∀ A : ArithmeticThetaFourTorsion.Mat4, A.det = 1 → ∃! M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A) ∧ ArithmeticThetaSchemeFourCharacterR0215.Changes E M M (1 : ArithmeticThetaFourTorsion.Mat4) ∧ (∀ (M' M'' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (A B : ArithmeticThetaFourTorsion.Mat4), A.det = 1 → B.det = 1 → ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A → ArithmeticThetaSchemeFourCharacterR0215.Changes E M' M'' B → ArithmeticThetaSchemeFourCharacterR0215.Changes E M M'' (A * B)) ∧ (∀ (M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A → ArithmeticThetaUniversalEvaluationR0213.evenPoint E M' = ArithmeticThetaUniversalEvaluationR0213.evenPoint E M) := by
  intro k _ _ S σ E M
  letI := pointGroup E (𝟙 S)
  let basis (M : FullLevel E 4) : Fin 2 → SchemeHomOver (𝟙 S) E.p :=
    ![M.x, M.y]
  have killed (M : FullLevel E 4) : ∀ i, basis M i ^ 4 = 1 := by
    intro i
    fin_cases i
    · exact (multiple_pow E (𝟙 S) 4 M.x).symm.trans M.killed_x
    · exact (multiple_pow E (𝟙 S) 4 M.y).symm.trans M.killed_y
  have changes (M N : FullLevel E 4) (A : Mat4) :
      Changes E M N A ↔ basis N = act (basis M) A := by
    simp only [Changes, multiple_pow E]
    constructor
    · rintro ⟨hx, hy⟩
      funext i
      fin_cases i
      · exact hx
      · exact hy
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hA
    let b := basis M
    let b' := act b A
    have hb := killed M
    have hb' := act_killed b hb A
    have hav : ∀ i j : Fin 4, i.val ≠ 0 ∨ j.val ≠ 0 →
        Disjoint (Set.range (E.law.mul (𝟙 S) (multiple E (𝟙 S) i.val (b' 0))
          (multiple E (𝟙 S) j.val (b' 1))).val) (Set.range (E.zero)) := by
      intro i j hij
      let z : Fin 2 → ZMod 4 := ![i, j]
      have hz : z ≠ 0 := by
        intro h
        rcases hij with hi | hj
        · exact hi (congrArg ZMod.val (congrFun h 0))
        · exact hj (congrArg ZMod.val (congrFun h 1))
      have hn := mulVec_nonzero A hA z hz
      let a : Fin 4 := ⟨(A.mulVec z 0).val, ZMod.val_lt _⟩
      let c : Fin 4 := ⟨(A.mulVec z 1).val, ZMod.val_lt _⟩
      have hac : a.val ≠ 0 ∨ c.val ≠ 0 := by
        by_contra h
        push Not at h
        apply hn
        funext k
        fin_cases k
        · exact (ZMod.val_eq_zero _).mp h.1
        · exact (ZMod.val_eq_zero _).mp h.2
      have he : E.law.mul (𝟙 S) (multiple E (𝟙 S) i.val (b' 0)) (multiple E (𝟙 S) j.val (b' 1)) =
          E.law.mul (𝟙 S) (multiple E (𝟙 S) a.val M.x) (multiple E (𝟙 S) c.val M.y) := by
        simp only [multiple_pow E]
        exact coord_act b hb A z
      rw [he]
      exact M.avoids a c hac
    let N : FullLevel E 4 :=
      { x := b' 0
        y := b' 1
        killed_x := (multiple_pow E (𝟙 S) 4 (b' 0)).trans (hb' 0)
        killed_y := (multiple_pow E (𝟙 S) 4 (b' 1)).trans (hb' 1)
        avoids := hav }
    have hN : Changes E M N A := by
      simp only [Changes, multiple_pow E]
      exact ⟨rfl, rfl⟩
    refine ⟨N, hN, ?_⟩
    intro N' hN'
    exact fullLevel_ext E N' N (hN'.1.trans hN.1.symm) (hN'.2.trans hN.2.symm)
  · exact (changes M M 1).mpr (act_one (basis M)).symm
  · intro M' M'' A B _ _ hA hB
    apply (changes M M'' (A * B)).mpr
    rw [(changes M' M'' B).mp hB, (changes M M' A).mp hA]
    exact act_mul (basis M) (killed M) A B

  · intro M' A hA hchange
    have hx4 : M.x^4 = 1 := (multiple_pow E _ 4 M.x).symm.trans M.killed_x
    have hy4 : M.y^4 = 1 := (multiple_pow E _ 4 M.y).symm.trans M.killed_y
    have hcx : M'.x = M.x^(A 0 0).val * M.y^(A 1 0).val := by
      have h := hchange.1
      simp only [multiple_pow E] at h
      exact h
    have hcy : M'.y = M.x^(A 0 1).val * M.y^(A 1 1).val := by
      have h := hchange.2
      simp only [multiple_pow E] at h
      exact h
    have hdoubleX : M'.x^2 = M.x^((A 0 0).val*2%4) * M.y^((A 1 0).val*2%4) := by
      rw [hcx, mul_pow, ← pow_mul, ← pow_mul,
        pow_mod_four M.x hx4, pow_mod_four M.y hy4]
    have hdoubleY : M'.y^2 = M.x^((A 0 1).val*2%4) * M.y^((A 1 1).val*2%4) := by
      rw [hcy, mul_pow, ← pow_mul, ← pow_mul,
        pow_mod_four M.x hx4, pow_mod_four M.y hy4]
    unfold ArithmeticThetaUniversalEvaluationR0213.evenPoint
    simp only [multiple_pow E]
    apply congrArg Subtype.val
    change M'.x^2 * M'.y^2 = M.x^2 * M.y^2
    rw [hdoubleX, hdoubleY]
    rcases even_residues A hA with h | h
    · simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, pow_zero, one_mul, mul_one]
    · simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, pow_zero, one_mul, mul_one]
      exact mul_comm _ _

#print axioms scheme_four_marking_action
end ArithmeticThetaSchemeFourCharacterR0215
