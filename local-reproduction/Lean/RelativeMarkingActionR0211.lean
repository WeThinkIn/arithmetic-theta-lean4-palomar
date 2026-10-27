import RelativeFourCharacterDefinitionsR0211
import FullLevelTorsionSplittingR0175
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Right matrix action on the actual relative full-four marking sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
namespace RelativeMarkingActionR0211
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaFullLevelCoverR0175.FullLevelTorsionSplittingR0175
open ArithmeticThetaFourTorsion

section GroupCalculations
variable {H : Type*} [CommGroup H]

def coord (b : Fin 2 → H) (z : Fin 2 → ZMod 4) : H :=
  b 0 ^ (z 0).val * b 1 ^ (z 1).val

def act (b : Fin 2 → H) (A : Mat4) (i : Fin 2) : H :=
  coord b (fun j => A j i)

lemma val_add_pow (x : H) (hx : x ^ 4 = 1) (a b : ZMod 4) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, pow_residue x 4 _ hx, pow_add]

lemma val_mul_pow (x : H) (hx : x ^ 4 = 1) (a b : ZMod 4) :
    x ^ (a * b).val = (x ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_residue x 4 _ hx, pow_mul]

lemma act_killed (b : Fin 2 → H) (hb : ∀ i, b i ^ 4 = 1) (A : Mat4) :
    ∀ i, act b A i ^ 4 = 1 := by
  intro i
  simp only [act, coord, mul_pow, ← pow_mul]
  rw [Nat.mul_comm (A 0 i).val 4, Nat.mul_comm (A 1 i).val 4,
    pow_mul, pow_mul, hb 0, hb 1, one_pow, one_pow, one_mul]

lemma coord_act (b : Fin 2 → H) (hb : ∀ i, b i ^ 4 = 1)
    (A : Mat4) (z : Fin 2 → ZMod 4) :
    coord (act b A) z = coord b (A.mulVec z) := by
  simp only [coord, act, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [val_add_pow _ (hb 0), val_add_pow _ (hb 1)]
  simp only [val_mul_pow _ (hb 0), val_mul_pow _ (hb 1), mul_pow]
  ac_rfl

lemma act_one (b : Fin 2 → H) : act b 1 = b := by
  have hv : (1 : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by decide)
  funext i
  fin_cases i <;> simp [act, coord, Matrix.one_apply, hv]

lemma act_mul (b : Fin 2 → H) (hb : ∀ i, b i ^ 4 = 1) (A B : Mat4) :
    act (act b A) B = act b (A * B) := by
  funext i
  exact coord_act b hb A (fun j => B j i)

lemma mulVec_nonzero (A : Mat4) (hA : A.det = 1)
    (z : Fin 2 → ZMod 4) (hz : z ≠ 0) : A.mulVec z ≠ 0 := by
  intro h
  have hl : A.adjugate * A = 1 := by rw [Matrix.adjugate_mul, hA, one_smul]
  have he := congrArg (fun v => A.adjugate.mulVec v) h
  rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec, Matrix.mulVec_zero] at he
  exact hz he
end GroupCalculations

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} (G : Law R W)
    (hG : IsOriginLaw R W G) {T : Scheme.{u}} (t : T ⟶ Base R)

lemma fullLevel_ext (M N : FullLevel R W G 4 t) (hx : M.x = N.x) (hy : M.y = N.y) :
    M = N := by
  cases M
  cases N
  cases hx
  cases hy
  rfl

end RelativeMarkingActionR0211
open RelativeMarkingActionR0211
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaFullLevelCoverR0175.FullLevelTorsionSplittingR0175
open ArithmeticThetaFourTorsion

/-- Determinant-one matrices act on full-four scheme markings on the right. -/
theorem relative_marking_action :
∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ (T : AlgebraicGeometry.Scheme.{u}) (t : Quiver.Hom T (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 t) (A : ArithmeticThetaFourTorsion.Mat4), A.det = 1 → ∃! M' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 t, ArithmeticThetaRelativeFourCharacterR0211.Changes R W G t M M' A) ∧ (∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 t, ArithmeticThetaRelativeFourCharacterR0211.Changes R W G t M M 1) ∧ (∀ (M M' M'' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 t) (A B : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaRelativeFourCharacterR0211.Changes R W G t M M' A → ArithmeticThetaRelativeFourCharacterR0211.Changes R W G t M' M'' B → ArithmeticThetaRelativeFourCharacterR0211.Changes R W G t M M'' (A * B)) := by
  intro R _ W G hG T t
  letI : CommGroup (SchemeHomOver t (structureMap R W)) :=
    { G.pointGroup t with mul_comm := hG.2 t }
  let basis (M : FullLevel R W G 4 t) : Fin 2 → SchemeHomOver t (structureMap R W) :=
    ![M.x, M.y]
  have killed (M : FullLevel R W G 4 t) : ∀ i, basis M i ^ 4 = 1 := by
    intro i
    fin_cases i
    · exact (nsmul_pow G t 4 M.x).symm.trans M.killed_x
    · exact (nsmul_pow G t 4 M.y).symm.trans M.killed_y
  have changes (M N : FullLevel R W G 4 t) (A : Mat4) :
      Changes R W G t M N A ↔ basis N = act (basis M) A := by
    simp only [Changes, nsmul_pow G]
    constructor
    · rintro ⟨hx, hy⟩
      funext i
      fin_cases i
      · exact hx
      · exact hy
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro M A hA
    let b := basis M
    let b' := act b A
    have hb := killed M
    have hb' := act_killed b hb A
    have hav : ∀ i j : Fin 4, i.val ≠ 0 ∨ j.val ≠ 0 →
        Disjoint (Set.range (G.mul t (G.nsmul t i.val (b' 0))
          (G.nsmul t j.val (b' 1))).val) (Set.range (origin R W)) := by
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
      have he : G.mul t (G.nsmul t i.val (b' 0)) (G.nsmul t j.val (b' 1)) =
          G.mul t (G.nsmul t a.val M.x) (G.nsmul t c.val M.y) := by
        simp only [nsmul_pow G]
        exact coord_act b hb A z
      rw [he]
      exact M.avoids a c hac
    let N : FullLevel R W G 4 t :=
      { x := b' 0
        y := b' 1
        killed_x := (nsmul_pow G t 4 (b' 0)).trans (hb' 0)
        killed_y := (nsmul_pow G t 4 (b' 1)).trans (hb' 1)
        avoids := hav }
    have hN : Changes R W G t M N A := by
      simp only [Changes, nsmul_pow G]
      exact ⟨rfl, rfl⟩
    refine ⟨N, hN, ?_⟩
    intro N' hN'
    exact fullLevel_ext G t N' N (hN'.1.trans hN.1.symm) (hN'.2.trans hN.2.symm)
  · intro M
    exact (changes M M 1).mpr (act_one (basis M)).symm
  · intro M M' M'' A B hA hB
    apply (changes M M'' (A * B)).mpr
    rw [(changes M' M'' B).mp hB, (changes M M' A).mp hA]
    exact act_mul (basis M) (killed M) A B

#print axioms relative_marking_action
end ArithmeticThetaRelativeFourCharacterR0211

