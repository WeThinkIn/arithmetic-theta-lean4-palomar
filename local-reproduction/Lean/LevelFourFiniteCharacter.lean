import FourTorsionDefinitions
import Mathlib.Data.Fintype.Card

namespace ArithmeticThetaFourTorsion

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance preservesEvenDecidable (M : Mat4) : Decidable (PreservesEven M) :=
  inferInstanceAs (Decidable (M.det = 1 ∧ ∀ v : Fin 2 → ZMod 2,
    (Matrix.mulVec (reduceTwo M) v) 0 * (Matrix.mulVec (reduceTwo M) v) 1 = v 0 * v 1))

/-- Sixteen explicit words in the two specified generators. -/
def evenWord (i : Fin 4) (j k : Fin 2) : Mat4 :=
  generatorS ^ i.val * generatorT2 ^ j.val *
    (generatorS * generatorT2 * generatorS ^ 3) ^ k.val

theorem even_word_exhaustive : ∀ M : Mat4, PreservesEven M →
    ∃ i : Fin 4, ∃ j k : Fin 2, M = evenWord i j k := by
  decide

theorem even_stabilizer_card : Nat.card {M : Mat4 // PreservesEven M} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem even_word_product : ∀ (i : Fin 4) (j k : Fin 2)
    (a : Fin 4) (b c : Fin 2),
    PreservesEven (evenWord i j k * evenWord a b c) ∧
    characterExponent (evenWord i j k * evenWord a b c) =
      characterExponent (evenWord i j k) + characterExponent (evenWord a b c) := by
  decide

theorem finite_character_laws :
    PreservesEven (1 : Mat4) ∧ PreservesEven generatorS ∧ PreservesEven generatorT2 ∧
    characterExponent (1 : Mat4) = 0 ∧ characterExponent generatorS = -1 ∧
    characterExponent generatorT2 = 0 ∧
    (∀ M N : Mat4, PreservesEven M → PreservesEven N →
      PreservesEven (M*N) ∧ characterExponent (M*N) = characterExponent M + characterExponent N) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro M N hM hN
  obtain ⟨i,j,k,rfl⟩ := even_word_exhaustive M hM
  obtain ⟨a,b,c,rfl⟩ := even_word_exhaustive N hN
  exact even_word_product i j k a b c

theorem even_stabilizer_generated : ∀ M : Mat4, PreservesEven M ↔
    M ∈ Submonoid.closure ({generatorS, generatorT2} : Set Mat4) := by
  intro M
  constructor
  · intro h
    obtain ⟨i,j,k,rfl⟩ := even_word_exhaustive M h
    have hS : generatorS ∈ Submonoid.closure ({generatorS, generatorT2} : Set Mat4) :=
      Submonoid.subset_closure (by simp)
    have hT : generatorT2 ∈ Submonoid.closure ({generatorS, generatorT2} : Set Mat4) :=
      Submonoid.subset_closure (by simp)
    exact mul_mem (mul_mem (pow_mem hS _) (pow_mem hT _))
      (pow_mem (mul_mem (mul_mem hS hT) (pow_mem hS _)) _)
  · intro h
    induction h using Submonoid.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact finite_character_laws.2.1
      · obtain rfl := Set.mem_singleton_iff.mp hx
        exact finite_character_laws.2.2.1
    | one => exact finite_character_laws.1
    | mul x y hx hy ihx ihy => exact (finite_character_laws.2.2.2.2.2.2 x y ihx ihy).1

theorem finite_character_unique : ∀ f : Mat4 → ZMod 4,
    f 1 = 0 → f generatorS = -1 → f generatorT2 = 0 →
    (∀ M N : Mat4, PreservesEven M → PreservesEven N → f (M*N) = f M + f N) →
    ∀ M : Mat4, PreservesEven M → f M = characterExponent M := by
  intro f h1 hS hT hmul M hM
  have hc := (even_stabilizer_generated M).mp hM
  induction hc using Submonoid.closure_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hS.trans finite_character_laws.2.2.2.2.1.symm
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact hT.trans finite_character_laws.2.2.2.2.2.1.symm
  | one => exact h1.trans finite_character_laws.2.2.2.1.symm
  | mul x y hx hy ihx ihy =>
    have px := (even_stabilizer_generated x).mpr hx
    have py := (even_stabilizer_generated y).mpr hy
    rw [hmul x y px py, ihx px, ihy py]
    exact (finite_character_laws.2.2.2.2.2.2 x y px py).2.symm

end ArithmeticThetaFourTorsion
