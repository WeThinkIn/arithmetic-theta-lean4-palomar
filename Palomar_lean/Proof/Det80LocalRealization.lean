module

public import BinaryDefinitions
public import Det80ReducedClassification
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat

@[expose] public section

universe u

namespace ArithmeticThetaBinary

theorem ambient_realization : ∀ j : Fin 3,
    (embeddings j).det ≠ 0 ∧
    (embeddings j).transpose * (forms 0).map (Int.castRingHom ℚ) * embeddings j =
      (![1,3,1] : Fin 3 → ℚ) j • (forms j).map (Int.castRingHom ℚ) := by
  intro j
  fin_cases j <;> constructor
  all_goals first
    | solve | norm_num [embeddings, Matrix.det_fin_two]
    | (ext i k; fin_cases i <;> fin_cases k <;>
        norm_num [embeddings, forms, gram, Matrix.mul_apply, Fin.sum_univ_two])


end ArithmeticThetaBinary

namespace ArithmeticThetaBinary

lemma integer_smith_witnesses (j : Fin 3) :
    ∃ U V : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit U.det ∧ IsUnit V.det ∧ U * forms j * V = gram 1 0 20 := by
  fin_cases j
  · refine ⟨1,1,?_,?_,?_⟩ <;> decide
  · refine ⟨!![1,0;7,-1], !![0,1;1,-3],?_,?_,?_⟩ <;> decide
  · refine ⟨!![-1,1;-5,4], !![1,-5;1,-4],?_,?_,?_⟩ <;> decide

theorem universal_smith_basechange (R : Type u) [CommRing R] (j : Fin 3) :
    ∃ U V : Matrix (Fin 2) (Fin 2) R, IsUnit U.det ∧ IsUnit V.det ∧
      U * (forms j).map (Int.castRingHom R) * V =
        (gram 1 0 20).map (Int.castRingHom R) := by
  obtain ⟨U,V,hu,hv,h⟩ := integer_smith_witnesses j
  let f := Int.castRingHom R
  refine ⟨U.map f, V.map f, ?_, ?_, ?_⟩
  · have hh := hu.map f
    simpa only [f, Int.coe_castRingHom, Int.cast_det] using hh
  · have hh := hv.map f
    simpa only [f, Int.coe_castRingHom, Int.cast_det] using hh
  · simpa only [Matrix.map_mul] using congrArg (fun M => M.map f) h

end ArithmeticThetaBinary
