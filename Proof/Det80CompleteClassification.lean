module

public import BinaryReduction
public import Det80ReducedClassification

@[expose] public section

namespace ArithmeticThetaBinary

def signChange : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

lemma signChange_det : signChange.det = -1 := by
  norm_num [signChange, Matrix.det_fin_two]

lemma signChange_gram (a b c : ℤ) :
    signChange.transpose * gram a b c * signChange = gram a (-b) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signChange, gram, Matrix.mul_apply, Fin.sum_univ_two]

theorem all_positive_classes (a b c : ℤ) (ha : 0 < a)
    (hdelta : 4*a*c-b^2 = 80) (hcontent : gramContent a b c = 2) :
    ∃ (j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ),
      IsUnit U.det ∧ U.transpose * gram a b c * U = forms j := by
  have hpos : 0 < 4*a*c-b^2 := by omega
  obtain ⟨a', b', c', ha', hb', hac', hd', hg', U, hU, hcong⟩ :=
    reduced_representative a b c ha hpos
  have hd80 : 4*a'*c'-b'^2 = 80 := hd'.trans hdelta
  have hg2 : gramContent a' b' c' = 2 := hg'.trans hcontent
  have hcases := (ArithmeticThetaDet80.smith_gcd_classification a' b' c').mp
    ⟨ha', hb', hac', hd80, hg2⟩
  rcases hcases with hc | hc | hc | hc
  · rcases hc with ⟨rfl, rfl, rfl⟩
    exact ⟨0, U, hU, by simpa [forms] using hcong⟩
  · rcases hc with ⟨rfl, rfl, rfl⟩
    refine ⟨1, U * signChange, ?_, ?_⟩
    · rw [Matrix.det_mul, signChange_det]
      simpa using hU.neg
    · rw [gram_congruence_comp, hcong, signChange_gram]
      norm_num [forms]
  · rcases hc with ⟨rfl, rfl, rfl⟩
    exact ⟨1, U, hU, by simpa [forms] using hcong⟩
  · rcases hc with ⟨rfl, rfl, rfl⟩
    exact ⟨2, U, hU, by simpa [forms] using hcong⟩

end ArithmeticThetaBinary
