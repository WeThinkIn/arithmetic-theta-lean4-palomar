module

public import BinaryDefinitions
public import Det80ReducedClassification
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

@[expose] public section

/-!
Elementary integral changes of variables for normalized binary Gram matrices.
The definitions and accepted reduced-classification snapshot are imported once.
The balanced shear requires only positivity of the first coefficient.
-/

namespace ArithmeticThetaBinary

lemma dvd_gramContent_iff (d : ℕ) (a b c : ℤ) :
    d ∣ gramContent a b c ↔ (d : ℤ) ∣ 2 * a ∧ (d : ℤ) ∣ b ∧ (d : ℤ) ∣ 2 * c := by
  rw [gramContent, Nat.dvd_gcd_iff, Int.dvd_gcd_iff, ← Int.natCast_dvd]
  tauto

lemma content_shear_dvd (a b c k : ℤ) :
    gramContent a b c ∣ gramContent a (b + 2*a*k) (a*k^2+b*k+c) := by
  have hh := (dvd_gramContent_iff (gramContent a b c) a b c).mp (dvd_refl _)
  rw [dvd_gramContent_iff]
  refine ⟨hh.1, hh.2.1.add (hh.1.mul_right k), ?_⟩
  rw [show 2 * (a*k^2+b*k+c) = (2*a)*k^2+b*(2*k)+2*c by ring]
  exact ((hh.1.mul_right _).add (hh.2.1.mul_right _)).add hh.2.2

lemma content_shear (a b c k : ℤ) :
    gramContent a (b+2*a*k) (a*k^2+b*k+c) = gramContent a b c := by
  apply Nat.dvd_antisymm
  · have hh := content_shear_dvd a (b+2*a*k) (a*k^2+b*k+c) (-k)
    have hb : b+2*a*k+2*a*(-k) = b := by ring
    have hc : a*(-k)^2+(b+2*a*k)*(-k)+(a*k^2+b*k+c) = c := by ring
    simpa only [hb, hc] using hh
  · exact content_shear_dvd a b c k

lemma shear_gram (a b c k : ℤ) :
    (shear k).transpose * gram a b c * shear k =
      gram a (b+2*a*k) (a*k^2+b*k+c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, gram, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma shear_det (k : ℤ) : (shear k).det = 1 := by
  simp [shear, Matrix.det_fin_two]

theorem balanced_shear (a b c : ℤ) (ha : 0 < a) :
    ∃ k : ℤ, |b+2*a*k| ≤ a ∧ (shear k).det = 1 ∧
      (shear k).transpose * gram a b c * shear k = gram a (b+2*a*k) (a*k^2+b*k+c) ∧
      4*a*(a*k^2+b*k+c)-(b+2*a*k)^2 = 4*a*c-b^2 ∧
      gramContent a (b+2*a*k) (a*k^2+b*k+c) = gramContent a b c := by
  let k : ℤ := -((b+a)/(2*a))
  refine ⟨k, ?_, shear_det k, shear_gram a b c k, by ring, content_shear a b c k⟩
  have hpos : 0 < 2*a := by omega
  have hn := Int.emod_nonneg (b+a) (ne_of_gt hpos)
  have hl := Int.emod_lt_of_pos (b+a) hpos
  have he := Int.emod_add_mul_ediv (b+a) (2*a)
  have hk : b+2*a*k = (b+a) % (2*a) - a := by dsimp [k]; nlinarith
  rw [hk, abs_le]
  constructor <;> omega

def swapVariables : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

lemma swapVariables_det : swapVariables.det = -1 := by
  norm_num [swapVariables, Matrix.det_fin_two]

lemma swapVariables_gram (a b c : ℤ) :
    swapVariables.transpose * gram a b c * swapVariables = gram c b a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapVariables, gram, Matrix.mul_apply, Fin.sum_univ_two]

lemma content_swap (a b c : ℤ) : gramContent c b a = gramContent a b c := by
  apply Nat.dvd_antisymm
  · rw [dvd_gramContent_iff]
    have hh := (dvd_gramContent_iff (gramContent c b a) c b a).mp (dvd_refl _)
    exact ⟨hh.2.2, hh.2.1, hh.1⟩
  · rw [dvd_gramContent_iff]
    have hh := (dvd_gramContent_iff (gramContent a b c) a b c).mp (dvd_refl _)
    exact ⟨hh.2.2, hh.2.1, hh.1⟩

lemma gram_congruence_comp (G P Q : Matrix (Fin 2) (Fin 2) ℤ) :
    (P*Q).transpose * G * (P*Q) = Q.transpose * (P.transpose * G * P) * Q := by
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

end ArithmeticThetaBinary
