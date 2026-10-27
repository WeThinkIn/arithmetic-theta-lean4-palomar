import GramThetaDefinitions
import Rank16Basis
import Rank16Coordinates
import Rank16Definitions
import Rank16LatticeDefinitions
import Rank16Nonisometry

universe u v
set_option maxHeartbeats 8000000
set_option maxRecDepth 2000

namespace ArithmeticThetaRank16Gram

open ArithmeticThetaRank16

lemma doubled_basis_injective (n : ℕ) (hn : n = 8 ∨ n = 16) :
    Function.Injective (doubledBasis n).mulVec := by
  have hu : IsUnit (latticeBasis n) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [lattice_basis_det n hn]
    exact isUnit_one)
  intro x z h
  have he : (latticeBasis n).mulVec (fun i => (x i : ℚ)) =
      (latticeBasis n).mulVec (fun i => (z i : ℚ)) := by
    rw [doubled_basis_mul, doubled_basis_mul, h]
  have hv := Matrix.mulVec_injective_of_isUnit hu he
  ext i
  exact_mod_cast congrFun hv i

lemma coordinates_doubled_inverse (n : ℕ) (hn : n = 8 ∨ n = 16) (z : Fin n → ℤ) :
    basisCoordinates n ((doubledBasis n).mulVec z) = z := by
  apply doubled_basis_injective n hn
  exact doubled_basis_inverse n hn _ (doubled_basis_member n hn z)

def latticeShellEquiv (n : ℕ) (hn : n = 8 ∨ n = 16) (m : ℕ) :
    GramShell n (latticeGram n) m ≃ NormShell n (8*m) where
  toFun x := ⟨(doubledBasis n).mulVec x.val, doubled_basis_member n hn x.val, by
    rw [doubled_basis_norm n hn, x.property]
    push_cast
    ring⟩
  invFun y := ⟨basisCoordinates n y.val, by
    have h := doubled_basis_norm n hn (basisCoordinates n y.val)
    rw [doubled_basis_inverse n hn y.val y.property.1, y.property.2] at h
    push_cast at h
    omega⟩
  left_inv x := Subtype.ext (coordinates_doubled_inverse n hn x.val)
  right_inv y := Subtype.ext (doubled_basis_inverse n hn y.val y.property.1)

theorem lattice_shell_correspondence (n : ℕ) (hn : n = 8 ∨ n = 16) (m : ℕ) :
    ∃ e : GramShell n (latticeGram n) m ≃ NormShell n (8*m),
      (∀ x, (e x).val = (doubledBasis n).mulVec x.val) ∧
      ∀ y, (e.symm y).val = basisCoordinates n y.val :=
  ⟨latticeShellEquiv n hn m, fun _ => rfl, fun _ => rfl⟩

lemma join_split (z : Fin 16 → ℤ) : join (split z) = z := by
  funext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
    simp only [join, split, Fin.addCases_left, Fin.addCases_right]

lemma split_join (p : (Fin 8 → ℤ) × (Fin 8 → ℤ)) : split (join p) = p := by
  ext i <;> simp only [split, join, Fin.addCases_left, Fin.addCases_right]

lemma sum_quadratic (z : Fin 16 → ℤ) :
    z ⬝ᵥ sumGram.mulVec z =
      (split z).1 ⬝ᵥ (latticeGram 8).mulVec (split z).1 +
      (split z).2 ⬝ᵥ (latticeGram 8).mulVec (split z).2 := by
  have hs : z ∘ (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16) =
      Sum.elim (split z).1 (split z).2 := by
    funext i
    cases i <;> rfl
  unfold sumGram
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [dotProduct_comp_equiv_symm, hs, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def]

lemma sum_doubled_member (z : Fin 16 → ℤ) :
    DPlusDoubled 8 (sumDoubled z).1 ∧ DPlusDoubled 8 (sumDoubled z).2 :=
  ⟨doubled_basis_member 8 (Or.inl rfl) _, doubled_basis_member 8 (Or.inl rfl) _⟩

lemma sum_coordinates_inverse (z : Fin 16 → ℤ) : sumCoordinates (sumDoubled z) = z := by
  simp only [sumCoordinates, sumDoubled, coordinates_doubled_inverse 8 (Or.inl rfl)]
  exact join_split z

lemma sum_doubled_inverse (p : (Fin 8 → ℤ) × (Fin 8 → ℤ))
    (hp : DPlusDoubled 8 p.1 ∧ DPlusDoubled 8 p.2) :
    sumDoubled (sumCoordinates p) = p := by
  simp only [sumDoubled, sumCoordinates, split_join,
    doubled_basis_inverse 8 (Or.inl rfl) p.1 hp.1,
    doubled_basis_inverse 8 (Or.inl rfl) p.2 hp.2]

lemma sum_doubled_norm (z : Fin 16 → ℤ) :
    normNumerator 8 (sumDoubled z).1 + normNumerator 8 (sumDoubled z).2 =
      4 * (z ⬝ᵥ sumGram.mulVec z) := by
  simp only [sumDoubled, doubled_basis_norm 8 (Or.inl rfl), sum_quadratic]
  ring

def sumShellEquiv (m : ℕ) : GramShell 16 sumGram m ≃ SumNormShell (8*m) where
  toFun x := ⟨sumDoubled x.val, (sum_doubled_member x.val).1,
    (sum_doubled_member x.val).2, by
      rw [sum_doubled_norm, x.property]
      push_cast
      ring⟩
  invFun y := ⟨sumCoordinates y.val, by
    have h := sum_doubled_norm (sumCoordinates y.val)
    rw [sum_doubled_inverse y.val ⟨y.property.1, y.property.2.1⟩, y.property.2.2] at h
    push_cast at h
    omega⟩
  left_inv x := Subtype.ext (sum_coordinates_inverse x.val)
  right_inv y := Subtype.ext (sum_doubled_inverse y.val ⟨y.property.1, y.property.2.1⟩)

theorem sum_shell_correspondence (m : ℕ) :
    ∃ e : GramShell 16 sumGram m ≃ SumNormShell (8*m),
      (∀ x, (e x).val = sumDoubled x.val) ∧
      ∀ y, (e.symm y).val = sumCoordinates y.val :=
  ⟨sumShellEquiv m, fun _ => rfl, fun _ => rfl⟩

end ArithmeticThetaRank16Gram
