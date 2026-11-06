module

public import Rank16Definitions
public import Rank16LatticeDefinitions
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Data.Rat.Star
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

universe u v
set_option maxHeartbeats 8000000
set_option maxRecDepth 2000

namespace ArithmeticThetaRank16

lemma sum_parameter (n : ℕ) (x : Fin n → ℤ) (r : ℤ) :
    (∑ i, (2*x i+r)) = 2*(∑ i, x i)+(n:ℤ)*r := by
  simp [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma doubled_parameter (n : ℕ) (hn : n = 8 ∨ n = 16) (y : Fin n → ℤ) :
    DPlusDoubled n y ↔ ∃ (r : ℤ) (x : Fin n → ℤ),
      (r = 0 ∨ r = 1) ∧ (∑ i, x i) % 2 = 0 ∧ ∀ i, y i = 2*x i+r := by
  constructor
  · rintro ⟨he | ho, hs⟩
    · let x : Fin n → ℤ := fun i => y i / 2
      have hx : ∀ i, y i = 2*x i+0 := by intro i; dsimp [x]; have := he i; omega
      have hsum : (∑ i, y i) = 2*∑ i, x i := by simp_rw [hx]; simp [← Finset.mul_sum]
      exact ⟨0, x, Or.inl rfl, by omega, hx⟩
    · let x : Fin n → ℤ := fun i => (y i-1) / 2
      have hx : ∀ i, y i = 2*x i+1 := by intro i; dsimp [x]; have := ho i; omega
      have hsum : (∑ i, y i) = 2*(∑ i, x i)+(n:ℤ) := by
        simp_rw [hx]; simpa using sum_parameter n x 1
      refine ⟨1, x, Or.inr rfl, ?_, hx⟩
      rcases hn with rfl | rfl <;> norm_num at hsum <;> omega
  · rintro ⟨r, x, hr, hs, hx⟩
    have hsum : (∑ i, y i) = 2*(∑ i, x i)+(n:ℤ)*r := by
      simp_rw [hx]; exact sum_parameter n x r
    rcases hr with rfl | rfl
    · refine ⟨Or.inl (fun i => ?_), ?_⟩
      · have := hx i; omega
      · omega
    · refine ⟨Or.inr (fun i => ?_), ?_⟩
      · have := hx i; omega
      · rcases hn with rfl | rfl <;> norm_num at hsum <;> omega

theorem original_doubled (n : ℕ) (hn : n = 8 ∨ n = 16) (y : Fin n → ℤ) :
    DPlusDoubled n y ↔ originalDPlus n (doubledRealization n y) := by
  rw [doubled_parameter n hn]
  constructor
  · rintro ⟨r, x, hr, hs, hx⟩
    rcases hr with rfl | rfl
    · left
      refine ⟨x, hs, ?_⟩
      intro i
      have hi : (y i : ℚ) = 2*(x i : ℚ)+0 := by exact_mod_cast hx i
      dsimp [doubledRealization]
      linarith
    · right
      refine ⟨x, hs, ?_⟩
      intro i
      have hi : (y i : ℚ) = 2*(x i : ℚ)+1 := by exact_mod_cast hx i
      dsimp [doubledRealization]
      linarith
  · rintro (⟨x, hs, hx⟩ | ⟨x, hs, hx⟩)
    · refine ⟨0, x, Or.inl rfl, hs, ?_⟩
      intro i
      have hi := hx i
      dsimp [doubledRealization] at hi
      have hq : (y i : ℚ) = 2*(x i : ℚ)+0 := by linarith
      exact_mod_cast hq
    · refine ⟨1, x, Or.inr rfl, hs, ?_⟩
      intro i
      have hi := hx i
      dsimp [doubledRealization] at hi
      have hq : (y i : ℚ) = 2*(x i : ℚ)+1 := by linarith
      exact_mod_cast hq

lemma doubled_basis_mul (n : ℕ) (z : Fin n → ℤ) :
    (latticeBasis n).mulVec (fun i => (z i : ℚ)) =
      doubledRealization n ((doubledBasis n).mulVec z) := by
  have hb (i j : Fin n) : latticeBasis n i j = (doubledBasis n i j : ℚ)/2 := by
    dsimp [latticeBasis, doubledBasis]
    split_ifs <;> norm_num
  ext i
  simp only [Matrix.mulVec, dotProduct, doubledRealization, hb, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma doubled_basis_inverse (n : ℕ) (hn : n = 8 ∨ n = 16)
    (y : Fin n → ℤ) (hy : DPlusDoubled n y) :
    (doubledBasis n).mulVec (basisCoordinates n y) = y := by
  have hnpos : 0 < n := by omega
  let o : Fin n := ⟨0, hnpos⟩
  have hp : ∀ i, 2*((y i-y o)/2) = y i-y o := by
    intro i
    have heq : y i % 2 = y o % 2 := by
      rcases hy.1 with he | ho
      · rw [he i, he o]
      · rw [ho i, ho o]
    omega
  have hl : 4*(((∑ i, y i)-(n:ℤ)*y o)/4) = (∑ i, y i)-(n:ℤ)*y o := by
    have hs := hy.2
    rcases hn with rfl | rfl <;> norm_num <;> omega
  clear hy
  rcases hn with rfl | rfl
  all_goals
    simp only [Fin.forall_fin_succ] at hp
    norm_num [o, Fin.succ, Fin.sum_univ_succ] at hp hl
    ext i
    fin_cases i <;>
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      norm_num [doubledBasis, basisCoordinates, Fin.sum_univ_succ, Fin.ext_iff, Fin.succ] <;>
      omega

lemma doubled_basis_member (n : ℕ) (hn : n = 8 ∨ n = 16) (z : Fin n → ℤ) :
    DPlusDoubled n ((doubledBasis n).mulVec z) := by
  rcases hn with rfl | rfl
  all_goals
    have hpar : z 0 % 2 = 0 ∨ z 0 % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    all_goals
      simp only [DPlusDoubled, Fin.forall_fin_succ, Fin.sum_univ_succ,
        Matrix.mulVec, dotProduct]
      norm_num [doubledBasis, Fin.ext_iff, Fin.succ]
      omega

theorem lattice_basis_image (n : ℕ) (hn : n = 8 ∨ n = 16) (y : Fin n → ℤ) :
    DPlusDoubled n y ↔ ∃ z : Fin n → ℤ,
      (latticeBasis n).mulVec (fun i => (z i : ℚ)) = doubledRealization n y := by
  constructor
  · intro hy
    refine ⟨basisCoordinates n y, ?_⟩
    rw [doubled_basis_mul, doubled_basis_inverse n hn y hy]
  · rintro ⟨z, hz⟩
    rw [doubled_basis_mul] at hz
    have heq : (doubledBasis n).mulVec z = y := by
      ext i
      have h := congrFun hz i
      dsimp [doubledRealization] at h
      exact_mod_cast (by linarith : (((doubledBasis n).mulVec z) i : ℚ) = (y i : ℚ))
    rw [← heq]
    exact doubled_basis_member n hn z

theorem original_basis_image (n : ℕ) (hn : n = 8 ∨ n = 16) (v : Fin n → ℚ) :
    originalDPlus n v ↔ ∃ z : Fin n → ℤ,
      (latticeBasis n).mulVec (fun i => (z i : ℚ)) = v := by
  constructor
  · rintro (⟨x, hs, hx⟩ | ⟨x, hs, hx⟩)
    · let y : Fin n → ℤ := fun i => 2*x i
      have hy : DPlusDoubled n y := (doubled_parameter n hn y).mpr
        ⟨0, x, Or.inl rfl, hs, by intro i; simp [y]⟩
      obtain ⟨z, hz⟩ := (lattice_basis_image n hn y).mp hy
      refine ⟨z, hz.trans ?_⟩
      ext i
      simp [doubledRealization, y, hx i]
    · let y : Fin n → ℤ := fun i => 2*x i+1
      have hy : DPlusDoubled n y := (doubled_parameter n hn y).mpr
        ⟨1, x, Or.inr rfl, hs, by intro i; rfl⟩
      obtain ⟨z, hz⟩ := (lattice_basis_image n hn y).mp hy
      refine ⟨z, hz.trans ?_⟩
      ext i
      simp only [doubledRealization, y, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hx i]
      ring
  · rintro ⟨z, hz⟩
    have hy := (original_doubled n hn ((doubledBasis n).mulVec z)).mp
      (doubled_basis_member n hn z)
    rw [← doubled_basis_mul n z, hz] at hy
    exact hy

end ArithmeticThetaRank16
