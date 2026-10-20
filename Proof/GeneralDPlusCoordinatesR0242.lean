module

public import Rank16Coordinates

@[expose] public section

set_option maxHeartbeats 800000

namespace ArithmeticThetaGeneralDPlusR0242
namespace Coordinates
open ArithmeticThetaRank16

lemma doubled_parameter (n : ℕ) (hn : 8 ∣ n) (y : Fin n → ℤ) :
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
      obtain ⟨k, rfl⟩ := hn
      push_cast at hsum
      omega
  · rintro ⟨r, x, hr, hs, hx⟩
    have hsum : (∑ i, y i) = 2*(∑ i, x i)+(n:ℤ)*r := by
      simp_rw [hx]; exact sum_parameter n x r
    rcases hr with rfl | rfl
    · refine ⟨Or.inl (fun i => ?_), ?_⟩
      · have := hx i; omega
      · omega
    · refine ⟨Or.inr (fun i => ?_), ?_⟩
      · have := hx i; omega
      · obtain ⟨k, rfl⟩ := hn
        push_cast at hsum
        omega

theorem original_doubled (n : ℕ) (hn : 8 ∣ n) (y : Fin n → ℤ) :
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


lemma split_sum {n : ℕ} (o l : Fin n) (hol : o ≠ l) (f : Fin n → ℤ) :
    ∑ i, f i = f o + f l + ∑ i ∈ (Finset.univ.erase o).erase l, f i := by
  have ho := Finset.sum_erase_add Finset.univ f (Finset.mem_univ o)
  have hl := Finset.sum_erase_add (Finset.univ.erase o) f
    (Finset.mem_erase.mpr ⟨Ne.symm hol, Finset.mem_univ l⟩)
  omega

lemma rows {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℤ) :
    let o : Fin n := ⟨0, by omega⟩
    let l : Fin n := ⟨n-1, by omega⟩
    let s := ∑ j ∈ (Finset.univ.erase o).erase l, z j
    ∀ i, (doubledBasis n).mulVec z i =
      z o + if i = l then 4*z l-2*s else if i = o then 0 else 2*z i := by
  dsimp only
  let o : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n-1, by omega⟩
  have hol : o ≠ l := by intro h; have := congrArg Fin.val h; dsimp [o,l] at this; omega
  have hz (j : Fin n) : (j.val = 0) ↔ j = o := by simp [o, Fin.ext_iff]
  have hl (j : Fin n) : (j.val = n-1) ↔ j = l := by simp [l, Fin.ext_iff]
  intro i
  change (∑ j, doubledBasis n i j * z j) = z o +
    if i = l then 4*z l-2*(∑ j ∈ (Finset.univ.erase o).erase l, z j)
    else if i = o then 0 else 2*z i
  rw [split_sum o l hol]
  simp only [doubledBasis, hz, hl, if_neg (Ne.symm hol)]
  have hs : (∑ j ∈ (Finset.univ.erase o).erase l,
      (if j = o then 1 else if j = l then (if i = l then 4 else 0)
       else if i = j then 2 else if i = l then -2 else 0) * z j) =
      ∑ j ∈ (Finset.univ.erase o).erase l,
        (if i = j then 2 else if i = l then -2 else 0) * z j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjo : j ≠ o := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hjl : j ≠ l := (Finset.mem_erase.mp hj).1
    simp [hjo,hjl]
  rw [hs]
  by_cases hil : i = l
  · subst i
    have he : (∑ j ∈ (Finset.univ.erase o).erase l,
        (if l = j then 2 else if l = l then -2 else 0) * z j) =
        -2 * ∑ j ∈ (Finset.univ.erase o).erase l, z j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Ne.symm (Finset.mem_erase.mp hj).1]
    rw [he]
    simp
    ring
  · simp only [hil, if_false]
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    by_cases hio : i = o
    · subst i; simp
    · simp [hio, hil]

lemma sum_rows {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℤ) :
    let o : Fin n := ⟨0, by omega⟩
    let l : Fin n := ⟨n-1, by omega⟩
    (∑ i, (doubledBasis n).mulVec z i) = (n:ℤ)*z o + 4*z l := by
  dsimp only
  simp_rw [rows hn z]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  let o : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n-1, by omega⟩
  have hol : o ≠ l := by intro h; have := congrArg Fin.val h; dsimp [o,l] at this; omega
  change (n:ℤ)*z o + (∑ i, if i = l then
    4*z l-2*(∑ j ∈ (Finset.univ.erase o).erase l, z j)
    else if i = o then 0 else 2*z i) = _
  rw [split_sum o l hol]
  simp only [hol, if_false, if_true]
  have h : (∑ i ∈ (Finset.univ.erase o).erase l,
      if i = l then 4*z l-2*(∑ j ∈ (Finset.univ.erase o).erase l, z j)
      else if i = o then 0 else 2*z i) =
      2 * ∑ i ∈ (Finset.univ.erase o).erase l, z i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1,
      (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1]
  rw [h]
  ring

lemma coordinates_doubled_inverse {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℤ) :
    basisCoordinates n ((doubledBasis n).mulVec z) = z := by
  let o : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n-1, by omega⟩
  have hol : o ≠ l := by intro h; have := congrArg Fin.val h; dsimp [o,l] at this; omega
  have hzero : (doubledBasis n).mulVec z o = z o := by
    have h := rows hn z o
    change (doubledBasis n).mulVec z o = z o + (if o = l then _ else if o = o then _ else _) at h
    simpa only [hol, if_false, if_true, add_zero] using h
  have hsum := sum_rows hn z
  change (∑ i, (doubledBasis n).mulVec z i) = (n:ℤ)*z o+4*z l at hsum
  ext j
  by_cases hjo : j = o
  · subst j
    simpa [basisCoordinates, o] using hzero
  · have hj0 : j.val ≠ 0 := by simpa [o, Fin.ext_iff] using hjo
    by_cases hjl : j = l
    · subst j
      simp only [basisCoordinates, hj0, dite_false, l]
      change ((∑ i, (doubledBasis n).mulVec z i) - (n:ℤ)*
        (doubledBasis n).mulVec z o)/4 = z l
      rw [hsum, hzero]
      omega
    · have hjlast : j.val ≠ n-1 := by simpa [l, Fin.ext_iff] using hjl
      simp only [basisCoordinates, hj0, dite_false, hjlast, if_false]
      change ((doubledBasis n).mulVec z j - (doubledBasis n).mulVec z o)/2 = z j
      have hj := rows hn z j
      change (doubledBasis n).mulVec z j = z o +
        (if j = l then _ else if j = o then _ else _) at hj
      simp only [hjl, hjo, if_false] at hj
      rw [hj, hzero]
      omega

lemma doubled_basis_member {n : ℕ} (hn : 8 ∣ n) (z : Fin n → ℤ) :
    DPlusDoubled n ((doubledBasis n).mulVec z) := by
  by_cases hn0 : n = 0
  · subst n
    simp [DPlusDoubled]
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  let o : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n-1, by omega⟩
  have hp (i : Fin n) : (doubledBasis n).mulVec z i % 2 = z o % 2 := by
    rw [rows hn2 z]
    change (z o + if i = l then _ else if i = o then _ else _) % 2 = _
    split_ifs <;> omega
  refine ⟨?_, ?_⟩
  · have h : z o % 2 = 0 ∨ z o % 2 = 1 := by omega
    rcases h with h | h
    · exact Or.inl (fun i => (hp i).trans h)
    · exact Or.inr (fun i => (hp i).trans h)
  · rw [sum_rows hn2 z]
    obtain ⟨k, hk⟩ := hn
    have hn4 : (n:ℤ) % 4 = 0 := by rw [hk]; omega
    simp [Int.add_emod, Int.mul_emod, hn4]

lemma doubled_basis_inverse {n : ℕ} (hn : 8 ∣ n)
    (y : Fin n → ℤ) (hy : DPlusDoubled n y) :
    (doubledBasis n).mulVec (basisCoordinates n y) = y := by
  by_cases hn0 : n = 0
  · subst n; exact Subsingleton.elim _ _
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  let o : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n-1, by omega⟩
  have hol : o ≠ l := by intro h; have := congrArg Fin.val h; dsimp [o,l] at this; omega
  have hp (i : Fin n) : 2*((y i-y o)/2) = y i-y o := by
    have heq : y i % 2 = y o % 2 := by
      rcases hy.1 with he | ho
      · rw [he i, he o]
      · rw [ho i, ho o]
    omega
  have hl : 4*(((∑ i, y i)-(n:ℤ)*y o)/4) = (∑ i, y i)-(n:ℤ)*y o := by
    have hs := hy.2
    obtain ⟨k, hk⟩ := hn
    have hn4 : (n:ℤ) % 4 = 0 := by rw [hk]; omega
    have hm : ((n:ℤ)*y o) % 4 = 0 := by simp [Int.mul_emod, hn4]
    omega
  have hc0 : basisCoordinates n y o = y o := by simp [basisCoordinates, o]
  have hcl : basisCoordinates n y l = ((∑ i, y i)-(n:ℤ)*y o)/4 := by
    have hl0 : l.val ≠ 0 := by dsimp [l]; omega
    simp [basisCoordinates, hl0, l, o]
  have hother (i : Fin n) (hil : i ≠ l) :
      (doubledBasis n).mulVec (basisCoordinates n y) i = y i := by
    rw [rows hn2]
    change basisCoordinates n y o + (if i = l then _ else if i = o then _ else _) = _
    rw [hc0, if_neg hil]
    by_cases hio : i = o
    · subst i; simp
    · have hi0 : i.val ≠ 0 := by simpa [o, Fin.ext_iff] using hio
      have hilast : i.val ≠ n-1 := by simpa [l, Fin.ext_iff] using hil
      simp only [hio, if_false, basisCoordinates, hi0, dite_false, hilast]
      change y o + 2*((y i-y o)/2) = y i
      rw [hp]; omega
  have hsum : (∑ i, (doubledBasis n).mulVec (basisCoordinates n y) i) = ∑ i, y i := by
    rw [sum_rows hn2]
    change (n:ℤ)*basisCoordinates n y o + 4*basisCoordinates n y l = _
    rw [hc0, hcl, hl]
    ring
  ext i
  by_cases hil : i = l
  · subst i
    have he : (∑ j ∈ Finset.univ.erase l,
        (doubledBasis n).mulVec (basisCoordinates n y) j) = ∑ j ∈ Finset.univ.erase l, y j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hother j (Finset.mem_erase.mp hj).1
    have h1 := Finset.sum_erase_add Finset.univ
      (fun j => (doubledBasis n).mulVec (basisCoordinates n y) j) (Finset.mem_univ l)
    have h2 := Finset.sum_erase_add Finset.univ y (Finset.mem_univ l)
    omega
  · exact hother i hil

theorem lattice_basis_image (n : ℕ) (hn : 8 ∣ n) (y : Fin n → ℤ) :
    DPlusDoubled n y ↔ ∃ z : Fin n → ℤ,
      (latticeBasis n).mulVec (fun i => (z i : ℚ)) = doubledRealization n y := by
  constructor
  · intro hy
    refine ⟨basisCoordinates n y, ?_⟩
    rw [doubled_basis_mul, doubled_basis_inverse hn y hy]
  · rintro ⟨z, hz⟩
    rw [doubled_basis_mul] at hz
    have heq : (doubledBasis n).mulVec z = y := by
      ext i
      have h := congrFun hz i
      dsimp [doubledRealization] at h
      exact_mod_cast (by linarith : (((doubledBasis n).mulVec z) i : ℚ) = (y i : ℚ))
    rw [← heq]
    exact doubled_basis_member hn z

theorem original_basis_image (n : ℕ) (hn : 8 ∣ n) (v : Fin n → ℚ) :
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
      (doubled_basis_member hn z)
    rw [← doubled_basis_mul n z, hz] at hy
    exact hy

lemma doubled_basis_injective (n : ℕ) (hn : 8 ∣ n) :
    Function.Injective (doubledBasis n).mulVec := by
  by_cases hn0 : n = 0
  · subst n; intro x z _; exact Subsingleton.elim _ _
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  intro x z h
  have he := congrArg (basisCoordinates n) h
  simpa only [coordinates_doubled_inverse hn2] using he

lemma lattice_basis_injective (n : ℕ) (hn : 8 ∣ n) :
    Function.Injective (fun z : Fin n → ℤ =>
      (latticeBasis n).mulVec (fun i => (z i : ℚ))) := by
  intro x z h
  apply doubled_basis_injective n hn
  dsimp only at h
  rw [doubled_basis_mul, doubled_basis_mul] at h
  ext i
  have hi := congrFun h i
  dsimp [doubledRealization] at hi
  exact_mod_cast (by linarith :
    (((doubledBasis n).mulVec x) i : ℚ) = (((doubledBasis n).mulVec z) i : ℚ))

end Coordinates

/-- Source-union, doubled parity and unique integral basis coordinates in every
rank divisible by eight, including the empty lattice. -/
theorem general_dplus_coordinates : ∀ n : ℕ, 8 ∣ n →
    (∀ y : Fin n → ℤ, ArithmeticThetaRank16.DPlusDoubled n y ↔
      ArithmeticThetaRank16.originalDPlus n (ArithmeticThetaRank16.doubledRealization n y)) ∧
    (∀ v : Fin n → ℚ, ArithmeticThetaRank16.originalDPlus n v ↔
      ∃! z : Fin n → ℤ, (ArithmeticThetaRank16.latticeBasis n).mulVec
        (fun i => (z i : ℚ)) = v) := by
  intro n hn
  refine ⟨Coordinates.original_doubled n hn, ?_⟩
  intro v
  rw [Coordinates.original_basis_image n hn]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz, fun w hw => Coordinates.lattice_basis_injective n hn (hw.trans hz.symm)⟩
  · rintro ⟨z, hz, _⟩
    exact ⟨z, hz⟩

end ArithmeticThetaGeneralDPlusR0242

#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_coordinates
