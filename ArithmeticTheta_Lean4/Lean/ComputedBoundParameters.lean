import ComputedOrthogonalization
namespace ArithmeticThetaOrthogonalAlgorithm

theorem computed_bound_parameters (n h : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ)
    (hs : ∀ i, (A i).IsSymm) (he : ∀ i j, Even (A i j j))
    (hp : ∀ i, ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm').PosDef) :
    (∀ m : ℕ, m ∈ normSet A ↔ ∃ i : Fin h, ∃ j : Fin n, naturalNorms (A i) j = m) ∧
    (∀ m ∈ normSet A, 0 < m ∧ Even m) ∧ 0 < commonModulus A ∧
    (∀ d : ℕ, commonModulus A ∣ d ↔ ∀ i : Fin h, ∀ j : Fin n, naturalNorms (A i) j ∣ d) ∧
    0 < level A ∧ 0 < normExponent A ∧
    (∀ i : Fin h, ∀ j : Fin n, 2 * naturalNorms (A i) j ∣ level A) ∧
    distinctNormCount A ≤ h * n ∧ (0 < h → 0 < n → 0 < distinctNormCount A) := by
  have hm (m : ℕ) : m ∈ normSet A ↔ ∃ i : Fin h, ∃ j : Fin n, naturalNorms (A i) j = m := by
    simp [normSet, Finset.mem_image, Prod.exists]
  have hd (i : Fin h) := (computed_natural_data n (A i) (hs i) (he i) (hp i)).1
  have hnorm (m : ℕ) (hmem : m ∈ normSet A) : 0 < m ∧ Even m := by
    obtain ⟨i, j, rfl⟩ := (hm m).mp hmem
    exact ⟨(hd i j).1, (hd i j).2.1⟩
  have hN : 0 < commonModulus A := by
    change 0 < (normSet A).lcm id
    exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun m hmem =>
      ne_of_gt (hnorm m hmem).1))
  refine ⟨hm, hnorm, hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rw [commonModulus, Finset.lcm_dvd_iff]
    constructor
    · intro hdvd i j
      exact hdvd _ ((hm _).mpr ⟨i, j, rfl⟩)
    · intro hdvd m hmem
      obtain ⟨i, j, rfl⟩ := (hm m).mp hmem
      exact hdvd i j
  · dsimp [level]
    positivity
  · dsimp [normExponent]
    have hh : 1 < (1 + 12 * commonModulus A) ^ 2 := by nlinarith
    omega
  · intro i j
    have hdiv : naturalNorms (A i) j ∣ commonModulus A :=
      Finset.dvd_lcm ((hm _).mpr ⟨i, j, rfl⟩)
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨12 * t * commonModulus A, ?_⟩
    change 24 * commonModulus A ^ 2 = 2 * naturalNorms (A i) j * (12 * t * commonModulus A)
    rw [ht]
    ring
  · change (Finset.univ.image (fun p : Fin h × Fin n => naturalNorms (A p.1) p.2)).card ≤ h * n
    calc
      _ ≤ (Finset.univ : Finset (Fin h × Fin n)).card := Finset.card_image_le
      _ = h * n := by simp
  · intro hh hn
    apply Finset.card_pos.mpr
    refine ⟨naturalNorms (A ⟨0, hh⟩) ⟨0, hn⟩, ?_⟩
    exact (hm _).mpr ⟨⟨0, hh⟩, ⟨0, hn⟩, rfl⟩

end ArithmeticThetaOrthogonalAlgorithm
