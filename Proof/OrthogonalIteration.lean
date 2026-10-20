module

public import OrthogonalPrimitives

@[expose] public section
namespace ArithmeticThetaOrthogonalAlgorithm

lemma step_column_past {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ)
    (k j : Fin n) (h : j ≤ k) :
    (fun i => step A C k i j) = (fun i => C i j) := by
  ext i
  simp [step, not_lt_of_ge h]

lemma step_column_future {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ)
    (k j : Fin n) (h : k < j) :
    (fun i => step A C k i j) = project A (fun a => C a k) (fun a => C a j) := by
  ext i
  simp [step, h]

theorem step_invariant (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (k : Fin n) (hi : Invariant A C k.val) : Invariant A (step A C k) (k.val + 1) := by
  rcases hi with ⟨_, ht, hd, ho⟩
  have hk : (fun i => C i k) ≠ 0 := by
    intro h
    have hkk := congrFun h k
    have hh := hd k
    simp only [Pi.zero_apply] at hkk
    omega
  have hpos := pairing_positive A hp (fun i => C i k) hk
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i j hji
    by_cases hkj : k < j
    · simp [step, hkj, project, ht i j hji, ht i k (lt_trans hkj hji)]
    · simp [step, hkj, ht i j hji]
  · intro i
    by_cases hki : k < i
    · simpa [step, hki, project, ht i k hki] using mul_pos hpos (hd i)
    · simpa [step, hki] using hd i
  · intro i j hik hij
    have hikle : i ≤ k := by omega
    rw [step_column_past A C k i hikle]
    by_cases hkj : k < j
    · rw [step_column_future A C k j hkj]
      by_cases hik_eq : i = k
      · subst i
        exact (projection_identities n A (fun a => C a k) (fun a => C a j)
          (fun a => C a k)).2
      · have hiklt : i.val < k.val := by omega
        rw [(projection_identities n A (fun a => C a k) (fun a => C a j)
          (fun a => C a i)).1, ho i j hiklt hij, ho i k hiklt hik_eq]
        ring
    · have hjk : j ≤ k := le_of_not_gt hkj
      rw [step_column_past A C k j hjk]
      by_cases hik_eq : i = k
      · subst i
        rw [pairing_symm A hs]
        apply ho j k
        · omega
        · exact hij.symm
      · apply ho i j
        · omega
        · exact hij

lemma runPrefix_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    runPrefix A (k + 1) = step A (runPrefix A k) ⟨k, hk⟩ := by
  have ht := List.take_concat_get' (List.finRange n) k (by simpa using hk)
  simp only [runPrefix]
  rw [← ht, List.foldl_append]
  simp

theorem prefix_invariant (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (k : ℕ) (hk : k ≤ n) : Invariant A (runPrefix A k) k := by
  induction k with
  | zero =>
    simp only [runPrefix, List.take_zero, List.foldl_nil]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i j hji
      simp [ne_of_gt hji]
    · intro i
      simp
    · intro i j hi
      omega
  | succ k ih =>
    have hkn : k < n := by omega
    rw [runPrefix_succ A k hkn]
    exact step_invariant n A _ hs hp ⟨k, hkn⟩ (ih (by omega))

end ArithmeticThetaOrthogonalAlgorithm
