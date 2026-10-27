import BinaryDefinitions

namespace ArithmeticThetaBinary

universe u

theorem entries_dvd_mul {R : Type u} [CommRing R] (d : R)
    (M U V : Matrix (Fin 2) (Fin 2) R)
    (h : ∀ i j, d ∣ M i j) : ∀ i j, d ∣ (U*M*V) i j := by
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.dvd_sum
  intro k hk
  apply dvd_mul_of_dvd_left
  rw [Matrix.mul_apply]
  apply Finset.dvd_sum
  intro l hl
  exact dvd_mul_of_dvd_right (h l k) (U i l)

theorem entries_dvd_smith_iff {R : Type u} [CommRing R] (d : R)
    (M N U V : Matrix (Fin 2) (Fin 2) R)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (h : U*M*V=N) :
    (∀ i j, d ∣ M i j) ↔ (∀ i j, d ∣ N i j) := by
  constructor
  · intro hd
    rw [← h]
    exact entries_dvd_mul d M U V hd
  · intro hd
    have hinv : U⁻¹*N*V⁻¹=M := by
      rw [← h]
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul U hU, one_mul]
      exact Matrix.mul_nonsing_inv_cancel_right V M hV
    rw [← hinv]
    exact entries_dvd_mul d N U⁻¹ V⁻¹ hd

theorem determinant_dvd_smith_iff {R : Type u} [CommRing R] (d : R)
    (M N U V : Matrix (Fin 2) (Fin 2) R)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (h : U*M*V=N) :
    d ∣ M.det ↔ d ∣ N.det := by
  rw [← h, Matrix.det_mul, Matrix.det_mul, hV.dvd_mul_right, hU.dvd_mul_left]

theorem gram_map_det (R : Type u) [CommRing R] (a b c : ℤ) :
    ((gram a b c).map (Int.castRingHom R)).det=((4*a*c-b^2 : ℤ) : R) := by
  simp [Matrix.det_fin_two, gram, Matrix.map_apply]
  ring

theorem gramContent_dvd_iff (a b c : ℤ) (d : ℕ) :
    d ∣ gramContent a b c ↔ ∀ i j, (d : ℤ) ∣ gram a b c i j := by
  rw [gramContent, Nat.dvd_gcd_iff, Int.dvd_gcd_iff, ← Int.natCast_dvd]
  constructor
  · rintro ⟨⟨ha,hb⟩,hc⟩ i j
    fin_cases i <;> fin_cases j <;> simpa [gram] using (by assumption)
  · intro h
    exact ⟨⟨by simpa [gram] using h 0 0, by simpa [gram] using h 0 1⟩,
      by simpa [gram] using h 1 1⟩

theorem nat_eq_of_prime_power_dvd (m n : ℕ)
    (h : ∀ p : ℕ, p.Prime → ∀ k : ℕ, p^k ∣ m ↔ p^k ∣ n) : m=n := by
  apply Nat.dvd_antisymm
  · apply (Nat.dvd_iff_prime_pow_dvd_dvd n m).mpr
    intro p k hp hd
    exact (h p hp k).mp hd
  · apply (Nat.dvd_iff_prime_pow_dvd_dvd m n).mpr
    intro p k hp hd
    exact (h p hp k).mpr hd

theorem local_determinant_prime_power (a b c : ℤ) (h : sameLocalSmith a b c)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (p : ℤ)^k ∣ 4*a*c-b^2 ↔ (p : ℤ)^k ∣ 80 := by
  obtain ⟨U,V,hU,hV,hUV⟩ := h p
  have hd := determinant_dvd_smith_iff ((p : PadicInt p)^k)
    ((gram a b c).map (Int.castRingHom (PadicInt p)))
    ((gram 1 0 20).map (Int.castRingHom (PadicInt p))) U V hU hV hUV
  rw [gram_map_det, gram_map_det] at hd
  norm_num only at hd
  exact (PadicInt.pow_p_dvd_int_iff k (4*a*c-b^2)).symm.trans
    (hd.trans (PadicInt.pow_p_dvd_int_iff k 80))

theorem local_content_prime_power (a b c : ℤ) (h : sameLocalSmith a b c)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    p^k ∣ gramContent a b c ↔ p^k ∣ 2 := by
  obtain ⟨U,V,hU,hV,hUV⟩ := h p
  have hd := entries_dvd_smith_iff ((p : PadicInt p)^k)
    ((gram a b c).map (Int.castRingHom (PadicInt p)))
    ((gram 1 0 20).map (Int.castRingHom (PadicInt p))) U V hU hV hUV
  simp only [Matrix.map_apply, Int.coe_castRingHom, PadicInt.pow_p_dvd_int_iff] at hd
  have hc : gramContent 1 0 20=2 := by norm_num [gramContent]
  rw [← hc, gramContent_dvd_iff, gramContent_dvd_iff]
  simpa only [Nat.cast_pow] using hd

theorem local_smith_invariants (a b c : ℤ) (_ha : 0<a)
    (hpos : 0<4*a*c-b^2) (h : sameLocalSmith a b c) :
    4*a*c-b^2=80 ∧ gramContent a b c=2 := by
  have hdet : (4*a*c-b^2).natAbs=80 := by
    apply nat_eq_of_prime_power_dvd
    intro p hp k
    let : Fact p.Prime := ⟨hp⟩
    have hd := local_determinant_prime_power a b c h p k
    simpa only [← Nat.cast_pow, Int.natCast_dvd, show (80 : ℤ).natAbs=80 from rfl] using hd
  constructor
  · have hc := congrArg (fun d : ℕ => (d : ℤ)) hdet
    simpa [abs_of_pos hpos] using hc
  · apply nat_eq_of_prime_power_dvd
    intro p hp k
    let : Fact p.Prime := ⟨hp⟩
    exact local_content_prime_power a b c h p k

end ArithmeticThetaBinary

#print axioms ArithmeticThetaBinary.entries_dvd_smith_iff
#print axioms ArithmeticThetaBinary.local_smith_invariants
