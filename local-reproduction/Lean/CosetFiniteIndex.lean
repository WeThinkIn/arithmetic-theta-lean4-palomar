import Mathlib


/-!
# Finite-index lattice cosets

For a nonsingular integral square matrix, its image has index equal to
the absolute determinant. Choosing representatives gives a unique
parametrization of every integral vector by a coset and an integral vector.
-/

namespace ArithmeticThetaCosets

/-- The actual quotient by the image of an integral matrix is finite and has
cardinality equal to its absolute determinant. -/
theorem finite_quotient_index (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) :
    Finite ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) ∧
    Nat.card ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = Int.natAbs B.det := by
  let f := Matrix.mulVecLin B
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_det_ne_zero hB
  let e := LinearEquiv.ofInjective f hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range f) e
  have he : (LinearMap.range f).subtype ∘ₗ AddMonoidHom.toIntLinearMap
      (e : (Fin n → ℤ) →+ LinearMap.range f) = f := by
    ext x i
    rfl
  rw [he] at h
  have hd : LinearMap.det f = B.det := by
    exact LinearMap.det_toLin' B
  rw [hd] at h
  exact ⟨Nat.finite_of_card_ne_zero (by rw [← h]; exact Int.natAbs_ne_zero.mpr hB), h.symm⟩

/-- Complete quotient representatives yield a bijection onto the integer lattice. -/
theorem representatives_bijection (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) :
    ∃ (e : Fin (Int.natAbs B.det) ≃ ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)))
      (ρ : Fin (Int.natAbs B.det) → (Fin n → ℤ)),
      (∀ i, (LinearMap.range (Matrix.mulVecLin B)).mkQ (ρ i) = e i) ∧
      Function.Bijective (fun p : Fin (Int.natAbs B.det) × (Fin n → ℤ) => ρ p.1 + B.mulVec p.2) := by
  classical
  let f := Matrix.mulVecLin B
  let S := LinearMap.range f
  obtain ⟨hfin, hcard⟩ := finite_quotient_index n B hB
  let : Finite ((Fin n → ℤ) ⧸ S) := hfin
  let e : Fin (Int.natAbs B.det) ≃ ((Fin n → ℤ) ⧸ S) :=
    (finCongr hcard.symm).trans (Finite.equivFin _).symm
  choose ρ hρ using fun i => S.mkQ_surjective (e i)
  have hz (k : Fin n → ℤ) : S.mkQ (B.mulVec k) = 0 := by
    change Submodule.Quotient.mk (B.mulVec k) = Submodule.Quotient.mk (0 : Fin n → ℤ)
    apply (Submodule.Quotient.eq S).mpr
    simpa using (show B.mulVec k ∈ S from ⟨k, rfl⟩)
  refine ⟨e, ρ, hρ, ?_, ?_⟩
  · rintro ⟨i, k⟩ ⟨j, l⟩ h
    have hij : i = j := by
      apply e.injective
      have hh := congrArg S.mkQ h
      simpa only [map_add, hz, add_zero, hρ] using hh
    subst j
    have hkl : k = l := Matrix.mulVec_injective_of_det_ne_zero hB (add_left_cancel h)
    subst l
    rfl
  · intro x
    let i := e.symm (S.mkQ x)
    have hx : x - ρ i ∈ S := by
      apply (Submodule.Quotient.eq S).mp
      change S.mkQ x = S.mkQ (ρ i)
      rw [hρ, Equiv.apply_symm_apply]
    obtain ⟨k, hk⟩ := hx
    refine ⟨(i, k), ?_⟩
    change ρ i + f k = x
    rw [hk]
    abel

end ArithmeticThetaCosets
