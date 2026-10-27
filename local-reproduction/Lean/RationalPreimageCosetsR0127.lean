import OrthogonalConsumerDefinitionsR0127
import CosetFiniteIndex

/-! The actual rational preimage quotient and its integral image quotient. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaOrthogonalConsumerR0127

private theorem castVec_injective (n : ℕ) : Function.Injective (castVec n) := by
  intro x y h
  ext j
  exact Int.cast_injective (congrFun h j)

private theorem castVec_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    castVec n (B.mulVec x) = (B.map (Int.castRingHom ℚ)).mulVec (castVec n x) := by
  ext j
  simp [castVec, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

private def integralImage {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : preimageLattice B) : Fin n → ℤ := Classical.choose t.property

private theorem integralImage_spec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : preimageLattice B) :
    castVec n (integralImage B t) = (B.map (Int.castRingHom ℚ)).mulVec t.val :=
  Classical.choose_spec t.property

private def integralImageHom {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    preimageLattice B →+ (Fin n → ℤ) where
  toFun := integralImage B
  map_zero' := by
    apply castVec_injective n
    rw [integralImage_spec, map_zero]
    exact Matrix.mulVec_zero _
  map_add' := by
    intro t u
    apply castVec_injective n
    rw [map_add, integralImage_spec, integralImage_spec, integralImage_spec]
    exact Matrix.mulVec_add _ _ _

/-- The quotient map induced by the actual rational matrix action, with its
specified value, finite cardinality, and a complete set of rational representatives. -/
theorem rational_preimage_cosets :
    ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
    ∃ E : RationalCosets B ≃+ ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)),
    (∀ (t : preimageLattice B) (x : Fin n → ℤ),
      (B.map (Int.castRingHom ℚ)).mulVec t.val = castVec n x →
      E (cosetClass B t) = (LinearMap.range (Matrix.mulVecLin B)).mkQ x) ∧
    Finite (RationalCosets B) ∧ Nat.card (RationalCosets B) = B.det.natAbs ∧
    ∃ t : Fin B.det.natAbs → preimageLattice B, Representatives B t := by
  intro n B hB
  classical
  let C := B.map (Int.castRingHom ℚ)
  have hC : C.det ≠ 0 := by
    change (B.map (Int.castRingHom ℚ)).det ≠ 0
    have hd : (B.det : ℚ) = (B.map (Int.castRingHom ℚ)).det :=
      (Int.castRingHom ℚ).map_det B
    rw [← hd]
    exact Int.cast_ne_zero.mpr hB
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_of_det_ne_zero hC
  have hsurj : Function.Surjective C.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (C.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hC))
  let S := LinearMap.range (Matrix.mulVecLin B)
  let f : preimageLattice B →+ ((Fin n → ℤ) ⧸ S) :=
    S.mkQ.toAddMonoidHom.comp (integralImageHom B)
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    obtain ⟨v, hv⟩ := hsurj (castVec n x)
    have hv' : v ∈ preimageLattice B := ⟨x, hv.symm⟩
    refine ⟨⟨v, hv'⟩, ?_⟩
    change S.mkQ (integralImage B ⟨v, hv'⟩) = S.mkQ x
    congr 1
    apply castVec_injective n
    exact (integralImage_spec B ⟨v, hv'⟩).trans hv
  have hker : periods B = f.ker := by
    ext t
    change (∃ k, castVec n k = t.val) ↔ S.mkQ (integralImage B t) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply castVec_injective n
      change castVec n (B.mulVec k) = castVec n (integralImage B t)
      rw [castVec_mulVec, integralImage_spec, hk]
    · rintro ⟨k, hk⟩
      refine ⟨k, hinj ?_⟩
      rw [← castVec_mulVec, ← integralImage_spec]
      exact congrArg (castVec n) hk
  let E : RationalCosets B ≃+ ((Fin n → ℤ) ⧸ S) :=
    QuotientAddGroup.liftEquiv (periods B) hfsurj hker
  obtain ⟨hfin, hcard⟩ := ArithmeticThetaCosets.finite_quotient_index n B hB
  let : Finite ((Fin n → ℤ) ⧸ S) := hfin
  have hRfin : Finite (RationalCosets B) := Finite.of_injective E E.injective
  refine ⟨E, ?_, hRfin, (Nat.card_congr E.toEquiv).trans hcard, ?_⟩
  · intro t x hx
    change S.mkQ (integralImage B t) = S.mkQ x
    congr 1
    exact castVec_injective n ((integralImage_spec B t).trans hx)
  · obtain ⟨e, ρ, hρ, _⟩ := ArithmeticThetaCosets.representatives_bijection n B hB
    have hex (i : Fin B.det.natAbs) : ∃ t : preimageLattice B, f t = e i := hfsurj (e i)
    choose t ht using hex
    refine ⟨t, ?_⟩
    have heq : (fun i => cosetClass B (t i)) = fun i => E.symm (e i) := by
      funext i
      apply E.injective
      rw [AddEquiv.apply_symm_apply]
      exact ht i
    unfold Representatives
    rw [heq]
    exact E.symm.bijective.comp e.bijective

end ArithmeticThetaOrthogonalConsumerR0127
