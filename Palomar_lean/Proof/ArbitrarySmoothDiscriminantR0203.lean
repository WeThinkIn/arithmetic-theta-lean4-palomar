module

public import RelativeWeierstrassPresentationR0174

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Formal smoothness of the affine coordinate algebra detects the discriminant
unit over arbitrary rational rings. Regularity of the monic relation replaces
all domain assumptions in the conormal splitting argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
open TensorProduct Polynomial
namespace ArithmeticThetaLocalWeierstrassR0203
namespace ArbitrarySmoothDiscriminant
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]

lemma exists_derivation_of_regular_relation (f : P) (hf : IsRightRegular f)
    [Algebra.FormallySmooth R P] [Algebra.FormallySmooth R (P ⧸ Ideal.span {f})] :
    ∃ D : Derivation R P (P ⧸ Ideal.span {f}), D f=1 := by
  let I : Ideal P := Ideal.span {f}
  let A := P ⧸ I
  let J := RingHom.ker (algebraMap P A)
  have hJ : J=I := Ideal.mk_ker
  let e : P ≃ₗ[P] I :=
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton P P f) hf).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton f))
  let q : I →ₗ[P] A := I.mkQ ∘ₗ e.symm.toLinearMap
  have he (x : I) : e.symm x * f=(x:P) := by
    exact congrArg Subtype.val (e.apply_symm_apply x)
  have hq (x y : I) : q (x*y)=0 := by
    have hxy : e.symm (x*y) = (x:P)*e.symm y := by
      apply hf
      change e.symm (x*y) * f = ((x:P)*e.symm y)*f
      rw [he]
      change (x:P)*(y:P)=(x:P)*e.symm y*f
      rw [mul_assoc,he]
    change I.mkQ (e.symm (x*y))=0
    rw [hxy]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (I.mul_mem_right _ x.2)
  let φ : J.Cotangent →ₗ[P] A := (Ideal.Cotangent.lift q hq) ∘ₗ
    (Ideal.Cotangent.equivOfEq J I hJ).toLinearMap
  have hfJ : f ∈ J := hJ ▸ Ideal.subset_span (Set.mem_singleton f)
  have hφ : φ (J.toCotangent ⟨f,hfJ⟩)=1 := by
    change q (LinearEquiv.ofEq J I hJ ⟨f,hfJ⟩)=1
    change I.mkQ (e.symm ⟨f,_⟩)=1
    rw [show e.symm ⟨f,_⟩=1 from by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      change f = 1 * f
      exact (one_mul f).symm]
    rfl
  obtain ⟨l,hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R:=R) (P:=P) (A:=A)
    (Ideal.Quotient.mk_surjective)).mp inferInstance
  let δ : Ω[P⁄R] →ₗ[P] A := φ ∘ₗ l ∘ₗ (TensorProduct.mk P A Ω[P⁄R] 1)
  refine ⟨δ.compDer (KaehlerDifferential.D R P),?_⟩
  change φ (l (1 ⊗ₜ[P] KaehlerDifferential.D R P f))=1
  rw [← KaehlerDifferential.kerCotangentToTensor_toCotangent (R:=R) (A:=P) (B:=A) ⟨f,hfJ⟩]
  have hl' := LinearMap.congr_fun hl (J.toCotangent ⟨f,hfJ⟩)
  change l (KaehlerDifferential.kerCotangentToTensor R P A (J.toCotangent ⟨f,hfJ⟩))=J.toCotangent ⟨f,hfJ⟩ at hl'
  rw [hl',hφ]
end ArbitrarySmoothDiscriminant

open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.SmoothHypersurface

theorem arbitrary_smooth_discriminant (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R)
    [Algebra.FormallySmooth R (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial})] :
    IsUnit W.Δ := by
  nontriviality R
  letI : Algebra.FormallySmooth R (Polynomial (Polynomial R)) := Algebra.FormallySmooth.comp R (Polynomial R) (Polynomial (Polynomial R))
  obtain ⟨D,hD⟩ := ArbitrarySmoothDiscriminant.exists_derivation_of_regular_relation (R:=R)
    W.toAffine.polynomial W.toAffine.monic_polynomial.isRegular.right
  by_contra hΔ
  obtain ⟨m,hm,hmΔ⟩ := exists_max_ideal_of_mem_nonunits hΔ
  letI := hm
  let K := R ⧸ m
  letI : Field K := Ideal.Quotient.field m
  letI : Algebra ℚ K := inferInstanceAs (Algebra ℚ (R ⧸ m))
  letI : CharZero K := algebraRat.charZero K
  let ρ : R →+* K := Ideal.Quotient.mk m
  have hρΔ : (W.map ρ).Δ=0 := by
    rw [WeierstrassCurve.map_Δ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmΔ
  obtain ⟨x,y,hxy,hy,hx⟩ := singular_coordinates (W.map ρ) hρΔ
  let E : Polynomial (Polynomial R) →+* K :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom ρ x) y
  have hE : E W.toAffine.polynomial=0 := by
    simpa [E,WeierstrassCurve.Affine.polynomial,Polynomial.eval₂_pow,add_mul,add_assoc] using hxy
  let I : Ideal (Polynomial (Polynomial R)) := Ideal.span {W.toAffine.polynomial}
  let φ : (Polynomial (Polynomial R) ⧸ I) →+* K := Ideal.Quotient.lift I E (by
    change Ideal.span {W.toAffine.polynomial} ≤ RingHom.ker E
    rw [Ideal.span_le]
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact hE)
  have hX : φ (Ideal.Quotient.mk I (X : Polynomial (Polynomial R)))=y := by
    change E X=y
    simp [E]
  have hCX : φ (Ideal.Quotient.mk I (C X : Polynomial (Polynomial R)))=x := by
    change E (C X)=x
    simp [E]
  have hC (r : R) : φ (Ideal.Quotient.mk I (C (C r)))=ρ r := by
    change E (C (C r))=ρ r
    simp [E]
  have h := congrArg φ (derivation_polynomial W D)
  rw [hD,map_one] at h
  simp only [map_add,map_sub,map_mul,map_pow] at h
  change (1:K) = (φ 2 * φ (Ideal.Quotient.mk I X) + φ (Ideal.Quotient.mk I (C (C W.a₁))) * φ (Ideal.Quotient.mk I (C X)) + φ (Ideal.Quotient.mk I (C (C W.a₃)))) * φ (D X) +
    (φ (Ideal.Quotient.mk I (C (C W.a₁))) * φ (Ideal.Quotient.mk I X) - (φ 3 * φ (Ideal.Quotient.mk I (C X))^2 + φ 2 * φ (Ideal.Quotient.mk I (C (C W.a₂))) * φ (Ideal.Quotient.mk I (C X)) + φ (Ideal.Quotient.mk I (C (C W.a₄))))) * φ (D (C X)) at h
  rw [hX,hCX,hC,hC,hC,hC,show φ 2=2 from map_ofNat φ 2,show φ 3=3 from map_ofNat φ 3] at h
  change 2*y+ρ W.a₁*x+ρ W.a₃=0 at hy
  change ρ W.a₁*y-(3*x^2+2*ρ W.a₂*x+ρ W.a₄)=0 at hx
  rw [hy,hx,zero_mul,zero_mul,add_zero] at h
  exact one_ne_zero h

#print axioms arbitrary_smooth_discriminant
end ArithmeticThetaLocalWeierstrassR0203
end
