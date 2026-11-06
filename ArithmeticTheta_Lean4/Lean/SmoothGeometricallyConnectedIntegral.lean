import Mathlib

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct nonZeroDivisors
open TensorProduct

namespace ArithmeticThetaCompletedCharts

universe u
noncomputable section

/-- Smooth base change of a normal domain is integrally closed in its generic fiber.
No domain assumption is imposed on the smooth algebra. -/
theorem smooth_integrallyClosedIn_genericFiber
    (R S : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] FractionRing R) := by
  let K := FractionRing R
  let T := S ⊗[R] K
  have hi : Function.Injective (algebraMap S T) :=
    Algebra.TensorProduct.includeLeft_injective (S := S) (IsFractionRing.injective R K)
  have himage (z : S ⊗[R] integralClosure R K) :
      ∃ s : S, algebraMap S T s = (TensorProduct.toIntegralClosure R S K z : T) := by
    induction z with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨sx, hsx⟩ := hx
      obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by simp [map_add, hsx, hsy]⟩
    | tmul s b =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp b.property
      refine ⟨s * algebraMap R S r, ?_⟩
      change (s * algebraMap R S r) ⊗ₜ[R] (1 : K) = s ⊗ₜ[R] (b : K)
      rw [← hr, mul_comm]
      simp only [← Algebra.smul_def, smul_tmul]
      rw [Algebra.smul_def, mul_one]
  refine ⟨hi, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := K)).2 ⟨x, hx⟩
    obtain ⟨s, hs⟩ := himage z
    exact ⟨s, hs.trans (congrArg Subtype.val hz)⟩
  · rintro ⟨s, rfl⟩
    exact isIntegral_algebraMap

/-- An idempotent is integral over any coefficient ring. -/
theorem idempotent_isIntegral (R : Type*) [CommRing R]
    {T : Type*} [CommRing T] [Algebra R T] {e : T} (he : IsIdempotentElem e) :
    _root_.IsIntegral R e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X,
    Polynomial.monic_X_pow_sub (lt_of_le_of_lt Polynomial.degree_X_le (by decide)), ?_⟩
  simpa [pow_two, IsIdempotentElem] using sub_eq_zero.mpr he

/-- A coordinate idempotent in an injective product representation cuts out a domain. -/
theorem domain_localization_of_coordinate
    {S : Type*} [CommRing S] {ι : Type*} [DecidableEq ι] {F : ι → Type*} [∀ i, Field (F i)]
    (φ : S →+* ∀ i, F i) (hφ : Function.Injective φ)
    (i : ι) (e : S) (he : φ e = Pi.single i 1) :
    IsDomain (Localization.Away e) := by
  classical
  have hee : IsIdempotentElem e := by
    apply hφ
    ext j
    simp only [map_mul, he, Pi.mul_apply]
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  let ψ : S →+* F i := (Pi.evalRingHom F i).comp φ
  have hψ : IsUnit (ψ e) := by simp [ψ, he]
  let θ : Localization.Away e →+* F i := IsLocalization.Away.lift e hψ
  apply Function.Injective.isDomain θ
  intro x y hxy
  obtain ⟨a, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e hee x
  obtain ⟨b, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e hee y
  have hab : ψ a = ψ b := by
    simpa only [θ, IsLocalization.Away.lift_eq] using hxy
  apply (IsLocalization.eq_iff_exists (.powers e) (Localization.Away e)).mpr
  refine ⟨⟨e, Submonoid.mem_powers e⟩, ?_⟩
  apply hφ
  ext j
  by_cases h : j = i
  · subst j
    simpa [he, ψ] using hab
  · simp [he, Pi.single_eq_of_ne h]

/-- Relative integral closure in a reduced Artinian overring supplies domain
principal neighborhoods at every prime, including for rings with many components. -/
theorem exists_domain_localization_of_artinian_overring
    (S T : Type u) [CommRing S] [CommRing T] [Algebra S T]
    [IsIntegrallyClosedIn S T] [IsArtinianRing T] [_root_.IsReduced T]
    (p : Ideal S) [p.IsPrime] :
    ∃ e : S, e ∉ p ∧ IsDomain (Localization.Away e) := by
  classical
  let ι := MaximalSpectrum T
  let : Fintype ι := Fintype.ofFinite ι
  let F (i : ι) := T ⧸ i.asIdeal
  let (i : ι) : Field (F i) := Ideal.Quotient.field i.asIdeal
  let E := IsArtinianRing.equivPi T
  have hi : Function.Injective (algebraMap S T) := IsIntegralClosure.algebraMap_injective S S T
  let φ : S →+* ∀ i, F i := E.toRingHom.comp (algebraMap S T)
  have hφ : Function.Injective φ := E.injective.comp hi
  have hex (i : ι) : ∃ e : S, φ e = Pi.single i 1 := by
    have hid : IsIdempotentElem (E.symm (Pi.single i 1)) := by
      apply E.injective
      ext j
      simp only [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply]
      by_cases h : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne h]
    obtain ⟨e, he⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral
      (idempotent_isIntegral S hid)
    exact ⟨e, by change E (algebraMap S T e) = _; rw [he, E.apply_symm_apply]⟩
  choose e he using hex
  have hsum : ∑ i, e i = 1 := by
    apply hφ
    ext j
    simp [map_sum, he]
  have hex' : ∃ i, e i ∉ p := by
    by_contra! h
    have hmem := p.sum_mem (fun i (_ : i ∈ Finset.univ) => h i)
    rw [hsum] at hmem
    exact (inferInstance : p.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem p hmem isUnit_one)
  obtain ⟨i, hi⟩ := hex'
  exact ⟨e i, hi, domain_localization_of_coordinate φ hφ i (e i) (he i)⟩

/-- An étale algebra over a normal domain has domain principal neighborhoods. -/
theorem etale_exists_domain_localization
    (R S : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ e : S, e ∉ p ∧ IsDomain (Localization.Away e) := by
  let K := FractionRing R
  let T := S ⊗[R] K
  let : Algebra K T := Algebra.TensorProduct.rightAlgebra
  let E : K ⊗[R] S ≃ₐ[K] T :=
    { (Algebra.TensorProduct.comm R K S).toRingEquiv with
      commutes' x := by
        change (Algebra.TensorProduct.comm R K S) (x ⊗ₜ[R] 1) = 1 ⊗ₜ[R] x
        exact Algebra.TensorProduct.comm_tmul _ _ _ }
  let : Algebra.Etale K T := Algebra.Etale.of_equiv E
  let := Algebra.FormallyUnramified.finite_of_free K T
  let : IsArtinianRing T := IsArtinianRing.of_finite K T
  let : _root_.IsReduced T := Algebra.FormallyUnramified.isReduced_of_field K T
  let := smooth_integrallyClosedIn_genericFiber R S
  exact exists_domain_localization_of_artinian_overring S T p

/-- Every point of a smooth affine algebra over a field has an integral open
neighborhood, obtained from its actual standard étale polynomial chart. -/
theorem smooth_spec_exists_integral_neighborhood
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (p : PrimeSpectrum A) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of A)),
      IsOpenImmersion g ∧ IsIntegral Y ∧ p ∈ Set.range g := by
  obtain ⟨r, hrp, n, alg, htower, hstd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p.asIdeal)
  let := alg
  let := htower
  let := hstd
  let S := Localization.Away r
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S r]
    exact hrp
  obtain ⟨e, heq, hdomain⟩ :=
    etale_exists_domain_localization (MvPolynomial (Fin n) k) S q.asIdeal
  let := hdomain
  let T := Localization.Away e
  obtain ⟨z, hz⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S T)) := by
    rw [PrimeSpectrum.localization_away_comap_range T e]
    exact heq
  let g₁ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A S))
  let g₂ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S T))
  refine ⟨Spec (CommRingCat.of T), g₂ ≫ g₁, inferInstance, inferInstance, z, ?_⟩
  change PrimeSpectrum.comap (algebraMap A S) (PrimeSpectrum.comap (algebraMap S T) z) = p
  rw [hz, hq]

set_option backward.isDefEq.respectTransparency false in
/-- The actual structure morphism supplies integral open neighborhoods at all points. -/
theorem smooth_exists_integral_neighborhood
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
      IsOpenImmersion g ∧ IsIntegral Y ∧ x ∈ Set.range g := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  let φ : k →+* Γ(X, U) :=
    (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hφ : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.bijective)
    (f.smooth_appLE (isAffineOpen_top _) hU (by simp))
  let := φ.toAlgebra
  let : Algebra.Smooth k Γ(X, U) := hφ
  obtain ⟨Y, g, hg, hY, z, hz⟩ :=
    smooth_spec_exists_integral_neighborhood k Γ(X, U) (hU.primeIdealOf ⟨x, hxU⟩)
  let := hg
  refine ⟨Y, g ≫ hU.fromSpec, inferInstance, hY, z, ?_⟩
  rw [Scheme.Hom.comp_apply, hz]
  exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩

/-- A connected space with irreducible open neighborhoods is irreducible.
The argument requires neither quasi-compactness nor a finite component set. -/
theorem irreducibleSpace_of_connected_of_local
    {T : Type*} [TopologicalSpace T] [ConnectedSpace T]
    (h : ∀ x : T, ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    IrreducibleSpace T := by
  obtain ⟨x⟩ := (inferInstance : Nonempty T)
  obtain ⟨U, hU, hx, hUi⟩ := h x
  have hopen : IsOpen (closure U) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨V, hV, hyV, hVi⟩ := h y
    have hUV : (U ∩ V).Nonempty :=
      (closure_inter_open_nonempty_iff hV).mp ⟨y, hy, hyV⟩
    have hsub : V ⊆ closure U :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hVi.2 hU
        (Set.inter_comm U V ▸ hUV)).trans (closure_mono Set.inter_subset_right)
    exact ⟨V, hsub, hV, hyV⟩
  have heq : closure U = Set.univ :=
    (show IsClopen (closure U) from ⟨isClosed_closure, hopen⟩).eq_univ
      ⟨x, subset_closure hx⟩
  apply (irreducibleSpace_def T).mpr
  change IsIrreducible (Set.univ : Set T)
  rw [← heq]
  exact hUi.closure

/-- Domain stalks follow from the actual integral open neighborhoods. -/
theorem smooth_stalk_isDomain
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  obtain ⟨Y, g, hg, hY, y, rfl⟩ := smooth_exists_integral_neighborhood k X f x
  let := hg
  let := hY
  exact Function.Injective.isDomain (g.stalkMap y).hom
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv.injective

/-- Smooth schemes over a field are reduced, including the empty scheme. -/
theorem smooth_isReduced
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    let := smooth_stalk_isDomain k X f x
    infer_instance
  exact isReduced_of_isReduced_stalk X

/-- Connected smooth schemes over fields are integral. -/
theorem smooth_connected_isIntegral
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [ConnectedSpace X] :
    IsIntegral X := by
  let := smooth_isReduced k X f
  have : IrreducibleSpace X := irreducibleSpace_of_connected_of_local fun x => by
    obtain ⟨Y, g, hg, hY, hx⟩ := smooth_exists_integral_neighborhood k X f x
    let := hg
    let := hY
    exact ⟨Set.range g, g.isOpenEmbedding.isOpen_range, hx,
      by simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ Y).image g g.continuous.continuousOn⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- A smooth geometrically connected scheme over an arbitrary field is
geometrically integral, with all field base changes retained. -/
theorem smooth_geometrically_connected_integral :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f] [AlgebraicGeometry.GeometricallyConnected f],
      AlgebraicGeometry.GeometricallyIntegral f := by
  intro k _ X f _ _
  refine ⟨?_⟩
  intro K _ y Z fst snd H
  have : Smooth snd := MorphismProperty.of_isPullback H ‹Smooth f›
  have : ConnectedSpace Z :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) y fst snd H
  exact smooth_connected_isIntegral K Z snd

end
end ArithmeticThetaCompletedCharts
