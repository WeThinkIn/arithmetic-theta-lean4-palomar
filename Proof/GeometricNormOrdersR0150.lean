module

public import FiniteEtaleLocalNormR0150
public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaGeometricNormR0150.NormOrders
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

theorem ord_prod {R ι : Type*} [CommRing R] [IsDomain R]
    (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ring.ord_of_isUnit]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (ha i (Finset.mem_insert_self _ _))),
      ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]


/-- The determinant order is the length of its multiplication cokernel.
This applies to the finite free algebra over a target discrete valuation ring. -/
theorem ord_norm_eq_length {R S ι : Type*}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Fintype ι]
    (b : Module.Basis ι R S) (a : S) (ha : a ≠ 0) :
    Ring.ord R (Algebra.norm R a) = Module.length R (S ⧸ Ideal.span {a}) := by
  have hI : (Ideal.span {a} : Ideal S) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  rw [Ring.ord_eq_of_associated (associated_norm_prod_smith b ha),
    ord_prod _ _ (fun i _ => Ideal.smithCoeffs_ne_zero b _ hI i),
    (Ideal.quotientEquivPiSpan (Ideal.span {a}) b hI).length_eq,
    Module.length_pi_of_fintype]
  rfl

open P2MW.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton.FinSuppLen

/-- Composition factors give the weighted length formula over a semilocal
algebra. The weights are lengths over the original base ring. -/
theorem length_eq_sum_localLength (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Fintype (MaximalSpectrum S)]
    (H : Type u) [AddCommGroup H] [Module S H] (hH : IsFiniteLength S H)
    [hRH : Module R H] [hTower : IsScalarTower R S H] :
    Module.length R H = ∑ m : MaximalSpectrum S,
      Module.length R (S ⧸ m.asIdeal) * loclen m H := by
  classical
  revert hTower hRH
  induction hH with
  | @of_subsingleton H _ _ _ =>
    intro _ _
    have hzero (m : MaximalSpectrum S) :
        Subsingleton (LocalizedModule m.asIdeal.primeCompl H) := by
      exact (IsLocalizedModule.map_injective m.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap m.asIdeal.primeCompl H)
        (LocalizedModule.mkLinearMap m.asIdeal.primeCompl H)
        (0 : H →ₗ[S] H) (fun a b _ => Subsingleton.elim a b)).subsingleton
    haveI := hzero
    simp [loclen, Module.length_eq_zero]
  | @of_simple_quotient H _ _ N hs hN ih =>
    intro _ _
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hq : Module.length R (H ⧸ N) = ∑ p : MaximalSpectrum S,
        Module.length R (S ⧸ p.asIdeal) * loclen p (H ⧸ N) := by
      rw [Finset.sum_eq_single (⟨m, hm⟩ : MaximalSpectrum S)]
      · rw [loclen_eq_one_of_equiv_quotient (H ⧸ N) m hm e, mul_one]
        exact (e.restrictScalars R).length_eq
      · intro p _ hp
        rw [loclen_eq_zero_of_equiv_quotient (H ⧸ N) m hm e p hp, mul_zero]
      · simp
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars R)
      (N.mkQ.restrictScalars R) N.injective_subtype (Submodule.mkQ_surjective N)
      (LinearMap.exact_subtype_mkQ N), ih, hq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [loclen_eq_add H N m, mul_add]

/-- Local algebra formula before identifying maximal ideals with scheme points. -/
theorem ord_norm_eq_sum_localLength (R S : Type u)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Fintype (MaximalSpectrum S)] {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R S) (a : S) (ha : a ≠ 0) :
    Ring.ord R (Algebra.norm R a) = ∑ m : MaximalSpectrum S,
      Module.length R (S ⧸ m.asIdeal) *
        loclen m (S ⧸ Ideal.span {a}) := by
  have hfinite : IsFiniteLength R (S ⧸ Ideal.span {a}) := by
    rw [← Module.length_ne_top_iff, ← ord_norm_eq_length b a ha]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero
      ((Algebra.norm_ne_zero_iff_of_basis b).mpr ha))
  have hfiniteS : IsFiniteLength S (S ⧸ Ideal.span {a}) := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfinite ⊢
    exact hfinite.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [ord_norm_eq_length b a ha]
  exact length_eq_sum_localLength R S _ hfiniteS

section LocalizedFiber
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    [Algebra.IsIntegral R S] [Algebra.IsIntegral A B]
    (p : Ideal R) [p.IsMaximal] [IsLocalization.AtPrime A p] [IsLocalRing A]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) B]

/-- The semilocal maximal ideals are precisely the original primes above p.
This uses the given scalar maps and the actual localization homomorphism. -/
def localizedMaximalEquiv : p.primesOver S ≃ MaximalSpectrum B where
  toFun Q := by
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver p := Q.property.2
    haveI : (Q.val.map (algebraMap S B)).IsPrime :=
      IsLocalization.AtPrime.isPrime_map_of_liesOver S p B Q.val
    haveI : (Q.val.map (algebraMap S B)).LiesOver (IsLocalRing.maximalIdeal A) :=
      IsLocalization.AtPrime.liesOver_map_of_liesOver p A B Q.val
    haveI : ((Q.val.map (algebraMap S B)).under A).IsMaximal := by
      rw [← Ideal.over_def _ (IsLocalRing.maximalIdeal A)]
      infer_instance
    exact ⟨Q.val.map (algebraMap S B),
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _ inferInstance⟩
  invFun m := by
    haveI : m.asIdeal.IsMaximal := m.isMaximal
    have hm : m.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := by
      refine ⟨?_⟩
      exact (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m.asIdeal)).symm
    letI := hm
    exact ⟨m.asIdeal.under S, inferInstance,
      IsLocalization.AtPrime.liesOver_comap_of_liesOver p A m.asIdeal⟩
  left_inv Q := by
    apply Subtype.ext
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver p := Q.property.2
    haveI : (Q.val.under R).IsMaximal := by
      rw [← Ideal.over_def Q.val p]
      infer_instance
    haveI : Q.val.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) _ inferInstance
    exact IsLocalization.AtPrime.under_map_of_isMaximal S p B Q.val
  right_inv m := by
    apply MaximalSpectrum.ext
    exact IsLocalization.map_under (Algebra.algebraMapSubmonoid S p.primeCompl) B m.asIdeal

end LocalizedFiber

theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord R a = Ring.ord S (e a) := by
  have hi : (Ideal.span {e a}).comap e.toRingHom = Ideal.span {a} := by
    simpa only [Ideal.map_span, Set.image_singleton, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] using
      (Ideal.comap_map_of_bijective e.toRingHom e.bijective (I := Ideal.span {a}))
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient, ← hi]
  exact Ideal.coheight_comap_of_surjective e.toRingHom e.surjective _

/-- The quotient length at a prime can be computed in any actual localization
model, in particular in the stalk supplied by an affine chart. -/
theorem localLength_span_eq_ord {S C : Type u} [CommRing S] [CommRing C]
    [Algebra S C] (m : MaximalSpectrum S) [IsLocalization.AtPrime C m.asIdeal] (a : S) :
    loclen m (S ⧸ Ideal.span {a}) = Ring.ord C (algebraMap S C a) := by
  rw [loclen_of_equiv_quotient (S ⧸ Ideal.span {a}) (Ideal.span {a})
    (LinearEquiv.refl _ _) m, Ideal.map_span, Set.image_singleton]
  exact (ord_ringEquiv (Localization.algEquiv m.asIdeal.primeCompl C).toRingEquiv
    (algebraMap S (Localization.AtPrime m.asIdeal) a)).trans
      (congrArg (Ring.ord C) ((Localization.algEquiv m.asIdeal.primeCompl C).commutes a))

/-- Localizing the semilocal algebra once more gives the original source stalk. -/
theorem localLength_span_twice {S B C : Type u}
    [CommRing S] [CommRing B] [CommRing C] [Algebra S B] [Algebra S C]
    (M : Submonoid S) [IsLocalization M B]
    (Q : MaximalSpectrum S) (m : MaximalSpectrum B)
    (hm : m.asIdeal.under S = Q.asIdeal) [IsLocalization.AtPrime C Q.asIdeal] (a : S) :
    loclen m (B ⧸ Ideal.span {algebraMap S B a}) = Ring.ord C (algebraMap S C a) := by
  let D := Localization.AtPrime m.asIdeal
  haveI : IsLocalization.AtPrime D Q.asIdeal := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M D m.asIdeal
    simpa only [← Ideal.under_def, hm] using h
  rw [localLength_span_eq_ord (C := D)]
  rw [← IsScalarTower.algebraMap_apply S B D]
  exact (ord_ringEquiv (IsLocalization.algEquiv Q.asIdeal.primeCompl D C).toRingEquiv
    (algebraMap S D a)).trans
      (congrArg (Ring.ord C) ((IsLocalization.algEquiv Q.asIdeal.primeCompl D C).commutes a))

theorem residue_length_eq_inertia {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing A] (m : MaximalSpectrum B)
    [m.asIdeal.LiesOver (IsLocalRing.maximalIdeal A)] :
    (Module.length A (B ⧸ m.asIdeal)).toNat = m.asIdeal.inertiaDeg A := by
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A)]
  rw [Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A)),
    Module.length_eq_rank]
  rfl

/-- Residue weights are unchanged by passage to the semilocal model. -/
theorem localized_residue_weight {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    [Algebra.IsIntegral R S] [Algebra.IsIntegral A B]
    (p : Ideal R) [p.IsMaximal] [IsLocalization.AtPrime A p] [IsLocalRing A]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) B]
    (Q : p.primesOver S) :
    (Module.length A (B ⧸ (localizedMaximalEquiv (A := A) (B := B) p Q).asIdeal)).toNat =
      Q.val.inertiaDeg R := by
  letI : Q.val.IsPrime := Q.property.1
  letI : Q.val.LiesOver p := Q.property.2
  letI : Q.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q.val p
  let m := localizedMaximalEquiv (A := A) (B := B) p Q
  haveI : m.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver p A B Q.val
  rw [residue_length_eq_inertia m, ← Ideal.inertiaDeg'_eq_inertiaDeg
    (IsLocalRing.maximalIdeal A) m.asIdeal]
  haveI : (Q.val.map (algebraMap S B)).LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver p A B Q.val
  exact (IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg p A B Q.val).trans
    (Ideal.inertiaDeg'_eq_inertiaDeg p Q.val)

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem smooth_coheight_le_one (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p] (x : X) :
    Order.coheight x ≤ 1 := by
  have hdim := SmoothOfRelativeDimension.topologicalKrullDim_le p 1
  have he : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  exact WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans (he ▸ hdim))

theorem smooth_coheight_one_of_ne_generic (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (x : X) (hx : x ≠ genericPoint X) : Order.coheight x = 1 := by
  rcases Order.le_one_iff.mp (smooth_coheight_le_one F p x) with hz | h
  · have hm := Order.coheight_eq_zero.mp hz
    have h : genericPoint X ≤ x := hm (show x ≤ (⊤ : X) from le_top)
    exact False.elim (hx (Specializes.antisymm h (genericPoint_specializes x)).eq)
  · exact h

theorem smooth_closed_of_ne_generic (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  have hco := smooth_coheight_one_of_ne_generic F p x hx
  apply isClosed_of_closure_subset
  intro z hz
  have hzx : z ≤ x := specializes_iff_mem_closure.mpr hz
  have heq : z = x := by
    by_contra hne
    have hstrict : z < x := ⟨hzx, fun hxz => hne (Specializes.antisymm hxz hzx).eq⟩
    have hlt := Order.coheight_strictAnti hstrict
      (show Order.coheight x < ⊤ by rw [hco]; exact ENat.one_lt_top)
    rw [hco] at hlt
    exact (not_lt_of_ge (smooth_coheight_le_one F p z)) hlt
  exact Set.mem_singleton_iff.mpr heq

theorem smooth_stalk_pid (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (x : X) (hx : Order.coheight x = 1) : IsPrincipalIdealRing (X.presheaf.stalk x) := by
  letI := Smooth.isRegularLocalRing_stalk (f := p) x
  have hspan : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank = 1 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal.trans
      ((ringKrullDim_stalk_eq_coheight x).trans (congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hx)))
  have hp := ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank_eq_one_iff.mp hspan).1
  exact (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 5 1 |>.mp hp

/-- On a nonzero affine section, scheme order is the local principal quotient length. -/
theorem section_order [IsLocallyNoetherian X] (U : X.Opens) [Nonempty U] (x : X) (hx : x ∈ U)
    (hco : Order.coheight x = 1) (a : Γ(X, U)) (ha : a ≠ 0) :
    Scheme.ord (X.germToFunctionField U a) x =
      ((Ring.ord (X.presheaf.stalk x) (X.presheaf.germ U x hx a)).toNat : ℤ) := by
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx a]
  exact ArithmeticThetaCurveDegree.principalOrder_stalk_eq_length X x hco _
    ((map_ne_zero_iff _ (germ_injective_of_isIntegral X x hx)).mpr ha)

/-- The integer version retains the residue weights and permits direct
comparison with `Scheme.ord`. Finiteness is proved before applying `toNat`. -/
theorem int_ord_norm_eq_sum_localLength (R S : Type u)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Fintype (MaximalSpectrum S)] {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R S) (a : S) (ha : a ≠ 0) :
    ((Ring.ord R (Algebra.norm R a)).toNat : ℤ) = ∑ m : MaximalSpectrum S,
      ((Module.length R (S ⧸ m.asIdeal)).toNat : ℤ) *
        ((loclen m (S ⧸ Ideal.span {a})).toNat : ℤ) := by
  have h := ord_norm_eq_sum_localLength R S b a ha
  have hn : Ring.ord R (Algebra.norm R a) ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero
      ((Algebra.norm_ne_zero_iff_of_basis b).mpr ha))
  rw [h] at hn ⊢
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hn), Nat.cast_sum]
  simp only [ENat.toNat_mul, Nat.cast_mul]

theorem ord_generic [IsLocallyNoetherian X] (g : X.functionField) :
    Scheme.ord g (genericPoint X) = 0 := by
  apply Scheme.ord_eq_zero_of_coheight_neq_one
  change Order.coheight (⊤ : X) ≠ 1
  simp

theorem map_generic (f : X ⟶ Y) [Surjective f] :
    f (genericPoint X) = genericPoint Y := by
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  have h : f (genericPoint X) ⤳ genericPoint Y :=
    hx ▸ (genericPoint_specializes x).map f.continuous
  exact (h.antisymm (genericPoint_specializes _)).eq

theorem eq_generic_of_map_eq_generic (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (x : X) (hx : f x = genericPoint Y) : x = genericPoint X := by
  exact ((f.isDiscrete_preimage_singleton (genericPoint Y)).eq_of_specializes
    (genericPoint_specializes x) (map_generic f) hx).symm

theorem norm_order_generic [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (φ : Y.functionField →+* X.functionField) (g : X.functionField) :
    Scheme.ord (fieldNorm φ g) (genericPoint Y) = pushOrder f g (genericPoint Y) := by
  rw [ord_generic]
  symm
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  rw [eq_generic_of_map_eq_generic f x.val x.property, ord_generic, mul_zero]

theorem fieldNorm_ne_zero (f : X ⟶ Y) [IsFinite f] [Etale f] [Surjective f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    {g : X.functionField} (hg : g ≠ 0) : fieldNorm φ g ≠ 0 := by
  letI := φ.toAlgebra
  letI : FiniteDimensional Y.functionField X.functionField :=
    (finite_etale_local_norm X Y f φ hφ).1
  exact Algebra.norm_ne_zero_iff.mpr hg

theorem fieldNorm_mul (φ : Y.functionField →+* X.functionField)
    (g h : X.functionField) : fieldNorm φ (g * h) = fieldNorm φ g * fieldNorm φ h := by
  letI := φ.toAlgebra
  exact map_mul (Algebra.norm Y.functionField) g h

/-- The residue-length weight is exactly the degree of the actual residue map.
Both scalar actions here are induced by the specified stalk map. -/
theorem stalk_residue_length (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    (Module.length (Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).toNat = f.residueDegree x := by
  letI := (f.stalkMap x).hom.toAlgebra
  letI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    (inferInstance : IsLocalHom (f.stalkMap x).hom)
  rw [Module.length_eq_of_surjective (IsLocalRing.residue_surjective
    (R := Y.presheaf.stalk (f x))), Module.length_eq_rank]
  change Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) = _
  have hA : (inferInstance : Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))) =
      (f.residueFieldMap x).hom.toAlgebra := by
    apply Algebra.algebra_ext
    intro a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    rfl
  dsimp only [Scheme.Hom.residueDegree]
  rw [← hA]
  rfl

theorem pushOrder_mul [IsLocallyNoetherian X]
    (f : X ⟶ Y) [IsFinite f] {g h : X.functionField}
    (hg : g ≠ 0) (hh : h ≠ 0) (y : Y) :
    pushOrder f (g * h) y = pushOrder f g y + pushOrder f h y := by
  classical
  letI : Finite {x : X // f x = y} := (f.finite_preimage_singleton y).to_subtype
  unfold pushOrder
  simp_rw [Scheme.ord_mul hg hh, mul_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

/-- A norm-order identity on nonzero regular sections extends to every nonzero
rational function, using the actual affine section embedding. -/
theorem of_affine_sections [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f] [Surjective f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty (f ⁻¹ᵁ U)] (y : Y)
    (hsections : ∀ a : Γ(X, f ⁻¹ᵁ U), a ≠ 0 →
      Scheme.ord (fieldNorm φ (X.germToFunctionField (f ⁻¹ᵁ U) a)) y =
        pushOrder f (X.germToFunctionField (f ⁻¹ᵁ U) a) y)
    (g : X.functionField) (hg : g ≠ 0) :
    Scheme.ord (fieldNorm φ g) y = pushOrder f g y := by
  let V := f ⁻¹ᵁ U
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V (hU.preimage f)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, V)) g
  have hb : (b : Γ(X, V)) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbF : X.germToFunctionField V (b : Γ(X, V)) ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr hb
  change g * X.germToFunctionField V (b : Γ(X, V)) = X.germToFunctionField V a at hab
  have haF : X.germToFunctionField V a ≠ 0 := hab ▸ mul_ne_zero hg hbF
  have ha : a ≠ 0 := fun h => haF (by rw [h, map_zero])
  have h := hsections a ha
  rw [← hab, fieldNorm_mul, Scheme.ord_mul (fieldNorm_ne_zero f φ hφ hg)
    (fieldNorm_ne_zero f φ hφ hbF), pushOrder_mul f hg hbF, hsections b hb] at h
  exact add_right_cancel h

/-- The local norm formula on an affine free chart, at a nongeneric point. -/
theorem affine_section_norm_order [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (F : Type u) [Field F]
    (p : X ⟶ Spec (CommRingCat.of F)) (q : Y ⟶ Spec (CommRingCat.of F))
    [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension 1 q]
    (f : X ⟶ Y) [IsFinite f] [Etale f] [Surjective f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (hfree : AffineFree f U) (hnorm : NormOnOpen f φ U)
    (y : Y) (hy : y ∈ U) (hyng : y ≠ genericPoint Y)
    (a : Γ(X, f ⁻¹ᵁ U)) (ha : a ≠ 0) :
    Scheme.ord (fieldNorm φ (X.germToFunctionField (f ⁻¹ᵁ U) a)) y =
      pushOrder f (X.germToFunctionField (f ⁻¹ᵁ U) a) y := by
  classical
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let A := Y.presheaf.stalk y
  have hV := hU.preimage f
  letI := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := f.finite_app U hU
  letI : Module.Free R S := hfree
  letI := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  let P := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩
    (smooth_closed_of_ne_generic F q y hyng)
  letI : IsLocalization.AtPrime A P := hU.isLocalization_stalk ⟨y, hy⟩
  letI : IsPrincipalIdealRing A := smooth_stalk_pid F q y
    (smooth_coheight_one_of_ne_generic F q y hyng)
  have hinj : Function.Injective (algebraMap R S) := by
    intro a b hab
    apply Y.germToFunctionField_injective U
    apply φ.injective
    have he := DFunLike.congr_fun (LocalNorm.section_field_square f φ hφ U hU)
    exact (he a).symm.trans ((congrArg (X.germToFunctionField _) hab).trans (he b))
  let M := Algebra.algebraMapSubmonoid S P.primeCompl
  let B := Localization M
  have hM : M ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective _ hinj P.primeCompl_le_nonZeroDivisors
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  letI : Algebra A B := localizationAlgebra P.primeCompl S
  letI : IsScalarTower R A B := isScalarTower_localizationAlgebra P.primeCompl S
  letI : Module.Finite A B := Module.Finite.of_isLocalization R S P.primeCompl
  let e₁ := Equiv.ofBijective
    (ArithmeticThetaDegreeAssembly.affineFiberPrime f U hU hV y hy)
    (ArithmeticThetaDegreeAssembly.affineFiberPrime_bijective f U hU hV y hy)
  let e₂ := localizedMaximalEquiv (S := S) (A := A) (B := B) P
  let e := e₁.trans e₂
  letI : Finite {x : X // f x = y} := (f.finite_preimage_singleton y).to_subtype
  letI : Fintype {x : X // f x = y} := Fintype.ofFinite _
  letI : Finite (MaximalSpectrum B) := Finite.of_equiv _ e
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let b := (Module.Free.chooseBasis R S).localizationLocalization A P.primeCompl B
  have haB : algebraMap S B a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective B hM)).mpr ha
  have hsum := int_ord_norm_eq_sum_localLength A B b (algebraMap S B a) haB
  rw [Algebra.norm_localization R P.primeCompl a] at hsum
  have hanorm : affineNorm f U a ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (Module.Free.chooseBasis R S)).mpr ha
  rw [← hnorm a, section_order U y hy (smooth_coheight_one_of_ne_generic F q y hyng)
    (affineNorm f U a) hanorm]
  change ((Ring.ord A (algebraMap R A (Algebra.norm R a))).toNat : ℤ) = _
  rw [hsum, ← finsum_eq_sum_of_fintype, ← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  have hxU : f x.val ∈ U := by rw [x.property]; exact hy
  have hxng : x.val ≠ genericPoint X := by
    intro hx
    exact hyng (x.property.symm.trans (hx ▸ map_generic f))
  let Q := (hV.primeIdealOf ⟨x.val, hxU⟩).asIdeal
  have heQ : (e₁ x).val = Q := rfl
  letI : Q.LiesOver P := heQ ▸ (e₁ x).property.2
  letI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q P
  haveI : (hU.primeIdealOf ⟨f x.val, hxU⟩).asIdeal.IsMaximal := by
    simpa only [x.property] using (inferInstance : P.IsMaximal)
  have hw : (Module.length A (B ⧸ (e x).asIdeal)).toNat = f.residueDegree x.val := by
    exact (localized_residue_weight (A := A) (B := B) P (e₁ x)).trans
      (ArithmeticThetaDegreeAssembly.residueDegree_eq_affine_inertia f U hU hV x.val hxU).symm
  have hl : loclen (e x) (B ⧸ Ideal.span {algebraMap S B a}) =
      Ring.ord (X.presheaf.stalk x.val) (X.presheaf.germ (f ⁻¹ᵁ U) x.val hxU a) := by
    letI := X.presheaf.algebra_section_stalk (⟨x.val, hxU⟩ : f ⁻¹ᵁ U)
    letI := hV.isLocalization_stalk ⟨x.val, hxU⟩
    apply localLength_span_twice M (⟨Q, inferInstance⟩ : MaximalSpectrum S) (e x)
    exact IsLocalization.AtPrime.under_map_of_isMaximal S P B Q
  rw [hw, hl, section_order (f ⁻¹ᵁ U) x.val hxU
    (smooth_coheight_one_of_ne_generic F p x.val hxng) a ha]

end ArithmeticThetaGeometricNormR0150.NormOrders

#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.ord_norm_eq_length
#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.length_eq_sum_localLength
#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.int_ord_norm_eq_sum_localLength
#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.norm_order_generic
#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.stalk_residue_length
#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.of_affine_sections

namespace ArithmeticThetaGeometricNormR0150
open CategoryTheory AlgebraicGeometry

/-- The actual function-field norm pushes forward principal orders at every
scheme point, including nonsplit closed points and the generic point. -/
theorem geometric_norm_orders :
    ∀ (F : Type u) [Field F] (X Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y] (p : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of F))) (q : Quiver.Hom Y (AlgebraicGeometry.Spec (CommRingCat.of F))) [AlgebraicGeometry.IsProper p] [AlgebraicGeometry.IsProper q] [AlgebraicGeometry.SmoothOfRelativeDimension 1 p] [AlgebraicGeometry.SmoothOfRelativeDimension 1 q] (f : Quiver.Hom X Y), CategoryTheory.CategoryStruct.comp f q = p → ∀ [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Surjective f] (φ : Y.functionField →+* X.functionField), ArithmeticThetaGeometricNormR0150.IsFieldMap f φ → ∀ (g : X.functionField), g ≠ 0 → ∀ y : Y, AlgebraicGeometry.Scheme.ord (ArithmeticThetaGeometricNormR0150.fieldNorm φ g) y = ArithmeticThetaGeometricNormR0150.pushOrder f g y := by
  intro F _ X Y _ _ _ _ p q _ _ _ _ f hf _ _ _ φ hφ g hg y
  by_cases hyng : y = genericPoint Y
  · subst y
    exact NormOrders.norm_order_generic f φ g
  · obtain ⟨U, hy, hU, hfree, hnorm⟩ := (finite_etale_local_norm X Y f φ hφ).2.2 y
    letI : Nonempty U := ⟨⟨y, hy⟩⟩
    obtain ⟨x, hx⟩ := f.surjective y
    letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by change f x ∈ U; rwa [hx]⟩⟩
    exact NormOrders.of_affine_sections f φ hφ U hU y
      (NormOrders.affine_section_norm_order F p q f φ hφ U hU hfree hnorm y hy hyng) g hg

end ArithmeticThetaGeometricNormR0150

#print axioms ArithmeticThetaGeometricNormR0150.NormOrders.affine_section_norm_order
#print axioms ArithmeticThetaGeometricNormR0150.geometric_norm_orders
