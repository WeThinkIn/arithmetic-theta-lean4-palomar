module

public import Mathlib

@[expose] public section

/-!
# Selected components of finite etale covers

The auxiliary generic-fibre, component, and rank arguments below adapt candidate
proofs from the local FLT library (see FormalizationMapping.md). They are defined
and compiled in this module: no candidate theorem or unproved interface is imported.
The only import is Mathlib. All algebra structures in the scheme bridges are
induced by the displayed appLE and section-to-stalk maps.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
universe u
noncomputable section
namespace ArithmeticThetaGlobalization
namespace SelectedComponent

namespace EtaleLocNormalAux

theorem isIntegral_of_isIdempotentElem {T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral T e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    map_one, mul_sub, mul_one, he.eq, sub_self]

section Core
variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable (S : Type u) [CommRing S] [Algebra R S]

theorem tensorMap_integralClosure_mem_bot (y : S ⊗[R] (integralClosure R K)) :
    (Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R K).val) y
      ∈ (⊥ : Subalgebra S (S ⊗[R] K)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s k =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((mem_integralClosure_iff R K).mp k.2)
    rw [Algebra.TensorProduct.map_tmul, Algebra.mem_bot]
    refine ⟨r • s, ?_⟩
    calc algebraMap S (S ⊗[R] K) (r • s)
        = (r • s) ⊗ₜ[R] (1 : K) := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
            RingHom.id_apply]
      _ = s ⊗ₜ[R] (r • (1 : K)) := TensorProduct.smul_tmul r s 1
      _ = s ⊗ₜ[R] (algebraMap R K r) := by rw [Algebra.algebraMap_eq_smul_one]
      _ = (AlgHom.id S S) s ⊗ₜ[R] ((integralClosure R K).val k) := by rw [hr]; simp
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb

theorem smooth_integrallyClosed_in_genericFibre [Algebra.Smooth R S] :
    integralClosure S (S ⊗[R] K) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, hy⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).2 ⟨x, hx⟩
  have hy' : (Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R K).val) y = x := by
    have h := congrArg Subtype.val hy
    simpa only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict] using h
  rw [← hy']
  exact tensorMap_integralClosure_mem_bot R K S y

theorem exists_algebraMap_eq_of_isIntegral_genericFibre [Algebra.Smooth R S]
    {x : S ⊗[R] K} (hx : IsIntegral S x) : ∃ s : S, algebraMap S (S ⊗[R] K) s = x := by
  have hmem : x ∈ integralClosure S (S ⊗[R] K) := (mem_integralClosure_iff S (S ⊗[R] K)).mpr hx
  rw [smooth_integrallyClosed_in_genericFibre R K S, Algebra.mem_bot] at hmem
  exact hmem

theorem algebraMap_genericFibre_injective [Module.Flat R S] :
    Function.Injective (algebraMap S (S ⊗[R] K)) := by
  have h := Algebra.TensorProduct.includeLeft_injective (S := S) (A := S) (B := K)
    (IsFractionRing.injective R K)
  intro a b hab
  apply h
  simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.algebraMap_apply] using hab

end Core

end EtaleLocNormalAux

open EtaleLocNormalAux in
theorem etale_local_domain
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type u) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type u) [CommRing A_q] [Algebra A A_q] [IsLocalization.AtPrime A_q q] :
    IsDomain A_q := by
  classical
  have hq : q.IsPrime := inferInstance
  let L := FractionRing P
  let B₀ := A ⊗[P] L

  obtain ⟨I, hI, F, hF, hFalg, e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod L (L ⊗[P] A)).mp inferInstance
  haveI : Fintype I := Fintype.ofFinite I
  let e₀ : B₀ ≃+* (Π j, F j) := (Algebra.TensorProduct.comm P A L).toRingEquiv.trans e.toRingEquiv

  let θ : A →+* (Π j, F j) := e₀.toRingHom.comp (algebraMap A B₀)
  have hθ : ∀ a, θ a = e₀ (algebraMap A B₀ a) := fun a => rfl
  have hinj : Function.Injective (algebraMap A B₀) := algebraMap_genericFibre_injective P L A
  have hθinj : Function.Injective θ := e₀.injective.comp hinj
  have hIC : ∀ y : B₀, IsIntegral A y → ∃ a, algebraMap A B₀ a = y :=
    fun y hy => exists_algebraMap_eq_of_isIntegral_genericFibre P L A hy

  have hε : ∀ j : I, ∃ ε : A, θ ε = Pi.single j 1 := by
    intro j
    have hid : IsIdempotentElem (e₀.symm (Pi.single j 1) : B₀) := by
      have : IsIdempotentElem (Pi.single j (1 : F j) : Π j, F j) := by
        simp [IsIdempotentElem, ← Pi.single_mul]
      simpa [IsIdempotentElem, map_mul] using congrArg e₀.symm this.eq
    obtain ⟨a, ha⟩ := hIC _ (isIntegral_of_isIdempotentElem hid)
    exact ⟨a, by rw [hθ, ha, RingEquiv.apply_symm_apply]⟩
  choose ε hε using hε

  have hsum : ∑ j, ε j = 1 := by
    apply hθinj
    rw [map_sum, map_one]
    simp only [hε]
    exact Finset.univ_sum_single (1 : Π j, F j) ▸ by simp
  obtain ⟨i, hi⟩ : ∃ i, ε i ∉ q := by
    by_contra h
    push Not at h
    have : (1 : A) ∈ q := hsum ▸ q.sum_mem fun j _ => h j
    exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr this)

  let ρ : A →+* F i := (Pi.evalRingHom F i).comp θ
  have hρ : ∀ a, ρ a = θ a i := fun a => rfl
  have hρε : ∀ a, θ (a * ε i) = Pi.single i (ρ a) := by
    intro a
    rw [map_mul, hε]
    ext j
    by_cases hj : j = i
    · subst hj; simp [hρ]
    · simp [hj]
  have hker : ∀ a, ρ a = 0 → a * ε i = 0 := by
    intro a ha
    apply hθinj
    rw [hρε, ha, Pi.single_zero, map_zero]
  have hunit : ∀ s : q.primeCompl, IsUnit (ρ s) := by
    intro s
    rw [isUnit_iff_ne_zero]
    intro h0
    have := hker s h0
    rcases hq.mem_or_mem (this ▸ q.zero_mem : (s : A) * ε i ∈ q) with h | h
    · exact s.2 h
    · exact hi h

  let ρ' : A_q →+* F i := IsLocalization.lift (M := q.primeCompl) hunit
  have hρ' : ∀ a, ρ' (algebraMap A A_q a) = ρ a := fun a => IsLocalization.lift_eq hunit a
  have hρ'inj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    rw [IsLocalization.lift_mk'] at hx
    have ha : ρ a = 0 := by simpa using hx
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨ε i, hi⟩, by simpa [mul_comm] using hker a ha⟩
  exact Function.Injective.isDomain ρ' hρ'inj

namespace FltWs29
namespace C2
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem eq_irreducibleComponent_of_mem {X : Scheme.{u}} {x : X} (hx : IsDomain (X.presheaf.stalk x))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hxZ : x ∈ Z) : Z = irreducibleComponent x := by
  have hZ' := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  obtain ⟨ξ', hξ'⟩ := QuasiSober.sober hZ'.1 isClosed_irreducibleComponent
  have h1 : ξ ⤳ x := hξ.specializes hxZ
  have h2 : ξ' ⤳ x := hξ'.specializes mem_irreducibleComponent
  have hr : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} := Scheme.range_fromSpecStalk
  obtain ⟨p, hp⟩ : ξ ∈ Set.range (X.fromSpecStalk x).base := by rw [hr]; exact h1
  obtain ⟨p', hp'⟩ : ξ' ∈ Set.range (X.fromSpecStalk x).base := by rw [hr]; exact h2
  haveI : IsDomain (X.presheaf.stalk x) := hx
  set g : X := (X.fromSpecStalk x).base (genericPoint (Spec (X.presheaf.stalk x))) with hg
  have hc : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hg1 : g ⤳ ξ := hp ▸ (genericPoint_specializes p).map hc
  have hg2 : g ⤳ ξ' := hp' ▸ (genericPoint_specializes p').map hc
  have hcl : IsIrreducible (closure ({g} : Set X)) := isIrreducible_singleton.closure
  have hsub : Z ⊆ closure {g} := by
    rw [← hξ.def]; exact specializes_iff_closure_subset.mp hg1
  have hsub' : irreducibleComponent x ⊆ closure {g} := by
    rw [← hξ'.def]; exact specializes_iff_closure_subset.mp hg2
  have e1 : closure {g} = Z := Set.Subset.antisymm (hZ.2 hcl hsub) hsub
  have e2 : closure {g} = irreducibleComponent x := Set.Subset.antisymm (hZ'.2 hcl hsub') hsub'
  exact e1.symm.trans e2

theorem exists_open_subset_irreducibleComponent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (z : X) :
    ∃ O : Set X, IsOpen O ∧ z ∈ O ∧ O ⊆ irreducibleComponent z := by

  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩

  let φ : ↥(Spec Γ(X, U)) → (U : Set X) := fun q => ⟨hU.fromSpec.base q, by
    have : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at this⟩
  have hφc : Continuous φ := hU.fromSpec.continuous.subtype_mk _
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have : y ∈ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hy
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, rfl⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_surjective φ hφc hφs

  set z' : (U : Set X) := ⟨z, hzU⟩
  set F : Set (U : Set X) := ⋃ C ∈ {C ∈ irreducibleComponents (U : Set X) | z' ∉ C}, C with hF
  have hFfin : {C ∈ irreducibleComponents (U : Set X) | z' ∉ C}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
  have hFcl : IsClosed F := hFfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hzF : z' ∉ F := by
    simp only [hF, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, and_imp]
    exact fun C _ hzC hzC' => hzC hzC'
  refine ⟨Subtype.val '' Fᶜ, U.isOpen.isOpenMap_subtype_val _ hFcl.isOpen_compl, ⟨z', hzF, rfl⟩, ?_⟩
  rintro _ ⟨y, hyF, rfl⟩

  have hC := irreducibleComponent_mem_irreducibleComponents y
  have hzC : z' ∈ irreducibleComponent y := by
    by_contra h
    exact hyF (Set.mem_biUnion (x := irreducibleComponent y) ⟨hC, h⟩ mem_irreducibleComponent)

  have hS : IsIrreducible (Subtype.val '' irreducibleComponent y : Set X) :=
    hC.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨W, hWpre, hSW, hWmax⟩ := exists_preirreducible _ hS.2
  have hWirr : IsIrreducible W := ⟨⟨z, hSW ⟨z', hzC, rfl⟩⟩, hWpre⟩
  have hWcomp : W ∈ irreducibleComponents X :=
    ⟨hWirr, fun u hu hWu => (hWmax u hu.2 hWu).le⟩
  have hWeq : W = irreducibleComponent z := eq_irreducibleComponent_of_mem (hX z) hWcomp (hSW ⟨z', hzC, rfl⟩)
  rw [← hWeq]
  exact hSW ⟨y, mem_irreducibleComponent, rfl⟩

theorem main {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    IsOpen (irreducibleComponent x) ∧ ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x := by
  refine ⟨?_, fun Z hZ hxZ => eq_irreducibleComponent_of_mem (hX x) hZ hxZ⟩
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  have hzx : irreducibleComponent x = irreducibleComponent z :=
    eq_irreducibleComponent_of_mem (hX z) (irreducibleComponent_mem_irreducibleComponents x) hz
  obtain ⟨O, hO, hzO, hOsub⟩ := exists_open_subset_irreducibleComponent hX z
  exact ⟨O, hzx ▸ hOsub, hO, hzO⟩

end FltWs29.C2

namespace E160RC

open TopologicalSpace Opposite

theorem finrank_add_of_bijective_prod {R A A₁ A₂ : Type*} [CommRing R] [CommRing A]
    [CommRing A₁] [CommRing A₂] (φ : R →+* A) (r₁ : A →+* A₁) (r₂ : A →+* A₂)
    (hbij : Function.Bijective (RingHom.prod r₁ r₂))
    (h₁fin : (r₁.comp φ).Finite) (h₁flat : (r₁.comp φ).Flat)
    (h₂fin : (r₂.comp φ).Finite) (h₂flat : (r₂.comp φ).Flat) (x : PrimeSpectrum R) :
    (r₁.comp φ).finrank x + (r₂.comp φ).finrank x = φ.finrank x := by
  letI iA : Algebra R A := φ.toAlgebra
  letI i₁ : Algebra R A₁ := (r₁.comp φ).toAlgebra
  letI i₂ : Algebra R A₂ := (r₂.comp φ).toAlgebra
  haveI : Module.Finite R A₁ := h₁fin
  haveI : Module.Flat R A₁ := h₁flat
  haveI : Module.Finite R A₂ := h₂fin
  haveI : Module.Flat R A₂ := h₂flat
  let e : A ≃ₗ[R] A₁ × A₂ :=
    { toFun := fun a => (r₁ a, r₂ a)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        ext
        · change r₁ (φ c * a) = (r₁.comp φ) c * r₁ a
          rw [map_mul]; rfl
        · change r₂ (φ c * a) = (r₂.comp φ) c * r₂ a
          rw [map_mul]; rfl
      invFun := fun p => (Equiv.ofBijective _ hbij).symm p
      left_inv := fun a => (Equiv.ofBijective _ hbij).left_inv a
      right_inv := fun p => (Equiv.ofBijective _ hbij).right_inv p }
  change Module.rankAtStalk A₁ x + Module.rankAtStalk A₂ x = Module.rankAtStalk A x
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  rfl

theorem bijective_restrict_prod {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) :
    Function.Bijective (RingHom.prod (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) := by
  have hnot : ∀ x : X, x ∉ U ⊓ V := by
    intro x hx; rw [hdisj] at hx; exact hx
  constructor
  · intro a b hab
    have h1 : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op b :=
      congrArg Prod.fst hab
    have h2 : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op b :=
      congrArg Prod.snd hab
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ a b
    intro x hx
    have hx' : x ∈ U ⊔ V := by rw [hUV]; trivial
    rcases hx' with hU | hV
    · have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x hU a
      have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x hU b
      change X.presheaf.germ ⊤ x _ a = X.presheaf.germ ⊤ x _ b
      rw [← ha, ← hb, h1]
    · have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) x hV a
      have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) x hV b
      change X.presheaf.germ ⊤ x _ a = X.presheaf.germ ⊤ x _ b
      rw [← ha, ← hb, h2]
  · rintro ⟨b, c⟩
    let p : RingHom.eqLocus
        (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom
          (RingHom.fst (X.sheaf.obj.obj <| op U) (X.sheaf.obj.obj <| op V)))
        (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom
          (RingHom.snd (X.sheaf.obj.obj <| op U) (X.sheaf.obj.obj <| op V))) :=
      ⟨(b, c), TopCat.Presheaf.section_ext X.sheaf (U ⊓ V) _ _ (fun x hx => absurd hx (hnot x))⟩
    let s : X.presheaf.obj (op (U ⊔ V)) := (X.sheaf.objSupIsoProdEqLocus U V).inv p
    have hsU : X.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op s = b :=
      TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U V p
    have hsV : X.presheaf.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op s = c :=
      TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U V p
    have htop : (⊤ : X.Opens) ≤ U ⊔ V := hUV.symm.le
    refine ⟨X.presheaf.map (homOfLE htop).op s, ?_⟩
    ext
    · change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (X.presheaf.map (homOfLE htop).op s) = b
      rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have : homOfLE (le_top : U ≤ ⊤) ≫ homOfLE htop = homOfLE (le_sup_left : U ≤ U ⊔ V) :=
        Subsingleton.elim _ _
      rw [this, hsU]
    · change X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (X.presheaf.map (homOfLE htop).op s) = c
      rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have : homOfLE (le_top : V ≤ ⊤) ≫ homOfLE htop = homOfLE (le_sup_right : V ≤ U ⊔ V) :=
        Subsingleton.elim _ _
      rw [this, hsV]

theorem finrank_eq_finrank_appTop {R : CommRingCat.{u}} {Z : Scheme.{u}} [IsAffine Z]
    (k : Z ⟶ Spec R) [IsFinite k] [Flat k] (x : Spec R) :
    k.finrank x = ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.finrank x := by
  have hk : k = Z.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop) := by
    rw [Spec.map_comp, ← Category.assoc]
    change k = (Z.toSpecΓ ≫ Spec.map k.appTop) ≫ Spec.map (Scheme.ΓSpecIso R).inv
    rw [← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hk' : Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop) = Z.isoSpec.inv ≫ k :=
    (Iso.eq_inv_comp Z.isoSpec).mpr hk.symm
  haveI : IsFinite (Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop)) := by rw [hk']; infer_instance
  haveI : Flat (Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop)) := by rw [hk']; infer_instance
  have h1 : ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.Finite := (IsFinite.SpecMap_iff _).mp inferInstance
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.Flat := Flat.SpecMap_iff.mp inferInstance
  conv_lhs => rw [hk]
  rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank h1 h2]

theorem finrank_add_affine {R : CommRingCat.{u}} {Y : Scheme.{u}} (h : Y ⟶ Spec R)
    [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) (x : Spec R) :
    (U.ι ≫ h).finrank x + (V.ι ≫ h).finrank x = h.finrank x := by
  haveI : IsAffine Y := isAffine_of_isAffineHom h

  have hUc : IsClosed (U : Set Y) := by
    have : (U : Set Y) = (V : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy, hy'⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact h; exact absurd h hy
    rw [this, isClosed_compl_iff]; exact V.isOpen
  have hVc : IsClosed (V : Set Y) := by
    have : (V : Set Y) = (U : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy', hy⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact absurd h hy; exact h
    rw [this, isClosed_compl_iff]; exact U.isOpen
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUc)
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVc)
  haveI : IsAffine (U : Scheme.{u}) := isAffine_of_isAffineHom (U.ι ≫ h)
  haveI : IsAffine (V : Scheme.{u}) := isAffine_of_isAffineHom (V.ι ≫ h)
  rw [finrank_eq_finrank_appTop h, finrank_eq_finrank_appTop (U.ι ≫ h),
    finrank_eq_finrank_appTop (V.ι ≫ h)]

  set φ : R →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom with hφ
  have hU' : ((Scheme.ΓSpecIso R).inv ≫ (U.ι ≫ h).appTop).hom = U.ι.appTop.hom.comp φ := rfl
  have hV' : ((Scheme.ΓSpecIso R).inv ≫ (V.ι ≫ h).appTop).hom = V.ι.appTop.hom.comp φ := rfl
  rw [hU', hV']

  have hsurj : Function.Surjective (Scheme.ΓSpecIso R).inv.hom := by
    intro y; refine ⟨(Scheme.ΓSpecIso R).hom y, ?_⟩
    change ((Scheme.ΓSpecIso R).hom ≫ (Scheme.ΓSpecIso R).inv) y = y
    rw [Iso.hom_inv_id]; rfl
  have hbijι : Function.Bijective (Scheme.ΓSpecIso R).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv
  have h₁fin : (U.ι.appTop.hom.comp φ).Finite := by
    rw [← hU']; exact ((U.ι ≫ h).finite_appTop).comp (RingHom.Finite.of_surjective _ hsurj)
  have h₁flat : (U.ι.appTop.hom.comp φ).Flat := by
    rw [← hU']; exact (RingHom.Flat.of_bijective hbijι).comp (U.ι ≫ h).flat_appTop
  have h₂fin : (V.ι.appTop.hom.comp φ).Finite := by
    rw [← hV']; exact ((V.ι ≫ h).finite_appTop).comp (RingHom.Finite.of_surjective _ hsurj)
  have h₂flat : (V.ι.appTop.hom.comp φ).Flat := by
    rw [← hV']; exact (RingHom.Flat.of_bijective hbijι).comp (V.ι ≫ h).flat_appTop

  have hbij : Function.Bijective (RingHom.prod U.ι.appTop.hom V.ι.appTop.hom) := by
    have hUV' : (U.ι ''ᵁ ⊤) ⊔ (V.ι ''ᵁ ⊤) = ⊤ := by rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, hUV]
    have hdisj' : (U.ι ''ᵁ ⊤) ⊓ (V.ι ''ᵁ ⊤) = ⊥ := by rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, hdisj]
    exact bijective_restrict_prod (U.ι ''ᵁ ⊤) (V.ι ''ᵁ ⊤) hUV' hdisj'
  exact finrank_add_of_bijective_prod φ U.ι.appTop.hom V.ι.appTop.hom hbij h₁fin h₁flat h₂fin h₂flat x

end E160RC

theorem finrank_clopen_add
    {Y S : Scheme.{u}} (f : Y ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) (s : S) :
    (U.ι ≫ f).finrank s + (V.ι ≫ f).finrank s = f.finrank s := by

  have hUc : IsClosed (U : Set Y) := by
    have : (U : Set Y) = (V : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy, hy'⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact h; exact absurd h hy
    rw [this, isClosed_compl_iff]; exact V.isOpen
  have hVc : IsClosed (V : Set Y) := by
    have : (V : Set Y) = (U : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy', hy⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact absurd h hy; exact h
    rw [this, isClosed_compl_iff]; exact U.isOpen
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUc)
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVc)

  obtain ⟨R, g, hg, s', rfl⟩ := S.exists_Spec_apply_eq s
  have sqY : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have sqU := (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert sqY
  have sqV := (isPullback_morphismRestrict (pullback.fst f g) V).paste_vert sqY
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqY s',
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqU s',
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqV s']
  apply E160RC.finrank_add_affine (pullback.snd f g)
  · rw [← Scheme.Hom.preimage_sup, hUV]; rfl
  · rw [← Scheme.Hom.preimage_inf, hdisj]; rfl


/-- Normality on stalks gives normality on any nonempty affine chart. -/
theorem normal_affine {X : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let z : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
  let x := hV.fromSpec z
  have hx : x ∈ V := (hV.isoSpec.inv z).2
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV.isLocalization_stalk' z hx
  letI := h x
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime P)).toRingEquiv

/-- Every stalk of an etale cover of a normal integral scheme is a domain. -/
theorem etale_stalk_domain {X Y : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Y ⟶ X) [Etale p] (y : Y) : IsDomain (Y.presheaf.stalk y) := by
  obtain ⟨V, hV, hyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := p y) trivial
  obtain ⟨W, hW, hyW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (U := p ⁻¹ᵁ V) (x := y) hyV
  letI : Nonempty V := ⟨⟨p y, hyV⟩⟩
  letI := normal_affine h V hV
  have hφ : RingHom.Etale (p.appLE V W hWV).hom :=
    HasRingHomProperty.appLE @Etale p inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hWV
  letI := (p.appLE V W hWV).hom.toAlgebra
  haveI : Algebra.Etale Γ(X, V) Γ(Y, W) := hφ
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨y, hyW⟩
  exact etale_local_domain Γ(X, V) Γ(Y, W)
    (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (Y.presheaf.stalk y)

end SelectedComponent

/-- The connected component through a chosen point is an integral finite etale
surjective cover, with positive rank bounded by that of the full cover. -/
theorem finite_etale_selected_component :
    ∀ (X Y : Scheme.{u}) [IsIntegral X] [IsNoetherian X],
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∀ (p : Y ⟶ X) [IsFinite p] [Etale p] (y : Y),
    ∃ U : Y.Opens, (U : Set Y) = connectedComponent y ∧ IsIntegral U ∧
      IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) ∧ Surjective (U.ι ≫ p) ∧
      (∀ x : X, 0 < (U.ι ≫ p).finrank x ∧ (U.ι ≫ p).finrank x ≤ p.finrank x) := by
  intro X Y _ _ hX p _ _ y
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hdom := SelectedComponent.etale_stalk_domain hX p
  have hopen := (SelectedComponent.FltWs29.C2.main hdom y).1
  have heq : connectedComponent y = irreducibleComponent y := by
    apply Set.Subset.antisymm
    · exact (IsClopen.connectedComponent_subset ⟨isClosed_irreducibleComponent, hopen⟩
        mem_irreducibleComponent)
    · exact isIrreducible_irreducibleComponent.2.isPreconnected.subset_connectedComponent
        mem_irreducibleComponent
  let U : Y.Opens := ⟨irreducibleComponent y, hopen⟩
  have hU : (U : Set Y) = connectedComponent y := heq.symm
  haveI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
    (show IsIrreducible (U : Set Y) from isIrreducible_irreducibleComponent)
  haveI : ∀ z : (U : Scheme), _root_.IsReduced ((U : Scheme).presheaf.stalk z) := by
    intro z
    letI := hdom (U.ι z)
    let e := (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv
    letI : IsDomain ((U : Scheme).presheaf.stalk z) :=
      MulEquiv.isDomain (Y.presheaf.stalk (U.ι z)) e.symm.toMulEquiv
    infer_instance
  haveI : IsReduced (U : Scheme) := isReduced_of_isReduced_stalk _
  haveI : IsIntegral (U : Scheme) :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_irreducibleComponent)
  haveI : Surjective (U.ι ≫ p) := by
    constructor
    apply Set.range_eq_univ.mp
    apply IsClopen.eq_univ
    · exact ⟨(U.ι ≫ p).isClosedMap.isClosed_range,
        (U.ι ≫ p).isOpenMap.isOpen_range⟩
    · exact ⟨(U.ι ≫ p) ⟨y, mem_irreducibleComponent⟩, ⟨_, rfl⟩⟩
  refine ⟨U, hU, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro x
  refine ⟨(Scheme.Hom.one_le_finrank_iff_surjective (U.ι ≫ p)).mpr inferInstance x, ?_⟩
  let V : Y.Opens := ⟨(U : Set Y)ᶜ, isClosed_irreducibleComponent.isOpen_compl⟩
  have hUV : U ⊔ V = ⊤ := by ext z; simp [V]
  have hdisj : U ⊓ V = ⊥ := by ext z; simp [V]
  have hadd := SelectedComponent.finrank_clopen_add p U V hUV hdisj x
  omega

end ArithmeticThetaGlobalization
