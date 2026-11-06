module

public import SchemeSchrodingerDefinitionsR0261
public import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
public import SchemeThetaSectionCohomologyR0259

@[expose] public section

/-! Canonical sheaf base change for the actual conormal theta line. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u

namespace ArithmeticThetaSchemeSchrodingerR0261
namespace SchemeThetaPushforwardBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259

/-- The frozen adjoint-counit map is the library's mate base-change map,
with the same Cartesian square and the same theta line. -/
theorem baseChangeMap_eq {S : Scheme.{u}} (E : Family S) (m : ℕ)
    {T : Scheme.{u}} (b : T ⟶ S) :
    baseChangeMap E m b = Scheme.Modules.baseChangeHom
      (pullback.condition (f := E.p) (g := b)) (thetaLine E m) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.snd E.p b)).homEquiv _ _).symm.injective
  rw [baseChangeMap, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit]
  rw [Scheme.Modules.baseChangeHom_counit]
  rfl

/-- Restriction to an open base commutes with this exact base-change map. -/
theorem baseChangeMap_isIso_of_isOpenImmersion {S : Scheme.{u}}
    (E : Family S) (m : ℕ) {T : Scheme.{u}} (b : T ⟶ S) [IsOpenImmersion b] :
    IsIso (baseChangeMap E m b) := by
  rw [baseChangeMap_eq]
  exact Scheme.Modules.isIso_baseChangeHom_of_isOpenImmersion
    (IsPullback.of_hasPullback E.p b) (thetaLine E m)

/-- The affine-test section provider keeps the structural scalar map induced
by the specified map to the characteristic-zero field. -/
theorem affine_test_sections (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 0 < m)
    (R : Type u) [CommRing R] (b : Base R ⟶ S) :
    let f := pullback.snd E.p b
    let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤;
      ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m) ∧
      SchemeThetaSectionCohomology.CanonicalBaseChange f L := by
  let scalar : k →+* R := (Spec.preimage (b ≫ σ)).hom
  letI : Algebra k R := scalar.toAlgebra
  letI : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ k)
  exact SchemeThetaSectionCohomology.affine_test E m hm b

/-- A line on a quasi-compact quasi-separated scheme has quasicoherent
pushforward to an affine base. This applies before imposing positivity. -/
theorem pushforward_fromTilde {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Base R) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of R) ((Scheme.Modules.pushforward f).obj L)) := by
  apply Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen (R := .of R)
  intro g
  have h := Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs L
    hL.exists_trivialization (U := ⊤) (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
    (by simpa using (isQuasiSeparated_univ : IsQuasiSeparated (Set.univ : Set X))) (f.appTop g)
  have ht : ∀ (U : X.Opens), U = X.basicOpen (f.appTop g) →
      (∀ x : Γ(L, U), ∃ (n : ℕ) (y : Γ(L, ⊤)),
        L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op y =
          X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ((f.appTop g) ^ n) • x) ∧
      (∀ y : Γ(L, ⊤), L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op y = 0 →
        ∃ n : ℕ, (f.appTop g) ^ n • y = 0) := by
    intro U hU
    subst U
    exact h
  obtain ⟨hs, hi⟩ := ht (f ⁻¹ᵁ (Base R).basicOpen g) (Scheme.preimage_basicOpen_top f g)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := hs x
    refine ⟨n, y, ?_⟩
    have hn := ConcreteCategory.congr_hom
      (f.naturality (homOfLE ((Base R).basicOpen_le g)).op) (g ^ n)
    change (L.presheaf.map (homOfLE le_top).op) y =
      (f.app ((Base R).basicOpen g)).hom
        (((Base R).presheaf.map (homOfLE ((Base R).basicOpen_le g)).op).hom (g ^ n)) • (show Γ(L, f ⁻¹ᵁ (Base R).basicOpen g) from x)
    rw [hy]
    congr 1
    rw [← map_pow f.appTop.hom]
    exact hn.symm
  · intro y hy
    obtain ⟨n, hn⟩ := hi y hy
    refine ⟨n, ?_⟩
    change (f.appTop.hom (g ^ n)) • (show Γ(L, ⊤) from y) = 0
    rwa [map_pow]



open Scheme.Modules
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom.AlgebraicGeometry.Scheme.Modules
  (ΓMod globalSectionsEquiv exists_linearEquiv_tensor_ΓMod_pullback
   isIso_fromTildeΓ_pullback_pushforward isIso_of_isIso_moduleSpecΓFunctor_map resM resM_refl map_eq_resM)

/-- Canonical scalar extension on sections identifies the actual sheaf map.
Quasicoherence is proved using quasi-compactness and quasi-separatedness. -/
theorem affine_baseChange {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Base R) [QuasiCompact f] [QuasiSeparated f]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hbc : SchemeThetaSectionCohomology.CanonicalBaseChange f L)
    (A : Type u) [CommRing A] [Algebra R A] :
    IsIso (Scheme.Modules.baseChangeHom
      (pullback.condition (f := f) (g := Scheme.TwoAffineOpenCover.specMap R A)) L) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let b := Scheme.TwoAffineOpenCover.specMap R A
  let g := pullback.fst f b
  let p := pullback.snd f b
  let LA := (Scheme.Modules.pullback g).obj L
  letI : CompactSpace (pullback f b : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace p
  letI : QuasiSeparatedSpace (pullback f b : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated p
  have hsource := isIso_fromTildeΓ_pullback_pushforward f A L
    (pushforward_fromTilde f L hL)
  have htarget := pushforward_fromTilde p LA (hL.pullback g)
  let β := Scheme.Modules.baseChangeHom (pullback.condition (f := f) (g := b)) L
  apply isIso_of_isIso_moduleSpecΓFunctor_map hsource htarget β
  obtain ⟨σ, hσ⟩ := exists_linearEquiv_tensor_ΓMod_pullback A
    ((Scheme.Modules.pushforward f).obj L) (pushforward_fromTilde f L hL)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p LA ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj L)
    ((pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
  obtain ⟨e, he⟩ := hbc A
  let gX := globalSectionsEquiv f L
  let gP := globalSectionsEquiv p LA
  let Γβ : ΓMod ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj L)) →ₗ[A]
      ΓMod ((Scheme.Modules.pushforward p).obj LA) :=
    ((moduleSpecΓFunctor (R := .of A)).map β).hom
  let L₁ : A ⊗[R] ΓMod ((Scheme.Modules.pushforward f).obj L) →ₗ[A] Γ(LA, ⊤) :=
    gP.toLinearMap ∘ₗ Γβ ∘ₗ σ.toLinearMap
  let L₂ : A ⊗[R] ΓMod ((Scheme.Modules.pushforward f).obj L) →ₗ[A] Γ(LA, ⊤) :=
    e.toLinearMap ∘ₗ (LinearEquiv.baseChange R A _ _ gX).toLinearMap
  have hL₁₂ : ∀ x, L₁ x = L₂ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      have ht : a ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, _root_.map_smul, _root_.map_smul]
      congr 1
      have hr : L₂ ((1 : A) ⊗ₜ[R] x) =
          (((pullbackPushforwardAdjunction g).unit.app L).app ⊤).hom x := by
        change e ((LinearEquiv.baseChange R A _ _ gX) ((1 : A) ⊗ₜ[R] x)) = _
        rw [LinearEquiv.baseChange_tmul, he, one_smul]
        rfl
      have hl : L₁ ((1 : A) ⊗ₜ[R] x) =
          (((pullbackPushforwardAdjunction g).unit.app L).app ⊤).hom x := by
        change gP (Γβ (σ ((1 : A) ⊗ₜ[R] x))) = _
        rw [hσ x]
        have h4 := unit_app_app_comp_baseChangeHom_app f b p g
          (pullback.condition (f := f) (g := b)) L ⊤
        have h4x := ConcreteCategory.congr_hom h4 x
        simp only [CategoryTheory.comp_apply] at h4x
        change ((β.app ⊤).hom _) = _
        erw [h4x]
        erw [map_eq_resM]
        change resM LA (le_refl (⊤ : (pullback f b).Opens))
          ((((pullbackPushforwardAdjunction g).unit.app L).app ⊤).hom x) = _
        rw [resM_refl]
      exact hl.trans hr.symm
  have hbij₂ : Function.Bijective L₂ :=
    e.bijective.comp (LinearEquiv.baseChange R A _ _ gX).bijective
  have hΓβ : (Γβ : _ → _) = gP.symm ∘ L₂ ∘ σ.symm := by
    funext x
    have hx := hL₁₂ (σ.symm x)
    change gP (Γβ (σ (σ.symm x))) = L₂ (σ.symm x) at hx
    rw [LinearEquiv.apply_symm_apply] at hx
    change Γβ x = gP.symm (L₂ (σ.symm x))
    rw [← hx, LinearEquiv.symm_apply_apply]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective Γβ
  rw [hΓβ]
  exact gP.symm.bijective.comp (hbij₂.comp σ.symm.bijective)


/-- Arbitrary scheme base change follows by identifying the canonical map
on affine neighborhoods of every point of the new base. -/
theorem baseChangeMap_isIso (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 0 < m)
    {T : Scheme.{u}} (b : T ⟶ S) : IsIso (baseChangeMap E m b) := by
  rw [baseChangeMap_eq]
  letI : IsProper E.p := E.proper
  refine Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback
    (IsPullback.of_hasPullback E.p b) (thetaLine E m) ?_
  intro y
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show b.base y ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W', hW', hyW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show y ∈ b ⁻¹ᵁ W from hyW)
  letI : Algebra Γ(S, W) Γ(T, W') := (b.appLE W W' hle).hom.toAlgebra
  have hφ : (hW'.isoSpec.symm.hom ≫ Scheme.Opens.ι W') ≫ b =
      Scheme.TwoAffineOpenCover.specMap Γ(S, W) Γ(T, W') ≫ hW.isoSpec.symm.hom ≫ Scheme.Opens.ι W := by
    rw [Iso.symm_hom, Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι]
    change _ = Spec.map (CommRingCat.ofHom (b.appLE W W' hle).hom) ≫ hW.fromSpec
    rw [CommRingCat.ofHom_hom]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec b hW hW' hle).symm
  have hu : IsPullback (pullback.fst E.p hW.fromSpec) (pullback.snd E.p hW.fromSpec) E.p
      (hW.isoSpec.symm.hom ≫ Scheme.Opens.ι W) := by
    rw [Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι]
    exact IsPullback.of_hasPullback _ _
  refine ⟨W, W', hyW', Base Γ(S, W), Base Γ(T, W'),
    pullback E.p hW.fromSpec,
    pullback (pullback.snd E.p hW.fromSpec) (Scheme.TwoAffineOpenCover.specMap Γ(S, W) Γ(T, W')),
    hW.isoSpec.symm, hW'.isoSpec.symm, Scheme.TwoAffineOpenCover.specMap Γ(S, W) Γ(T, W'), hφ,
    pullback.snd E.p hW.fromSpec, pullback.fst E.p hW.fromSpec, hu,
    pullback.snd _ _, pullback.fst _ _, IsPullback.of_hasPullback _ _, ?_⟩
  exact affine_baseChange (pullback.snd E.p hW.fromSpec)
    ((Scheme.Modules.pullback (pullback.fst E.p hW.fromSpec)).obj (thetaLine E m))
    (SchemeThetaSectionCohomology.test_line_invertible E m hW.fromSpec)
    (affine_test_sections k σ E m hm Γ(S, W) hW.fromSpec).2 Γ(T, W')


/-- Finite projectivity and geometric rank are transported through the
canonical sheaf base-change isomorphism on each affine test. -/
theorem bundleRank (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 0 < m) :
    BundleRank (V E m) m := by
  intro R _ b
  let W := (Scheme.Modules.pullback b).obj (V E m)
  let f := pullback.snd E.p b
  let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Base R)) W ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
  letI := baseChangeMap_isIso k σ E m hm b
  let e : W ≅ (Scheme.Modules.pushforward f).obj L := asIso (baseChangeMap E m b)
  let e₀ : (Scheme.Modules.pushforward (𝟙 (Base R))).obj W ≅ W :=
    (Scheme.Modules.pushforwardId (Base R)).app W
  let eΓ := (moduleSpecΓFunctor (R := .of R)).mapIso (e₀ ≪≫ e)
  let ε : Γ(W, ⊤) ≃ₗ[R] Γ(L, ⊤) :=
    ((globalSectionsEquiv (𝟙 (Base R)) W).symm.trans eΓ.toLinearEquiv).trans
      (globalSectionsEquiv f L)
  exact SchemeThetaSectionCohomology.finiteProjectiveRank_equiv ε.symm m
    (affine_test_sections k σ E m hm R b).1

/-- A public affine quasicoherence interface for consumers of the actual
pushforward sheaf. The conclusion is a specific sheaf predicate. -/
theorem affine_pullback_quasicoherent (k : Type u) [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (m : ℕ) (hm : 0 < m)
    (R : Type u) [CommRing R] (b : Base R ⟶ S) :
    ((Scheme.Modules.pullback b).obj (V E m)).IsQuasicoherent := by
  letI : IsProper E.p := E.proper
  let f := pullback.snd E.p b
  let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
  letI : CompactSpace (pullback E.p b : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace (pullback E.p b : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated f
  have h := pushforward_fromTilde f L
    (SchemeThetaSectionCohomology.test_line_invertible E m b)
  have hq := (isQuasicoherent_iff_isIso_fromTildeΓ ((Scheme.Modules.pushforward f).obj L)).mpr h
  letI := baseChangeMap_isIso k σ E m hm b
  exact (SheafOfModules.isQuasicoherent (Base R).ringCatSheaf).prop_of_iso
    (asIso (baseChangeMap E m b)).symm hq

end SchemeThetaPushforwardBaseChange

/-- The actual theta pushforward has rank m and its canonical adjoint-counit
base-change map is an isomorphism for every scheme base change. -/
theorem scheme_theta_pushforward_base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ∀ E : ArithmeticThetaLocalWeierstrassR0203.Family S, ∀ (m : ℕ), 0 < m →
      ArithmeticThetaSchemeSchrodingerR0261.BundleRank
        (ArithmeticThetaSchemeSchrodingerR0261.V E m) m ∧
      ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : Quiver.Hom T S),
        CategoryTheory.IsIso (ArithmeticThetaSchemeSchrodingerR0261.baseChangeMap E m b) := by
  intro k _ _ S σ E m hm
  exact ⟨SchemeThetaPushforwardBaseChange.bundleRank k σ E m hm,
    fun T b => SchemeThetaPushforwardBaseChange.baseChangeMap_isIso k σ E m hm b⟩

end ArithmeticThetaSchemeSchrodingerR0261

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.baseChangeMap_eq
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.baseChangeMap_isIso_of_isOpenImmersion
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.affine_test_sections
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.pushforward_fromTilde

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.affine_baseChange

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.baseChangeMap_isIso

#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.bundleRank
#print axioms ArithmeticThetaSchemeSchrodingerR0261.SchemeThetaPushforwardBaseChange.affine_pullback_quasicoherent
#print axioms ArithmeticThetaSchemeSchrodingerR0261.scheme_theta_pushforward_base_change
