module

public import ProperTowerAutomorphismEffectivityPreludeR0137

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open _root_.AlgebraicGeometry


open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by
  obtain ⟨K, M, i1, i2, iΓ, i4, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF, hϑs, hθEs, hθFs, hϑn, hθEn, hθFn,
    hexact, hsurj, hϑi, hc1, hc2, hc3, u, hub, hus, hun, huϑ, huθE⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  letI := i1; letI := i2; letI := iΓ; letI := i4
  exact AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete
    I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
    K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3
    u hub hus hun huϑ huθE

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace RedC6bSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

section FSide

variable (F : OModulePresheaf π)

theorem eq_of_forall_isLocalizedModule_eq {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (f : ∀ i, M →ₗ[S] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    (x y : M) (h : ∀ i, f i x = f i y) : x = y := by
  classical
  have hex : ∀ i, ∃ n : ℕ, g i ^ n • x = g i ^ n • y := fun i => by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g i)) (f i)).mp (h i)
    exact ⟨n, hn⟩
  choose n hn using hex
  let N := Finset.univ.sup n
  have hN : ∀ i, g i ^ N • x = g i ^ N • y := fun i => by
    have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm, mul_smul, mul_smul, hn i]
  have hspan : Ideal.span (Set.range fun i => g i ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg N
    rw [← Set.range_comp] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan.symm ▸ Submodule.mem_top (x := (1 : S)))
  calc x = (1 : S) • x := (one_smul S x).symm
    _ = (∑ i, c i * g i ^ N) • x := by rw [hc]
    _ = ∑ i, c i • (g i ^ N • x) := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = ∑ i, c i • (g i ^ N • y) := by simp_rw [hN]
    _ = (∑ i, c i * g i ^ N) • y := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = y := by rw [hc, one_smul]

def FO (O : V.Opens) (W : V.Opens) (h : W ≤ O) : Type u := F.obj W

scoped instance instACG_FO (O W : V.Opens) (h : W ≤ O) : AddCommGroup (FO F O W h) :=
  inferInstanceAs (AddCommGroup (F.obj W))

scoped instance instMod_FO (O W : V.Opens) (h : W ≤ O) : Module Γ(V, O) (FO F O W h) :=
  Module.compHom (F.obj W) (V.presheaf.map (homOfLE h).op).hom

theorem FO_smul_def (O W : V.Opens) (h : W ≤ O) (a : Γ(V, O)) (x : FO F O W h) :
    a • x = (show FO F O W h from (V.presheaf.map (homOfLE h).op).hom a • (show F.obj W from x)) := rfl

def FresO (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) :
    FO F O W hW →ₗ[Γ(V, O)] FO F O W' hW' where
  toFun x := (show FO F O W' hW' from F.res h (show F.obj W from x))
  map_add' x y := map_add (F.res h) _ _
  map_smul' a x := by
    show F.res h ((V.presheaf.map (homOfLE hW).op).hom a • (show F.obj W from x)) =
      (V.presheaf.map (homOfLE hW').op).hom a • F.res h _
    rw [F.res_smul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl

theorem FresO_apply (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) (x : FO F O W hW) :
    FresO F O hW hW' h x = (show FO F O W' hW' from F.res h (show F.obj W from x)) := rfl

def Fres₀ (O : V.Opens) {W : V.Opens} (hW : W ≤ O) : F.obj O →ₗ[Γ(V, O)] FO F O W hW where
  toFun x := (show FO F O W hW from F.res hW x)
  map_add' x y := map_add (F.res hW) _ _
  map_smul' a x := F.res_smul hW a x

theorem Fres₀_apply (O : V.Opens) {W : V.Opens} (hW : W ≤ O) (x : F.obj O) :
    Fres₀ F O hW x = (show FO F O W hW from F.res hW x) := rfl

variable {F}

theorem isLocalizedModule_FresO (hF : F.IsQuasicoherent) (O : V.Opens) (W : V.affineOpens) (hW : W.1 ≤ O)
    (g : Γ(V, O)) :
    IsLocalizedModule (Submonoid.powers g)
      (FresO F O hW ((V.basicOpen_le _).trans hW)
        (V.basicOpen_le ((V.presheaf.map (homOfLE hW).op).hom g))) := by
  set gW := (V.presheaf.map (homOfLE hW).op).hom g with hgW
  have hq := hF W gW
  have hres : ∀ n : ℕ, (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) =
      (V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom (gW ^ n) := fun n => by
    rw [hgW, ← map_pow, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom gW) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen gW
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n)) := by
      rw [hres, map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen gW) =>
        (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    refine ⟨((show FO F O W.1 hW from x), ⟨g ^ n, n, rfl⟩), ?_⟩
    show (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • (show F.obj _ from y) = F.res _ x
    rw [hres]; exact hx.symm
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le gW) ((show F.obj W.1 from x₁) - (show F.obj W.1 from x₂)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₁) =
      (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₂)
    rw [map_pow, ← hgW, ← sub_eq_zero, ← smul_sub, hn]

theorem isLocalizedModule_Fres₀ (hF : F.IsQuasicoherent) (U : V.affineOpens) (g : Γ(V, U.1)) :
    IsLocalizedModule (Submonoid.powers g) (Fres₀ F U.1 (V.basicOpen_le g)) := by
  have hq := hF U g
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom g) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n)) := by
      rw [map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen g) =>
        (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    exact ⟨(x, ⟨g ^ n, n, rfl⟩), hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le g) (x₁ - x₂) = 0 := by rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show g ^ n • x₁ = g ^ n • x₂
    rw [← sub_eq_zero, ← smul_sub, hn]

theorem F_eq_of_forall_res_basicOpen_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type*} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤) (x y : F.obj U.1)
    (h : ∀ i, F.res (V.basicOpen_le (g i)) x = F.res (V.basicOpen_le (g i)) y) : x = y :=
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  eq_of_forall_isLocalizedModule_eq g hg (fun i => Fres₀ F U.1 (V.basicOpen_le (g i))) x y h

theorem F_exists_of_forall_res_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type u} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i, F.obj (V.basicOpen (g i)))
    (hx : ∀ i j, F.res (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))) (x i) =
      F.res (by rw [Scheme.basicOpen_res]; exact inf_le_right) (x j)) :
    ∃ m : F.obj U.1, ∀ i, F.res (V.basicOpen_le (g i)) m = x i := by
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  let Ui : ι → V.affineOpens := fun i => ⟨V.basicOpen (g i), U.2.basicOpen (g i)⟩
  haveI := fun i j => isLocalizedModule_FresO hF U.1 (Ui i) (V.basicOpen_le (g i)) (g j)
  obtain ⟨m, hm⟩ := IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top g hg
    (fun i => Fres₀ F U.1 (V.basicOpen_le (g i)))
    (fun i j => FresO F U.1 (V.basicOpen_le (g i)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))))
    (fun i j => FresO F U.1 (V.basicOpen_le (g j)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (by rw [Scheme.basicOpen_res]; exact inf_le_right))
    (fun i j => LinearMap.ext fun m => by
      show F.res _ (F.res _ m) = F.res _ (F.res _ m)
      rw [F.res_res, F.res_res])
    (fun i => (show FO F U.1 _ _ from x i)) (fun i j => hx i j)
  exact ⟨m, hm⟩

end FSide

section Hom

variable {F₁ F₂ : OModulePresheaf π}

def appO (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) : F₁.obj U.1 →ₗ[Γ(V, U.1)] F₂.obj U.1 where
  toFun x := Φ.app U x
  map_add' x y := map_add _ x y
  map_smul' a x := Φ.app_smul U a x

theorem appO_apply (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (x : F₁.obj U.1) : appO Φ U x = Φ.app U x := rfl

abbrev bU (U : V.affineOpens) (g : Γ(V, U.1)) : V.affineOpens := ⟨V.basicOpen g, U.2.basicOpen g⟩

def appB (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    FO F₁ U.1 (V.basicOpen g) (V.basicOpen_le g) →ₗ[Γ(V, U.1)] FO F₂ U.1 (V.basicOpen g) (V.basicOpen_le g) where
  toFun x := (show FO F₂ U.1 _ _ from Φ.app (bU U g) (show F₁.obj (V.basicOpen g) from x))
  map_add' x y := map_add (Φ.app (bU U g)) _ _
  map_smul' a x := Φ.app_smul (bU U g) _ _

theorem appB_comp (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    appB Φ U g ∘ₗ Fres₀ F₁ U.1 (V.basicOpen_le g) = Fres₀ F₂ U.1 (V.basicOpen_le g) ∘ₗ appO Φ U := by
  refine LinearMap.ext fun x => ?_
  show Φ.app (bU U g) (F₁.res (V.basicOpen_le g) x) = F₂.res (V.basicOpen_le g) (Φ.app U x)
  have := Φ.naturality (U := bU U g) (U' := U) (V.basicOpen_le g)
  exact (LinearMap.congr_fun this x)

theorem map_eq_appB (hF₁ : F₁.IsQuasicoherent) (hF₂ : F₂.IsQuasicoherent)
    (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    haveI := isLocalizedModule_Fres₀ hF₁ U g
    haveI := isLocalizedModule_Fres₀ hF₂ U g
    IsLocalizedModule.map (Submonoid.powers g) (Fres₀ F₁ U.1 (V.basicOpen_le g)) (Fres₀ F₂ U.1 (V.basicOpen_le g))
      (appO Φ U) = appB Φ U g := by
  haveI := isLocalizedModule_Fres₀ hF₁ U g
  haveI := isLocalizedModule_Fres₀ hF₂ U g
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers g) (Fres₀ F₁ U.1 (V.basicOpen_le g))
    (Fres₀ F₂ U.1 (V.basicOpen_le g))
  rw [IsLocalizedModule.map_comp, appB_comp]

theorem app_eq_of_forall_basicOpen (hF₂ : F₂.IsQuasicoherent) (Φ Ψ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens)
    (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (h : ∀ g ∈ T, Φ.app (bU U g) = Ψ.app (bU U g)) (x : F₁.obj U.1) : Φ.app U x = Ψ.app U x := by
  classical
  have hrange : Set.range (fun g : ↥T => (g.1 : Γ(V, U.1))) = (T : Set Γ(V, U.1)) := by
    ext a; exact ⟨by rintro ⟨g, rfl⟩; exact g.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  refine F_eq_of_forall_res_basicOpen_eq hF₂ U (fun g : ↥T => (g.1 : Γ(V, U.1))) (by rw [hrange]; exact hT) _ _ fun g => ?_
  show F₂.res (V.basicOpen_le g.1) (Φ.app U x) = F₂.res (V.basicOpen_le g.1) (Ψ.app U x)
  rw [← Φ.naturality_apply (U := bU U g.1) (U' := U) (V.basicOpen_le g.1) x,
    ← Ψ.naturality_apply (U := bU U g.1) (U' := U) (V.basicOpen_le g.1) x, h g.1 g.2]

end Hom

theorem exists_cover (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1) (U : V.affineOpens) :
    ∃ T : Finset Γ(V, U.1), Ideal.span (T : Set Γ(V, U.1)) = ⊤ ∧ ∀ g ∈ T, bU U g ∈ B := by
  classical
  let s : Set Γ(V, U.1) := {g | bU U g ∈ B}
  have hs : Ideal.span s = ⊤ := by
    rw [← U.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => V.basicOpen_le _) ?_
    intro x hx
    obtain ⟨W, hWB, hxW⟩ := hcov x
    obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hx
    have hf : f ∈ s := hdown W (bU U f) hfW hWB
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨T, hTs, hT⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hs)
  exact ⟨T, (Ideal.eq_top_iff_one _).mpr hT, fun g hg => hTs hg⟩

end RedC6bSol
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol"

end
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol"

open RedC6bSol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
      (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U)) ∧
      (∀ U : P.affineOpens, Function.Surjective (β.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) := by
  classical
  obtain ⟨B, hdown, hcov, M, i1, i2, i3, i4, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF,
    hϑs, hθEs, hθFs, hϑn, hθEn, hθFn, hexact, hsurj, hc1, hc2, hc3⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨G, e, hGc, hGq, he_smul, he_res, hout, hin⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis q B hdown hcov M res
      res_smul res_refl res_comp hqc hfg
  obtain ⟨α, hα, -⟩ := hin GK hGKq ϑ hϑs hϑn
  obtain ⟨β, hβ, -⟩ := hout GE hGEq θE hθEs hθEn
  choose ψ hψ using fun k => (hout (F k) (hFq k) (θF k) (hθFs k) (hθFn k)).exists

  have hβW : ∀ (W : ↥B) (x : G.obj W.1.1), β.app W.1 x = θE W (e W x) := hβ
  have hαW : ∀ (W : ↥B) (x : GK.obj W.1.1), α.app W.1 x = (e W).symm (ϑ W x) := fun W x => by
    rw [← hα W x, LinearEquiv.symm_apply_apply]
  refine ⟨G, α, β, ψ, hGc, hGq, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGKq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGEq U g.1
    have hrange : Set.range (fun g : ↥T => (g.1 : Γ(P, U.1))) = (T : Set Γ(P, U.1)) := by
      ext a; exact ⟨by rintro ⟨g, rfl⟩; exact g.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
    have key : Function.Exact (appO α U) (appO β U) := by
      refine exact_of_isLocalized_span (T : Set Γ(P, U.1)) hT
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GK U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GK U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO G U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ G U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GE U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GE U.1 (P.basicOpen_le g.1))
        (appO α U) (appO β U) fun g => ?_
      rw [map_eq_appB hGKq hGq α U g.1, map_eq_appB hGq hGEq β U g.1]

      intro y
      let W : ↥B := ⟨bU U g.1, hB g.1 g.2⟩
      show β.app W.1 y = 0 ↔ y ∈ Set.range (fun x => α.app W.1 x)
      rw [hβW W, ← LinearMap.mem_ker, ← hexact W, LinearMap.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        show α.app W.1 x = y
        rw [hαW W, hx, LinearEquiv.symm_apply_apply]
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        change α.app W.1 x = y at hx
        rw [← hx, hαW W, LinearEquiv.apply_symm_apply]
    have key' : Function.Exact (α.app U) (β.app U) := key
    exact (LinearMap.exact_iff.mp key').symm
  ·
    intro U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGEq U g.1
    have key : Function.Surjective (appO β U) := by
      refine surjective_of_isLocalized_span (T : Set Γ(P, U.1)) hT
        (fun g : ↥(T : Set Γ(P, U.1)) => FO G U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ G U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GE U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GE U.1 (P.basicOpen_le g.1))
        (appO β U) fun g => ?_
      rw [map_eq_appB hGq hGEq β U g.1]
      intro z
      let W : ↥B := ⟨bU U g.1, hB g.1 g.2⟩
      obtain ⟨m, hm⟩ := hsurj W (show GE.obj W.1.1 from z)
      refine ⟨(show FO G U.1 _ _ from (e W).symm m), ?_⟩
      show β.app W.1 ((e W).symm m) = z
      rw [hβW W, LinearEquiv.apply_symm_apply, hm]
    exact key
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((φ k).comp (ψ (k + 1))).app U x = (ψ k).app U x
    refine app_eq_of_forall_basicOpen (hFq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (φ k).app W.1 ((ψ (k + 1)).app W.1 y) = (ψ k).app W.1 y
    rw [hψ (k + 1) W, hψ k W]
    exact LinearMap.congr_fun (hc1 k W) (e W y)
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((ψ k).comp α).app U x = (lam k).app U x
    refine app_eq_of_forall_basicOpen (hFq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (ψ k).app W.1 (α.app W.1 y) = (lam k).app W.1 y
    rw [hψ k W, hαW W, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (hc2 k W) y
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((ε k).comp (ψ k)).app U x = ((ψE k).comp β).app U x
    refine app_eq_of_forall_basicOpen (hEq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (ε k).app W.1 ((ψ k).app W.1 y) = (ψE k).app W.1 (β.app W.1 y)
    rw [hψ k W, hβW W]
    exact LinearMap.congr_fun (hc3 k W) (e W y)

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
      (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U)) ∧
      (∀ U : P.affineOpens, Function.Surjective (β.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  obtain ⟨G, α, β, ψ, hGc, hGq, hαβ, hβs, hψc, hψα, hψβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  exact AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
    I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami G hGc hGq α β hαβ hβs ψ hψc hψα hψβ

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory open _root_.AlgebraicGeometry hiding ChowDatum

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open TopologicalSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace GEDriver

theorem support_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).support = T :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal T)

theorem radical_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).radical = Scheme.IdealSheafData.vanishingIdeal T := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]

theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal T
  refine @IsReduced.of_openCover _ I.subschemeCover.openCover (fun U => ?_)
  have hrad : (I.ideal U).IsRadical := by
    rw [← Ideal.radical_eq_iff]
    have := congrArg (fun J : X.IdealSheafData => J.ideal U) (radical_vanishingIdeal T)
    simp [Scheme.IdealSheafData.radical_ideal] at this
    exact this
  haveI : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := (Ideal.isRadical_iff_quotient_reduced _).1 hrad
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  infer_instance

theorem irreducibleSpace_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) (hT : IsIrreducible (T : Set X)) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal T).subscheme :=
  Subtype.irreducibleSpace hT

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) (hT : IsIrreducible (T : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  haveI := isReduced_subscheme_vanishingIdeal T
  haveI := irreducibleSpace_subscheme_vanishingIdeal T hT
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem compactSpace_of_isProper {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    [IsProper q] : CompactSpace P :=
  QuasiCompact.compactSpace_of_compactSpace q

theorem isNoetherian_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : IsNoetherian P :=
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := compactSpace_of_isProper q
  {}

theorem noetherianSpace_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : NoetherianSpace P :=
  haveI := isNoetherian_of_isProper q
  inferInstance

theorem isProper_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) : IsProper I.subschemeι := inferInstance

theorem isProper_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] : IsProper (f ≫ g) :=
  inferInstance

theorem isSeparated_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsSeparated f := inferInstance

theorem idealAnnihilates_ker_subschemeι {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (J : P.IdealSheafData) (F : ℕ → OModulePresheaf q)
    (hS : ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ J.ideal U ^ 1, ∀ x : (F k).obj U.1, a • x = 0) :
    ∀ k, OModulePresheaf.IdealAnnihilates q J.subschemeι.ker (F k) := by
  intro k U a ha x
  rw [Scheme.IdealSheafData.ker_subschemeι] at ha
  exact hS k U a (by rwa [pow_one]) x

private theorem _root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.GEDriver.nonempty_orderedAffineCover_of_compactSpace_univ (X : Scheme.{u}) [CompactSpace X] :
    Nonempty X.OrderedAffineCover := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  letI : LinearOrder ↥t := LinearOrder.lift' (Fintype.equivFin ↥t) (Fintype.equivFin ↥t).injective
  refine ⟨{ ι := ↥t, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨U, hUt, hxU⟩ := hx
  exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

p2m_export "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.GEDriver" "nonempty_orderedAffineCover_of_compactSpace_univ"

theorem exists_closeds_lt_sup_eq {X : Type*} [TopologicalSpace X] (T : Closeds X) (hne : (T : Set X).Nonempty)
    (hT : ¬ IsIrreducible (T : Set X)) : ∃ T₁ T₂ : Closeds X, T₁ < T ∧ T₂ < T ∧ T = T₁ ⊔ T₂ := by
  have hpre : ¬ IsPreirreducible (T : Set X) := fun h => hT ⟨hne, h⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  push Not at hpre
  obtain ⟨z₁, z₂, hz₁, hz₂, hsub, h₁, h₂⟩ := hpre
  refine ⟨T ⊓ ⟨z₁, hz₁⟩, T ⊓ ⟨z₂, hz₂⟩, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun h => h₁ ?_
    have : (T : Set X) ∩ z₁ = (T : Set X) := congrArg (fun S : Closeds X => (S : Set X)) h
    rw [← this]; exact Set.inter_subset_right
  · refine lt_of_le_of_ne inf_le_left fun h => h₂ ?_
    have : (T : Set X) ∩ z₂ = (T : Set X) := congrArg (fun S : Closeds X => (S : Set X)) h
    rw [← this]; exact Set.inter_subset_right
  · apply Closeds.ext
    show (T : Set X) = (T : Set X) ∩ z₁ ∪ (T : Set X) ∩ z₂
    rw [← Set.inter_union_distrib_left]
    exact (Set.inter_eq_left.2 hsub).symm

theorem vanishingIdeal_sup_pow_mul_le {X : Scheme.{u}} (T₁ T₂ : Closeds X) (U : X.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal T₂).ideal U ^ 1 * (Scheme.IdealSheafData.vanishingIdeal T₁).ideal U
      ≤ (Scheme.IdealSheafData.vanishingIdeal (T₁ ⊔ T₂)).ideal U ^ 1 := by
  rw [pow_one, pow_one, Scheme.IdealSheafData.vanishingIdeal_sup, Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
  exact Ideal.mul_le_inf.trans (by rw [inf_comm])

theorem vanishingIdeal_top_ideal_le_radical_bot {X : Scheme.{u}} (U : X.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).ideal U ≤ ((⊥ : X.IdealSheafData).ideal U).radical := by
  rw [Scheme.IdealSheafData.vanishingIdeal_top, ← Scheme.IdealSheafData.radical_bot,
    Scheme.IdealSheafData.radical_ideal]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]

structure AdicSys where
  F : ℕ → OModulePresheaf q
  hc : ∀ k, (F k).IsCoherent
  hq : ∀ k, (F k).IsQuasicoherent
  φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k)
  hs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U)
  hk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))

variable {I q}

def AdicSys.Algebraised (S : AdicSys I q) : Prop :=
  ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (S.F k)),
    G.IsCoherent ∧ G.IsQuasicoherent ∧
    (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
    (∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
    (∀ (k : ℕ) (U : P.affineOpens), (S.φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)

theorem algebraised_of_quot_of_ker (S : AdicSys I q) (𝓙 : P.IdealSheafData)
    (hQ : ∀ Q : AdicSys I q, (∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (Q.F k)) → Q.Algebraised)
    (hK : ∀ (K : AdicSys I q) (j : ∀ k, OModulePresheaf.AffHom (K.F k) (S.F k)),
      (∀ (k : ℕ) (U : P.affineOpens), (S.φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (K.φ k).app U) →
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.range ((j k).app U) = OModulePresheaf.idealPowSub q 𝓙 (S.F k) 1 U.1) →
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K.F (k + c)).obj U.1))) →
      K.Algebraised) :
    S.Algebraised := by
  classical

  obtain ⟨Q, τ, ε, hQc, hQq, hτs, hτk, hεc, hεs, hεk, hann⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
      I 𝓙 S.F S.hc S.hq S.φ S.hs S.hk
  let QS : AdicSys I q := ⟨Q, hQc, hQq, τ, hτs, hτk⟩

  obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, huj, hAR, hsurj, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I S.F S.hc S.hq S.φ S.hs S.hk Q hQc hQq τ hτs hτk ε hεc
  let KS : AdicSys I q := ⟨Ks, hKc, hKq, κ, hκs, hκk⟩
  have hjr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((j k).app U) = LinearMap.ker ((ε k).app U) := hsurj hεs

  obtain ⟨GQ, ψQ, hGQc, hGQq, hψQs, hψQk, hψQc⟩ := hQ QS hann
  obtain ⟨GK, ψK, hGKc, hGKq, hψKs, hψKk, hψKc⟩ :=
    hK KS j hjc (fun k U => (hjr k U).trans (hεk k U)) (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).2⟩)

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q S.F S.hc S.hq S.φ S.hs S.hk Q hQc hQq τ hτs hτk ε hεs hεc GQ hGQc hGQq ψQ hψQs hψQk hψQc
      GK hGKc hGKq (fun k => (j k).comp (ψK k))
      (by
        intro k U
        show (S.φ k).app U ∘ₗ ((j (k + 1)).app U ∘ₗ (ψK (k + 1)).app U)
          = (j k).app U ∘ₗ (ψK k).app U
        rw [← LinearMap.comp_assoc, hjc, LinearMap.comp_assoc, hψKc])
      (by
        intro k U
        show LinearMap.range ((j k).app U ∘ₗ (ψK k).app U) = LinearMap.ker ((ε k).app U)
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hψKs k U))]
        exact hjr k U)
      (by
        intro U
        obtain ⟨c, hc⟩ := hAR U
        refine ⟨c, fun k => ?_⟩
        intro x hx
        have hx' : (ψK (k + c)).app U x ∈ LinearMap.ker ((j (k + c)).app U) := by
          simpa [LinearMap.mem_ker] using hx
        have h1 : (ψK (k + c)).app U x ∈ I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) :=
          (hc k).2 hx'

        have hmap : Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
            = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hψKs (k + c) U)]
        have h2 : x ∈ Submodule.comap ((ψK (k + c)).app U)
            (Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))) := by
          rw [hmap]; exact h1
        rw [Submodule.comap_map_eq, hψKk] at h2
        have hle : I ^ (k + c + 1) • (⊤ : Submodule A (GK.obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact (sup_le le_rfl hle) h2)
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

def AdicSys.KilledBy (S : AdicSys I q) (𝓙 : P.IdealSheafData) (t : ℕ) : Prop :=
  ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ t, ∀ x : (S.F k).obj U.1, a • x = 0

theorem AdicSys.killedBy_one_iff (S : AdicSys I q) (𝓙 : P.IdealSheafData) :
    S.KilledBy 𝓙 1 ↔ ∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (S.F k) := by
  simp [AdicSys.KilledBy, OModulePresheaf.IdealAnnihilates, pow_one]

noncomputable abbrev idealOf (T : Closeds P) : P.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T

theorem AdicSys.algebraised_of_forall_eq_zero (S : AdicSys I q)
    (h : ∀ (k : ℕ) (U : P.affineOpens) (x : (S.F k).obj U.1), x = 0) : S.Algebraised := by
  have hcoh : (OModulePresheaf.zero q).IsCoherent := fun U => Module.Finite.of_finite
  have hqc : (OModulePresheaf.zero q).IsQuasicoherent := fun U f =>
    ⟨fun x => ⟨0, 0, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨OModulePresheaf.zero q, fun k => OModulePresheaf.AffHom.zeroFrom (S.F k), hcoh, hqc,
    fun k U y => ⟨0, by rw [h k U y]; exact map_zero _⟩, fun k U => ?_, fun k U => ?_⟩
  · haveI : Subsingleton (Submodule A ((OModulePresheaf.zero q).obj U.1)) := (Submodule.subsingleton_iff A).2 inferInstance
    exact Subsingleton.elim _ _
  · exact LinearMap.ext fun x => (h k U _).trans (h k U _).symm

theorem AdicSys.algebraised_of_killedBy_zero (S : AdicSys I q) (𝓙 : P.IdealSheafData) (h : S.KilledBy 𝓙 0) :
    S.Algebraised :=
  S.algebraised_of_forall_eq_zero (fun k U x => by
    have := h k U 1 (by rw [pow_zero, Ideal.one_eq_top]; trivial) x
    rwa [one_smul] at this)

theorem AdicSys.algebraised_of_killedBy_coe_eq_empty (S : AdicSys I q) (T : Closeds P) (hT : (T : Set P) = ∅)
    (h : S.KilledBy (idealOf T) 1) : S.Algebraised :=
  S.algebraised_of_forall_eq_zero (fun k U x => by
    have h1 : (1 : Γ(P, U.1)) ∈ (idealOf T).ideal U ^ 1 := by
      have hT' : T = ⊥ := Closeds.ext (by simpa using hT)
      subst hT'
      rw [pow_one, show idealOf (⊥ : Closeds P) = ⊤ from Scheme.IdealSheafData.vanishingIdeal_bot,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply]
      trivial
    have := h k U 1 h1 x
    rwa [one_smul] at this)

theorem stepC
    (T : Closeds P) (hTirr : IsIrreducible (T : Set P))
    (ih : ∀ T' : Closeds P, T' < T → ∀ (t : ℕ) (S : AdicSys I q), S.KilledBy (idealOf T') t → S.Algebraised)
    (S : AdicSys I q) (hS : S.KilledBy (idealOf T) 1) : S.Algebraised := by
  classical

  let Z : Scheme.{u} := (idealOf T).subscheme
  let i : Z ⟶ P := (idealOf T).subschemeι
  haveI : IsIntegral Z := isIntegral_subscheme_vanishingIdeal T hTirr
  haveI : IsProper i := isProper_subschemeι _
  haveI : IsProper (i ≫ q) := inferInstance
  obtain ⟨cd⟩ := AlgebraicGeometry.ChowDatumProj.nonempty_of (i ≫ q)
    (AlgebraicGeometry.ChowDatum.nonempty (i ≫ q))
  haveI : IsProper (cd.p ≫ i) := inferInstance
  haveI : IsSeparated (cd.p ≫ i) := inferInstance
  haveI : IsProper ((cd.p ≫ i) ≫ q) := inferInstance
  haveI : CompactSpace cd.V' := compactSpace_of_isProper ((cd.p ≫ i) ≫ q)
  obtain ⟨K'⟩ := AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ cd.V'
  have hSZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (S.F k) :=
    idealAnnihilates_ker_subschemeι q (idealOf T) S.F hS

  obtain ⟨F', φ', η, hF'c, hF'q, hφ's, hφ'k, hηs, hηV, hηU, hηφ, hβ, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom I q (cd.p ≫ i) S.F S.hc S.hq S.φ S.hs S.hk

  have hιq : cd.ιN ≫ ProjSpace.π A cd.Nd = (cd.p ≫ i) ≫ q := by rw [cd.hoverN, Category.assoc]
  obtain ⟨G', ψ', hG'c, hG'q, hψ's, hψ'k, hψ'c⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete I cd.ιN hιq F' hF'c hF'q φ' hφ's hφ'k

  obtain ⟨v, hvη, hvc⟩ : ∃ v : ∀ k, OModulePresheaf.AffHom (S.F k)
      (OModulePresheaf.cechPushforward (cd.p ≫ i) q K' (F' k)),
      (∀ (k : ℕ) (U₀ : P.affineOpens) (x : (S.F k).obj U₀.1) (jx : K'.ι),
        ((v k).app U₀ x).1 jx = η k U₀ (OModulePresheaf.AffHom.affineChart (cd.p ≫ i) q K' U₀ jx)
          (OModulePresheaf.cechPushforward.chart_le_preimage (cd.p ≫ i) K' U₀.1 jx) x) ∧
      (∀ (k : ℕ) (U₀ : P.affineOpens),
        ((φ' k).cechPushforward (cd.p ≫ i) q K').app U₀ ∘ₗ (v (k + 1)).app U₀ = (v k).app U₀ ∘ₗ (S.φ k).app U₀) :=
    by
      choose v hv using fun k =>
        AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
          q (cd.p ≫ i) K' (S.F k) (F' k) (η k) (hηs k) (hηV k) (hηU k)
      refine ⟨v, hv, fun k U₀ => ?_⟩
      apply LinearMap.ext
      intro x
      apply OModulePresheaf.cechPushforward.ext
      intro jx
      show (((φ' k).cechPushforward (cd.p ≫ i) q K').app U₀ ((v (k + 1)).app U₀ x)).1 jx
        = ((v k).app U₀ ((S.φ k).app U₀ x)).1 jx
      rw [OModulePresheaf.AffHom.coe_cechPushforward_app, hv, hv, hηφ]

  obtain ⟨hGPc, hGPq, Ps, π, ψP, ν, u, hPsc, hPsq, hπs, hπk, hψPs, hψPk, hψPc, hνc, hνψP, hνi, huc, hνu⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper I q (cd.p ≫ i) K' F' φ' G' hG'c hG'q ψ' hψ's hψ'k hψ'c S.F S.φ S.hs S.hk v hvc

  have hZne : Nonempty Z := by
    haveI := irreducibleSpace_subscheme_vanishingIdeal T hTirr
    infer_instance
  have hrange : Set.range i.base = (T : Set P) := by
    show Set.range (idealOf T).subschemeι.base = (T : Set P)
    rw [Scheme.IdealSheafData.range_subschemeι, support_vanishingIdeal]
  obtain ⟨T', hT'lt, hT'⟩ :=
    AlgebraicGeometry.exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
      i T hrange cd.U (cd.hU_dense.nonempty)
  obtain ⟨N, hcoker, hker⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
      I q i cd.p K' cd.U cd.hp_isoU T' hT' S.F S.hc S.hq S.φ S.hs S.hk hSZ F' φ' η hηs hηV hηU hηφ hβ
      G' hG'c hG'q ψ' hψ's hψ'k hψ'c v hvη Ps hPsc hPsq π hπs hπk ψP hψPs hψPk hψPc ν hνc hνψP hνi u huc hνu

  obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, huj, hAR, -, hCc, hCq, hγs, hγk, hθc, hθs, hθk⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I S.F S.hc S.hq S.φ S.hs S.hk Ps hPsc hPsq π hπs hπk u huc

  obtain ⟨GK, ψK, hGKc, hGKq, hψKs, hψKk, hψKc⟩ :=
    ih T' hT'lt N ⟨Ks, hKc, hKq, κ, hκs, hκk⟩
      (AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
        I S.F S.φ S.hs S.hk Ks κ hκs hκk j hjc (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).2⟩)
        Ps u huj (idealOf T') N hker)
  obtain ⟨GC, ψC, hGCc, hGCq, hψCs, hψCk, hψCc⟩ :=
    ih T' hT'lt N ⟨Cs, hCc, hCq, γ, hγs, hγk⟩ (by
      intro k U a ha z
      obtain ⟨y, rfl⟩ := hθs k U z
      obtain ⟨x, hx⟩ := hcoker k U a ha y
      rw [← (θ k).app_smul, ← hx]
      have hmem : (u k).app U x ∈ LinearMap.ker ((θ k).app U) := by
        rw [hθk]; exact LinearMap.mem_range_self _ x
      exact LinearMap.mem_ker.mp hmem)

  obtain ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, huEc, huEr, huEi⟩ :
      ∃ (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k)),
        (∀ k, (E k).IsCoherent) ∧ (∀ k, (E k).IsQuasicoherent) ∧
        (∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((τ k).app W)) ∧
        (∀ (k : ℕ) (W : P.affineOpens),
          LinearMap.ker ((τ k).app W) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj W.1))) ∧
        ∃ ε : ∀ k, OModulePresheaf.AffHom (S.F k) (E k),
        (∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ε k).app W)) ∧
        (∀ (k : ℕ) (W : P.affineOpens), (τ k).app W ∘ₗ (ε (k + 1)).app W = (ε k).app W ∘ₗ (S.φ k).app W) ∧
        (∀ (k : ℕ) (W : P.affineOpens), LinearMap.ker ((ε k).app W) = LinearMap.range ((j k).app W)) ∧
        ∃ uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k),
        (∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (uE (k + 1)).app W = (uE k).app W ∘ₗ (τ k).app W) ∧
        (∀ (k : ℕ) (W : P.affineOpens), LinearMap.range ((uE k).app W) = LinearMap.ker ((θ k).app W)) ∧
        (∀ W : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
          LinearMap.ker ((uE (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj W.1))) :=
    by
      obtain ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, -, huEc, huEr, huEi⟩ :=
        AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
          I S.F S.hc S.hq S.φ S.hs S.hk Ks hKq κ hκs j hjc Ps π u huc huj
          (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).1⟩)
      exact ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, huEc, fun k U => (huEr k U).trans (hθk k U).symm, huEi⟩

  obtain ⟨GE, ψE, hGEc, hGEq, hψEs, hψEk, hψEc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q E hEc hEq τ hτs hτk Ps hPsc hPsq π hπs hπk Cs hCc hCq γ hγs hγk θ hθc uE huEc huEr huEi
      (OModulePresheaf.cechPushforward (cd.p ≫ i) q K' G') hGPc hGPq ψP hψPs hψPk hψPc GC hGCc hGCq ψC hψCs hψCk hψCc

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q S.F S.hc S.hq S.φ S.hs S.hk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc
      GK hGKc hGKq (fun k => (j k).comp (ψK k))
      (by
        intro k U
        show (S.φ k).app U ∘ₗ ((j (k + 1)).app U ∘ₗ (ψK (k + 1)).app U) = (j k).app U ∘ₗ (ψK k).app U
        rw [← LinearMap.comp_assoc, hjc, LinearMap.comp_assoc, hψKc])
      (by
        intro k U
        show LinearMap.range ((j k).app U ∘ₗ (ψK k).app U) = LinearMap.ker ((ε k).app U)
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hψKs k U))]
        exact (hεk k U).symm)
      (by
        intro U
        obtain ⟨c, hc⟩ := hAR U
        refine ⟨c, fun k => ?_⟩
        intro x hx
        have hx' : (ψK (k + c)).app U x ∈ LinearMap.ker ((j (k + c)).app U) := by
          simpa [LinearMap.mem_ker] using hx
        have h1 := (hc k).2 hx'
        have hmap : Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
            = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hψKs (k + c) U)]
        have h2 : x ∈ Submodule.comap ((ψK (k + c)).app U)
            (Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))) := by
          rw [hmap]; exact h1
        rw [Submodule.comap_map_eq, hψKk] at h2
        have hle : I ^ (k + c + 1) • (⊤ : Submodule A (GK.obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact (sup_le le_rfl hle) h2)
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

theorem algebraised_of_killedBy
    (T : Closeds P) (t : ℕ) (S : AdicSys I q) (hS : S.KilledBy (idealOf T) t) : S.Algebraised := by
  haveI : NoetherianSpace P := noetherianSpace_of_isProper q
  induction T using (wellFounded_lt (α := Closeds P)).induction generalizing t S with
  | _ T ih =>

  have h1 : ∀ S : AdicSys I q, S.KilledBy (idealOf T) 1 → S.Algebraised := by
    intro S hS1
    by_cases hirr : IsIrreducible (T : Set P)
    · exact stepC T hirr ih S hS1
    ·
      by_cases hT : (T : Set P) = ∅
      · exact AdicSys.algebraised_of_killedBy_coe_eq_empty S T hT hS1
      ·
        obtain ⟨T₁, T₂, hT₁, hT₂, hT12⟩ : ∃ T₁ T₂ : Closeds P, T₁ < T ∧ T₂ < T ∧ T = T₁ ⊔ T₂ := by
          exact exists_closeds_lt_sup_eq T (Set.nonempty_iff_ne_empty.2 hT) hirr
        refine algebraised_of_quot_of_ker S (idealOf T₁)
          (fun Q hQ => ih T₁ hT₁ 1 Q ((Q.killedBy_one_iff _).2 hQ)) ?_
        intro K j hjc hjr hji
        refine ih T₂ hT₂ 1 K ?_
        exact AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
          I S.F S.φ S.hs S.hk K.F K.φ K.hs K.hk j hjc (idealOf T) (idealOf T₁) (idealOf T₂) 1 1 hjr hji
          (fun U => by rw [hT12]; exact vanishingIdeal_sup_pow_mul_le T₁ T₂ U) hS1

  induction t generalizing S with
  | zero =>
    exact AdicSys.algebraised_of_killedBy_zero S _ hS
  | succ t iht =>
    refine algebraised_of_quot_of_ker S (idealOf T)
      (fun Q hQ => h1 Q ((Q.killedBy_one_iff _).2 hQ)) ?_
    intro K j hjc hjr hji
    refine iht K ?_
    exact AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
      I S.F S.φ S.hs S.hk K.F K.φ K.hs K.hk j hjc (idealOf T) (idealOf T) (idealOf T) (t + 1) t hjr hji
      (fun U => by rw [pow_succ]) hS

end GEDriver

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  haveI : IsNoetherian P := GEDriver.isNoetherian_of_isProper q

  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_ideal_pow_le_of_forall_le_radical
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds P)) ⊥ (GEDriver.vanishingIdeal_top_ideal_le_radical_bot)
  exact GEDriver.algebraised_of_killedBy (I := I) (q := q) ⊤ e ⟨F, hc, hq, φ, hφs, hφk⟩ (by
    intro k U a ha x
    have ha' : a ∈ (⊥ : P.IdealSheafData).ideal U := he U ha
    rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot] at ha'
    rw [ha', zero_smul])

end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub
attribute [-instance] AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val
attribute [-simp] AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.OModulePresheaf

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
attribute [-instance] AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-instance] AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace _root_.AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GraphAlgAux

open _root_.AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

abbrev A (U : X.affineOpens) : Type u := X.presheaf.obj (op U.1)

section MkAffHom

variable {M N : OModulePresheaf f}

def linR (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) : M.obj U.1 →ₗ[R] N.obj U.1 where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
    haveI := M.isScalarTower U.1
    haveI := N.isScalarTower U.1
    change g (r • x) = r • g x
    rw [← algebraMap_smul (A := A U) r x, g.map_smul, algebraMap_smul]

@[scoped simp] theorem linR_apply (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) (x : M.obj U.1) :
    linR U g x = g x := rfl

def mkAffHom (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1)
    (nat : ∀ (U U' : X.affineOpens) (h : U.1 ≤ U'.1) (x : M.obj U'.1), app U (M.res h x) = N.res h (app U' x)) :
    AffHom M N where
  app U := linR U (app U)
  app_smul U a x := (app U).map_smul a x
  naturality h := LinearMap.ext fun x => nat _ _ h x

@[scoped simp] theorem mkAffHom_app (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1) (nat) (U : X.affineOpens)
    (x : M.obj U.1) : (mkAffHom app nat).app U x = app U x := rfl

theorem affHom_ext (a b : AffHom M N) (h : ∀ (W : X.affineOpens) (x : M.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

end MkAffHom

theorem unit_isCoherent : (unit f).IsCoherent := fun U => Module.Finite.self (A U)

theorem unit_isQuasicoherent : (unit f).IsQuasicoherent := by
  intro U r
  haveI := U.2.isLocalization_basicOpen r
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) (show Γ(X, X.basicOpen r) from x)
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, y, ?_⟩
    change (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y =
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ n) * (show Γ(X, X.basicOpen r) from x)
    have e : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) = (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom := rfl
    have hn' : r ^ n = s.1 := hn
    rw [← e, hn', mul_comm]
    exact hs.symm
  · have hy' : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (show Γ(X, U.1) from y) = 0 := hy
    obtain ⟨⟨m, k, hk⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers r) Γ(X, X.basicOpen r) _).mp hy'
    refine ⟨k, ?_⟩
    have hk' : r ^ k = m := hk
    change r ^ k * (show Γ(X, U.1) from y) = 0
    rw [hk']
    exact hm

structure Sys {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R)
  hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))
  tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))
  htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n
  xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1))
  hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n)
  hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n
  Y : ℕ → Scheme.{u}
  g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)
  hg : ∀ n : ℕ, IsFinite (g n)
  yn : ∀ n : ℕ, Y n ⟶ Y (n + 1)
  hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)

variable [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R] [IsProper f] (S : Sys I f)

namespace Sys

abbrev h (n : ℕ) : S.Y n ⟶ X := S.g n ≫ pullback.fst f (S.sR n)

abbrev B (n : ℕ) : OModulePresheaf f := pushforwardUnit f (S.h n)

abbrev BΓ (n : ℕ) (U : X.Opens) : Type u := (S.Y n).presheaf.obj (op ((S.h n) ⁻¹ᵁ U))

abbrev bapp (n : ℕ) (U : X.Opens) : Γ(X, U) →+* S.BΓ n U := ((S.h n).appLE U ((S.h n) ⁻¹ᵁ U) le_rfl).hom

theorem yn_comp_h (n : ℕ) : S.yn n ≫ S.h (n + 1) = S.h n := by
  change S.yn n ≫ S.g (n + 1) ≫ pullback.fst f (S.sR (n + 1)) = S.g n ≫ pullback.fst f (S.sR n)
  rw [← Category.assoc, (S.hY n).w, Category.assoc, S.hxn₁]

theorem pre_le (n : ℕ) (U : X.Opens) : (S.h n) ⁻¹ᵁ U ≤ (S.yn n) ⁻¹ᵁ ((S.h (n + 1)) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, S.yn_comp_h]

abbrev ynapp (n : ℕ) (U : X.Opens) : S.BΓ (n + 1) U →+* S.BΓ n U :=
  ((S.yn n).appLE ((S.h (n + 1)) ⁻¹ᵁ U) ((S.h n) ⁻¹ᵁ U) (S.pre_le n U)).hom

scoped instance isFinite_g (n : ℕ) : IsFinite (S.g n) := S.hg n

theorem B_smul (n : ℕ) (U : X.Opens) (a : Γ(X, U)) (z : (S.B n).obj U) :
    (a • z : (S.B n).obj U) = (show (S.B n).obj U from S.bapp n U a * (show S.BΓ n U from z)) := rfl

theorem B_res (n : ℕ) {U U' : X.Opens} (hU : U ≤ U') (z : (S.B n).obj U') :
    ((S.B n).res hU z : S.BΓ n U) =
      ((S.Y n).presheaf.map (homOfLE ((Opens.map (S.h n).base).monotone hU)).op).hom (show S.BΓ n U' from z) := rfl

theorem B_coh_qc (n : ℕ) : (S.B n).IsCoherent ∧ (S.B n).IsQuasicoherent :=
  (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
    R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).1 n

theorem B_coh (n : ℕ) : (S.B n).IsCoherent := (S.B_coh_qc n).1
theorem B_qc (n : ℕ) : (S.B n).IsQuasicoherent := (S.B_coh_qc n).2

theorem exists_τ : ∃ τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n),
    (∀ (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1),
      (τ n).app U z = (show (S.B n).obj U.1 from S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z))) ∧
    (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
    (∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((τ n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((S.B (n + 1)).obj U.1))) := by
  obtain ⟨τ, hτ, hs, hk⟩ :=
    (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
      R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).2.2
  exact ⟨τ, hτ, hs, hk⟩

def τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n) := S.exists_τ.choose

theorem τ_app (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1) :
    ((S.τ n).app U z : S.BΓ n U.1) = S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z) :=
  S.exists_τ.choose_spec.1 n U z

theorem τ_surj (n : ℕ) (U : X.affineOpens) : Function.Surjective ((S.τ n).app U) :=
  S.exists_τ.choose_spec.2.1 n U

theorem τ_ker (n : ℕ) (U : X.affineOpens) :
    LinearMap.ker ((S.τ n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((S.B (n + 1)).obj U.1)) :=
  S.exists_τ.choose_spec.2.2 n U

def u (n : ℕ) : AffHom (unit f) (S.B n) :=
  mkAffHom
    (fun U =>
      { toFun := fun a => show (S.B n).obj U.1 from S.bapp n U.1 (show A U from a)
        map_add' := fun a b => map_add _ _ _
        map_smul' := fun a b => by
          change S.bapp n U.1 (a * (show A U from b)) = a • (show (S.B n).obj U.1 from S.bapp n U.1 (show A U from b))
          rw [B_smul, map_mul] })
    (fun U U' hU a => by
      change S.bapp n U.1 ((X.presheaf.map (homOfLE hU).op).hom a) =
        (S.B n).res hU (show (S.B n).obj U'.1 from S.bapp n U'.1 a)
      rw [B_res, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map])

theorem u_app (n : ℕ) (U : X.affineOpens) (a : A U) :
    ((S.u n).app U (show (unit f).obj U.1 from a) : S.BΓ n U.1) = S.bapp n U.1 a := rfl

theorem ynapp_bapp (n : ℕ) (U : X.Opens) (a : Γ(X, U)) : S.ynapp n U (S.bapp (n + 1) U a) = S.bapp n U a := by
  change ((S.h (n + 1)).appLE U _ le_rfl ≫ (S.yn n).appLE _ _ (S.pre_le n U)).hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (k : S.Y n ⟶ X) (hk : k = S.h n) (e : (S.h n) ⁻¹ᵁ U ≤ k ⁻¹ᵁ U),
      (k.appLE U ((S.h n) ⁻¹ᵁ U) e).hom a = S.bapp n U a := by
    rintro k rfl e; rfl
  exact key _ (S.yn_comp_h n) _

theorem hτu (n : ℕ) : (S.τ n).comp (S.u (n + 1)) = S.u n :=
  affHom_ext _ _ fun U a => by
    rw [AffHom.comp_app]
    exact (S.τ_app n U _).trans (S.ynapp_bapp n U.1 a)

theorem k42 (F : OModulePresheaf f) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (ρ : ∀ n : ℕ, AffHom F (S.B n))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hτρ : ∀ n : ℕ, (S.τ n).comp (ρ (n + 1)) = ρ n)
    (M : OModulePresheaf f) (hMc : M.IsCoherent) (hMq : M.IsQuasicoherent)
    (ψ : ∀ n : ℕ, AffHom M (S.B n)) (hψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : AffHom M F, (∀ n : ℕ, (ρ n).comp φ = ψ n) ∧
      ∀ φ' : AffHom M F, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ :=
  AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I f M F hMc hMq
    hFc hFq S.B S.τ ρ hρs hρk hτρ ψ hψ

end Sys
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys"

section IdealLemmas

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

theorem comap_map_of_isClosedImmersion {Z W : Scheme.{u}} (ι : Z ⟶ W) [IsClosedImmersion ι]
    (K : Z.IdealSheafData) : (K.map ι).comap ι = K := by
  have h1 : K.map ι = (K.subschemeι ≫ ι).ker := by
    rw [← Scheme.IdealSheafData.map_ker, ker_subschemeι]
  rw [h1, ← ker_fst_of_isClosedImmersion]
  have h2 : pullback.fst ι (K.subschemeι ≫ ι) = pullback.snd ι (K.subschemeι ≫ ι) ≫ K.subschemeι := by
    rw [← cancel_mono ι, Category.assoc, pullback.condition]
  rw [h2, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

theorem comap_sup_ker {Z W : Scheme.{u}} (ι : Z ⟶ W) (J : W.IdealSheafData) :
    (J ⊔ ι.ker).comap ι = J.comap ι := by
  have h : ι.ker.comap ι = ⊥ :=
    le_bot_iff.mp (by rw [← Scheme.IdealSheafData.map_bot]; exact comap_map_le _ _)
  rw [Scheme.IdealSheafData.comap_sup, h, sup_bot_eq]

end IdealLemmas
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys"

theorem appLE_ΓSpecIso_inv_eq_zero {Zn : Scheme.{u}} (𝔞 : Ideal R) (t : Zn ⟶ Spec (.of (R ⧸ 𝔞)))
    (W : Zn.Opens) (r : R) (hr : r ∈ 𝔞)
    (k : Zn ⟶ Spec (.of R)) (hk : k = t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))
    (e : W ≤ k ⁻¹ᵁ ⊤) :
    (k.appLE ⊤ W e).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) = 0 := by
  subst hk
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top, CommRingCat.comp_apply]
  have : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (.of (R ⧸ 𝔞))).inv.hom (Ideal.Quotient.mk 𝔞 r) := by
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).appTop).hom r = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [this, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]

end GraphAlgAux
p2m_reactivate "ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux"

open GraphAlgAux _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (Jn : ∀ n : ℕ, (adicThickening p I n).IdealSheafData)
    (hJn : ∀ n : ℕ, (Jn (n + 1)).comap (adicThickeningTransition p I n) = Jn n) :
    ∃ J : P.IdealSheafData, ∀ n : ℕ, J.comap (adicThickeningι p I n) = Jn n := by

  have Hle : ∀ n : ℕ, Jn (n + 1) ≤ (Jn n).map (adicThickeningTransition p I n) := fun n =>
    le_map_iff_comap_le.mpr (hJn n).le
  let S : Sys I p :=
    { sR := fun n => adicThickeningBase I n
      hsR := fun n => rfl
      tR := fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))
      htR := fun n => adicThickeningBase_succ_comp I n
      xn := fun n => adicThickeningTransition p I n
      hxn₁ := fun n => adicThickeningTransition_ι p I n
      hxn₂ := fun n => adicThickeningTransition_toBase p I n
      Y := fun n => (Jn n).subscheme
      g := fun n => (Jn n).subschemeι
      hg := fun n => (inferInstance : IsFinite (Jn n).subschemeι)
      yn := fun n => subschemeMap (Jn n) (Jn (n + 1)) (adicThickeningTransition p I n) (Hle n)
      hY := fun n => (isPullback_of_isClosedImmersion (Jn n).subschemeι (Jn (n + 1)).subschemeι
        (subschemeMap (Jn n) (Jn (n + 1)) (adicThickeningTransition p I n) (Hle n))
        (adicThickeningTransition p I n) (by rw [subschemeMap_subschemeι])
        (by rw [ker_subschemeι, ker_subschemeι, hJn])).flip }

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
      I p S.B S.B_coh S.B_qc S.τ S.τ_surj S.τ_ker
  have hτψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n := fun n =>
    affHom_ext _ _ fun U x => by
      rw [AffHom.comp_app]
      exact congrFun (congrArg DFunLike.coe (hψc n U)) x

  obtain ⟨η, hη, -⟩ := S.k42 G hGc hGq ψ hψs hψk hτψ (unit p) unit_isCoherent unit_isQuasicoherent S.u S.hτu

  have hbapp : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective (S.bapp n U.1) := fun n U => by
    haveI : IsClosedImmersion (S.h n) :=
      (inferInstance : IsClosedImmersion ((Jn n).subschemeι ≫ adicThickeningι p I n))
    have e : (S.h n).app U.1 = (S.h n).appLE U.1 _ le_rfl := Scheme.Hom.app_eq_appLE _
    have := (S.h n).app_surjective U.1 U.2
    rw [e] at this
    exact this
  have hηs : ∀ U : P.affineOpens, Function.Surjective (η.app U) := fun U =>
    AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
      I (IsAdicComplete.le_jacobson_bot I) unit_isQuasicoherent hGc hGq η (fun U => by
        refine eq_top_iff.mpr fun m _ => ?_
        obtain ⟨a, ha⟩ := hbapp 0 U ((ψ 0).app U m : S.BΓ 0 U.1)
        have h1 : (ψ 0).app U (η.app U (show (unit p).obj U.1 from a)) = (ψ 0).app U m := by
          have := congrArg (fun θ : AffHom (unit p) (S.B 0) => θ.app U (show (unit p).obj U.1 from a)) (hη 0)
          dsimp only at this
          rw [AffHom.comp_app] at this
          rw [this]
          exact ha
        have h2 : m - η.app U (show (unit p).obj U.1 from a) ∈ LinearMap.ker ((ψ 0).app U) := by
          rw [LinearMap.mem_ker, map_sub, h1, sub_self]
        rw [hψk 0 U, pow_one] at h2
        have : m = η.app U (show (unit p).obj U.1 from a) + (m - η.app U (show (unit p).obj U.1 from a)) := by
          abel
        rw [this]
        exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) h2) U

  have hnat : ∀ (U U' : P.affineOpens) (hU : U.1 ≤ U'.1) (a : Γ(P, U'.1)),
      η.app U (show (unit p).obj U.1 from (P.presheaf.map (homOfLE hU).op).hom a) =
        G.res hU (η.app U' (show (unit p).obj U'.1 from a)) := fun U U' hU a =>
    η.naturality_apply (U := U) (U' := U') hU _
  have hmul : ∀ (U : P.affineOpens) (a b : Γ(P, U.1)),
      η.app U (show (unit p).obj U.1 from a * b) = a • η.app U (show (unit p).obj U.1 from b) := fun U a b =>
    η.app_smul U a (show (unit p).obj U.1 from b)
  let Jideal : ∀ U : P.affineOpens, Ideal Γ(P, U.1) := fun U =>
    { carrier := {a | η.app U (show (unit p).obj U.1 from a) = 0}
      add_mem' := fun {a b} ha hb => by
        change η.app U (show (unit p).obj U.1 from a + b) = 0
        rw [show (show (unit p).obj U.1 from a + b) = (show (unit p).obj U.1 from a) + (show (unit p).obj U.1 from b)
          from rfl, map_add]
        rw [Set.mem_setOf_eq] at ha hb
        rw [ha, hb, add_zero]
      zero_mem' := map_zero (η.app U)
      smul_mem' := fun a b hb => by
        rw [Set.mem_setOf_eq] at hb ⊢
        rw [smul_eq_mul, hmul, hb, smul_zero] }
  have hJmem : ∀ (U : P.affineOpens) (a : Γ(P, U.1)),
      a ∈ Jideal U ↔ η.app U (show (unit p).obj U.1 from a) = 0 := fun U a => Iff.rfl
  have hJbasic : ∀ (U : P.affineOpens) (r : Γ(P, U.1)),
      (Jideal U).map (P.presheaf.map (homOfLE <| P.basicOpen_le r).op).hom = Jideal (P.affineBasicOpen r) := by
    intro U r
    haveI := U.2.isLocalization_basicOpen r
    have eρ : algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) = (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom := rfl
    apply le_antisymm
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap]
      refine (hJmem (P.affineBasicOpen r) _).mpr ?_
      rw [hJmem] at ha
      exact (hnat (P.affineBasicOpen r) U (P.basicOpen_le r) a).trans (by rw [ha, map_zero])
    · intro x hx
      replace hx := (hJmem (P.affineBasicOpen r) x).mp hx
      obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) x
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
      simp only at hs hn

      have hy0 : η.app (P.affineBasicOpen r)
          (show (unit p).obj (P.basicOpen r) from algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) y) = 0 := by
        rw [← hs, mul_comm]
        exact (hmul (P.affineBasicOpen r) _ x).trans (by rw [hx, smul_zero])
      have hy1 : G.res (P.basicOpen_le r) (η.app U (show (unit p).obj U.1 from y)) = 0 :=
        (hnat (P.affineBasicOpen r) U (P.basicOpen_le r) y).symm.trans hy0
      obtain ⟨k, hk⟩ := (hGq U r).2 _ hy1

      have hmem : r ^ k * y ∈ Jideal U := by rw [hJmem, hmul]; exact hk
      have hunit : IsUnit (algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * (s : Γ(P, U.1)))) :=
        IsLocalization.map_units (M := Submonoid.powers r) _
          ⟨r ^ k * (s : Γ(P, U.1)), (Submonoid.mem_powers_iff _ _).mpr ⟨k + n, by rw [pow_add, hn]⟩⟩
      obtain ⟨v, hv⟩ := hunit.exists_left_inv
      have hx' : x = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * y) := by
        calc x = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * (s : Γ(P, U.1))) * x := by
                rw [hv, one_mul]
          _ = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * y) := by
                rw [map_mul, map_mul, mul_assoc, mul_assoc, ← hs, mul_comm x]
      rw [hx', eρ]
      exact Ideal.mul_mem_left _ v (Ideal.mem_map_of_mem _ hmem)
  let J : P.IdealSheafData := ⟨Jideal, hJbasic, _, rfl⟩
  have hJideal : ∀ U : P.affineOpens, J.ideal U = Jideal U := fun U => rfl
  refine ⟨J, fun n => ?_⟩

  haveI : IsClosedImmersion (S.h n) :=
    (inferInstance : IsClosedImmersion ((Jn n).subschemeι ≫ adicThickeningι p I n))
  have step3 : J ⊔ (adicThickeningι p I n).ker = (Jn n).map (adicThickeningι p I n) := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, hJideal, Scheme.Hom.ker_apply, ideal_map_of_isAffineHom]

    have hJn : (Jn n).ideal ⟨_, U.2.preimage (adicThickeningι p I n)⟩ =
        RingHom.ker ((Jn n).subschemeι.app ((adicThickeningι p I n) ⁻¹ᵁ U.1)).hom := by
      conv_lhs => rw [← ker_subschemeι (Jn n)]
      rw [Scheme.Hom.ker_apply]
    have hcomp : ∀ a : Γ(P, U.1), ((Jn n).subschemeι.app ((adicThickeningι p I n) ⁻¹ᵁ U.1)).hom
        (((adicThickeningι p I n).app U.1).hom a) = S.bapp n U.1 a := by
      intro a
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_app]
      change ((S.h n).app U.1).hom a = _
      rw [Scheme.Hom.app_eq_appLE]

    have hR : ∀ a : Γ(P, U.1), a ∈ ((Jn n).ideal ⟨_, U.2.preimage (adicThickeningι p I n)⟩).comap
        ((adicThickeningι p I n).app U.1).hom ↔
        η.app U (show (unit p).obj U.1 from a) ∈ I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)) := by
      intro a
      rw [Ideal.mem_comap, hJn, RingHom.mem_ker, hcomp, ← hψk n U, LinearMap.mem_ker]
      have := congrArg (fun θ : AffHom (unit p) (S.B n) => θ.app U (show (unit p).obj U.1 from a)) (hη n)
      dsimp only at this
      rw [AffHom.comp_app] at this
      rw [this]
      exact Iff.rfl
    apply le_antisymm
    · refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [hR]; rw [hJmem] at ha; rw [ha]; exact Submodule.zero_mem _
      · rw [Ideal.mem_comap, hJn, RingHom.mem_ker]
        rw [RingHom.mem_ker] at ha
        rw [ha, map_zero]
    · intro a ha
      rw [hR] at ha

      have hrange : (I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1))) =
          (I ^ (n + 1) • (⊤ : Submodule R ((unit p).obj U.1))).map (η.app U) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hηs U)]
      rw [hrange] at ha
      obtain ⟨b, hb, hηb⟩ := ha
      have hab : (show Γ(P, U.1) from a) - (show Γ(P, U.1) from b) ∈ Jideal U := by
        rw [hJmem]
        change η.app U ((show (unit p).obj U.1 from a) - b) = 0
        rw [map_sub, hηb, sub_self]
      have hbker : (show Γ(P, U.1) from b) ∈ RingHom.ker ((adicThickeningι p I n).app U.1).hom := by
        refine Submodule.smul_induction_on hb (fun r hr c _ => ?_) (fun x y hx hy => ?_)
        · rw [RingHom.mem_ker]
          letI := Scheme.TwoAffineOpenCover.algebraOfHom p U.1
          letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι p I n ≫ p) ((adicThickeningι p I n) ⁻¹ᵁ U.1)
          change ((adicThickeningι p I n).app U.1).hom (algebraMap R Γ(P, U.1) r * (show Γ(P, U.1) from c)) = 0
          rw [map_mul, Scheme.Hom.app_eq_appLE, appLE_algebraMap]
          rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
            appLE_ΓSpecIso_inv_eq_zero (I ^ (n + 1)) (adicThickeningToBase p I n) _ r hr _
              (adicThickeningι_comp p I n), zero_mul]
        · exact Ideal.add_mem _ hx hy
      have : a = ((show Γ(P, U.1) from a) - (show Γ(P, U.1) from b)) + (show Γ(P, U.1) from b) := by
        change a = a - _ + _; abel
      rw [this]
      exact Submodule.add_mem_sup hab hbker
  calc J.comap (adicThickeningι p I n)
      = (J ⊔ (adicThickeningι p I n).ker).comap (adicThickeningι p I n) := (comap_sup_ker _ J).symm
    _ = ((Jn n).map (adicThickeningι p I n)).comap (adicThickeningι p I n) := by rw [step3]
    _ = Jn n := comap_map_of_isClosedImmersion _ _

end
end P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open _root_.AlgebraicGeometry hiding OModulePresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (Jn : ∀ n : ℕ, (adicThickening p I n).IdealSheafData)
    (hJn : ∀ n : ℕ, (Jn (n + 1)).comap (adicThickeningTransition p I n) = Jn n) :
    ∃ J : P.IdealSheafData, ∀ n : ℕ, J.comap (adicThickeningι p I n) = Jn n := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry

/- Adapted source: P2M.Sol.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
namespace P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsProper g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) :
    ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by

  have hgr : ∀ n : ℕ, adicThickeningι f I n ≫ f = (φ n ≫ adicThickeningι g I n) ≫ g := by
    intro n
    rw [adicThickeningι_comp, Category.assoc, adicThickeningι_comp, ← Category.assoc, hφ n]
  have hgrp : ∀ n : ℕ, pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n) ≫ (pullback.fst f g ≫ f) =
      adicThickeningToBase f I n ≫ adicThickeningBase I n := by
    intro n
    rw [← Category.assoc, pullback.lift_fst, adicThickeningι_comp]
  obtain ⟨γ, hγdef⟩ : ∃ γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n, ∀ n, γ n =
      pullback.lift (pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n)) (adicThickeningToBase f I n) (hgrp n) :=
    ⟨_, fun n => rfl⟩
  have hγ0 : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n =
      pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n) := fun n => by
    rw [hγdef]; exact pullback.lift_fst _ _ _
  have hγ₁ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n := by
    intro n
    rw [← Category.assoc, hγ0, pullback.lift_fst]
  have hγ₂ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g = φ n ≫ adicThickeningι g I n := by
    intro n
    rw [← Category.assoc, hγ0, pullback.lift_snd]
  have hGK := AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph I f g φ hφ hφt γ hγ₁ hγ₂

  obtain ⟨J, hJ⟩ := AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isProper I
    (pullback.fst f g ≫ f) (fun n => (γ n).ker) (fun n => (hGK n).2)

  have hζw : ∀ n : ℕ, (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g) ≫ f =
      adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ adicThickeningBase I n := by
    intro n
    rw [Category.assoc, Category.assoc, adicThickeningι_comp]
  let ζ : ∀ n : ℕ, adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening f I n := fun n =>
    pullback.lift (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g)
      (adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n) (hζw n)
  have hζ : ∀ n : ℕ, ζ n ≫ adicThickeningι f I n =
      adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g := fun n => by
    rw [adicThickeningι_def]; exact pullback.lift_fst _ _ _
  have hζ' : ∀ n : ℕ, ζ n ≫ adicThickeningToBase f I n = adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n := fun n => by
    rw [adicThickeningToBase_def]; exact pullback.lift_snd _ _ _
  have hGT := fun n : ℕ => AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq I f g J γ
    (fun n => (hGK n).1) hJ hγ₁ n (ζ n) (hζ n)

  have hiso : IsIso (J.subschemeι ≫ pullback.fst f g) := by
    apply AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
      R I f (J.subschemeι ≫ pullback.fst f g) (adicThickeningBase I) (fun _ => rfl)
    intro n
    let e := J.subschemeι ≫ pullback.fst f g
    have t : IsPullback (adicThickeningToBase f I n) (adicThickeningι f I n)
        (adicThickeningBase I n) f := (IsPullback.of_hasPullback _ _).flip
    have s : IsPullback (ζ n ≫ adicThickeningToBase f I n)
        (adicThickeningι (e ≫ f) I n) (adicThickeningBase I n) (e ≫ f) := by
      rw [hζ']; exact (IsPullback.of_hasPullback _ _).flip
    have hp := (IsPullback.of_right s (hζ n) t).flip
    haveI : IsIso (ζ n) := (hGT n).1
    change IsIso (pullback.snd e (adicThickeningι f I n))
    rw [← hp.isoPullback_inv_snd]
    infer_instance

  refine ⟨inv (J.subschemeι ≫ pullback.fst f g) ≫ J.subschemeι ≫ pullback.snd f g, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (J.subschemeι), IsIso.inv_hom_id_assoc]
  · intro n
    haveI := (hGT n).1
    have e1 : adicThickeningι f I n = inv (ζ n) ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫
        (J.subschemeι ≫ pullback.fst f g) := by
      rw [IsIso.eq_inv_comp, hζ n]
    rw [e1, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc (adicThickeningι _ I n), (hGT n).2,
      Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hγ₂ n]
  · rintro ψ' ⟨hψ'g, hψ'n⟩
    apply AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete R I f g (adicThickeningBase I) (fun _ => rfl) ψ' _ hψ'g
    · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (J.subschemeι), IsIso.inv_hom_id_assoc]
    · intro n
      haveI := (hGT n).1
      have e1 : adicThickeningι f I n = inv (ζ n) ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫
          (J.subschemeι ≫ pullback.fst f g) := by
        rw [IsIso.eq_inv_comp, hζ n]
      change adicThickeningι f I n ≫ ψ' = adicThickeningι f I n ≫ _
      rw [hψ'n n]
      conv_rhs => rw [e1, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc (adicThickeningι _ I n), (hGT n).2,
        Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hγ₂ n]

end P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity


/- Adapted source: Theorems.Thm_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj. -/
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
section
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open _root_.AlgebraicGeometry 

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsProper g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) :
    ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by p2m_exact_reverting @_root_.ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj.solution


end
end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity
open ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry

noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- Formal restrictions determine a morphism from the whole proper model. -/
theorem hom_ext (M : Model k T) (hM : IsModel k T M)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (PowerSeries k))) [IsSeparated p]
    {f f' : M.X ⟶ Y} (hf : f ≫ p = M.p) (hf' : f' ≫ p = M.p)
    (h : ∀ n, M.inclusion n ≫ f = M.inclusion n ≫ f') : f = f' := by
  letI : IsProper M.p := hM.1
  apply AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
    (PowerSeries k) (Ideal.span {PowerSeries.X}) M.p p
    (baseInclusion k) (fun _ => rfl) f f' hf hf'
  intro n
  rw [← (hM.2.2.1 n).isoPullback_inv_fst]
  simp only [Category.assoc, h n]

/-- Inverses of a compatible family remain compatible over the same base. -/
theorem compatible_symm (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X)
    (hg : CompatibleAutos k T g) : CompatibleAutos k T (fun n => (g n).symm) := by
  constructor
  · intro n
    change (g n).inv ≫ (T.atlas n).p = (T.atlas n).p
    rw [Iso.inv_comp_eq]
    exact (hg.1 n).symm
  · intro n N h
    change T.transition n N h ≫ (g N).inv = (g n).inv ≫ T.transition n N h
    apply (cancel_epi (g n).hom).mp
    apply (cancel_mono (g N).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using (hg.2 n N h).symm

/-- There is at most one automorphism with the prescribed restrictions. -/
theorem algebraizes_unique (M : Model k T) (hM : IsModel k T M)
    {g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X} {f f' : M.X ≅ M.X}
    (hf : Algebraizes k M g f) (hf' : Algebraizes k M g f') : f = f' := by
  letI : IsProper M.p := hM.1
  apply Iso.ext
  exact hom_ext k M hM M.p hf.1 hf'.1 (fun n => (hf.2 n).trans (hf'.2 n).symm)

/-- Transport the given stage automorphisms through the actual cartesian
squares and algebraize their graphs on the proper model. -/
theorem hom_effectivity (M : Model k T) (hM : IsModel k T M)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) (hg : CompatibleAutos k T g) :
    ∃ F : M.X ⟶ M.X, F ≫ M.p = M.p ∧
      ∀ n, M.inclusion n ≫ F = (g n).hom ≫ M.inclusion n := by
  letI : IsProper M.p := hM.1
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  let e (n : ℕ) : (T.atlas n).X ≅ adicThickening M.p I n :=
    (hM.2.2.1 n).isoPullback
  have he₁ (n : ℕ) : (e n).hom ≫ adicThickeningι M.p I n = M.inclusion n :=
    (hM.2.2.1 n).isoPullback_hom_fst
  have he₂ (n : ℕ) : (e n).hom ≫ adicThickeningToBase M.p I n = (T.atlas n).p :=
    (hM.2.2.1 n).isoPullback_hom_snd
  have hei₂ (n : ℕ) : (e n).inv ≫ (T.atlas n).p = adicThickeningToBase M.p I n :=
    (hM.2.2.1 n).isoPullback_inv_snd
  have het (n : ℕ) : T.transition n (n+1) (Nat.le_succ n) ≫ (e (n+1)).hom =
      (e n).hom ≫ adicThickeningTransition M.p I n := by
    apply pullback.hom_ext
    · change _ ≫ adicThickeningι M.p I (n+1) = _ ≫ adicThickeningι M.p I (n+1)
      rw [Category.assoc, he₁, hM.2.2.2, Category.assoc, adicThickeningTransition_ι, he₁]
    · change _ ≫ adicThickeningToBase M.p I (n+1) = _ ≫ adicThickeningToBase M.p I (n+1)
      rw [Category.assoc, he₂, (T.transition_spec n (n+1) (Nat.le_succ n)).1,
        Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, he₂]
      rfl
  let φ (n : ℕ) : adicThickening M.p I n ⟶ adicThickening M.p I n :=
    (e n).inv ≫ (g n).hom ≫ (e n).hom
  have hφ (n : ℕ) : φ n ≫ adicThickeningToBase M.p I n = adicThickeningToBase M.p I n := by
    simp only [φ, Category.assoc, he₂, hg.1, hei₂]
  have hφt (n : ℕ) : adicThickeningTransition M.p I n ≫ φ (n+1) =
      φ n ≫ adicThickeningTransition M.p I n := by
    apply (cancel_epi (e n).hom).mp
    dsimp only [φ]
    rw [← Category.assoc, ← het]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← het]
    rw [← Category.assoc, hg.2 n (n+1) (Nat.le_succ n), Category.assoc]
  obtain ⟨F, hF, -⟩ :=
    CoherentEffectivity.AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
      I M.p M.p φ hφ hφt
  refine ⟨F, hF.1, fun n => ?_⟩
  rw [← he₁ n, Category.assoc, hF.2 n]
  simp only [φ, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Algebraizing a family and its inverse gives inverse morphisms on the
whole model, by proper adic faithfulness. -/
theorem exists_unique_algebraizes (M : Model k T) (hM : IsModel k T M)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) (hg : CompatibleAutos k T g) :
    ∃! f : M.X ≅ M.X, Algebraizes k M g f := by
  letI : IsProper M.p := hM.1
  obtain ⟨F, hFp, hF⟩ := hom_effectivity k M hM g hg
  obtain ⟨G, hGp, hG⟩ := hom_effectivity k M hM (fun n => (g n).symm) (compatible_symm k g hg)
  have hFG : F ≫ G = 𝟙 M.X := by
    apply hom_ext k M hM M.p (by rw [Category.assoc, hGp, hFp]) (Category.id_comp _)
    intro n
    rw [← Category.assoc, hF, Category.assoc, hG]
    simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, Category.comp_id]
  have hGF : G ≫ F = 𝟙 M.X := by
    apply hom_ext k M hM M.p (by rw [Category.assoc, hFp, hGp]) (Category.id_comp _)
    intro n
    rw [← Category.assoc, hG, Category.assoc, hF]
    simp only [Iso.symm_hom, Iso.inv_hom_id_assoc, Category.comp_id]
  let f : M.X ≅ M.X := ⟨F, G, hFG, hGF⟩
  have hf : Algebraizes k M g f := ⟨hFp, hF⟩
  exact ⟨f, hf, fun f' hf' => algebraizes_unique k M hM hf' hf⟩

end ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137

namespace ArithmeticThetaModelSymmetriesR0137
open CategoryTheory AlgebraicGeometry

/-- Every compatible family of stage automorphisms algebraizes uniquely on
every proper-flat model of the specified polygon tower. -/
theorem proper_tower_automorphism_effectivity :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
    ∀ (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T),
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
    ∀ (g : ∀ n : ℕ, (T.atlas n).X ≅ (T.atlas n).X),
    CompatibleAutos k T g → ∃! f : M.X ≅ M.X, Algebraizes k M g f := by
  intro k _ _ r hr _ T M hM g hg
  exact ProperTowerAutomorphismEffectivityR0137.exists_unique_algebraizes k M hM g hg

end ArithmeticThetaModelSymmetriesR0137

#print axioms ArithmeticThetaModelSymmetriesR0137.proper_tower_automorphism_effectivity
