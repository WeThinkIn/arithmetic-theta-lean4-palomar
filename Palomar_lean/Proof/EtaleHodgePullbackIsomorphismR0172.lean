module

public import RelativeIsogenyHodgeDefinitionsR0172

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaPullback

namespace ArithmeticThetaRelativeIsogenyHodgeR0172
namespace EtaleHodgePullbackIsomorphismR0172
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension.OmegaPullBCGC7
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull

/-- The actual top-form map of an étale morphism over the same affine base is
invertible. Affine neighborhoods are chosen in the source; no Cartesian square
with the base is asserted. -/
theorem topMap_isIso_etale {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of A))
    (φ : X ⟶ Y) (h : φ ≫ gY = gX) (d : ℕ)
    [Etale φ] [SmoothOfRelativeDimension d gY] :
    IsIso (θ gY gX φ (by simpa using h) d) := by
  classical
  let hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A A)) := by simpa using h
  let t := θ gY gX φ hφ d
  have key : ∀ x : X, ∃ (V : X.Opens)
      (p : Γ((Scheme.Modules.pullback φ).obj (gY.topDifferentials d), V)),
      x ∈ V ∧ Scheme.Modules.IsFrameOn p V ∧ Scheme.Modules.IsFrameOn (t.app V p) V := by
    intro x
    obtain ⟨U₀, hyU₀, e, he⟩ :=
      Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension gY d (φ.base x)
    obtain ⟨U, hU, hyU, hUU₀⟩ := exists_affineOpen_le U₀ (φ.base x) hyU₀
    letI := gY.sectionsAlgebra U
    obtain ⟨bU, hbU⟩ := he U hUU₀ hU
    let κU := LinearEquiv.ofBijective (gY.kaehlerToSectionsₗ U)
      (Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen gY hU)
    let η : Module.Basis (Fin d) Γ(Y, U) (Ω[Γ(Y, U)⁄A]) := bU.map κU.symm
    have hs : Scheme.Modules.IsFrameOn
        (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η)) U := by
      refine Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
        gY d hU η fun W hW hWaff => ?_
      intro
      exact Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
        gY hU hWaff hW (ι := Fin d) η
    have hp := Scheme.Modules.IsFrameOn.pullbackLocalSection φ hs
    obtain ⟨V, hV, hxV, hVU⟩ := exists_affineOpen_le (φ ⁻¹ᵁ U) x hyU
    letI := gX.sectionsAlgebra V
    letI : Algebra Γ(Y, U) Γ(X, V) := (φ.appLE U V hVU).hom.toAlgebra
    haveI : IsScalarTower A Γ(Y, U) Γ(X, V) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gX.appLE ⊤ V le_top).hom a =
        (φ.appLE U V hVU).hom
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top).hom a)
      rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE,
        appLE_congr' h]
    haveI : Algebra.Etale Γ(Y, U) Γ(X, V) := φ.etale_appLE hU hV hVU
    let η' : Fin d → Ω[Γ(X, V)⁄A] := fun i =>
      KaehlerDifferential.map A A Γ(Y, U) Γ(X, V) (η i)
    let ηV : Module.Basis (Fin d) Γ(X, V) (Ω[Γ(X, V)⁄A]) :=
      (Algebra.TensorProduct.basis Γ(X, V) η).map
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A Γ(Y, U) Γ(X, V))
    have hηV : ∀ i, ηV i = η' i := by
      intro i
      simp only [ηV, η', Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
        KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul, one_smul]
    let p := ((Scheme.Modules.pullback φ).obj (gY.topDifferentials d)).presheaf.map
      (homOfLE hVU).op (Scheme.Modules.pullbackLocalSection φ
        (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η)))
    have htp : t.app V p = gX.topToSections d V (exteriorPower.ιMulti Γ(X, V) d η') := by
      have hn := ConcreteCategory.congr_hom
        ((t.mapPresheaf).naturality (homOfLE hVU).op)
        (Scheme.Modules.pullbackLocalSection φ
          (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η)))
      change t.app V p = _ at hn
      rw [hn]
      change (gX.topDifferentials d).presheaf.map (homOfLE hVU).op
        ((θ gY gX φ hφ d).app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ
          (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η)))) = _
      rw [topMap_local_formula gY gX φ hφ d U hU V hV hVU]
      apply congrArg (gX.topToSections d V)
      exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
        (NeronModelInfra.TopFormOrder.ιMultiAlong A A Γ(Y, U) Γ(X, V) d) η
    refine ⟨V, p, hxV, (hp.map (homOfLE hVU)).mono hVU, ?_⟩
    rw [htp]
    refine Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
      gX d hV η' fun W hW hWaff => ?_
    intro
    obtain ⟨b, hb⟩ := Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
      gX hV hWaff hW (ι := Fin d) ηV
    exact ⟨b, fun i => by rw [hb i, hηV i]⟩
  choose V p hV using key
  exact Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top t V
    (top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, (hV x).1⟩)
    p (fun x => t.app (V x) (p x))
    (fun x => (hV x).2.1) (fun x => (hV x).2.2) (fun x => rfl)

/-- The universal relative differential is the degree-one comparison. -/
theorem differentialMap_isIso_etale {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of A))
    (φ : X ⟶ Y) (h : φ ≫ gY = gX)
    [Etale φ] [SmoothOfRelativeDimension 1 gY] :
    IsIso (differentialMap gY gX φ (by simpa using h)) := by
  letI := topMap_isIso_etale gY gX φ h 1
  rw [differentialMap_eq_topMap]
  infer_instance

theorem tensorMap_isIso {X : Scheme.{u}} {H K : X.Modules}
    (f : H ⟶ K) [IsIso f] (n : ℕ) : IsIso (tensorMap f n) := by
  induction n with
  | zero => change IsIso (𝟙 _); infer_instance
  | succ n ih =>
    letI := ih
    change IsIso (sheafTensorCongr X (asIso (tensorMap f n)) (asIso f)).hom
    infer_instance
end EtaleHodgePullbackIsomorphismR0172

/-- Étale pointed maps induce isomorphisms on relative differentials and on
all genuine Hodge tensor powers, including the tensor unit. -/
theorem etale_hodge_pullback_isomorphism :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (V : WeierstrassCurve R) [V.IsElliptic] (f : PointedMap R W V) [Etale f.map],
      IsIso (curveDifferential f) ∧ ∀ n : ℕ, IsIso (powerMap f n) := by
  intro R _ _ _ _ _ W _ V _ f _
  letI : SmoothOfRelativeDimension 1 (structureMap R V) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V.toProjective
  haveI : IsIso (curveDifferential f) :=
    EtaleHodgePullbackIsomorphismR0172.differentialMap_isIso_etale
      (structureMap R V) (structureMap R W) f.map f.over_eq
  refine ⟨inferInstance, fun n => ?_⟩
  haveI : IsIso (hodgeMap f) := by unfold hodgeMap; infer_instance
  exact EtaleHodgePullbackIsomorphismR0172.tensorMap_isIso (hodgeMap f) n

end ArithmeticThetaRelativeIsogenyHodgeR0172
