module

public import RelativeIsogenyHodgeDefinitionsR0172

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
universe u
namespace ArithmeticThetaRelativeIsogenyHodgeR0172
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower ArithmeticThetaPullback
namespace PointedHodgeFunctoriality

/-- Evaluation of the canonical pointed pullback transport for any sheaf map. -/
theorem pointed_section {X Y T : Scheme.{u}} (φ : X ⟶ Y)
    (s : T ⟶ Y) (t : T ⟶ X) (h : s = t ≫ φ)
    (M : Y.Modules) (N : X.Modules) (k : (Scheme.Modules.pullback φ).obj M ⟶ N)
    (U : Y.Opens) (m : Γ(M,U)) (B : T.Opens)
    (h₁ : B ≤ s ⁻¹ᵁ U) (h₂ : B ≤ t ⁻¹ᵁ (φ ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback t).obj N) h₁
      (((pullbackEqIso h M).hom ≫ ((Scheme.Modules.pullbackComp t φ).app M).inv ≫
        (Scheme.Modules.pullback t).map k).app (s ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection s m)) =
    res ((Scheme.Modules.pullback t).obj N) h₂
      (Scheme.Modules.pullbackLocalSection t
        (k.app _ (Scheme.Modules.pullbackLocalSection φ m))) := by
  change res _ h₁ (((Scheme.Modules.pullback t).map k).app _
    (((Scheme.Modules.pullbackComp t φ).app M).inv.app _
      ((pullbackEqIso h M).hom.app _ (Scheme.Modules.pullbackLocalSection s m)))) = _
  rw [hom_res]
  erw [hom_res ((Scheme.Modules.pullbackComp t φ).app M).inv]
  erw [pullbackEqIso_section h M U m B h₁ h₂]
  erw [← hom_res ((Scheme.Modules.pullbackComp t φ).app M).inv h₂
    (Scheme.Modules.pullbackLocalSection (t ≫ φ) m)]
  erw [pullbackComp_inv_section t φ M U m]
  erw [← hom_res ((Scheme.Modules.pullback t).map k) h₂]
  rw [← Scheme.Modules.pullbackLocalSection_app]

/-- Universal relative differential formula with arbitrary pointed sections. -/
theorem pointed_D {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of R)) (gX : X ⟶ Spec (CommRingCat.of R))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap R R)))
    (s : Spec (CommRingCat.of R) ⟶ Y) (t : Spec (CommRingCat.of R) ⟶ X)
    (h : s = t ≫ φ) (U : Y.Opens) (a : Γ(Y,U)) (B : (Spec (CommRingCat.of R)).Opens)
    (h₁ : B ≤ s ⁻¹ᵁ U) (h₂ : B ≤ t ⁻¹ᵁ (φ ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback t).obj gX.kaehler) h₁
      (((pullbackEqIso h gY.kaehler).hom ≫ ((Scheme.Modules.pullbackComp t φ).app gY.kaehler).inv ≫
        (Scheme.Modules.pullback t).map (differentialMap gY gX φ hφ)).app (s ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection s
            (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a))) =
    res ((Scheme.Modules.pullback t).obj gX.kaehler) h₂
      (Scheme.Modules.pullbackLocalSection t
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gX (φ ⁻¹ᵁ U) (φ.app U a))) := by
  have H := pointed_section φ s t h gY.kaehler gX.kaehler (differentialMap gY gX φ hφ)
    U (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a) B h₁ h₂
  rw [differentialMap_D] at H
  exact H

/-- Dependent local sections respect composition of actual scheme pullbacks. -/
theorem section_comp {X Y Z T : Scheme.{u}} (p : T ⟶ X) (N : T.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(N,p ⁻¹ᵁ U))
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z,U))
    (B : T.Opens) (h₁ : B ≤ p ⁻¹ᵁ ((f ≫ g) ⁻¹ᵁ U))
    (h₂ : B ≤ p ⁻¹ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ U))) :
    res N h₁ (d _ ((f ≫ g).app U a)) =
      res N h₂ (d _ (f.app _ (g.app U a))) := rfl

/-- Dependent local sections respect the identity scheme pullback. -/
theorem section_id {X T : Scheme.{u}} (p : T ⟶ X) (N : T.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(N,p ⁻¹ᵁ U))
    (U : X.Opens) (a : Γ(X,U))
    (h : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ U)) :
    res N h (d _ ((𝟙 X : X ⟶ X).app U a)) = d U a := by
  change res N le_rfl (d U a) = d U a
  exact res_refl N _

/-- Composition is determined by compatible local section formulas. -/
theorem compose_sections {X : Scheme.{u}} {M N P : X.Modules}
    (F : N ⟶ P) (G : M ⟶ N) (H : M ⟶ P)
    (B C D : X.Opens) (s : Γ(M,B)) (t : Γ(N,C)) (v : Γ(P,D))
    (hg : B ≤ C) (hf : C ≤ D)
    (hG : res N le_rfl (G.app B s) = res N hg t)
    (hF : res P le_rfl (F.app C t) = res P hf v)
    (hH : res P le_rfl (H.app B s) = res P (hg.trans hf) v) :
    H.app B s = (G ≫ F).app B s := by
  rw [res_refl] at hG hF hH
  change H.app B s = F.app B (G.app B s)
  rw [hG, ← hom_res F hg, hF, res_res]
  exact hH

/-- A pointed square identifies the two inverse-image opens. -/
theorem pointed_preimage {X Y T : Scheme.{u}} (s : T ⟶ Y) (t : T ⟶ X)
    (f : X ⟶ Y) (h : t ≫ f = s) (U : Y.Opens) :
    s ⁻¹ᵁ U ≤ t ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro y hy
  change (t ≫ f) y ∈ U
  rw [h]
  exact hy

/-- All-open local formulas compose on arbitrary pointed schemes. -/
theorem local_composition {X Y Z T : Scheme.{u}}
    (p : T ⟶ X) (q : T ⟶ Y) (r : T ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : p ≫ f = q) (hg : q ≫ g = r)
    (P Q S : T.Modules)
    (dP : ∀ U : X.Opens, Γ(X,U) → Γ(P,p ⁻¹ᵁ U))
    (dQ : ∀ U : Y.Opens, Γ(Y,U) → Γ(Q,q ⁻¹ᵁ U))
    (dS : ∀ U : Z.Opens, Γ(Z,U) → Γ(S,r ⁻¹ᵁ U))
    (F : Q ⟶ P) (G : S ⟶ Q) (H : S ⟶ P)
    (hF : ∀ U a B (h₁ : B ≤ q ⁻¹ᵁ U) (h₂ : B ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)),
      res P h₁ (F.app _ (dQ U a)) = res P h₂ (dP _ (f.app U a)))
    (hG : ∀ U a B (h₁ : B ≤ r ⁻¹ᵁ U) (h₂ : B ≤ q ⁻¹ᵁ (g ⁻¹ᵁ U)),
      res Q h₁ (G.app _ (dS U a)) = res Q h₂ (dQ _ (g.app U a)))
    (hH : ∀ U a B (h₁ : B ≤ r ⁻¹ᵁ U) (h₂ : B ≤ p ⁻¹ᵁ ((f ≫ g) ⁻¹ᵁ U)),
      res P h₁ (H.app _ (dS U a)) = res P h₂ (dP _ ((f ≫ g).app U a)))
    (U : Z.Opens) (a : Γ(Z,U)) :
    H.app (r ⁻¹ᵁ U) (dS U a) = (G ≫ F).app (r ⁻¹ᵁ U) (dS U a) := by
  have hq := pointed_preimage r q g hg U
  have hp := pointed_preimage q p f hf (g ⁻¹ᵁ U)
  exact compose_sections F G H (r ⁻¹ᵁ U) (q ⁻¹ᵁ (g ⁻¹ᵁ U))
    (p ⁻¹ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ U))) (dS U a) (dQ _ (g.app U a))
    (dP _ (f.app _ (g.app U a))) hq hp
    (hG U a _ le_rfl hq) (hF _ (g.app U a) _ le_rfl hp)
    ((hH U a _ le_rfl (hq.trans hp)).trans (section_comp p P dP f g U a _ _ _))

attribute [local irreducible] origin structureMap

/-- The pointed transport carries actual local differentials to pullbacks. -/
theorem hodgeMap_D {R : Type u} [CommRing R] {W V : WeierstrassCurve R}
    (f : PointedMap R W V) (U : (Curve R V).Opens) (a : Γ(Curve R V, U))
    (B : (Base R).Opens) (h₁ : B ≤ origin R V ⁻¹ᵁ U)
    (h₂ : B ≤ origin R W ⁻¹ᵁ (f.map ⁻¹ᵁ U)) :
    res (Hodge R W) h₁ ((hodgeMap f).app (origin R V ⁻¹ᵁ U) (localDifferential R V U a)) =
      res (Hodge R W) h₂ (localDifferential R W (f.map ⁻¹ᵁ U) (f.map.app U a)) := by
  unfold hodgeMap localDifferential curveDifferential
  exact pointed_D (R := R) (X := Curve R W) (Y := Curve R V) (structureMap R V) (structureMap R W) f.map
    (by simpa using f.over_eq) (origin R V) (origin R W) f.origin_eq.symm U a B h₁ h₂

/-- The recursively defined tensor map acts on every pure local tensor. -/
theorem tensorMap_section {X : Scheme.{u}} {H K : X.Modules} (f : H ⟶ K)
    (n : ℕ) (U : X.Opens) (s : Γ(H,U)) :
    (tensorMap f n).app U (tensorPowerSection X H n U s) =
      tensorPowerSection X K n U (f.app U s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sheafTensorMap X (tensorMap f n) f).app U
      (tensorSection X _ _ U (tensorPowerSection X H n U s) s) = _
    rw [sheafTensorMap_section, ih]
    rfl

/-- Tensorization preserves an equality after restriction to a common open. -/
theorem tensorMap_res {X : Scheme.{u}} {H K : X.Modules} (f : H ⟶ K)
    (n : ℕ) (U V B : X.Opens) (s : Γ(H,U)) (t : Γ(K,V))
    (h₁ : B ≤ U) (h₂ : B ≤ V)
    (h : res K h₁ (f.app U s) = res K h₂ t) :
    res (tensorPower X K n) h₁ ((tensorMap f n).app U (tensorPowerSection X H n U s)) =
      res (tensorPower X K n) h₂ (tensorPowerSection X K n V t) := by
  rw [tensorMap_section]
  change (tensorPower X K n).presheaf.map (homOfLE h₁).op _ =
    (tensorPower X K n).presheaf.map (homOfLE h₂).op _
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection X K n B) h

end PointedHodgeFunctoriality
open PointedHodgeFunctoriality

attribute [local irreducible] origin structureMap

/-- All-open local formula, including the zeroth tensor power. -/
theorem pointed_hodge_local_formula :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve R) [V.IsElliptic] (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (n : ℕ) (U : (ArithmeticThetaRelativeKatoR0169.Curve R V).Opens) (a : (ArithmeticThetaRelativeKatoR0169.Curve R V).presheaf.obj (Opposite.op U)) (B : (ArithmeticThetaRelativeDiscriminantR0171.Base R).Opens) (h₁ : B ≤ (TopologicalSpace.Opens.map (ArithmeticThetaRelativeKatoR0169.origin R V).base).obj U) (h₂ : B ≤ (TopologicalSpace.Opens.map (ArithmeticThetaRelativeKatoR0169.origin R W).base).obj ((TopologicalSpace.Opens.map f.map.base).obj U)), ArithmeticThetaRelativeDiscriminantR0171.res (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W n) h₁ ((ArithmeticThetaRelativeIsogenyHodgeR0172.powerMap f n).app ((origin R V) ⁻¹ᵁ U) (ArithmeticThetaRelativeDiscriminantR0171.localPower R V n U a)) = ArithmeticThetaRelativeDiscriminantR0171.res (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W n) h₂ (ArithmeticThetaRelativeDiscriminantR0171.localPower R W n ((TopologicalSpace.Opens.map f.map.base).obj U) (f.map.app U a)) := by
  intro R _ _ _ _ _ W _ V _ f n U a B h₁ h₂
  unfold powerMap localPower
  exact tensorMap_res (X := Base R) (H := Hodge R V) (K := Hodge R W) (hodgeMap f) n
    (origin R V ⁻¹ᵁ U) (origin R W ⁻¹ᵁ (f.map ⁻¹ᵁ U)) B
    (localDifferential R V U a) (localDifferential R W (f.map ⁻¹ᵁ U) (f.map.app U a))
    h₁ h₂ (hodgeMap_D f U a B h₁ h₂)

namespace PointedHodgeFunctoriality

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R]

/-- Genuine local differential tensor frames determine a Hodge-power map. -/
theorem power_ext (V : WeierstrassCurve R) [V.IsElliptic] (n : ℕ)
    {N : (Base R).Modules} (F G : HodgePower R V n ⟶ N)
    (h : ∀ (U : (Curve R V).Opens) (a : Γ(Curve R V,U)),
      F.app (origin R V ⁻¹ᵁ U) (localPower R V n U a) =
        G.app (origin R V ⁻¹ᵁ U) (localPower R V n U a)) : F = G := by
  apply hom_ext_frames
  intro x
  letI : SmoothOfRelativeDimension 1 (structureMap R V) := by
    unfold structureMap
    exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V.toProjective
  obtain ⟨U, a, hxU, hU⟩ := exists_exact_differential_frame (structureMap R V) ((origin R V) x)
  refine ⟨origin R V ⁻¹ᵁ U, localPower R V n U a, hxU, ?_, h U a⟩
  exact tensorPower_frame (Hodge R V) (localDifferential R V U a)
    (pullback_frame (origin R V) (structureMap R V).kaehler
      (ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R V) U a) hU) n

/-- Composition on one pure local tensor, retaining the origin transports. -/
theorem power_comp_section (W V Z : WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic] [Z.IsElliptic]
    (f : PointedMap R W V) (g : PointedMap R V Z) (n : ℕ)
    (U : (Curve R Z).Opens) (a : Γ(Curve R Z,U)) :
    (powerMap (PointedMap.comp f g) n).app (origin R Z ⁻¹ᵁ U) (localPower R Z n U a) =
      (powerMap g n ≫ powerMap f n).app (origin R Z ⁻¹ᵁ U) (localPower R Z n U a) := by
  exact local_composition (origin R W) (origin R V) (origin R Z) f.map g.map
    f.origin_eq g.origin_eq (HodgePower R W n) (HodgePower R V n) (HodgePower R Z n)
    (localPower R W n) (localPower R V n) (localPower R Z n)
    (powerMap f n) (powerMap g n) (powerMap (PointedMap.comp f g) n)
    (pointed_hodge_local_formula R W V f n) (pointed_hodge_local_formula R V Z g n)
    (pointed_hodge_local_formula R W Z (PointedMap.comp f g) n) U a

/-- Identity on one pure local tensor. -/
theorem power_id_section (W : WeierstrassCurve R) [W.IsElliptic] (n : ℕ)
    (U : (Curve R W).Opens) (a : Γ(Curve R W,U)) :
    (powerMap (PointedMap.identity R W) n).app (origin R W ⁻¹ᵁ U) (localPower R W n U a) =
      (𝟙 (HodgePower R W n) : HodgePower R W n ⟶ HodgePower R W n).app (origin R W ⁻¹ᵁ U) (localPower R W n U a) := by
  have h := pointed_hodge_local_formula R W W (PointedMap.identity R W) n U a
    (origin R W ⁻¹ᵁ U) le_rfl le_rfl
  rw [res_refl] at h
  exact h.trans (section_id (origin R W) (HodgePower R W n) (localPower R W n) U a _)

end PointedHodgeFunctoriality

/-- Contravariant composition and identity for the actual Hodge tensor maps. -/
theorem pointed_hodge_functoriality :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve R) [V.IsElliptic] (Z : WeierstrassCurve R) [Z.IsElliptic] (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (g : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R V Z) (n : ℕ), ArithmeticThetaRelativeIsogenyHodgeR0172.powerMap (ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap.comp f g) n = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeIsogenyHodgeR0172.powerMap g n) (ArithmeticThetaRelativeIsogenyHodgeR0172.powerMap f n) ∧ ArithmeticThetaRelativeIsogenyHodgeR0172.powerMap (ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap.identity R W) n = CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W n) := by
  intro R _ _ _ _ _ W _ V _ Z _ f g n
  exact ⟨power_ext R Z n _ _ (power_comp_section R W V Z f g n),
    power_ext R W n _ _ (power_id_section R W n)⟩

#print axioms pointed_hodge_local_formula
#print axioms pointed_hodge_functoriality
end ArithmeticThetaRelativeIsogenyHodgeR0172
