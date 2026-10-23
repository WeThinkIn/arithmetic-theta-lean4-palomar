module
public import RelativeHodgePowerBaseChangeR0171
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
namespace PalomarPointedHodge1916

theorem kaehler_hom_ext {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of A)) {N : Y.Modules}
    {f g : gY.kaehler ⟶ N}
    (h : ∀ (U : Y.Opens) (a : Γ(Y, U)),
      f.app U (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a) =
      g.app U (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a)) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
    gY.kaehlerPresheaf N).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply kp_hom_ext gY U.unop
  intro a
  change f.app U.unop (gY.kaehlerToSections U.unop (dK gY U.unop a)) =
    g.app U.unop (gY.kaehlerToSections U.unop (dK gY U.unop a))
  exact h U.unop a

theorem twice_pullback_kaehler_hom_ext {A : Type u} [CommRing A]
    {Y X T : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (φ : X ⟶ Y) (t : T ⟶ X) {N : T.Modules}
    {f g : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback φ).obj gY.kaehler) ⟶ N}
    (h : ∀ (U : Y.Opens) (a : Γ(Y, U)),
      f.app (t ⁻¹ᵁ (φ ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.pullbackLocalSection φ
          (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a))) =
      g.app (t ⁻¹ᵁ (φ ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.pullbackLocalSection φ
          (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a)))) : f = g := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction t).homEquiv _ _).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).injective
  apply kaehler_hom_ext gY
  intro U a
  simpa only [Scheme.Modules.app_pullbackLocalSection] using h U a

section Pointed
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hc : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [SmoothOfRelativeDimension 1 gY]
    (s : Spec (CommRingCat.of A) ⟶ Y) (t : Spec (CommRingCat.of B) ⟶ X)
    (hpt : t ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ s)

def Compatible
    (q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((Scheme.Modules.pullback s).obj gY.kaehler) ≅
      (Scheme.Modules.pullback t).obj gX.kaehler) : Prop :=
  ∀ (U : Y.Opens) (a : Γ(Y, U)),
    ((squarePullbackIso (Spec.map (CommRingCat.ofHom (algebraMap A B))) s t φ
      hpt.symm gY.kaehler).inv ≫ q.hom).app (t ⁻¹ᵁ (φ ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.pullbackLocalSection φ
          (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a))) =
      Scheme.Modules.pullbackLocalSection t
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gX (φ ⁻¹ᵁ U) (φ.app U a))

theorem original_compatible : Compatible gY gX φ s t hpt
    (pointedDifferentialIso gY gX φ hc s t hpt) := by
  intro U a
  change (((squarePullbackIso _ s t φ hpt.symm gY.kaehler).inv ≫
    (squarePullbackIso _ s t φ hpt.symm gY.kaehler).hom ≫
    (Scheme.Modules.pullback t).map (differentialMap gY gX φ hc.w)).app _ _) = _
  rw [Iso.inv_hom_id_assoc]
  rw [← Scheme.Modules.pullbackLocalSection_app, differentialMap_D]

include hc in
theorem canonical_exists_unique : ∃! q, Compatible gY gX φ s t hpt q := by
  refine ⟨pointedDifferentialIso gY gX φ hc s t hpt,
    original_compatible gY gX φ hc s t hpt, ?_⟩
  intro q hq
  apply Iso.ext
  apply (cancel_epi (squarePullbackIso _ s t φ hpt.symm gY.kaehler).inv).1
  apply twice_pullback_kaehler_hom_ext gY φ t
  intro U a
  exact (hq U a).trans (original_compatible gY gX φ hc s t hpt U a).symm

theorem compatible_iff_original
    (q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((Scheme.Modules.pullback s).obj gY.kaehler) ≅
      (Scheme.Modules.pullback t).obj gX.kaehler) :
    Compatible gY gX φ s t hpt q ↔ q = pointedDifferentialIso gY gX φ hc s t hpt := by
  constructor
  · intro hq
    exact (canonical_exists_unique gY gX φ hc s t hpt).unique hq
      (original_compatible gY gX φ hc s t hpt)
  · rintro rfl
    exact original_compatible gY gX φ hc s t hpt
end Pointed
end PalomarPointedHodge1916
#print axioms PalomarPointedHodge1916.canonical_exists_unique
#print axioms PalomarPointedHodge1916.compatible_iff_original
