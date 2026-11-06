import SchemeHodgeDefinitionsR0205

/-! Naturality of the actual conormal derivative at the identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeHodgeR0205
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaRelativeDiscriminantR0171 (res)
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal

namespace AffineConormalHodgeNaturality

theorem differential_isIso {R : Type u} [CommRing R] (E : Family (Base R)) :
    IsIso (affineDifferential E) := by
  letI : IsProper E.p := E.proper
  letI : SmoothOfRelativeDimension 1 E.p := E.dimension
  have he : E.zero ≫ E.p = 𝟙 _ := (E.law.one (𝟙 _)).property
  haveI : IsClosedImmersion E.zero := by
    haveI : IsClosedImmersion (E.zero ≫ E.p) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp E.zero E.p
  exact section_conormal_isIso E.p E.zero he
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id E.zero he)
    ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (E.p.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1)

theorem twice_pullback_hom_ext {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} {N : X.Modules}
    {a b : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N}
    (h : ∀ (U : Z.Opens) (x : Γ(M,U)),
      a.app _ (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g x)) =
      b.app _ (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g x))) :
    a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply Scheme.Modules.pullback_hom_ext g
  intro U x
  exact (Scheme.Modules.app_pullbackLocalSection f a _).symm.trans
    ((h U x).trans (Scheme.Modules.app_pullbackLocalSection f b _))

theorem ideal_section {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (f : F.curve ⟶ E.curve)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module)
    (hi : IdealCompatible E F f i) (U : E.curve.Opens) (x : Γ(E.zero.ker.module,U)) :
    F.zero.ker.moduleι.app _ (i.hom.app _ (Scheme.Modules.pullbackLocalSection f x)) =
      f.app U (E.zero.ker.moduleι.app U x) := by
  have h := congrArg (fun k => k.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f x)) hi
  change _ = (ArithmeticThetaPullback.pullback_unit_iso F.curve E.curve f).hom.app _
    (((Scheme.Modules.pullback f).map E.zero.ker.moduleι).app _
      (Scheme.Modules.pullbackLocalSection f x)) at h
  rw [← Scheme.Modules.pullbackLocalSection_app] at h
  refine h.trans ?_
  have hunit := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  exact (Scheme.Modules.app_pullbackLocalSection f
    (ArithmeticThetaPullback.pullback_unit_iso F.curve E.curve f).hom _).trans
      (ConcreteCategory.congr_hom (congrArg (fun k => k.val.app (op U)) hunit)
        (E.zero.ker.moduleι.app U x))

theorem cotangent_section {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module)
    (U : E.curve.Opens) (x : Γ(E.zero.ker.module,U)) (V : T.Opens)
    (h₁ : V ≤ b ⁻¹ᵁ (E.zero ⁻¹ᵁ U)) (h₂ : V ≤ F.zero ⁻¹ᵁ (f ⁻¹ᵁ U)) :
    res (Cotangent F) h₁
      ((cotangentComparison E F b f hz i).hom.app _
        (Scheme.Modules.pullbackLocalSection b (Scheme.Modules.pullbackLocalSection E.zero x))) =
    res (Cotangent F) h₂
      (Scheme.Modules.pullbackLocalSection F.zero
        (i.hom.app _ (Scheme.Modules.pullbackLocalSection f x))) := by
  change res _ h₁ (((Scheme.Modules.pullback F.zero).map i.hom).app _
    ((squarePullbackIso b E.zero F.zero f hz.symm E.zero.ker.module).hom.app _
      (Scheme.Modules.pullbackLocalSection b (Scheme.Modules.pullbackLocalSection E.zero x)))) = _
  rw [hom_res, squarePullbackIso_section b E.zero F.zero f hz.symm E.zero.ker.module U x V h₁ h₂,
    ← hom_res, ← Scheme.Modules.pullbackLocalSection_app]

end AffineConormalHodgeNaturality

/-- The normalized conormal derivative is invertible and natural for arbitrary
affine Cartesian change of base and every inclusion-compatible ideal comparison. -/
theorem affine_conormal_hodge_naturality
    (R V : Type u) [CommRing R] [CommRing V]
    (E : Family (Base R)) (F : Family (Base V)) (ι : R →+* V)
    (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p (Spec.map (CommRingCat.ofHom ι)))
    (hz : F.zero ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ E.zero) :
    IsIso (affineDifferential E) ∧ IsIso (affineDifferential F) ∧
      ∀ i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module,
        IdealCompatible E F f i →
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).map (affineDifferential E) ≫
          (affineHodgeComparison E F ι f hc hz).hom =
        (cotangentComparison E F (Spec.map (CommRingCat.ofHom ι)) f hz i).hom ≫
          affineDifferential F := by
  refine ⟨AffineConormalHodgeNaturality.differential_isIso E,
    AffineConormalHodgeNaturality.differential_isIso F, ?_⟩
  intro i hi
  letI : Algebra R V := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 E.p := E.dimension
  apply AffineConormalHodgeNaturality.twice_pullback_hom_ext
    (Spec.map (CommRingCat.ofHom ι)) E.zero
  intro U x
  let W := (Spec.map (CommRingCat.ofHom ι)) ⁻¹ᵁ (E.zero ⁻¹ᵁ U)
  have h₂ : W ≤ F.zero ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change (Spec.map (CommRingCat.ofHom ι) ≫ E.zero) ⁻¹ᵁ U ≤ (F.zero ≫ f) ⁻¹ᵁ U
    rw [hz]
  change (affineHodgeComparison E F ι f hc hz).hom.app W
    (((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).map (affineDifferential E)).app W
      (Scheme.Modules.pullbackLocalSection _ (Scheme.Modules.pullbackLocalSection E.zero x))) =
    (affineDifferential F).app W
      ((cotangentComparison E F (Spec.map (CommRingCat.ofHom ι)) f hz i).hom.app W
        (Scheme.Modules.pullbackLocalSection _ (Scheme.Modules.pullbackLocalSection E.zero x)))
  rw [← Scheme.Modules.pullbackLocalSection_app, conormalMap_pullback]
  have hleft := pointedDifferentialIso_D E.p F.p f hc E.zero F.zero hz U
    (E.zero.ker.moduleι.app U x) W le_rfl h₂
  have hright := AffineConormalHodgeNaturality.cotangent_section E F
    (Spec.map (CommRingCat.ofHom ι)) f hz i U x W le_rfl h₂
  rw [res_refl] at hleft hright
  change (pointedDifferentialIso E.p F.p f hc E.zero F.zero hz).hom.app W _ = _
  erw [hleft, hright, ← hom_res, conormalMap_pullback,
    AffineConormalHodgeNaturality.ideal_section E F f i hi]

#print axioms affine_conormal_hodge_naturality
end ArithmeticThetaSchemeHodgeR0205
