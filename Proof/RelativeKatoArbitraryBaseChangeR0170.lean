module

public import RelativeKatoFiberSpecializationR0170

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
namespace RelativeKatoArbitraryBaseChange
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaGeometricNormR0150

/-- The actual generic-point square controls sheaf pullback on arbitrary
nonempty opens, without any affineness restriction. -/
lemma section_field_square {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)) :
    X.germToFunctionField V (f.appLE U V e a) = φ (Y.germToFunctionField U a) := by
  have hx : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (inferInstance : Nonempty V))
  have H := DFunLike.congr_fun
    (VerticalOrders.stalk_field_square f φ hφ (genericPoint X))
    (Y.presheaf.germ U (f (genericPoint X)) (e hx) a)
  rw [RingHom.comp_apply, RingHom.comp_apply,
    Y.algebraMap_germ_eq_germToFunctionField] at H
  rw [f.germ_stalkMap_apply U (genericPoint X) (e hx) a] at H
  letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, e hx⟩⟩
  rw [X.algebraMap_germ_eq_germToFunctionField] at H
  calc
    X.germToFunctionField V (f.appLE U V e a) =
        X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) := by
      rw [Scheme.Hom.appLE]
      change (f.app U ≫ X.presheaf.map (homOfLE e).op ≫
        X.presheaf.germ V (genericPoint X) _) a = _
      rw [X.presheaf.germ_res]
      rfl
    _ = _ := H

/-- Over a field, the accepted Kato function has the same relative
normalization. Every generic comparison is treated using its actual field map. -/
lemma normalized_of_isKato (F : Type u) [Field F] [Algebra ℚ F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)]
    [IsIntegral (GenericCurve F W)] [IsLocallyNoetherian (GenericCurve F W)]
    (G : Law F W) (hG : IsOriginLaw F W G)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve F W).functionField)
    (hg : ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction F W G c g) :
    Normalized F W G c g := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have hgeneric : ∀ D : GenericComparison F W G,
      ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing F)
        (W.map (algebraMap F (FractionRing F))) D.law c (D.field g) := by
    intro D
    obtain ⟨α, hα, _⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_base_change
      F W G hG (FractionRing F) _ D.law D.originLaw
      (algebraMap F (FractionRing F)) D.map
      ⟨D.cartesian, D.origin_eq, D.multiplication_eq⟩
    have he : α = D.field.toRingHom :=
      ActualMultiplicationFieldNorm.fieldMap_unique D.map D.field.toRingHom α
        D.field_eq hα.1
    have hv := hα.2 c hc hc6 g hg
    rw [he] at hv
    exact hv
  obtain ⟨D⟩ := relative_generic_comparison F W G hG
  exact ⟨(RelativeExistence.relative_of_generic F W G hG D c hc hc6 g (hgeneric D)).1,
    hgeneric⟩

end RelativeKatoArbitraryBaseChange
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169
open RelativeKatoArbitraryBaseChange

/-- Arbitrary pointed Cartesian base change preserves the actual Kato unit
sections. Equality is detected on the target generic fiber. -/
theorem relative_kato_arbitrary_base_change :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g) (gs : (ArithmeticThetaRelativeKatoR0169.Curve S Ws).functionField) (hgs : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized S Ws Gs c gs), ArithmeticThetaRelativeKatoNaturalityR0170.UnitPullback R W G S Ws b c g gs := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG S _ _ _ _ _ Ws _ _ _ _ _ Gs hGs ι b hb c hc hc6 g hg gs hgs
  obtain ⟨C⟩ := relative_generic_comparison S Ws Gs hGs
  let K := FractionRing S
  let Wk := Ws.map (algebraMap S K)
  letI : IsIntegral (GenericCurve K Wk) := (relative_curve_geometry K Wk).2.2.2.1
  letI : IsLocallyNoetherian (GenericCurve K Wk) := (relative_curve_geometry K Wk).2.2.2.2.1
  have hC : IsBaseChange S Ws Gs K Wk C.law (algebraMap S K) C.map :=
    ⟨C.cartesian, C.origin_eq, C.multiplication_eq⟩
  have hcomp : IsBaseChange R W G K Wk C.law
      ((algebraMap S K).comp ι) (C.map ≫ b) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact C.cartesian.paste_horiz hb.1
    · rw [← Category.assoc, hC.2.1, Category.assoc, hb.2.1,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · intro n
      rw [← Category.assoc, C.multiplication_eq, Category.assoc, hb.2.2,
        Category.assoc]
  have hgf : Normalized K Wk C.law c (C.field gs) :=
    normalized_of_isKato K Wk C.law C.originLaw c hc hc6 (C.field gs) (hgs.2 C)
  have hspec := relative_kato_fiber_specialization R W G hG K Wk C.law C.originLaw
    ((algebraMap S K).comp ι) (C.map ≫ b) hcomp c hc hc6 g hg (C.field gs) hgf
  intro U V _ _ e a hU ha
  refine ⟨RelativeKatoFiberSpecialization.pulled_section_unit R W G hG c hc hc6 g hg
    b U V e a hU ha, ?_⟩
  let j := Spec.map (CommRingCat.ofHom (algebraMap S K))
  letI : Flat j := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors S)))
  letI : Flat C.map := MorphismProperty.of_isPullback (P := @Flat) C.cartesian.flip
    (inferInstance : Flat j)
  have hv : genericPoint (Curve S Ws) ∈ V :=
    ((genericPoint_spec (Curve S Ws)).mem_open_set_iff V.isOpen).mpr
      (by simpa using (inferInstance : Nonempty V))
  let T := C.map ⁻¹ᵁ V
  letI : Nonempty T := ⟨⟨genericPoint (GenericCurve S Ws), by
    change C.map (genericPoint (GenericCurve S Ws)) ∈ V
    rwa [GenericComparisonProof.generic_eq_of_flat C.map]⟩⟩
  have et : T ≤ (C.map ≫ b) ⁻¹ᵁ U := fun x hx => e hx
  have H := (hspec U T et a hU ha).2
  apply C.field.injective
  change C.field.toRingHom ((Curve S Ws).germToFunctionField V (b.appLE U V e a)) = _
  rw [← section_field_square C.map C.field.toRingHom C.field_eq V T le_rfl]
  have happ : C.map.appLE V T le_rfl (b.appLE U V e a) =
      (C.map ≫ b).appLE U T et a := by
    exact congrArg (fun f : Γ(Curve R W, U) ⟶ Γ(GenericCurve S Ws, T) => f a)
      (Scheme.Hom.appLE_comp_appLE C.map b U V T e le_rfl)
  rw [happ]
  exact H

#print axioms relative_kato_arbitrary_base_change
end ArithmeticThetaRelativeKatoNaturalityR0170
