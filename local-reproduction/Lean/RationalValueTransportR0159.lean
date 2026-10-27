import MarkedKatoValueDefinitionsR0159

/-! Uniqueness and transport of rational values through actual local rings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaMarkedKatoValuesR0159
open CategoryTheory AlgebraicGeometry

private lemma inclusion_fromSpecStalk (X : Scheme.{u}) [IsIntegral X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((genericPoint_spec X).specializes trivial)

private lemma stalk_field_square {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (φ : X.functionField →+* Y.functionField)
    (hφ : ArithmeticThetaGeometricNormR0150.IsFieldMap f φ)
    (x : X) (y : Y) (t : X.presheaf.stalk x →+* Y.presheaf.stalk y)
    (ht : Y.fromSpecStalk y ≫ f =
      Spec.map (CommRingCat.ofHom t) ≫ X.fromSpecStalk x) :
    (algebraMap (Y.presheaf.stalk y) Y.functionField).comp t =
      φ.comp (algebraMap (X.presheaf.stalk x) X.functionField) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk x)).mp
  change Spec.map (CommRingCat.ofHom t ≫ CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) ≫
      CommRingCat.ofHom φ) ≫ _
  simp only [Spec.map_comp, Category.assoc]
  rw [← ht, ← Category.assoc, inclusion_fromSpecStalk,
    inclusion_fromSpecStalk]
  exact hφ

private lemma stalk_value_square
    {F L : Type u} [Field F] [Field L] (ι : F →+* L)
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Spec (CommRingCat.of F) ⟶ X) (q : Spec (CommRingCat.of L) ⟶ Y)
    (hpq : q ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ p)
    (t : X.presheaf.stalk (p (IsLocalRing.closedPoint F)) →+*
      Y.presheaf.stalk (q (IsLocalRing.closedPoint L)))
    (ht : Y.fromSpecStalk (q (IsLocalRing.closedPoint L)) ≫ f =
      Spec.map (CommRingCat.ofHom t) ≫
        X.fromSpecStalk (p (IsLocalRing.closedPoint F))) :
    (Scheme.stalkClosedPointTo q).hom.comp t =
      ι.comp (Scheme.stalkClosedPointTo p).hom := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (p (IsLocalRing.closedPoint F)))).mp
  change Spec.map (CommRingCat.ofHom t ≫ Scheme.stalkClosedPointTo q) ≫ _ =
    Spec.map (Scheme.stalkClosedPointTo p ≫ CommRingCat.ofHom ι) ≫ _
  simp only [Spec.map_comp, Category.assoc]
  rw [← ht, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact hpq

/-- Actual rational-function values are unique and commute with the given
scheme morphism and coefficient embedding. -/
theorem rational_value_transport :
    (∀ (F : Type u) [Field F] (X : Scheme.{u}) [IsIntegral X]
      (p : Spec (CommRingCat.of F) ⟶ X) (g : X.functionField) (v w : F),
      HasValue F X p g v → HasValue F X p g w → v = w) ∧
    (∀ (F L : Type u) [Field F] [Field L] (ι : F →+* L)
      (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
      (f : Y ⟶ X) (φ : X.functionField →+* Y.functionField),
      ArithmeticThetaGeometricNormR0150.IsFieldMap f φ →
      ∀ (p : Spec (CommRingCat.of F) ⟶ X) (q : Spec (CommRingCat.of L) ⟶ Y),
      q ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ p →
      ∀ (g : X.functionField) (v : F),
      HasValue F X p g v → HasValue L Y q (φ g) (ι v)) := by
  constructor
  · intro F _ X _ p g v w hv hw
    obtain ⟨b, hb, rfl⟩ := hv
    obtain ⟨c, hc, rfl⟩ := hw
    congr 1
    exact IsFractionRing.injective (X.presheaf.stalk (p (IsLocalRing.closedPoint F)))
      X.functionField (hb.trans hc.symm)
  · intro F L _ _ ι X Y _ _ f φ hφ p q hpq g v hv
    have hp : f (q (IsLocalRing.closedPoint L)) = p (IsLocalRing.closedPoint F) := by
      have h := congrArg (fun e : Spec (CommRingCat.of L) ⟶ X =>
        e (IsLocalRing.closedPoint L)) hpq
      simpa only [Scheme.Hom.comp_apply,
        Subsingleton.elim ((Spec.map (CommRingCat.ofHom ι)) (IsLocalRing.closedPoint L))
          (IsLocalRing.closedPoint F)] using h
    obtain ⟨t, ht⟩ :=
      ArithmeticThetaGeometricNormR0150.ActualMultiplicationFieldNorm.exists_stalk_square
        f _ _ hp
    obtain ⟨b, hb, hv⟩ := hv
    refine ⟨t b, ?_, ?_⟩
    · have h := DFunLike.congr_fun (stalk_field_square f φ hφ _ _ t ht) b
      exact h.trans (congrArg φ hb)
    · have h := DFunLike.congr_fun (stalk_value_square ι f p q hpq t ht) b
      exact h.trans (congrArg ι hv)

end ArithmeticThetaMarkedKatoValuesR0159
