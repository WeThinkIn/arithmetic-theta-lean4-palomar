module

public import RationalValueTransportR0159
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

/-! Descent of actual stalk values under field base change. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedKatoValuesR0159
open CategoryTheory AlgebraicGeometry

/-- Faithful flatness reflects whether a fraction belongs to the original ring. -/
private lemma fraction_regular_descent
    {A B K E : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra B E] [IsFractionRing B E]
    (t : A →+* B) (φ : K →+* E) (ht : t.FaithfullyFlat)
    (hsq : (algebraMap B E).comp t = φ.comp (algebraMap A K))
    (g : K) (b : B) (hb : algebraMap B E b = φ g) :
    ∃ a : A, algebraMap A K a = g := by
  letI := t.toAlgebra
  haveI : Module.FaithfullyFlat A B := ht
  obtain ⟨a, d, hd, hfrac⟩ := IsFractionRing.div_surjective A g
  have hdK : algebraMap A K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hmul : g * algebraMap A K d = algebraMap A K a :=
    (eq_div_iff hdK).mp hfrac.symm
  have htapp (x : A) : algebraMap B E (t x) = φ (algebraMap A K x) :=
    DFunLike.congr_fun hsq x
  have hmulB : b * t d = t a := by
    apply IsFractionRing.injective B E
    rw [map_mul, hb, htapp, htapp, ← map_mul, hmul]
  have hmem : a ∈ Ideal.span ({d} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B)
      (Ideal.span ({d} : Set A))]
    change t a ∈ (Ideal.span ({d} : Set A)).map t
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨b, hmulB⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨c, ?_⟩
  apply (mul_right_cancel₀ hdK)
  rw [hmul, ← map_mul, hc]

private lemma stalk_field_square {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (φ : X.functionField →+* Y.functionField)
    (hφ : ArithmeticThetaGeometricNormR0150.IsFieldMap f φ) (y : Y) :
    (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (f.stalkMap y).hom =
      φ.comp (algebraMap (X.presheaf.stalk (f y)) X.functionField) := by
  have inc (Z : Scheme.{u}) [IsIntegral Z] (z : Z) :
      Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk z) Z.functionField)) ≫
        Z.fromSpecStalk z = Z.fromSpecStalk (genericPoint Z) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec Z).specializes trivial)
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (f y))).mp
  change Spec.map (f.stalkMap y ≫ CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (f y)) X.functionField) ≫
      CommRingCat.ofHom φ) ≫ _
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, inc, inc]
  exact hφ

private lemma stalk_regular_descent {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [Flat f] (φ : X.functionField →+* Y.functionField)
    (hφ : ArithmeticThetaGeometricNormR0150.IsFieldMap f φ)
    (y : Y) (g : X.functionField)
    (b : Y.presheaf.stalk y) (hb : algebraMap _ Y.functionField b = φ g) :
    ∃ a : X.presheaf.stalk (f y), algebraMap _ X.functionField a = g := by
  have ht : (f.stalkMap y).hom.FaithfullyFlat := by
    algebraize [(f.stalkMap y).hom]
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f y) (f.toLRSHom.prop y)
  exact fraction_regular_descent (f.stalkMap y).hom φ ht
    (stalk_field_square f φ hφ y) g b hb

/-- Regularity and the specified rational-point value descend along genuine
field base change, including arbitrary infinite coefficient extensions. -/
theorem rational_value_field_descent :
    ∀ (F L : Type u) [Field F] [Field L] (ι : F →+* L)
      (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
      (bX : X ⟶ Spec (CommRingCat.of F)) (bY : Y ⟶ Spec (CommRingCat.of L))
      (f : Y ⟶ X), IsPullback f bY bX (Spec.map (CommRingCat.ofHom ι)) →
      ∀ (φ : X.functionField →+* Y.functionField),
      ArithmeticThetaGeometricNormR0150.IsFieldMap f φ →
      ∀ (p : Spec (CommRingCat.of F) ⟶ X) (q : Spec (CommRingCat.of L) ⟶ Y),
      p ≫ bX = 𝟙 _ → q ≫ bY = 𝟙 _ →
      q ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ p →
      ∀ (g : X.functionField) (v : F),
      HasValue F X p g v ↔ HasValue L Y q (φ g) (ι v) := by
  intro F L _ _ ι X Y _ _ bX bY f hpb φ hφ p q _hp _hq hpq g v
  haveI : Flat f := MorphismProperty.of_isPullback hpb.flip
    (inferInstance : Flat (Spec.map (CommRingCat.ofHom ι)))
  constructor
  · exact rational_value_transport.2 F L ι X Y f φ hφ p q hpq g v
  · intro hv
    obtain ⟨b, hb, hbval⟩ := hv
    have hpoint : f (q (IsLocalRing.closedPoint L)) = p (IsLocalRing.closedPoint F) := by
      have h := congrArg (fun e : Spec (CommRingCat.of L) ⟶ X =>
        e (IsLocalRing.closedPoint L)) hpq
      simpa only [Scheme.Hom.comp_apply,
        Subsingleton.elim ((Spec.map (CommRingCat.ofHom ι)) (IsLocalRing.closedPoint L))
          (IsLocalRing.closedPoint F)] using h
    have hreg := stalk_regular_descent f φ hφ _ g b hb
    rw [hpoint] at hreg
    obtain ⟨a, ha⟩ := hreg
    have hav : HasValue F X p g (Scheme.stalkClosedPointTo p a) := ⟨a, ha, rfl⟩
    have hval := rational_value_transport.1 L Y q (φ g)
      (ι (Scheme.stalkClosedPointTo p a)) (ι v)
      (rational_value_transport.2 F L ι X Y f φ hφ p q hpq g _ hav) ⟨b, hb, hbval⟩
    exact ⟨a, ha, ι.injective hval⟩

end ArithmeticThetaMarkedKatoValuesR0159
