import ActualNormalization

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaNormalization

namespace ArithmeticThetaNormalizationField

universe u
noncomputable section

variable (X : Scheme.{u}) [IsIntegral X] (E : Type u) [Field E]
  [Algebra X.functionField E]

theorem genericSectionsIso_base_compat (U : X.Opens) [Nonempty U] :
    (genericExtensionMap X E).app U ≫ (genericSectionsIso X E U).hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField E) := by
  have hU : genericExtensionMap X E (IsLocalRing.closedPoint (CommRingCat.of E)) ∈ U := by
    exact (genericExtensionMap_apply X E _).symm ▸
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  exact (Scheme.germ_stalkClosedPointTo (genericExtensionMap X E) U hU).symm.trans
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
      (CommRingCat.ofHom (algebraMap X.functionField E)) U hU)

/-- The canonical base-chart scalar map through the actual function field. -/
def baseSectionsToE (U : X.Opens) [Nonempty U] : Γ(X, U) →+* E :=
  (algebraMap X.functionField E).comp (X.germToFunctionField U).hom

instance baseSectionsAlgebra (U : X.Opens) [Nonempty U] : Algebra Γ(X, U) E :=
  (baseSectionsToE X E U).toAlgebra

instance baseSectionsTower (U : X.Opens) [Nonempty U] :
    IsScalarTower Γ(X, U) X.functionField E :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The source-section isomorphism respects the canonical base algebra. -/
def sourceSectionsAlgEquiv (U : X.Opens) [Nonempty U] :
    letI := ((genericExtensionMap X E).app U).hom.toAlgebra
    Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U) ≃ₐ[Γ(X,U)] E :=
  letI := ((genericExtensionMap X E).app U).hom.toAlgebra
  { (genericSectionsIso X E U).commRingCatIsoToRingEquiv with
    commutes' r := congr($(genericSectionsIso_base_compat X E U) r) }

/-- An actual normalization chart is the integral closure in E with the canonical scalars. -/
def normalizationChartRingEquiv (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U) ≃+*
      integralClosure Γ(X, U) E :=
  letI := ((genericExtensionMap X E).app U).hom.toAlgebra
  (extensionNormalizationObjIso X E U hU).commRingCatIsoToRingEquiv.trans
    (sourceSectionsAlgEquiv X E U).mapIntegralClosure.toRingEquiv

/-- Algebraicity makes E the actual fraction field of each canonical integral closure. -/
theorem closure_fractionField [Algebra.IsAlgebraic X.functionField E]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing (integralClosure Γ(X, U) E) E := by
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra.IsAlgebraic Γ(X,U) E := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic X.functionField E)
  apply integralClosure.isFractionRing_of_algebraic (A := Γ(X,U))
  intro r hr
  apply IsFractionRing.injective Γ(X,U) X.functionField
  apply (algebraMap X.functionField E).injective
  simpa only [IsScalarTower.algebraMap_apply Γ(X,U) X.functionField E, map_zero] using hr

/-- Dominance of the actual incoming map identifies its image point as the generic point. -/
theorem toNormalization_genericPoint :
    extensionToNormalization X E (IsLocalRing.closedPoint (CommRingCat.of E)) =
      genericPoint (extensionNormalization X E) := by
  have hr : Set.range (extensionToNormalization X E) =
      {extensionToNormalization X E (IsLocalRing.closedPoint (CommRingCat.of E))} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg (extensionToNormalization X E) (Subsingleton.elim _ _)
    · intro hz
      exact ⟨_, hz.symm⟩
  apply IsGenericPoint.eq _ (genericPoint_spec (extensionNormalization X E))
  rw [isGenericPoint_def, ← hr]
  exact (extensionToNormalization X E).denseRange.closure_range

/-- The actual function-field map induced by the incoming Spec E morphism. -/
def normalizationFunctionFieldMap : (extensionNormalization X E).functionField ⟶ CommRingCat.of E :=
  (extensionNormalization X E).presheaf.stalkSpecializes
    (specializes_of_eq (toNormalization_genericPoint X E)) ≫
      Scheme.stalkClosedPointTo (extensionToNormalization X E)

lemma toNormalization_closedPoint_mem (V : (extensionNormalization X E).Opens) [Nonempty V] :
    extensionToNormalization X E (IsLocalRing.closedPoint (CommRingCat.of E)) ∈ V :=
  (toNormalization_genericPoint X E).symm ▸
    ((genericPoint_spec (extensionNormalization X E)).mem_open_set_iff V.isOpen).mpr
      (by simpa using ‹Nonempty V›)

def normalizationSourceSectionsIso (V : (extensionNormalization X E).Opens) [Nonempty V] :
    Γ(Spec (CommRingCat.of E), extensionToNormalization X E ⁻¹ᵁ V) ≅ CommRingCat.of E :=
  (Spec (CommRingCat.of E)).presheaf.mapIso
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem (extensionToNormalization X E)
      (toNormalization_closedPoint_mem X E V)).symm).op ≪≫ Scheme.ΓSpecIso _

theorem normalizationFunctionFieldMap_germ
    (V : (extensionNormalization X E).Opens) [Nonempty V] :
    (extensionNormalization X E).germToFunctionField V ≫ normalizationFunctionFieldMap X E =
      (extensionToNormalization X E).app V ≫ (normalizationSourceSectionsIso X E V).hom := by
  rw [normalizationFunctionFieldMap, ← Category.assoc,
    TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.germ_stalkClosedPointTo (extensionToNormalization X E) V _

instance normalizationPreimageNonempty (U : X.Opens) [Nonempty U] :
    Nonempty (extensionFromNormalization X E ⁻¹ᵁ U) := by
  obtain ⟨x, hx⟩ := Classical.choice ‹Nonempty U›
  obtain ⟨y, hy⟩ := (extensionFromNormalization_surjective X E).surj x
  refine ⟨⟨y, ?_⟩⟩
  change extensionFromNormalization X E y ∈ U
  exact hy.symm ▸ hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual incoming field map evaluates chart functions by their integral-closure values. -/
theorem normalizationFunctionFieldMap_chart (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (a : Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U)) :
    normalizationFunctionFieldMap X E
      ((extensionNormalization X E).germToFunctionField (extensionFromNormalization X E ⁻¹ᵁ U) a) =
      (normalizationChartRingEquiv X E U hU a : E) := by
  let := ((genericExtensionMap X E).app U).hom.toAlgebra
  have h := normalizationFunctionFieldMap_germ X E (extensionFromNormalization X E ⁻¹ᵁ U)
  have happ := (genericExtensionMap X E).toNormalization_app_preimage ⟨U, hU⟩
  change (genericExtensionMap X E).toNormalization.app _ = _ at happ
  have h' := h.trans (congrArg (fun q => q ≫
    (normalizationSourceSectionsIso X E (extensionFromNormalization X E ⁻¹ᵁ U)).hom) happ)
  have he := congr($(h') a)
  simpa [normalizationSourceSectionsIso, normalizationChartRingEquiv,
    sourceSectionsAlgEquiv, genericSectionsIso, extensionNormalizationObjIso,
    CategoryTheory.Iso.commRingCatIsoToRingEquiv,
    Category.assoc, ← Functor.map_comp] using he

/-- Algebraicity proves surjectivity of the actual morphism-induced function-field map. -/
theorem normalizationFunctionFieldMap_surjective [Algebra.IsAlgebraic X.functionField E] :
    Function.Surjective (normalizationFunctionFieldMap X E) := by
  obtain ⟨U, hU, hηU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := genericPoint X) (U := ⊤) (by trivial)
  let : Nonempty U := ⟨⟨_, hηU⟩⟩
  let := closure_fractionField X E U hU
  intro z
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (integralClosure Γ(X,U) E) z
  refine ⟨((extensionNormalization X E).germToFunctionField _
    ((normalizationChartRingEquiv X E U hU).symm a)) /
    ((extensionNormalization X E).germToFunctionField _
      ((normalizationChartRingEquiv X E U hU).symm b)), ?_⟩
  change (normalizationFunctionFieldMap X E).hom (_ / _) = _
  rw [map_div₀]
  change normalizationFunctionFieldMap X E (_ : (extensionNormalization X E).functionField) /
    normalizationFunctionFieldMap X E (_ : (extensionNormalization X E).functionField) = _
  rw [normalizationFunctionFieldMap_chart X E U hU,
    normalizationFunctionFieldMap_chart X E U hU]
  simp

/-- The canonical function-field isomorphism, whose forward map is induced by Spec E → Y. -/
def normalizationFunctionFieldEquiv [Algebra.IsAlgebraic X.functionField E] :
    (extensionNormalization X E).functionField ≃+* E :=
  RingEquiv.ofBijective (normalizationFunctionFieldMap X E).hom
    ⟨(normalizationFunctionFieldMap X E).hom.injective,
      normalizationFunctionFieldMap_surjective X E⟩

theorem normalizationFunctionFieldEquiv_toRingHom [Algebra.IsAlgebraic X.functionField E] :
    (normalizationFunctionFieldEquiv X E).toRingHom = (normalizationFunctionFieldMap X E).hom := rfl

theorem fromNormalization_genericPoint :
    extensionFromNormalization X E (genericPoint (extensionNormalization X E)) = genericPoint X := by
  calc
    _ = extensionFromNormalization X E
        (extensionToNormalization X E (IsLocalRing.closedPoint (CommRingCat.of E))) :=
      congrArg (extensionFromNormalization X E) (toNormalization_genericPoint X E).symm
    _ = genericExtensionMap X E (IsLocalRing.closedPoint (CommRingCat.of E)) :=
      congr($(extensionNormalization_factorization X E) (IsLocalRing.closedPoint (CommRingCat.of E)))
    _ = genericPoint X := genericExtensionMap_apply X E _

/-- The actual pullback on function fields induced by the outgoing normalization map. -/
def normalizationBaseFieldMap : X.functionField ⟶ (extensionNormalization X E).functionField :=
  X.presheaf.stalkSpecializes (specializes_of_eq (fromNormalization_genericPoint X E)) ≫
    (extensionFromNormalization X E).stalkMap (genericPoint (extensionNormalization X E))

set_option backward.isDefEq.respectTransparency false in
theorem normalizationBaseFieldMap_germ (U : X.Opens) [Nonempty U] :
    X.germToFunctionField U ≫ normalizationBaseFieldMap X E =
      (extensionFromNormalization X E).app U ≫
        (extensionNormalization X E).germToFunctionField (extensionFromNormalization X E ⁻¹ᵁ U) := by
  rw [normalizationBaseFieldMap, ← Category.assoc,
    TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem normalizationChartRingEquiv_base (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (a : Γ(X,U)) :
    (normalizationChartRingEquiv X E U hU ((extensionFromNormalization X E).app U a) : E) =
      algebraMap X.functionField E (X.germToFunctionField U a) := by
  let := ((genericExtensionMap X E).app U).hom.toAlgebra
  have h : (extensionFromNormalization X E).app U ≫
      (extensionNormalizationObjIso X E U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X,U)
        (integralClosure Γ(X,U) Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U))) := by
    rw [(genericExtensionMap X E).fromNormalization_app hU]
    simp [extensionNormalizationObjIso]
  have he : normalizationChartRingEquiv X E U hU
      ((extensionFromNormalization X E).app U a) =
      algebraMap Γ(X,U) (integralClosure Γ(X,U) E) a := by
    change (sourceSectionsAlgEquiv X E U).mapIntegralClosure
      ((extensionNormalizationObjIso X E U hU).hom ((extensionFromNormalization X E).app U a)) = _
    rw [← ConcreteCategory.comp_apply, h]
    exact (sourceSectionsAlgEquiv X E U).mapIntegralClosure.commutes a
  exact congrArg (fun z : integralClosure Γ(X,U) E => (z : E)) he

/-- Both actual function-field maps compose to the prescribed extension-field embedding. -/
theorem normalizationFunctionFieldMap_base_compat :
    (normalizationFunctionFieldMap X E).hom.comp (normalizationBaseFieldMap X E).hom =
      algebraMap X.functionField E := by
  obtain ⟨U, hU, hηU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := genericPoint X) (U := ⊤) (by trivial)
  let : Nonempty U := ⟨⟨_, hηU⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  apply IsFractionRing.ringHom_ext (A := Γ(X,U))
  intro a
  change normalizationFunctionFieldMap X E
      (normalizationBaseFieldMap X E (X.germToFunctionField U a)) = _
  have h := congr($(normalizationBaseFieldMap_germ X E U) a)
  change normalizationBaseFieldMap X E (X.germToFunctionField U a) =
    (extensionNormalization X E).germToFunctionField (extensionFromNormalization X E ⁻¹ᵁ U)
      ((extensionFromNormalization X E).app U a) at h
  rw [h, normalizationFunctionFieldMap_chart X E U hU,
    normalizationChartRingEquiv_base X E U hU]
  rfl

theorem normalizationFunctionFieldEquiv_base_compat [Algebra.IsAlgebraic X.functionField E]
    (a : X.functionField) :
    normalizationFunctionFieldEquiv X E (normalizationBaseFieldMap X E a) =
      algebraMap X.functionField E a :=
  congr($(normalizationFunctionFieldMap_base_compat X E) a)

/-- The canonical isomorphism includes its geometric forward map and its base-field compatibility. -/
theorem exists_normalizationFunctionFieldEquiv [Algebra.IsAlgebraic X.functionField E] :
    ∃ e : (extensionNormalization X E).functionField ≃+* E,
      e.toRingHom = (normalizationFunctionFieldMap X E).hom ∧
      ∀ a : X.functionField, e (normalizationBaseFieldMap X E a) = algebraMap X.functionField E a :=
  ⟨normalizationFunctionFieldEquiv X E, normalizationFunctionFieldEquiv_toRingHom X E,
    normalizationFunctionFieldEquiv_base_compat X E⟩

/-- The canonical chart ring equivalence records the actual incoming function-field evaluation. -/
theorem exists_normalizationChartRingEquiv (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ∃ e : Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U) ≃+*
      integralClosure Γ(X,U) E,
      ∀ a, (e a : E) = normalizationFunctionFieldMap X E
        ((extensionNormalization X E).germToFunctionField (extensionFromNormalization X E ⁻¹ᵁ U) a) :=
  ⟨normalizationChartRingEquiv X E U hU, fun a => (normalizationFunctionFieldMap_chart X E U hU a).symm⟩

end
end ArithmeticThetaNormalizationField
