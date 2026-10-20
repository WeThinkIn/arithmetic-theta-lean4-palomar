module

public import SplitNormDefinitionsR0153

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaGeometricNormR0150 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
namespace MarkedFieldAction
open ActualMultiplicationFieldNorm

lemma field_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} {φ : Y.functionField →+* X.functionField}
    {ψ : Z.functionField →+* Y.functionField} (hf : IsFieldMap f φ) (hg : IsFieldMap g ψ) :
    IsFieldMap (f ≫ g) (φ.comp ψ) := by
  unfold IsFieldMap at *
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom φ)).symm

lemma field_id (X : Scheme.{u}) [IsIntegral X] : IsFieldMap (𝟙 X) (RingHom.id _) := by
  simp [IsFieldMap]

lemma iso_field (X : Scheme.{u}) [IsIntegral X] (e : X ≅ X) :
    ∃ E : X.functionField ≃+* X.functionField, IsFieldMap e.hom E.toRingHom := by
  obtain ⟨φ, hφ⟩ := exists_fieldMap e.hom
  obtain ⟨ψ, hψ⟩ := exists_fieldMap e.inv
  have h₁ : φ.comp ψ = RingHom.id _ := by
    apply fieldMap_unique (𝟙 X) _ _ (field_id X)
    simpa only [e.hom_inv_id] using field_comp hφ hψ
  have h₂ : ψ.comp φ = RingHom.id _ := by
    apply fieldMap_unique (𝟙 X) _ _ (field_id X)
    simpa only [e.inv_hom_id] using field_comp hψ hφ
  exact ⟨{ φ with invFun := ψ
                  left_inv := fun x => DFunLike.congr_fun h₂ x
                  right_inv := fun x => DFunLike.congr_fun h₁ x }, hφ⟩

lemma iterate_add {X : Scheme.{u}} (f : X ⟶ X) (m n : ℕ) :
    iterateHom f (m+n) = iterateHom f m ≫ iterateHom f n := by
  induction n with
  | zero => simp [iterateHom]
  | succ n ih =>
    change iterateHom f (m+n) ≫ f = iterateHom f m ≫ (iterateHom f n ≫ f)
    rw [ih, Category.assoc]

lemma iterate_mod {X : Scheme.{u}} (f : X ⟶ X) (r n : ℕ)
    (hf : iterateHom f r = 𝟙 X) : iterateHom f (n%r) = iterateHom f n := by
  have hmul (q : ℕ) : iterateHom f (r*q) = 𝟙 X := by
    induction q with
    | zero => simp [iterateHom]
    | succ q ih => rw [Nat.mul_succ, iterate_add, ih, hf, Category.id_comp]
  conv_rhs => rw [← Nat.mod_add_div n r, iterate_add, hmul, Category.comp_id]

lemma iterate_comm {X : Scheme.{u}} (f g : X ⟶ X) (h : f ≫ g = g ≫ f) (n : ℕ) :
    iterateHom f n ≫ g = g ≫ iterateHom f n := by
  induction n with
  | zero => simp [iterateHom]
  | succ n ih => rw [iterateHom, Category.assoc, h, ← Category.assoc, ih, Category.assoc]

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (M : Model k T) (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X))
variable (inv : M.X ≅ M.X) (ha : Actions k M rot scal inv)

lemma generic_iterate (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) (n : ℕ) :
    genericMap k M (iterateHom f n) (AlgebraizedActionLawsR0137.iterate_over M.p f hf n) =
      iterateHom (genericMap k M f hf) n := by
  induction n with
  | zero => exact ActualScalarTranslation.genericMap_id k M _
  | succ n ih =>
    change genericMap k M (iterateHom f n ≫ f) _ = iterateHom (genericMap k M f hf) n ≫ genericMap k M f hf
    rw [ActualScalarTranslation.genericMap_comp k M _ _ (AlgebraizedActionLawsR0137.iterate_over M.p f hf n) hf, ih]

def modelTranslation (i : Fin r) (a : kˣ) : M.X ⟶ M.X :=
  iterateHom rot.hom i.val ≫ (scal a).hom

include ha in
lemma model_over (i : Fin r) (a : kˣ) : modelTranslation k M rot scal i a ≫ M.p = M.p := by
  rw [modelTranslation, Category.assoc, modelOver k M id a false (scal a) (ha.2.1 a)]
  exact AlgebraizedActionLawsR0137.iterate_over M.p rot.hom (modelOver k M _ _ _ rot ha.1) _

lemma translation_generic (i : Fin r) (a : kˣ) :
    translation k M rot scal inv ha i a =
      genericMap k M (modelTranslation k M rot scal i a) (model_over k M rot scal inv ha i a) := by
  change _ = genericMap k M (iterateHom rot.hom i.val ≫ (scal a).hom) _
  rw [ActualScalarTranslation.genericMap_comp k M _ _
    (AlgebraizedActionLawsR0137.iterate_over M.p rot.hom (modelOver k M _ _ _ rot ha.1) i.val)
    (modelOver k M id a false (scal a) (ha.2.1 a)), generic_iterate]
  rfl

lemma translation_over (i : Fin r) (a : kˣ) :
    translation k M rot scal inv ha i a ≫ genericStructure k M = genericStructure k M := by
  rw [translation_generic]
  exact ActualRotationTranslation.genericMap_structure k M _ _

lemma translation_isIso (i : Fin r) (a : kˣ) : IsIso (translation k M rot scal inv ha i a) := by
  have hi (n : ℕ) : IsIso (iterateHom rot.hom n) := by
    induction n with
    | zero => exact inferInstanceAs (IsIso (𝟙 M.X))
    | succ n ih => letI := ih; exact inferInstanceAs (IsIso (iterateHom rot.hom n ≫ rot.hom))
  letI := hi i.val
  letI : IsIso (modelTranslation k M rot scal i a) := inferInstanceAs (IsIso (iterateHom rot.hom i.val ≫ (scal a).hom))
  rw [translation_generic]
  exact inferInstanceAs (IsIso (ActualScalarTranslation.genericIso k M
    (asIso (modelTranslation k M rot scal i a)) (model_over k M rot scal inv ha i a)).hom)

lemma translation_add (hM : IsModel k T M) (i j : Fin r) (a b : kˣ) :
    translation k M rot scal inv ha (shift (hr := hr) i j) (a*b) =
      translation k M rot scal inv ha i a ≫ translation k M rot scal inv ha j b := by
  have laws := AlgebraizedActionLawsR0137.laws M hM rot scal inv ha
  have hm : modelTranslation k M rot scal (shift (hr := hr) i j) (a*b) =
      modelTranslation k M rot scal i a ≫ modelTranslation k M rot scal j b := by
    simp only [modelTranslation, shift]
    rw [iterate_mod _ r _ laws.1, iterate_add, laws.2.2.1]
    have hc := iterate_comm rot.hom (scal a).hom (laws.2.2.2.2.1 a) j.val
    simp only [Category.assoc]
    rw [← Category.assoc (iterateHom rot.hom j.val), hc, Category.assoc]
  simp only [translation_generic]
  rw [← ActualScalarTranslation.genericMap_comp]
  exact ActualScalarTranslation.genericMap_congr k M _ _ _ _ hm

lemma point_rotation (h3 : 3 ≤ r) (hM : IsModel k T M) (i : Fin r) (a : kˣ) :
    (MarkedPointAddition.point k h3 M hM i a).val ≫ rotationMap k M rot scal inv ha =
      (MarkedPointAddition.point k h3 M hM (next r hr i) a).val := by
  apply MarkedPointAddition.point_map
  exact (algebraized_marked_transport k r hr h3 T M hM rot scal inv ha i a _
    (MarkedPointAddition.sectionAt_spec k h3 M hM i a)).1

lemma point_translation (h3 : 3 ≤ r) (hM : IsModel k T M) (i : Fin r) (a : kˣ) :
    (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) 1).val ≫
      translation k M rot scal inv ha i a = (MarkedPointAddition.point k h3 M hM i a).val := by
  have hn (n : ℕ) : (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) 1).val ≫
      iterateHom (rotationMap k M rot scal inv ha) n =
      (MarkedPointAddition.point k h3 M hM ((next r hr)^[n] (zeroIndex r hr)) 1).val := by
    induction n with
    | zero => simp [iterateHom]
    | succ n ih => rw [iterateHom, ← Category.assoc, ih, point_rotation, Function.iterate_succ_apply']
  have hi : (next r hr)^[i.val] (zeroIndex r hr) = i := by
    apply Fin.ext
    rw [AlgebraizedActionLawsR0137.next_iterate_val]
    simp only [zeroIndex, zero_add, Nat.mod_eq_of_lt i.isLt]
  rw [translation, ← Category.assoc, hn, hi]
  apply MarkedPointAddition.point_map
  simpa only [mul_one] using
    (algebraized_marked_transport k r hr h3 T M hM rot scal inv ha i 1 _
      (MarkedPointAddition.sectionAt_spec k h3 M hM i 1)).2.1 a

lemma translation_injective (h3 : 3 ≤ r) (hM : IsModel k T M) :
    Function.Injective (fun ia : Fin r × kˣ => translation k M rot scal inv ha ia.1 ia.2) := by
  intro ⟨i,a⟩ ⟨j,b⟩ h
  have hp := congrArg (fun f => (MarkedPointAddition.point k h3 M hM (zeroIndex r hr) 1).val ≫ f) h
  rw [point_translation, point_translation] at hp
  have hh := MarkedExactTorsion.labels_eq k M hM _ _
    (MarkedPointAddition.sectionAt_spec k h3 M hM i a)
    (MarkedPointAddition.sectionAt_spec k h3 M hM j b) (Subtype.ext hp)
  exact Prod.ext hh.1 hh.2

lemma field_faithful [IsIntegral (genericScheme k M)] (hM : IsModel k T M)
    (f g : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M)
    (hg : g ≫ genericStructure k M = genericStructure k M)
    (φ : (genericScheme k M).functionField →+* (genericScheme k M).functionField)
    (hφ : IsFieldMap f φ) (hψ : IsFieldMap g φ) : f = g := by
  let X := genericScheme k M
  letI : IsProper (genericStructure k M) := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI : IsDominant (X.fromSpecStalk (_root_.genericPoint X)) := by
    constructor
    apply (dense_iff_closure_eq.mpr (genericPoint_spec X)).mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [Scheme.range_fromSpecStalk]
    exact specializes_rfl
  exact ext_of_isDominant_of_isSeparated (genericStructure k M) (hf.trans hg.symm)
    (X.fromSpecStalk (_root_.genericPoint X)) (hφ.trans hψ.symm)

end MarkedFieldAction

open MarkedFieldAction ActualMultiplicationFieldNorm

/-- The specified actual translations act faithfully on the generic function field. -/
theorem marked_field_action :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∃! σ : Fin r → kˣ → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) ≃+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaSplitNormR0153.IsFieldAction k M rot scal inv ha σ ∧ Function.Injective (fun ia : Fin r × kˣ => σ ia.1 ia.2) ∧ (∀ (i j : Fin r) (a b : kˣ), σ (ArithmeticThetaSplitNormR0153.shift (hr := hr) i j) (a*b) = (σ i a).trans (σ j b)) ∧ (∀ (i : Fin r) (a : kˣ) (v : LaurentSeries k), σ i a (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) v) = ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (LaurentSeries k) (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) v) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ rot scal inv ha
  have hex (i : Fin r) (a : kˣ) : ∃ E : (genericScheme k M).functionField ≃+*
      (genericScheme k M).functionField, IsFieldMap (translation k M rot scal inv ha i a) E.toRingHom := by
    letI := translation_isIso k M rot scal inv ha i a
    exact iso_field _ (asIso (translation k M rot scal inv ha i a))
  choose σ hσ using hex
  refine ⟨σ, ⟨hσ, ?_, ?_, ?_⟩, ?_⟩
  · intro ⟨i,a⟩ ⟨j,b⟩ hij
    apply translation_injective k M rot scal inv ha h3 hM
    apply field_faithful k M hM _ _
      (translation_over k M rot scal inv ha i a)
      (translation_over k M rot scal inv ha j b) (σ i a).toRingHom (hσ i a)
    simpa only [hij] using hσ j b
  · intro i j a b
    apply RingEquiv.toRingHom_injective
    symm
    apply fieldMap_unique _ _ _ (hσ _ _)
    have hh := field_comp (hσ j b) (hσ i a)
    have hs : shift (hr := hr) j i = shift (hr := hr) i j := by
      apply Fin.ext
      exact congrArg (fun n => n % r) (Nat.add_comm j.val i.val)
    rw [← translation_add k M rot scal inv ha hM, hs, mul_comm b a] at hh
    exact hh
  · intro i a v
    exact fieldMap_baseScalar (X := genericScheme k M) (LaurentSeries k) (genericStructure k M)
      _ (translation_over k M rot scal inv ha i a) _ (hσ i a) v
  · intro τ hτ
    funext i a
    apply RingEquiv.toRingHom_injective
    exact fieldMap_unique _ _ _ (hσ i a) (hτ.1 i a)

#print axioms marked_field_action
end ArithmeticThetaSplitNormR0153
