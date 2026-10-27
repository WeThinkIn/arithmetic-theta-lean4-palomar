import RamifiedGenericBaseChangeR0155
import Mathlib.RingTheory.Etale.Field

/-! Function fields of the specified ramified generic base change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0155
namespace RamifiedFunctionFieldExpansion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152.CompletedChartFieldMaps

/-- Finite separable coefficient extensions retain their degree after geometric
base change. Both scalar instances are explicitly attached to the given map. -/
lemma finite_etale_base_change {R S : Type u} [Field R] [Field S] [CharZero R]
    (ell : R →+* S) (d : ℕ)
    (hdeg : letI := ell.toAlgebra
      letI : Module R S := @Algebra.toModule _ _ _ _ ell.toAlgebra
      FiniteDimensional R S ∧ Module.finrank R S = d)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (pX : X ⟶ Spec (.of S))
    (pY : Y ⟶ Spec (.of R))
    (H : IsPullback f pX pY (Spec.map (CommRingCat.ofHom ell))) :
    IsFinite f ∧ Etale f ∧ Surjective f ∧ ∀ y, f.finrank y = d := by
  letI : Algebra R S := ell.toAlgebra
  letI : Module R S := @Algebra.toModule _ _ _ _ ell.toAlgebra
  letI : FiniteDimensional R S := hdeg.1
  letI : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isSeparable R S
  letI : Algebra.Etale R S := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let b := Spec.map (CommRingCat.ofHom ell)
  letI : IsFinite b := (IsFinite.SpecMap_iff _).mpr hdeg.1
  letI : Etale b := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (show ell.Etale from inferInstanceAs (Algebra.Etale R S))
  letI : Surjective b := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  letI : IsFinite f := MorphismProperty.of_isPullback H.flip inferInstance
  letI : Etale f := MorphismProperty.of_isPullback H.flip inferInstance
  letI : Surjective f := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨inferInstance, inferInstance, inferInstance, fun y => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback pX f b pY H.flip y]
  change (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank (pY y) = d
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  exact hdeg.2

/-- Naturality at the generic point gives the complete scalar equation. -/
lemma fieldMap_scalar {R S : Type u} [Field R] [Field S]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (ell : R →+* S) (f : X ⟶ Y) (pX : X ⟶ Spec (.of S))
    (pY : Y ⟶ Spec (.of R)) (h : f ≫ pY = pX ≫ Spec.map (CommRingCat.ofHom ell))
    (α : Y.functionField →+* X.functionField) (hα : IsFieldMap f α) (v : R) :
    α (baseScalar R pY v) = baseScalar S pX (ell v) := by
  have he : α.comp (ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization.scalarHom R pY) =
      (ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization.scalarHom S pX).comp ell := by
    suffices hc : CommRingCat.ofHom (α.comp (ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization.scalarHom R pY)) =
        CommRingCat.ofHom ((ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization.scalarHom S pX).comp ell) from
      congrArg CommRingCat.Hom.hom hc
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization.scalarHom R pY) ≫
      CommRingCat.ofHom α) = Spec.map (CommRingCat.ofHom ell ≫
      CommRingCat.ofHom (ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization.scalarHom S pX))
    rw [Spec.map_comp, Spec.map_comp, scalarHom_square, scalarHom_square,
      ← Category.assoc, ← hα, Category.assoc, h, Category.assoc]
  exact RingHom.congr_fun he v

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152
open ArithmeticThetaRamifiedPeriodR0154

/-- The prescribed integral chart square descends to every rational function. -/
lemma fieldMap_chart (k : Type u) [Field k] [CharZero k]
    {r rb : ℕ} {hr : 0 < r} {hrb : 0 < rb}
    {T : Tower k r hr} {Tb : Tower k rb hrb}
    (M : Model k T) (Mb : Model k Tb)
    [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme k Mb)]
    (F : Mb.X ⟶ M.X) (f : genericScheme k Mb ⟶ genericScheme k M)
    (hf : f ≫ genericInclusion k M = genericInclusion k Mb ≫ F)
    (χ : chartScheme k ⟶ M.X) (χb : chartScheme k ⟶ Mb.X)
    (ρ : Chart k →+* Chart k)
    (hc : χb ≫ F = Spec.map (CommRingCat.ofHom ρ) ≫ χ)
    (α : (genericScheme k M).functionField →+* (genericScheme k Mb).functionField)
    (hα : IsFieldMap f α)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (φb : (genericScheme k Mb).functionField →+* ChartField k) (hφb : IsChartFieldMap k Mb χb φb)
    (E : ChartField k →+* ChartField k) (hE : ExtendsChart k ρ E) :
    φb.comp α = E.comp φ := by
  have hleft : IsChartFieldMap k M (χb ≫ F) (φb.comp α) := by
    change Spec.map (CommRingCat.ofHom α ≫ CommRingCat.ofHom φb) ≫ _ ≫ _ = _
    rw [Spec.map_comp, Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom α)),
      ← hα, Category.assoc, hf]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ F) hφb
  have hright : IsChartFieldMap k M (χb ≫ F) (E.comp φ) := by
    change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom E) ≫ _ ≫ _ = _
    rw [Spec.map_comp, Category.assoc, hφ, hc]
    have he : Spec.map (CommRingCat.ofHom E) ≫ Spec.map (CommRingCat.ofHom (chartToField k)) =
        Spec.map (CommRingCat.ofHom (chartToField k)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun z => Spec.map (CommRingCat.ofHom z)) (RingHom.ext hE)
    rw [← Category.assoc, he, Category.assoc]
  exact CompletedChartFieldMaps.fieldMap_unique k M (χb ≫ F) (E.comp φ) (φb.comp α) hright hleft

end RamifiedFunctionFieldExpansion

/-- The actual ramified function-field embedding, its exact degree, every chart
expansion, and its complete Laurent scalar action. -/
theorem ramified_function_field_expansion :
∀ (k : Type u)
    [Field k] [CharZero k] (d : ℕ)
    (hd : 0 < d)
    (r : ℕ)
    (hr : 0 < r)
    (h3 : 3 ≤ r)
    (hrd : 0 < r*d)
    (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
    (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (r*d) hrd)
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model k Tb)
    (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel k Tb Mb)
    [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb)] (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k))
    (hρ : ∀ q, ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q (ρ q))
    (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k)
    (M.X))
    (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j))
    (χb : Fin (r*d) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k)
    (Mb.X))
    (hχb : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k Mb j (χb j))
    (F : Quiver.Hom (Mb.X)
    (M.X))
    (hF : ArithmeticThetaRamifiedPeriodR0154.IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F)
    (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell)
    (f : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb)
    (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))
    (hf : ArithmeticThetaRamifiedPeriodR0154.IsGenericLift k T Tb M Mb F f)
    (φ : Fin r → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k))
    (hφ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j)
    (φ j))
    (φb : Fin (r*d) → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb)) →+* ArithmeticThetaKatoAnnularR0152.ChartField k))
    (hφb : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k Mb (χb j)
    (φb j))
    (E : Fin d → (ArithmeticThetaKatoAnnularR0152.ChartField k →+* ArithmeticThetaKatoAnnularR0152.ChartField k))
    (hE : ∀ q, ArithmeticThetaRamifiedPeriodR0154.ExtendsChart k (ρ q)
    (E q)), ∃! α : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb)), ArithmeticThetaGeometricNormR0150.IsFieldMap f α ∧ ArithmeticThetaRamifiedPeriodR0155.FiniteFieldMap α ∧ ArithmeticThetaRamifiedPeriodR0155.fieldDegree α = d ∧ (∀ (j : Fin (r*d))
    (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), φb j (α g) = E (ArithmeticThetaRamifiedPeriodR0154.residueIndex r d hd j)
    (φ (ArithmeticThetaRamifiedPeriodR0154.coarseIndex r d hd j) g)) ∧ (∀ v : LaurentSeries k, α (ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))
    (LaurentSeries k)
    (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) v) = ArithmeticThetaGeometricNormR0150.baseScalar (X := (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb))
    (LaurentSeries k)
    (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k Mb)
    (ell v)) := by
  intro k _ _ d hd r hr h3 hrd T Tb M hM Mb hMb _ _ ρ hρ χ hχ χb hχb F hF ell hell f hf φ hφ φb hφb E hE
  obtain ⟨f₀, hf₀, _⟩ := ramified_generic_base_change k d hd r hr h3 hrd T Tb M hM Mb hMb
    ρ hρ χ hχ χb hχb F hF ell hell
  have he : f = f₀ := by
    letI : AlgebraicGeometry.IsOpenImmersion (ArithmeticThetaGenericEvaluationR0140.genericInclusion k M) :=
      ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
    apply (CategoryTheory.cancel_mono (ArithmeticThetaGenericEvaluationR0140.genericInclusion k M)).mp
    exact hf.trans hf₀.1.symm
  have H : CategoryTheory.IsPullback f (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k Mb)
      (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ell)) := by
    rw [he]
    exact hf₀.2
  have hdegree : LaurentDegree k d ell := by
    obtain ⟨ell₀, h₀, _⟩ := ramified_laurent_extension k d hd
    have he : ell = ell₀ := IsFractionRing.ringHom_ext (fun x => (hell x).trans (h₀.1 x).symm)
    simpa only [he] using h₀.2
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨hfinite, hetale, hsurj, hrank⟩ :=
    RamifiedFunctionFieldExpansion.finite_etale_base_change ell d hdegree f
      (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k Mb)
      (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M) H
  letI := hfinite
  letI := hetale
  letI := hsurj
  obtain ⟨α, hα⟩ := ArithmeticThetaGeometricNormR0150.ActualMultiplicationFieldNorm.exists_fieldMap f
  obtain ⟨hfin, hdeg, _⟩ := ArithmeticThetaGeometricNormR0150.finite_etale_local_norm _ _ f α hα
  refine ⟨α, ⟨hα, hfin, ?_, ?_, ?_⟩, ?_⟩
  · exact (hdeg (_root_.genericPoint _)).symm.trans (hrank _)
  · intro j g
    exact RingHom.congr_fun (RamifiedFunctionFieldExpansion.fieldMap_chart k M Mb F f hf
      (χ _) (χb j) (ρ _) (hF.2 j) α hα (φ _) (hφ _) (φb j) (hφb j) (E _) (hE _)) g
  · intro v
    exact RamifiedFunctionFieldExpansion.fieldMap_scalar ell f _ _ H.w α hα v
  · intro β hβ
    exact ArithmeticThetaGeometricNormR0150.ActualMultiplicationFieldNorm.fieldMap_unique f α β hα hβ.1

end ArithmeticThetaRamifiedPeriodR0155

#print axioms ArithmeticThetaRamifiedPeriodR0155.ramified_function_field_expansion
