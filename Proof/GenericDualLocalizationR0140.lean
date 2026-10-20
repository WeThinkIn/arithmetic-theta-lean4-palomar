module

public import GenericThetaEvaluationDefinitionsR0140
public import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ihom_ev_app_monoidalV2

public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2

@[expose] public section

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

/-- A single power of the uniformizer clears any tensor, including zero. -/
lemma tensor_clear (k : Type u) [Field k] (V : Type*) [AddCommGroup V]
    [Module (PowerSeries k) V] (z : LaurentSeries k ⊗[PowerSeries k] V) :
    ∃ (b : ℕ) (v : V),
      (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^b • z = 1 ⊗ₜ v := by
  obtain ⟨⟨v, a⟩, ha⟩ := IsLocalizedModule.surj
    (Submonoid.powers (PowerSeries.X : PowerSeries k))
    (TensorProduct.mk (PowerSeries k) (LaurentSeries k) V 1) z
  obtain ⟨b, hb⟩ := a.property
  refine ⟨b, v, ?_⟩
  change (a.val : PowerSeries k) • z = 1 ⊗ₜ v at ha
  rw [← hb] at ha
  simpa only [← map_pow, algebraMap_smul] using ha

/-- Flat base change and localization produce an actual pulled-back section. -/
lemma section_clear (k : Type u) [Field k]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))
    [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of (LaurentSeries k))) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k)))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    letI : Algebra (LaurentSeries k) Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ f'.appTop).hom.toAlgebra
    letI : Module (LaurentSeries k) Γ((Scheme.Modules.pullback c).obj L, ⊤) :=
      Module.compHom _ (algebraMap (LaurentSeries k) Γ(X', ⊤))
    ∀ z : Γ((Scheme.Modules.pullback c).obj L, ⊤), ∃ (b : ℕ) (v : Γ(L, ⊤)),
      (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^b • z =
        Scheme.Modules.pullbackLocalSection c v := by
  letI : Algebra (PowerSeries k) Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv ≫ f.appTop).hom.toAlgebra
  letI : Module (PowerSeries k) Γ(L, ⊤) :=
    Module.compHom _ (algebraMap (PowerSeries k) Γ(X, ⊤))
  letI : Algebra (LaurentSeries k) Γ(X', ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ f'.appTop).hom.toAlgebra
  letI : Module (LaurentSeries k) Γ((Scheme.Modules.pullback c).obj L, ⊤) :=
    Module.compHom _ (algebraMap (LaurentSeries k) Γ(X', ⊤))
  letI : Module.Flat (PowerSeries k) (LaurentSeries k) :=
    IsLocalization.flat (S := LaurentSeries k) (Submonoid.powers (PowerSeries.X : PowerSeries k))
  obtain ⟨β, hβ⟩ := Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
    (LaurentSeries k) f f' c hc L hL
  intro z
  obtain ⟨b, v, hv⟩ := tensor_clear k Γ(L, ⊤) (β.symm z)
  refine ⟨b, v, ?_⟩
  have h := congrArg β hv
  simpa only [map_smul, LinearEquiv.apply_symm_apply, hβ,
    Scheme.Modules.pullbackLocalSection] using h

open MonoidalCategory
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133 (unitPullback_isIso)

lemma isIso_curry {X : Scheme.{u}} {L D : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (e : L ⊗ D ⟶ 𝟙_ X.Modules)
    [IsIso e] : IsIso (MonoidalClosed.curry e) := by
  obtain ⟨N, -, ⟨a⟩⟩ := hL.exists_tensor_inverse_monoidalV2
  let E := P2MW.S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit.ReflSol.tensorLeftEquiv a
  letI : (tensorLeft L).IsEquivalence := E.isEquivalence_functor
  letI := (hL.isIso_ihom_ev_app_monoidalV2).1 (𝟙_ X.Modules)
  have h : L ◁ MonoidalClosed.curry e ≫ (ihom.ev L).app (𝟙_ X.Modules) = e :=
    MonoidalClosed.uncurry_curry e
  haveI : IsIso (L ◁ MonoidalClosed.curry e) := by
    haveI : IsIso (L ◁ MonoidalClosed.curry e ≫ (ihom.ev L).app (𝟙_ X.Modules)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((ihom.ev L).app (𝟙_ X.Modules))
  letI : IsIso ((tensorLeft L).map (MonoidalClosed.curry e)) :=
    inferInstanceAs (IsIso (L ◁ MonoidalClosed.curry e))
  exact isIso_of_reflects_iso (MonoidalClosed.curry e) (tensorLeft L)

/-- The comparison is defined from the pulled-back evaluation morphism. -/
def dualComparison {X Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules) :
    (Scheme.Modules.pullback c).obj (Scheme.Modules.dual L) ⟶
      Scheme.Modules.dual ((Scheme.Modules.pullback c).obj L) :=
  MonoidalClosed.curry ((Scheme.Modules.pullbackTensorObjIso c L (Scheme.Modules.dual L)).inv ≫
    (Scheme.Modules.pullback c).map ((ihom.ev L).app (𝟙_ Y.Modules)) ≫ unitPullback c)

lemma dualComparison_isIso {X Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules)
    (hL : Scheme.Modules.IsInvertible L) : IsIso (dualComparison c L) := by
  letI := (hL.isIso_ihom_ev_app_monoidalV2).1 (𝟙_ Y.Modules)
  letI := unitPullback_isIso c
  exact isIso_curry (hL.pullback c) _

open Scheme.Modules

lemma unitPullback_app {X Y : Scheme.{u}} (c : X ⟶ Y) (U : Y.Opens)
    (a : Γ(Y, U)) :
    (unitPullback c).app (c ⁻¹ᵁ U) (pullbackLocalSection c a) = c.app U a := by
  rw [app_pullbackLocalSection]
  change (((SheafOfModules.pullbackPushforwardAdjunction c.toRingCatSheafHom).homEquiv _ _)
    (((SheafOfModules.pullbackPushforwardAdjunction c.toRingCatSheafHom).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))).val.app (Opposite.op U) a = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma dualComparison_eval {X Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules)
    (U : Y.Opens) (x : Γ(L, U)) (t : Γ(dual L, U)) :
    ihomEval _ _ (c ⁻¹ᵁ U) (pullbackLocalSection c x)
      ((dualComparison c L).app (c ⁻¹ᵁ U) (pullbackLocalSection c t)) =
        c.app U (ihomEval L (𝟙_ Y.Modules) U x t) := by
  unfold dualComparison
  rw [ihomEval_curry_app]
  have ht := pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 c x t
  rw [← ht]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hi := congrArg (fun q => q.app (c ⁻¹ᵁ U)
    (pullbackLocalSection c (tensorSections x t))) (pullbackTensorObjIso c L (dual L)).hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at hi
  rw [hi]
  rw [← pullbackLocalSection_app]
  have he := ihom_ev_app_tensorSections (M := L) (N := 𝟙_ Y.Modules) U x t
  exact (congrArg (fun a : Γ(𝟙_ Y.Modules, U) =>
    (unitPullback c).app (c ⁻¹ᵁ U) (pullbackLocalSection c a)) he).trans
      (unitPullback_app c U _)

lemma dualComparison_global {X Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules)
    (t : Γ(dual L, ⊤)) :
    ihomGlobalSectionsEquiv _ _
        ((dualComparison c L).app ⊤ (pullbackLocalSection c t)) =
      (Scheme.Modules.pullback c).map (ihomGlobalSectionsEquiv L (𝟙_ Y.Modules) t) ≫ unitPullback c := by
  apply pullback_hom_ext
  intro U x
  rw [ihomGlobalSectionsEquiv_app_apply]
  have hn := (dualComparison c L).mapPresheaf.naturality_apply
    (homOfLE (show c ⁻¹ᵁ U ≤ ⊤ from le_top)).op (pullbackLocalSection c t)
  erw [← hn]
  erw [map_homOfLE_pullbackLocalSection c (show U ≤ ⊤ from le_top) t]
  erw [dualComparison_eval c L U x (L.dual.presheaf.map (homOfLE le_top).op t)]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [← pullbackLocalSection_app]
  erw [unitPullback_app c U]
  rw [ihomGlobalSectionsEquiv_app_apply]

/-- Schematic density detects maps into the structure sheaf on every open. -/
lemma restriction_injective {X Y : Scheme.{u}} (c : X ⟶ Y)
    [IsSchemeTheoreticallyDominant c] [QuasiCompact c] (L : Y.Modules) :
    Function.Injective (fun φ : L ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) =>
      (Scheme.Modules.pullback c).map φ ≫ unitPullback c) := by
  intro φ ψ h
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  apply c.app_injective U
  have hv := congrArg (fun q => q.app (c ⁻¹ᵁ U) (pullbackLocalSection c x)) h
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hv
  erw [← pullbackLocalSection_app, ← pullbackLocalSection_app,
    unitPullback_app, unitPullback_app] at hv
  exact hv

lemma genericBase_schematic (k : Type u) [Field k] [CharZero k] :
    IsSchemeTheoreticallyDominant (ArithmeticThetaProjectiveEffectivityR0135.genericBase k) := by
  letI : IsDominant (ArithmeticThetaProjectiveEffectivityR0135.genericBase k) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap (PowerSeries k) (LaurentSeries k)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

lemma ihomGlobal_smul {X : Scheme.{u}} (L : X.Modules)
    (a : Γ(X, ⊤)) (t : Γ(dual L, ⊤)) (U : X.Opens) (x : Γ(L, U)) :
    (ihomGlobalSectionsEquiv L (𝟙_ X.Modules) (a • t)).app U x =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a *
        (show Γ(X, U) from (ihomGlobalSectionsEquiv L (𝟙_ X.Modules) t).app U x) := by
  rw [ihomGlobalSectionsEquiv_app_apply, ihomGlobalSectionsEquiv_app_apply,
    Scheme.Modules.map_smul, ihomEval_smul_right]
  rfl

end ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

namespace ArithmeticThetaGenericEvaluationR0140
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138
open GenericDualLocalizationR0140
open Scheme.Modules

/-- Restriction is faithful, and every actual generic dual section has one
uniform vertical denominator. All nonnegative powers are included. -/
theorem generic_dual_localization :
∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (d : ℕ), Function.Injective (ArithmeticThetaGenericEvaluationR0140.restrictDual k M s d) ∧ ∀ ψ : ArithmeticThetaGenericEvaluationR0140.GenericDual k M s d, ∃ (b : ℕ) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s d), ArithmeticThetaGenericEvaluationR0140.ScaledEq k M s d ((algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^b) ψ (ArithmeticThetaGenericEvaluationR0140.restrictDual k M s d φ) := by
  intro k _ _ r hr h3 T M hM s hs d
  letI : IsProper M.p := hM.1
  letI : Flat M.p := hM.2.1
  letI : IsSchemeTheoreticallyDominant (genericBase k) := genericBase_schematic k
  letI : IsSchemeTheoreticallyDominant (genericInclusion k M) :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.fst M.p (genericBase k)))
  letI : QuasiCompact (genericInclusion k M) :=
    inferInstanceAs (QuasiCompact (pullback.fst M.p (genericBase k)))
  constructor
  · exact restriction_injective (genericInclusion k M) (powerModule k M s d)
  · intro ψ
    let L := powerModule k M s d
    have hL : Scheme.Modules.IsInvertible L :=
      (AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d).isInvertible_module
    let c := genericInclusion k M
    let δ := dualComparison c L
    letI : IsIso δ := dualComparison_isIso c L hL
    let t : Γ(dual ((Scheme.Modules.pullback c).obj L), ⊤) :=
      (ihomGlobalSectionsEquiv _ _).symm ψ
    let z : Γ((Scheme.Modules.pullback c).obj (dual L), ⊤) := (inv δ).app ⊤ t
    letI : Algebra (LaurentSeries k) Γ(genericScheme k M, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫
        (genericStructure k M).appTop).hom.toAlgebra
    letI : Module (LaurentSeries k) Γ((Scheme.Modules.pullback c).obj (dual L), ⊤) :=
      Module.compHom _ (algebraMap (LaurentSeries k) Γ(genericScheme k M, ⊤))
    obtain ⟨b, v, hv⟩ := section_clear k M.p (genericStructure k M) c
      (IsPullback.of_hasPullback M.p (genericBase k)) (dual L) hL.dual.1 z
    refine ⟨b, ihomGlobalSectionsEquiv L (𝟙_ M.X.Modules) v, ?_⟩
    let a : LaurentSeries k := (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^b
    let A : Γ(genericScheme k M, ⊤) := (genericStructure k M).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv a)
    have hz : δ.app ⊤ z = t := by
      have h := congrArg (fun q => q.app ⊤ t) (IsIso.inv_hom_id δ)
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h
    have hδ : A • t = δ.app ⊤ (pullbackLocalSection c v) := by
      change A • z = pullbackLocalSection c v at hv
      have h := congrArg (fun w => δ.app ⊤ w) hv
      rw [Scheme.Modules.Hom.app_smul, hz] at h
      exact h
    have hg : ihomGlobalSectionsEquiv _ _ (δ.app ⊤ (pullbackLocalSection c v)) =
        restrictDual k M s d (ihomGlobalSectionsEquiv L (𝟙_ M.X.Modules) v) :=
      dualComparison_global c L v
    intro U x
    have h := congrArg (fun w => (ihomGlobalSectionsEquiv _ _ w).app U x) hδ
    rw [ihomGlobal_smul] at h
    erw [hg] at h
    have ht : ihomGlobalSectionsEquiv _ _ t = ψ :=
      (ihomGlobalSectionsEquiv ((Scheme.Modules.pullback c).obj L)
        (𝟙_ (genericScheme k M).Modules)).apply_symm_apply ψ
    erw [ht] at h
    exact h

end ArithmeticThetaGenericEvaluationR0140
#print axioms ArithmeticThetaGenericEvaluationR0140.generic_dual_localization

