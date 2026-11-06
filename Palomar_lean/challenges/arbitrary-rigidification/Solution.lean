module
public import Mathlib
public import ArbitraryEvenThetaRigidificationR0213
public import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
public import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u
open CategoryTheory MonoidalCategory Limits Opposite
namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
def Compatible (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Prop :=
  ∀ (t : Γ((ihom M).obj N, ⊤)) (U : X.Opens) (m : Γ(M, U)),
    (e t).app U m = ((ihom.ev M).app N).app U
      (Scheme.Modules.tensorSections m (((ihom M).obj N).presheaf.map (homOfLE le_top).op t))
theorem canonicalGlobalSectionsEquiv : ∃! e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N), Compatible M N e := by
  let e := Scheme.Modules.ihomGlobalSectionsEquiv M N
  have he : Compatible M N e := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply AddEquiv.ext
  intro t
  ext U m
  exact (he' t U m).trans (he t U m).symm
def globalSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N) :=
  (canonicalGlobalSectionsEquiv M N).exists.choose
end ArithmeticThetaPalomarDual465
namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
theorem compatible_iff_original (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Compatible M N e ↔ e = Scheme.Modules.ihomGlobalSectionsEquiv M N := by
  have he : Compatible M N (Scheme.Modules.ihomGlobalSectionsEquiv M N) := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  constructor
  · intro h
    exact (canonicalGlobalSectionsEquiv M N).unique h he
  · rintro rfl
    exact he
theorem globalSectionsEquiv_eq_original : globalSectionsEquiv M N = Scheme.Modules.ihomGlobalSectionsEquiv M N :=
  (compatible_iff_original M N _).mp (canonicalGlobalSectionsEquiv M N).exists.choose_spec
theorem evaluationSection_eq_original (φ : M ⟶ N) : (globalSectionsEquiv M N).symm φ = (Scheme.Modules.ihomGlobalSectionsEquiv M N).symm φ := by
  rw [globalSectionsEquiv_eq_original]
end ArithmeticThetaPalomarDual465
namespace ArithmeticThetaPalomarRigidification484
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (M : FullLevel R W G 4 (𝟙 (Base R)))
def evenPoint : Base R ⟶ Curve R W := twoLabel R W G 4 M 2
def thetaIdeal : (Curve R W).IdealSheafData := (evenPoint R W G M).ker
def thetaLine : (Curve R W).Modules := (thetaIdeal R W G M).invModule
def thetaMap : (𝟙_ (Curve R W).Modules) ⟶ thetaLine R W G M := (thetaIdeal R W G M).invModuleSection
def originGenerator : (𝟙_ (Base R).Modules) ⟶ (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) :=
  (Scheme.Modules.pullbackUnitIso (origin R W)).inv ≫ (Scheme.Modules.pullback (origin R W)).map (thetaMap R W G M)
def IsRigidification (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅ (𝟙_ (Base R).Modules)) : Prop := originGenerator R W G M ≫ e.hom = 𝟙 _
theorem thetaMap_eq_original : thetaMap R W G M = ArithmeticThetaThetaEvaluationR0212.thetaMap R W G M :=
  (ArithmeticThetaThetaEvaluationR0212.EvenThetaRigidification.thetaMap_eq R W G M).symm
theorem isRigidification_iff (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅ (𝟙_ (Base R).Modules)) : IsRigidification R W G M e ↔ ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M e := by
  unfold IsRigidification originGenerator
  rw [thetaMap_eq_original]
  rfl
theorem arbitraryEvenThetaRigidification :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (ArithmeticThetaPalomarRigidification484.thetaIdeal R W G M).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaPalomarRigidification484.thetaLine R W G M) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaPalomarRigidification484.thetaMap R W G M) = ArithmeticThetaPalomarRigidification484.thetaIdeal R W G M ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaPalomarRigidification484.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)), ArithmeticThetaPalomarRigidification484.IsRigidification R W G M e) := by
  intro R _ _ W _ G hG M
  have h := ArithmeticThetaUniversalEvaluationR0213.arbitrary_even_theta_rigidification R W G hG M
  convert h using 1 <;> (try simp only [thetaMap_eq_original, isRigidification_iff]) <;> rfl
theorem recover_original_094 :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (ArithmeticThetaThetaEvaluationR0212.thetaIdeal R W G M).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaThetaEvaluationR0212.thetaMap R W G M) = ArithmeticThetaThetaEvaluationR0212.thetaIdeal R W G M ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)), ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M e) := by
  intro R _ _ W _ G hG M
  have h := arbitraryEvenThetaRigidification R W G hG M
  convert h using 1 <;> (try simp only [thetaMap_eq_original, isRigidification_iff]) <;> rfl
end ArithmeticThetaPalomarRigidification484
