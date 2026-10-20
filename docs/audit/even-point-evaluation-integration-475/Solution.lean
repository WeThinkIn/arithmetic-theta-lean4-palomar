module
public import Mathlib
public import EvenPointThetaEvaluationR0217
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
namespace ArithmeticThetaPalomarTheta473
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def thetaIdeal : E.curve.IdealSheafData := P.point.val.ker
def thetaLine : E.curve.Modules := (thetaIdeal E P).invModule
def thetaMap : (𝟙_ E.curve.Modules) ⟶ thetaLine E P :=
  (thetaIdeal E P).invModuleSection
def pushforwardLine : S.Modules := (Scheme.Modules.pushforward E.p).obj (thetaLine E P)
def generator : (𝟙_ S.Modules) ⟶ pushforwardLine E P :=
  E.p.unitToPushforwardUnit ≫ (Scheme.Modules.pushforward E.p).map (thetaMap E P)
def originGenerator : (𝟙_ S.Modules) ⟶ (Scheme.Modules.pullback E.zero).obj (thetaLine E P) :=
  (Scheme.Modules.pullbackUnitIso E.zero).inv ≫
    (Scheme.Modules.pullback E.zero).map (thetaMap E P)
def IsRigidification (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Prop := originGenerator E P ≫ e.hom = 𝟙 _
def evaluation (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : pushforwardLine E P ⟶ (𝟙_ S.Modules) :=
  (Scheme.Modules.pushforward E.p).map
    ((Scheme.Modules.pullbackPushforwardAdjunction E.zero).unit.app (thetaLine E P) ≫
      (Scheme.Modules.pushforward E.zero).map e.hom) ≫
    (Scheme.Modules.pushforwardComp E.zero E.p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (E.law.one (𝟙 S)).property).hom.app _ ≫
    (Scheme.Modules.pushforwardId S).hom.app _
def evaluationSection (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Γ(Scheme.Modules.dual (pushforwardLine E P), ⊤) :=
  (ArithmeticThetaPalomarDual465.globalSectionsEquiv (pushforwardLine E P)
    (𝟙_ S.Modules)).symm (evaluation E P e)
theorem evaluationSection_eq_original (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : evaluationSection E P e = ArithmeticThetaMultiplierKeyR0217.evaluationSection E P e :=
  ArithmeticThetaPalomarDual465.evaluationSection_eq_original _ _ _
theorem evenPointThetaEvaluation :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), (ArithmeticThetaPalomarTheta473.thetaIdeal E P).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaPalomarTheta473.thetaLine E P) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaPalomarTheta473.thetaMap E P) = ArithmeticThetaPalomarTheta473.thetaIdeal E P ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaPalomarTheta473.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaPalomarTheta473.IsRigidification E P e) ∧ CategoryTheory.IsIso (ArithmeticThetaPalomarTheta473.generator E P) ∧ (∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaPalomarTheta473.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaPalomarTheta473.IsRigidification E P e → CategoryTheory.IsIso (ArithmeticThetaPalomarTheta473.evaluation E P e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaPalomarTheta473.generator E P) (ArithmeticThetaPalomarTheta473.evaluation E P e) = CategoryTheory.CategoryStruct.id (SheafOfModules.unit S.ringCatSheaf) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaPalomarTheta473.pushforwardLine E P)) ⊤ (ArithmeticThetaPalomarTheta473.evaluationSection E P e)) := by
  intro k _ _ S σ E P
  have h := ArithmeticThetaMultiplierKeyR0217.even_point_theta_evaluation k S σ E P
  convert h using 1 <;> (try simp only [evaluationSection_eq_original]) <;> rfl
theorem recover_original_099 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), (ArithmeticThetaMultiplierKeyR0217.thetaIdeal E P).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaMultiplierKeyR0217.thetaLine E P) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaMultiplierKeyR0217.thetaMap E P) = ArithmeticThetaMultiplierKeyR0217.thetaIdeal E P ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e) ∧ CategoryTheory.IsIso (ArithmeticThetaMultiplierKeyR0217.generator E P) ∧ (∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → CategoryTheory.IsIso (ArithmeticThetaMultiplierKeyR0217.evaluation E P e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaMultiplierKeyR0217.generator E P) (ArithmeticThetaMultiplierKeyR0217.evaluation E P e) = CategoryTheory.CategoryStruct.id (SheafOfModules.unit S.ringCatSheaf) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaMultiplierKeyR0217.pushforwardLine E P)) ⊤ (ArithmeticThetaMultiplierKeyR0217.evaluationSection E P e)) := by
  intro k _ _ S σ E P
  have h := evenPointThetaEvaluation k S σ E P
  convert h using 1 <;> (try simp only [evaluationSection_eq_original]) <;> rfl
end ArithmeticThetaPalomarTheta473
