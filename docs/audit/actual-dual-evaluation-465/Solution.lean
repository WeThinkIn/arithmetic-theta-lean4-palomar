module
public import Mathlib
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
/-- Every open and every local vector fixes the global section-to-morphism map. -/
def Compatible (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Prop :=
  ∀ (t : Γ((ihom M).obj N, ⊤)) (U : X.Opens) (m : Γ(M, U)),
    (e t).app U m = ((ihom.ev M).app N).app U
      (Scheme.Modules.tensorSections m (((ihom M).obj N).presheaf.map (homOfLE le_top).op t))
theorem canonicalGlobalSectionsEquiv :
    ∃! e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N), Compatible M N e := by
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
theorem compatible_iff_original (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) :
    Compatible M N e ↔ e = Scheme.Modules.ihomGlobalSectionsEquiv M N := by
  have he : Compatible M N (Scheme.Modules.ihomGlobalSectionsEquiv M N) := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  constructor
  · intro h
    exact (canonicalGlobalSectionsEquiv M N).unique h he
  · rintro rfl
    exact he
theorem globalSectionsEquiv_eq_original :
    globalSectionsEquiv M N = Scheme.Modules.ihomGlobalSectionsEquiv M N :=
  (compatible_iff_original M N _).mp (canonicalGlobalSectionsEquiv M N).exists.choose_spec
theorem evaluationSection_eq_original (φ : M ⟶ N) :
    (globalSectionsEquiv M N).symm φ = (Scheme.Modules.ihomGlobalSectionsEquiv M N).symm φ := by
  rw [globalSectionsEquiv_eq_original]
end ArithmeticThetaPalomarDual465
