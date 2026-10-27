import Mathlib

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ArithmeticThetaSmoothPrerequisites

universe u
noncomputable section

variable (X : Scheme.{u}) [IsIntegral X] (k : Type u) [Field k]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The genuine structure morphism supplies the scalar map on every actual open. -/
def constantSectionsMap (U : X.Opens) : k →+* Γ(X,U) :=
  (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The structure morphism supplies the base-field map into the actual generic stalk. -/
def constantFunctionFieldMap : k →+* X.functionField :=
  (f.stalkMap (genericPoint X)).hom.comp
    (((Spec (CommRingCat.of k)).presheaf.germ ⊤ (f (genericPoint X)) (by trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

theorem constantFunctionFieldMap_injective : Function.Injective (constantFunctionFieldMap X k f) :=
  (constantFunctionFieldMap X k f).injective

theorem constantSectionsMap_functionField (U : X.Opens) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (constantSectionsMap X k f U) =
      constantFunctionFieldMap X k f := by
  have h : f.appLE ⊤ U (by simp) ≫ X.germToFunctionField U =
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ (f (genericPoint X)) (by trivial) ≫
        f.stalkMap (genericPoint X) := by
    simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
      TopCat.Presheaf.germ_res]
    exact (f.germ_stalkMap ⊤ (genericPoint X) (by trivial)).symm
  ext a
  exact congr($(h) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))

include f in
theorem functionField_charZero [CharZero k] : CharZero X.functionField := by
  let := (constantFunctionFieldMap X k f).toAlgebra
  exact Algebra.charZero_of_charZero k X.functionField

omit [IsIntegral X] in
theorem smooth_locallyNoetherian [Smooth f] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

omit [IsIntegral X] in
theorem smooth_affine_noetherian [Smooth f] (U : X.Opens) (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(X,U) := by
  let := smooth_locallyNoetherian X k f
  exact IsLocallyNoetherian.component_noetherian (X := X) ⟨U, hU⟩

omit [IsIntegral X] in
theorem smooth_affine_structureMap [Smooth f] (U : X.Opens) (hU : IsAffineOpen U) :
    (constantSectionsMap X k f U).Smooth := by
  apply RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.bijective)
  exact f.smooth_appLE (isAffineOpen_top _) hU (by simp)

end
end ArithmeticThetaSmoothPrerequisites
