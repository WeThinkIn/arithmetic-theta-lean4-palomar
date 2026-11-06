module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.ENatToNat

@[expose] public section

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
