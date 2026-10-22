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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)

noncomputable def restrictPushforwardOpensIso :
    (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor : W.toScheme.Opens ⥤ X.Opens) ≅
      W.ι.opensFunctor ⋙ Opens.map g.base :=
  NatIso.ofComponents (fun U => eqToIso (image_morphismRestrict_preimage g W U))
    (fun _ => Subsingleton.elim _ _)

set_option maxHeartbeats 400000 in

noncomputable def pushforwardRestrictIso :
    restrictFunctor (g ⁻¹ᵁ W).ι ⋙ pushforward (g ∣_ W) ≅ pushforward g ⋙ restrictFunctor W.ι :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} (Opens.map (g ∣_ W).base) (g ⁻¹ᵁ W).ι.opensFunctor
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology ↑(g ⁻¹ᵁ W)) (Opens.grothendieckTopology X)
  letI := CategoryTheory.Functor.isContinuous_comp.{u} W.ι.opensFunctor (Opens.map g.base)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  by
    refine SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardNatIso _ (restrictPushforwardOpensIso g W).symm ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr ?_
    ext U x
    simp only [Functor.sheafPushforwardContinuous_obj_obj_obj, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, Hom.toRingCatSheafHom, op_unop, Opens.ι_appIso, Iso.refl_inv,
      Functor.sheafPushforwardContinuousNatTrans, restrictPushforwardOpensIso, Iso.symm_hom, ObjectProperty.ι_obj,
      Category.assoc, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      TopCat.Presheaf.pushforward_obj_obj, Functor.sheafPushforwardContinuous_map_hom_app, Functor.op_obj,
      NatTrans.op_app, NatIso.ofComponents_inv_app, eqToIso.inv, eqToHom_op, Functor.comp_map, RingCat.hom_comp,
      CommRingCat.forgetToRingCat_map_hom]
    change (X.presheaf.map (eqToHom _)) ((g ∣_ W).app (unop U) x) = g.app (W.ι ''ᵁ unop U) x
    rw [morphismRestrict_app']
    erw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]
    rfl

lemma pushforwardRestrictIso_hom_app_app (M : X.Modules) (U : W.toScheme.Opens) :
    ((pushforwardRestrictIso g W).hom.app M).app U =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage g W U).symm).op := by
  first
    | rfl
    | (ext x; simp [pushforwardRestrictIso, restrictPushforwardOpensIso, SheafOfModules.pushforwardCongr,
        SheafOfModules.pushforwardNatIso, SheafOfModules.pushforwardComp, eqToHom_op, Scheme.Modules.Hom.app])

end AlgebraicGeometry.Scheme.Modules
