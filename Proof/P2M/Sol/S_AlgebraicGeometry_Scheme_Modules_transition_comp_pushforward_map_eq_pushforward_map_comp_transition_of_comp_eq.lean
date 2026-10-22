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
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace NatKey

universe v₁ v₂ v₃ u₁ u₂ u₃

theorem key {CZ : Type u₁} {CZ' : Type u₂} {CX : Type u₃} [Category.{v₁} CZ] [Category.{v₂} CZ'] [Category.{v₃} CX]
    (Pbt : CZ' ⥤ CZ) (Pt : CZ ⥤ CZ') (Pι' : CZ' ⥤ CX) (P : CZ ⥤ CX) (Pι : CZ ⥤ CX)
    (η : 𝟭 CZ' ⟶ Pbt ⋙ Pt) (σ : Pt ⋙ Pι' ⟶ P) (κ : P ⟶ Pι)
    {M₁ M₁' : CZ'} (φ' : M₁ ⟶ M₁') {K K' M₂ M₂' : CZ}
    (α : Pbt.obj M₁ ≅ K) (β : K ≅ M₂) (α' : Pbt.obj M₁' ≅ K') (β' : K' ≅ M₂') :
    (Pι'.map (η.app M₁) ≫ σ.app (Pbt.obj M₁) ≫ P.map α.hom ≫ P.map β.hom ≫ κ.app M₂) ≫
        Pι.map ((α ≪≫ β).inv ≫ Pbt.map φ' ≫ (α' ≪≫ β').hom) =
      Pι'.map φ' ≫ (Pι'.map (η.app M₁') ≫ σ.app (Pbt.obj M₁') ≫ P.map α'.hom ≫ P.map β'.hom ≫ κ.app M₂') := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← κ.naturality, ← P.map_comp_assoc, ← P.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  erw [← σ.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← Pι'.map_comp_assoc, ← show φ' ≫ η.app M₁' = η.app M₁ ≫ Pt.map (Pbt.map φ') from by
    have e := η.naturality φ'
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at e
    exact e]
  erw [Pι'.map_comp_assoc]

end NatKey

theorem solution
    {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (ι' : Z' ⟶ X) (ι : Z ⟶ X) (h : t ≫ ι' = ι) (N N' : X.Modules)
    (φ' : (Scheme.Modules.pullback ι').obj N ⟶ (Scheme.Modules.pullback ι').obj N')
    (φ : (Scheme.Modules.pullback ι).obj N ⟶ (Scheme.Modules.pullback ι).obj N')
    (hφ : φ =
      ((Scheme.Modules.pullbackComp t ι').app N ≪≫ (Scheme.Modules.pullbackCongr h).app N).inv
        ≫ (Scheme.Modules.pullback t).map φ'
        ≫ ((Scheme.Modules.pullbackComp t ι').app N' ≪≫ (Scheme.Modules.pullbackCongr h).app N').hom) :
    ((Scheme.Modules.pushforward ι').map
          ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N))
      ≫ (Scheme.Modules.pushforward ι).map φ =
    (Scheme.Modules.pushforward ι').map φ'
      ≫ ((Scheme.Modules.pushforward ι').map
          ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N'))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N'))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N')
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N')
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N')) := by
  subst hφ
  exact NatKey.key (Scheme.Modules.pullback t) (Scheme.Modules.pushforward t) (Scheme.Modules.pushforward ι')
    (Scheme.Modules.pushforward (t ≫ ι')) (Scheme.Modules.pushforward ι)
    (Scheme.Modules.pullbackPushforwardAdjunction t).unit (Scheme.Modules.pushforwardComp t ι').hom
    (Scheme.Modules.pushforwardCongr h).hom φ'
    ((Scheme.Modules.pullbackComp t ι').app N) ((Scheme.Modules.pullbackCongr h).app N)
    ((Scheme.Modules.pullbackComp t ι').app N') ((Scheme.Modules.pullbackCongr h).app N')
