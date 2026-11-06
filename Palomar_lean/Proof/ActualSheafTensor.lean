module

public import LocalFrameBridge
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-!
# Actual binary tensor of module sheaves

The tensor is constructed by the module-presheaf sheafification adjunction.
The seven results below concern arbitrary module sheaves on a scheme; no
local-freeness or tensor universal-property interface is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaSheafTensor

variable (X : Scheme.{u})

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def tensorPresheaf (H K : X.Modules) : X.PresheafOfModules := H.val ⊗ K.val

/-- The actual sheafification of the actual categorical tensor of module presheaves. -/
def sheafTensor (H K : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf X H K)

def tensorUnitMap (H K : X.Modules) : tensorPresheaf X H K ⟶ (sheafTensor X H K).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- Universal property inherited from the actual module sheafification adjunction. -/
def tensorHomEquiv (H K P : X.Modules) :
    (sheafTensor X H K ⟶ P) ≃ (tensorPresheaf X H K ⟶ P.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)

theorem tensorHomEquiv_apply (H K P : X.Modules) (f : sheafTensor X H K ⟶ P) :
    tensorHomEquiv X H K P f = tensorUnitMap X H K ≫ f.val := by
  rfl

theorem tensorHomEquiv_symm_unit (H K P : X.Modules) (f : tensorPresheaf X H K ⟶ P.val) :
    tensorUnitMap X H K ≫ ((tensorHomEquiv X H K P).symm f).val = f := by
  simpa only [tensorHomEquiv_apply] using (tensorHomEquiv X H K P).apply_symm_apply f

theorem tensor_hom_ext (H K P : X.Modules) (f g : sheafTensor X H K ⟶ P)
    (h : tensorUnitMap X H K ≫ f.val = tensorUnitMap X H K ≫ g.val) : f = g := by
  apply (tensorHomEquiv X H K P).injective
  simpa only [tensorHomEquiv_apply] using h

theorem tensor_hom_bijective (H K P : X.Modules) :
    Function.Bijective (fun f : sheafTensor X H K ⟶ P ↦ tensorUnitMap X H K ≫ f.val) := by
  simp_rw [← tensorHomEquiv_apply]
  exact (tensorHomEquiv X H K P).bijective

def tensorSection (H K : X.Modules) (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    Γ(sheafTensor X H K, U) :=
  (tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X, U)] t)

theorem tensorSection_restrict (H K : X.Modules) (U V : X.Opens) (hVU : V ≤ U)
    (s : Γ(H, U)) (t : Γ(K, U)) :
    (sheafTensor X H K).presheaf.map (homOfLE hVU).op (tensorSection X H K U s t) =
      tensorSection X H K V (H.presheaf.map (homOfLE hVU).op s)
        (K.presheaf.map (homOfLE hVU).op t) := by
  exact (PresheafOfModules.naturality_apply (tensorUnitMap X H K)
    (homOfLE hVU).op (s ⊗ₜ[Γ(X, U)] t)).symm

def tensorLeftUnitIso (H : X.Modules) :
    sheafTensor X (SheafOfModules.unit X.ringCatSheaf) H ≅ H := by
  let H' : SheafOfModules.{u} X.ringCatSheaf := H
  let e := asIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app H')
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ H.val) ≪≫ e

def tensorLeftUnitorMap (H : X.Modules) :
    tensorPresheaf X (SheafOfModules.unit X.ringCatSheaf) H ⟶ H.val := (λ_ H.val).hom

theorem tensorLeftUnitIso_unit (H : X.Modules) :
    tensorUnitMap X (SheafOfModules.unit X.ringCatSheaf) H ≫
      (tensorLeftUnitIso X H).hom.val = tensorLeftUnitorMap X H := by
  have h := tensorHomEquiv_symm_unit X (SheafOfModules.unit X.ringCatSheaf) H H
    (tensorLeftUnitorMap X H)
  have he : tensorHomEquiv X (SheafOfModules.unit X.ringCatSheaf) H H =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        (tensorPresheaf X (SheafOfModules.unit X.ringCatSheaf) H)
        (show SheafOfModules.{u} X.ringCatSheaf from H) := by
    apply Equiv.ext
    intro f
    rfl
  rw [he] at h
  erw [Adjunction.homEquiv_counit] at h
  exact h

theorem tensorLeftUnitIso_section (H : X.Modules) (U : X.Opens) (s : Γ(H, U)) :
    (tensorLeftUnitIso X H).hom.app U
      (tensorSection X (SheafOfModules.unit X.ringCatSheaf) H U (1 : Γ(X, U)) s) = s := by
  have h := congrArg (fun f ↦ f.app (op U)) (tensorLeftUnitIso_unit X H)
  have h' := ConcreteCategory.congr_hom h ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U)] s)
  change (tensorLeftUnitIso X H).hom.app U
    (tensorSection X (SheafOfModules.unit X.ringCatSheaf) H U (1 : Γ(X, U)) s) =
      (1 : Γ(X, U)) • s at h'
  simpa only [one_smul] using h'

end ArithmeticThetaSheafTensor
