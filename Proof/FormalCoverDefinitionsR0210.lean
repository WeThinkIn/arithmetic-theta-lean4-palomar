module

public import ProperNoPoleRootR0089
public import FormalConstantDefinitions
public import GeometricPrerequisiteDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaFormalCoverR0210

variable (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))

abbrev ideal := ArithmeticThetaGeometricPrerequisites.parameterIdeal
  (PowerSeries k) X f PowerSeries.X
abbrev stage (n : ℕ) := (ideal k X f ^ n).subscheme
abbrev inclusion (n : ℕ) := (ideal k X f ^ n).subschemeι
abbrev StageSections (U : X.Opens) (n : ℕ) :=
  Γ(stage k X f n, inclusion k X f n ⁻¹ᵁ U)

def transition (U : X.Opens) (m n : ℕ)
    (h : ideal k X f ^ n ≤ ideal k X f ^ m) :
    StageSections k X f U n →+* StageSections k X f U m :=
  ((Scheme.IdealSheafData.inclusion h).appLE
    (inclusion k X f n ⁻¹ᵁ U) (inclusion k X f m ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])).hom

/-- Actual compatible sections on every thickening, not completion of the
section ring on a possibly nonaffine open. Includes the empty zeroth stage. -/
def formalSubring (U : X.Opens) : Subring (∀ n, StageSections k X f U n) where
  carrier := {s | ∀ m n h, transition k X f U m n h (s n) = s m}
  zero_mem' := by intro m n h; exact (transition k X f U m n h).map_zero
  one_mem' := by intro m n h; exact (transition k X f U m n h).map_one
  add_mem' := by
    intro a b ha hb m n h
    change transition k X f U m n h (a n + b n) = a m + b m
    rw [map_add, ha m n h, hb m n h]
  mul_mem' := by
    intro a b ha hb m n h
    change transition k X f U m n h (a n * b n) = a m * b m
    rw [map_mul, ha m n h, hb m n h]
  neg_mem' := by
    intro a ha m n h
    change transition k X f U m n h (-a n) = -a m
    rw [map_neg, ha m n h]

abbrev FormalRing (U : X.Opens) := formalSubring k X f U

def ofSection (U : X.Opens) : Γ(X, U) →+* FormalRing k X f U where
  toFun a := ⟨fun n => (inclusion k X f n).app U a, by
    intro m n h
    change ((inclusion k X f n).app U ≫
      (Scheme.IdealSheafData.inclusion h).appLE _ _ _) a = _
    rw [← Scheme.Hom.comp_appLE]
    simp only [inclusion, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.appLE_eq_app]⟩
  map_zero' := by ext n; exact map_zero _
  map_one' := by ext n; exact map_one _
  map_add' a b := by ext n; exact map_add _ a b
  map_mul' a b := by ext n; exact map_mul _ a b

def scalar (U : X.Opens) : PowerSeries k →+* FormalRing k X f U :=
  (ofSection k X f U).comp
    (ArithmeticThetaFormalConstants.structuralMap (PowerSeries k) X f U)
def parameter (U : X.Opens) : FormalRing k X f U := scalar k X f U PowerSeries.X
abbrev GenericRing (U : X.Opens) := Localization.Away (parameter k X f U)
def localize (U : X.Opens) : FormalRing k X f U →+* GenericRing k X f U :=
  algebraMap _ _
def genericScalar (U : X.Opens) : PowerSeries k →+* GenericRing k X f U :=
  (localize k X f U).comp (scalar k X f U)

/-- Ring maps are pinned to the actual structure-sheaf restrictions at every
thickness. Existence and uniqueness are assigned, rather than assumed. -/
structure Restrictions where
  map : ∀ (U V : X.Opens), V ≤ U → FormalRing k X f U →+* FormalRing k X f V
  component : ∀ (U V : X.Opens) (h : V ≤ U) (a : FormalRing k X f U) (n : ℕ),
    (map U V h a).val n =
      (stage k X f n).presheaf.map (homOfLE ((inclusion k X f n).preimage_mono h)).op
        (a.val n)
  genericMap : ∀ (U V : X.Opens), V ≤ U → GenericRing k X f U →+* GenericRing k X f V
  generic_extends : ∀ (U V : X.Opens) (h : V ≤ U) (a : FormalRing k X f U),
    genericMap U V h (localize k X f U a) = localize k X f V (map U V h a)

/-- A finite formal open cover. The opens need only cover the closed fiber;
no algebraic affineness, cyclic presentation, or chosen algebraization is imposed. -/
structure Cover where
  count : ℕ
  opens : Fin count → X.Opens
  covers : ∀ x : stage k X f 1, ∃ i, (inclusion k X f 1).base x ∈ opens i

def Compatible (ρ : Restrictions k X f) (C : Cover k X f)
    (z : ∀ i, FormalRing k X f (C.opens i)) : Prop :=
  ∀ i j, ρ.map (C.opens i) (C.opens i ⊓ C.opens j) inf_le_left (z i) =
    ρ.map (C.opens j) (C.opens i ⊓ C.opens j) inf_le_right (z j)

def LocalCompatible (ρ : Restrictions k X f) (C : Cover k X f)
    (z : ∀ i, GenericRing k X f (C.opens i)) : Prop :=
  ∀ i j, ρ.genericMap (C.opens i) (C.opens i ⊓ C.opens j) inf_le_left (z i) =
    ρ.genericMap (C.opens j) (C.opens i ⊓ C.opens j) inf_le_right (z j)

def globalRestriction (U : X.Opens) : Γ(X, ⊤) →+* FormalRing k X f U :=
  (ofSection k X f U).comp (X.presheaf.map (homOfLE le_top).op).hom

abbrev Fractions (U : X.Opens) := FractionRing (GenericRing k X f U)
def toFraction (U : X.Opens) : GenericRing k X f U →+* Fractions k X f U :=
  algebraMap _ _

def ChartConditions (C : Cover k X f) : Prop :=
  ∀ i, IsDomain (FormalRing k X f (C.opens i)) ∧
    IsNoetherianRing (FormalRing k X f (C.opens i)) ∧
    IsIntegrallyClosed (FormalRing k X f (C.opens i)) ∧ parameter k X f (C.opens i) ≠ 0

def RationalCompatible (ρ : Restrictions k X f) (C : Cover k X f)
    (v : ∀ i, Fractions k X f (C.opens i)) : Prop :=
  ∀ i j (a b : GenericRing k X f (C.opens i))
    (a' b' : GenericRing k X f (C.opens j)), b ≠ 0 → b' ≠ 0 →
    v i * toFraction k X f (C.opens i) b = toFraction k X f (C.opens i) a →
    v j * toFraction k X f (C.opens j) b' = toFraction k X f (C.opens j) a' →
    ρ.genericMap (C.opens i) (C.opens i ⊓ C.opens j) inf_le_left a *
      ρ.genericMap (C.opens j) (C.opens i ⊓ C.opens j) inf_le_right b' =
    ρ.genericMap (C.opens j) (C.opens i ⊓ C.opens j) inf_le_right a' *
      ρ.genericMap (C.opens i) (C.opens i ⊓ C.opens j) inf_le_left b

def NoPole (C : Cover k X f) (v : ∀ i, Fractions k X f (C.opens i)) : Prop :=
  ∀ i (p : Ideal (GenericRing k X f (C.opens i))), p.IsPrime → p.height = 1 →
    ∃ a b : GenericRing k X f (C.opens i), b ∉ p ∧
      v i * toFraction k X f (C.opens i) b = toFraction k X f (C.opens i) a

def FractionConstant (C : Cover k X f) (v : ∀ i, Fractions k X f (C.opens i))
    (c : LaurentSeries k) : Prop :=
  ∃ (n : ℕ) (r : PowerSeries k),
    algebraMap (PowerSeries k) (LaurentSeries k) r =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X ^ n) * c ∧
    ∀ i, toFraction k X f (C.opens i) (genericScalar k X f (C.opens i) r) =
      toFraction k X f (C.opens i) (genericScalar k X f (C.opens i) (PowerSeries.X ^ n)) * v i

end ArithmeticThetaFormalCoverR0210
