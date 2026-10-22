module

public import ScaledThetaFiniteSpecializationR0050
public import ScaledCompletedNodeNormalDomainR0051
public import ScaledGammaUnitProductR0050
public import ScaledAnnularDefinitionsR0050
public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

/-! Ordinary objects for the local chart part of the r-gon comparison.
The period thickness r is distinct from the local node thickness, which is 1.
No proper model, Kato function, or source theorem is asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAnnularTorsionPrereqR0053
variable (k : Type u) [Field k] [CharZero k]
abbrev Base := PowerSeries k
abbrev Node := ArithmeticThetaScaledTateBridgeR0046.Node k 1
abbrev Chart := ArithmeticThetaScaledTateBridgeR0046.CompletedNode k 1

def base : Base k →+* Chart k :=
  ArithmeticThetaScaledTateBridgeR0046.completedBaseMap k 1
def nodeBase : Base k →+* Node k := algebraMap _ _
def complete : Node k →+* Chart k :=
  ArithmeticThetaScaledTateBridgeR0046.toCompleted k 1
def tau : Chart k := ArithmeticThetaScaledAnnularR0050.tau k 1
def cx : Chart k := ArithmeticThetaScaledAnnularR0050.cx k 1
def cy : Chart k := ArithmeticThetaScaledAnnularR0050.cy k 1
def coord (side : Bool) : Chart k := if side then cx k else cy k
def nodeCoord (side : Bool) : Node k :=
  if side then ArithmeticThetaScaledTateBridgeR0046.x k 1
  else ArithmeticThetaScaledTateBridgeR0046.y k 1
abbrev CoordinateOpen (side : Bool) := Localization.Away (nodeCoord k side)
def filtration (n : ℕ) : Ideal (Chart k) :=
  ArithmeticThetaScaledTateBridgeR0046.completedPower k 1 n

def torsionExponent (r c a : ℕ) : ℕ := r * a / c
def torsionScalar (r c a b : ℕ) (ζ : k) : Base k :=
  PowerSeries.C (ζ ^ b) * PowerSeries.X ^ torsionExponent r c a

def chartCoordinate (j : ℕ) : Chart k := tau k ^ j * cx k

def sectionEquation (side : Bool) (α : k) : Chart k :=
  coord k side - base k (PowerSeries.C α)
def sectionIdeal (side : Bool) (α : k) : Ideal (Chart k) :=
  Ideal.span {sectionEquation k side α}

/-- A specified continuous section map; kernel and existence are NOT assumed. -/
def SectionAt (side : Bool) (α : k) (σ : Chart k →+* Base k) : Prop :=
  σ.comp (base k) = RingHom.id (Base k) ∧
  σ (coord k side) = PowerSeries.C α ∧
  σ (coord k (!side)) = PowerSeries.C α⁻¹ * PowerSeries.X ∧
  ∀ (n : ℕ) (f : Chart k), f ∈ filtration k n →
    σ f ∈ (Ideal.span {PowerSeries.X} : Ideal (Base k)) ^ n

def sectionMorphism (σ : Chart k →+* Base k) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ)
def algebraicSectionMorphism (σ : Chart k →+* Base k) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ.comp (complete k)))
def structureMorphism := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (base k))
def algebraicStructureMorphism :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (nodeBase k))

def horizontalEquation (side : Bool) (c : ℕ) : Chart k := 1 - coord k side ^ c
def horizontalIdeal (side : Bool) (c : ℕ) : Ideal (Chart k) :=
  Ideal.span {horizontalEquation k side c}

def leftExponent (r c j l : ℕ) : ℕ := r * l + c * j
def rightExponent (r c j l : ℕ) : ℤ :=
  (r : ℤ) * ((l : ℤ) + 1) - (c : ℤ) * ((j : ℤ) + 1)

def normalizedRight (r c j l : ℕ) : Chart k :=
  let e := rightExponent r c j l
  if e < 0 then 1 - tau k ^ (-e - (c : ℤ)).toNat * cx k ^ c
  else 1 - tau k ^ e.toNat * cy k ^ c

def normalizedFactor (r c j l : ℕ) : Chart k :=
  (1 - tau k ^ leftExponent r c j l * cx k ^ c) * normalizedRight k r c j l

def tailRight (r c j l : ℕ) : Chart k :=
  let e := rightExponent r c j l
  if e < 0 then
    if -e - (c : ℤ) = 0 then 1
    else 1 - tau k ^ (-e - (c : ℤ)).toNat * cx k ^ c
  else if e = 0 then 1 else 1 - tau k ^ e.toNat * cy k ^ c

def tailFactor (r c j l : ℕ) : Chart k :=
  (if leftExponent r c j l = 0 then 1
   else 1 - tau k ^ leftExponent r c j l * cx k ^ c) * tailRight k r c j l

def normalizedPartial (r c j N : ℕ) : Chart k :=
  ∏ l ∈ Finset.range N, normalizedFactor k r c j l
def tailPartial (r c j N : ℕ) : Chart k :=
  ∏ l ∈ Finset.range N, tailFactor k r c j l

def horizontal (r c j : ℕ) : Chart k :=
  (if r ∣ c * j then horizontalEquation k true c else 1) *
  (if r ∣ c * (j + 1) then horizontalEquation k false c else 1)

def cutoff (c j n : ℕ) : ℕ := n + c * (j + 1) + c + 1

abbrev GenericChart := Localization.Away (tau k)
def toGeneric : Chart k →+* GenericChart k := algebraMap _ _
def parameterUnit : (GenericChart k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (tau k) (S := GenericChart k)).unit
def tpower (e : ℤ) : GenericChart k := ↑(parameterUnit k ^ e)

def literalPartial (r c j N : ℕ) : GenericChart k :=
  ∏ l ∈ Finset.range N,
    (1 - tpower k (leftExponent r c j l : ℤ) * toGeneric k (cx k) ^ c) *
    (1 - tpower k (rightExponent r c j l) * toGeneric k (cy k) ^ c)

def clearingPartial (r c j N : ℕ) : GenericChart k :=
  ∏ l ∈ Finset.range N,
    if rightExponent r c j l < 0 then
      -(tpower k (rightExponent r c j l) * toGeneric k (cy k) ^ c)
    else 1
end ArithmeticThetaAnnularTorsionPrereqR0053
