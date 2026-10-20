module

public import GlobalizationDefinitions
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

noncomputable section

namespace ArithmeticThetaIntegralCuspsR0102

abbrev Marking := Matrix.SpecialLinearGroup (Fin 2) ℤ

def boundary (A : Marking) : WithTop ℚ :=
  if A 1 0 = 0 then ⊤ else ((A 0 0 : ℚ) / (A 1 0 : ℚ) : ℚ)

def Parabolic (p : Marking) : Prop := p 1 0 = 0

def MarkingRel (L : ℕ) (A B : Marking) : Prop :=
  ∃ γ : Marking, γ ∈ CongruenceSubgroup.Gamma L ∧
    ∃ p : Marking, Parabolic p ∧ B = γ * A * p

def BoundaryRel (L : ℕ) (x y : WithTop ℚ) : Prop :=
  ∃ A B : Marking, boundary A = x ∧ boundary B = y ∧ MarkingRel L A B

def RationalCusps (L : ℕ) := Quot (BoundaryRel L)

def cusp (L : ℕ) (x : WithTop ℚ) : RationalCusps L := Quot.mk _ x

def primitiveLabel (L : ℕ) (A : Marking) : ArithmeticThetaLevelCount.PrimitivePair L :=
  ⟨((A 0 0 : ZMod L), (A 1 0 : ZMod L)),
    (Matrix.SpecialLinearGroup.isCoprime_col A 0).map (Int.castRingHom (ZMod L))⟩

def signedLabel (L : ℕ) (A : Marking) : ArithmeticThetaLevelCount.SignedPrimitivePair L :=
  Quot.mk _ (primitiveLabel L A)

end ArithmeticThetaIntegralCuspsR0102

namespace ArithmeticThetaMarkingCuspsR0102

abbrev IntegralMarking := ArithmeticThetaIntegralCuspsR0102.Marking
abbrev FiniteMarking (L : ℕ) := Matrix.SpecialLinearGroup (Fin 2) (ZMod L)

def reduction (L : ℕ) : IntegralMarking →* FiniteMarking L :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod L))

instance gammaNormal (L : ℕ) : (CongruenceSubgroup.Gamma L).Normal :=
  CongruenceSubgroup.Gamma_normal L

abbrev CongruenceMarkings (L : ℕ) := IntegralMarking ⧸ CongruenceSubgroup.Gamma L

def markingClass (L : ℕ) (A : IntegralMarking) : CongruenceMarkings L :=
  QuotientGroup.mk A

def finiteLabel (L : ℕ) (B : FiniteMarking L) :
    ArithmeticThetaLevelCount.SignedPrimitivePair L :=
  Quot.mk _ (show ArithmeticThetaLevelCount.PrimitivePair L from
    ⟨(B 0 0, B 1 0), Matrix.SpecialLinearGroup.isCoprime_col B 0⟩)

def signedTranslation (L : ℕ) (s : Bool × ZMod L) : FiniteMarking L :=
  if s.1 then -(reduction L (ModularGroup.T ^ (s.2.val : Int)))
  else reduction L (ModularGroup.T ^ (s.2.val : Int))

def BaseFiber (L : ℕ) :=
  {B : FiniteMarking L // finiteLabel L B = finiteLabel L 1}

end ArithmeticThetaMarkingCuspsR0102
