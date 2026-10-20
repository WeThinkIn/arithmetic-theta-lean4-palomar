module

public import MatrixFamilyGlobalSectionsR0188
public import FixedLineFiniteJet
public import ComputedCoefficientMatrix
public import RankZero

@[expose] public section

/-! The actual lifted local completion and the source's conservative cutoff.
These definitions contain no theorem or assumed construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaConservativeKernelR0189
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaSectionCompletion
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183

/-- The completed coordinate extends this disk's actual local-ring map. -/
def CompatibleCompletion (k : Type) [Field k] [CharZero k]
    (Y : Scheme.{0}) (g : Disk k ⟶ Y)
    (e : completedLocalRing (Y.presheaf.stalk (g (closedPoint k))) ≃+* PowerSeries k) : Prop :=
  (diskGerm k).comp (completionExpansion (Y.presheaf.stalk (g (closedPoint k))) k e) =
    (g.stalkMap (closedPoint k)).hom

/-- Exact integer realization of n*K^s*I(L)/48. The final theorem must prove
its equality to the displayed rational source expression. -/
def cutoff {n h : ℕ} (A : Matrices n h) (U : Indexing A) : ℕ :=
  n * (exponent (commonN A)) ^ U.count *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) / 48

end ArithmeticThetaConservativeKernelR0189
