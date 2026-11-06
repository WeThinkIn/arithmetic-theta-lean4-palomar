module
public import FormalCoverSolution
import Lean
@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
universe u
namespace ArithmeticThetaFormalCoverRecovery2418
theorem recover_original_050 :
  ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))) [CharZero k] [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Smooth (ArithmeticThetaFormalConstants.genericStructure k X f)] [AlgebraicGeometry.GeometricallyConnected (ArithmeticThetaFormalConstants.genericStructure k X f)], ∃ ρ : ArithmeticThetaFormalCoverR0210.Restrictions k X f, ∀ C : ArithmeticThetaFormalCoverR0210.Cover k X f, ArithmeticThetaFormalCoverR0210.ChartConditions k X f C → ∀ v : (∀ i, ArithmeticThetaFormalCoverR0210.Fractions k X f (C.opens i)), ArithmeticThetaFormalCoverR0210.RationalCompatible k X f ρ C v → ArithmeticThetaFormalCoverR0210.NoPole k X f C v → ∃! c : LaurentSeries k, ArithmeticThetaFormalCoverR0210.FractionConstant k X f C v c := by
  intro k _ X f _ _ _ _ _
  obtain ⟨rho, hrho⟩ := ArithmeticThetaPalomarFormalCover275.arbitrary_formal_cover_constant k X f
  refine ⟨ArithmeticThetaPalomarFormalCover275.Bridges.toRestrictions k X f rho, ?_⟩
  intro C hC v hv hn
  exact hrho (ArithmeticThetaPalomarFormalCover275.Bridges.fromCover k X f C) hC v hv hn
end ArithmeticThetaFormalCoverRecovery2418
#print axioms ArithmeticThetaFormalCoverRecovery2418.recover_original_050
