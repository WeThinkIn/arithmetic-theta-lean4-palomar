module

public import TateMarkedCuspOrders
public import FourTorsionRoot
public import FormalPowerRootsR0094

@[expose] public section

/-! Literal Tate two-torsion coordinates after a positive formal substitution.
The split cubic below is an explicit Weierstrass curve over k((t)). Identifying
it with the proper Tate model is a separate, still open geometric bridge. -/
noncomputable section
universe u
namespace ArithmeticThetaAllCuspR0108

def rootSeries (k : Type u) [Field k] (w : PowerSeries k) (i : Fin 3) : PowerSeries k :=
  PowerSeries.subst w (if i = 0 then ArithmeticThetaTateSeries.e₁ k
    else if i = 1 then ArithmeticThetaTateSeries.e₂ k
    else ArithmeticThetaTateSeries.e₃ k)

def rootValue (k : Type u) [Field k] (w : PowerSeries k) (i : Fin 3) : LaurentSeries k :=
  ArithmeticThetaTateSeries.toLaurent k (rootSeries k w i)

def markedCurve (k : Type u) [Field k] (w : PowerSeries k) (σ : Equiv.Perm (Fin 3)) :
    WeierstrassCurve.Affine (LaurentSeries k) :=
  ArithmeticThetaFourTorsion.splitCurve (rootValue k w (σ 0))
    (rootValue k w (σ 1)) (rootValue k w (σ 2))

/-- The coefficient of 2gδ in the target invariant differential frame. -/
def alphaCoefficient (k : Type u) [Field k] (w : PowerSeries k)
    (σ : Equiv.Perm (Fin 3)) (x y : LaurentSeries k) : LaurentSeries k :=
  2 * ArithmeticThetaFourTorsion.rootExpression (rootValue k w (σ 0))
    (rootValue k w (σ 1)) (rootValue k w (σ 2)) x y

end ArithmeticThetaAllCuspR0108
