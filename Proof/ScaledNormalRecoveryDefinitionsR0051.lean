module

public import ScaledTateNodeCompletion
public import TateCompletedNodeNormal

@[expose] public section

/-! Ordinary predicates for a split embedding of the scaled node into the
unit-thickness node. Existence of every map and every predicate is a task
obligation; none of the definitions asserts normality of the scaled completion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaScaledNormalRecoveryR0051
open ArithmeticThetaScaledTateBridgeR0046
variable (k : Type u) [Field k] (r : ℕ)

/-- Filtration continuity with the actual factor r between the two adic ideals. -/
def ForwardFiltered (f : Node k r →+* ArithmeticThetaNodeCharts.Node k) : Prop :=
  ∀ (n : ℕ) (a : Node k r), a ∈ nodeIdeal k r ^ n →
    f a ∈ ArithmeticThetaNodeCharts.nodeIdeal k ^ (r * n)

def BackwardFiltered (p : ArithmeticThetaNodeCharts.Node k →+ Node k r) : Prop :=
  ∀ (n : ℕ) (b : ArithmeticThetaNodeCharts.Node k),
    b ∈ ArithmeticThetaNodeCharts.nodeIdeal k ^ (r * n) → p b ∈ nodeIdeal k r ^ n

/-- All maps are on concrete quotient rings. The coefficient identities fix the
base action. The last identities specify the monomial projection explicitly. -/
def AlgebraicSplit (f : Node k r →+* ArithmeticThetaNodeCharts.Node k)
    (p : ArithmeticThetaNodeCharts.Node k →+ Node k r) : Prop :=
  (∀ a : Base k, f (algebraMap (Base k) (Node k r) a) =
    algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k) a) ∧
  f (x k r) = ArithmeticThetaNodeCharts.x k ^ r ∧
  f (y k r) = ArithmeticThetaNodeCharts.y k ^ r ∧
  (∀ a : Node k r, p (f a) = a) ∧
  (∀ (a : Node k r) (b : ArithmeticThetaNodeCharts.Node k), p (f a * b) = a * p b) ∧
  ForwardFiltered k r f ∧ BackwardFiltered k r p ∧
  (∀ (a : Base k) (n : ℕ),
    p (algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k) a *
      ArithmeticThetaNodeCharts.x k ^ n) =
      if r ∣ n then algebraMap (Base k) (Node k r) a * x k r ^ (n / r) else 0) ∧
  (∀ (a : Base k) (n : ℕ),
    p (algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k) a *
      ArithmeticThetaNodeCharts.y k ^ n) =
      if r ∣ n then algebraMap (Base k) (Node k r) a * y k r ^ (n / r) else 0)

def RingExtension (f : Node k r →+* ArithmeticThetaNodeCharts.Node k)
    (F : CompletedNode k r →+* ArithmeticThetaNodeCharts.CompletedNode k) : Prop :=
  (∀ a : Node k r, F (toCompleted k r a) = ArithmeticThetaNodeCharts.toCompleted k (f a)) ∧
  (∀ (n : ℕ) (a : CompletedNode k r), a ∈ completedPower k r n →
    F a ∈ ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n))

def AdditiveExtension (p : ArithmeticThetaNodeCharts.Node k →+ Node k r)
    (P : ArithmeticThetaNodeCharts.CompletedNode k →+ CompletedNode k r) : Prop :=
  (∀ b : ArithmeticThetaNodeCharts.Node k,
    P (ArithmeticThetaNodeCharts.toCompleted k b) = toCompleted k r (p b)) ∧
  (∀ (n : ℕ) (b : ArithmeticThetaNodeCharts.CompletedNode k),
    b ∈ ArithmeticThetaNodeCharts.completedIdeal k ^ (r * n) → P b ∈ completedPower k r n)

end ArithmeticThetaScaledNormalRecoveryR0051
