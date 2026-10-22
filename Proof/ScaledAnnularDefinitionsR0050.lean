module

public import ScaledTateNodeAlgebra
public import ScaledTateNodeCompletion
public import ScaledTateCompletionSpecializationUniqueR0049
public import ScaledTateCompletionSpecializationExistsR0049

@[expose] public section

/-! Concrete scaled annular sums and products. Existence, normality,
convergence and exact expansion are new proof obligations. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledAnnularR0050

open ArithmeticThetaScaledTateBridgeR0046

variable (k : Type u) [Field k]

def tau (r : ℕ) : CompletedNode k r := completedBaseMap k r PowerSeries.X
def cx (r : ℕ) : CompletedNode k r := toCompleted k r (x k r)
def cy (r : ℕ) : CompletedNode k r := toCompleted k r (y k r)

def thetaShift (r j : ℕ) : ℕ := (j + r) ^ 2
def thetaExponent (r d j : ℕ) (b : ℤ) : ℤ :=
  (thetaShift r j : ℤ) + (d : ℤ) * b ^ 2 +
    if 0 ≤ b then (j : ℤ) * b else ((j + r : ℕ) : ℤ) * b

def thetaTerm (r d j : ℕ) (b : ℤ) : CompletedNode k r :=
  tau k r ^ (thetaExponent r d j b).toNat *
    if 0 ≤ b then cx k r ^ b.toNat else cy k r ^ (-b).toNat

def thetaPartial (r m d j : ℕ) (nu : ℤ) (N : ℕ) : CompletedNode k r :=
  ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    if b % (m : ℤ) = nu % (m : ℤ) then thetaTerm k r d j b else 0

def ThetaLimit (r m d j : ℕ) (nu : ℤ) (s : CompletedNode k r) : Prop :=
  ∀ (n N : ℕ), r * n + 2 * (j + r) + 1 ≤ N →
    s - thetaPartial k r m d j nu N ∈ completedPower k r n

def specializedExponent (r i d j : ℕ) (b : ℤ) : ℤ :=
  (thetaShift r j : ℤ) + (d : ℤ) * b ^ 2 + ((j + i : ℕ) : ℤ) * b

def specializedTerm (r i d j : ℕ) (a : k) (b : ℤ) : PowerSeries k :=
  PowerSeries.C (a ^ b) * PowerSeries.X ^ (specializedExponent r i d j b).toNat

def specializedPartial (r i m d j : ℕ) (nu : ℤ) (a : k) (N : ℕ) : PowerSeries k :=
  ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    if b % (m : ℤ) = nu % (m : ℤ) then specializedTerm k r i d j a b else 0

def specializedSeries (r i m d j : ℕ) (nu : ℤ) (a : k) : PowerSeries k :=
  PowerSeries.mk (fun n => PowerSeries.coeff n
    (specializedPartial k r i m d j nu a (n + 2 * (j + r) + 1)))

def gammaLeftExponent (R j l : ℕ) : ℕ := R * l + j
def gammaRightExponent (r R j l : ℕ) : ℕ := R * (l + 1) - j - r

def gammaFactor (r R j l : ℕ) : CompletedNode k r :=
  (1 - tau k r ^ gammaLeftExponent R j l * cx k r) *
    (1 - tau k r ^ gammaRightExponent r R j l * cy k r)

def gammaTailFactor (r R j l : ℕ) : CompletedNode k r :=
  (if gammaLeftExponent R j l = 0 then 1
    else 1 - tau k r ^ gammaLeftExponent R j l * cx k r) *
  (if gammaRightExponent r R j l = 0 then 1
    else 1 - tau k r ^ gammaRightExponent r R j l * cy k r)

def gammaPartial (r R j N : ℕ) : CompletedNode k r :=
  ∏ l ∈ Finset.range N, gammaFactor k r R j l

def gammaTailPartial (r R j N : ℕ) : CompletedNode k r :=
  ∏ l ∈ Finset.range N, gammaTailFactor k r R j l

def gammaHorizontal (r R j : ℕ) : CompletedNode k r :=
  (if j = 0 then 1 - cx k r else 1) *
    (if j + r = R then 1 - cy k r else 1)

variable [CharZero k]

/-- Choose the already accepted concrete extension; no new provider is assumed. -/
def specialization (r i : ℕ) (hr : 0 < r) (hi : i < r) (a : k) (ha : a ≠ 0) :
    CompletedNode k r →+* PowerSeries k :=
  Classical.choose
    (ArithmeticThetaScaledTateCompletionExtensionR0048.completion_specialization_exists_and_filtered
      k r i hr hi a ha)

end ArithmeticThetaScaledAnnularR0050
