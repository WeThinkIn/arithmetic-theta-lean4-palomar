module

public import CompletedTorsionSectionGluingR0058

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaCorrectedGammaR0061

variable (k : Type u) [Field k] [CharZero k]

abbrev Chart := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
abbrev OpenHat (j : ℕ) (side : Bool) :=
  ArithmeticThetaIndexedOverlapsR0058.OpenHat k j side

def tau : Chart k := ArithmeticThetaScaledAnnularR0050.tau k 1
def cx : Chart k := ArithmeticThetaScaledAnnularR0050.cx k 1
def cy : Chart k := ArithmeticThetaScaledAnnularR0050.cy k 1

def leftExponent (r j l : ℕ) : ℕ := r * l + j
def rightExponent (r j l : ℕ) : ℕ := r * l - j - 1

def leftFactor (r j l : ℕ) : Chart k :=
  1 - tau k ^ leftExponent r j l * cx k
def rightFactor (r j l : ℕ) : Chart k :=
  1 - tau k ^ rightExponent r j l * cy k

def leftPartial (r j N : ℕ) : Chart k :=
  ∏ l ∈ Finset.range N, leftFactor k r j l
def rightPartial (r j N : ℕ) : Chart k :=
  ∏ l ∈ Finset.range N, rightFactor k r j (l + 1)
def fullPartial (r j N : ℕ) : Chart k :=
  leftPartial k r j N * rightPartial k r j N

def horizontal (r j : ℕ) : Chart k :=
  (if j = 0 then 1 - cx k else 1) *
    (if j + 1 = r then 1 - cy k else 1)

def leftTailFactor (r j l : ℕ) : Chart k :=
  if j = 0 ∧ l = 0 then 1 else leftFactor k r j l
def rightTailFactor (r j l : ℕ) : Chart k :=
  if j + 1 = r ∧ l = 0 then 1 else rightFactor k r j (l + 1)
def tailPartial (r j N : ℕ) : Chart k :=
  (∏ l ∈ Finset.range N, leftTailFactor k r j l) *
    (∏ l ∈ Finset.range N, rightTailFactor k r j l)

def Converges (r j : ℕ) (s : ℕ → Chart k) (v : Chart k) : Prop :=
  ∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    v - s N ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n

def IsGammaData (r j : ℕ) (v u : Chart k) : Prop :=
  IsUnit v ∧ Converges k r j (tailPartial k r j) v ∧
    Converges k r j (fullPartial k r j) u ∧
    u = horizontal k r j * v

def restrict (j : ℕ) (side : Bool) : Chart k →+* OpenHat k j side :=
  Classical.choose
    (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions k j side).exists

def overlap (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    OpenHat k j false ≃+*
      OpenHat k (ArithmeticThetaIndexedOverlapsR0058.next r j) true :=
  Classical.choose
    (ArithmeticThetaIndexedOverlapsR0058.completed_indexed_adjacent k r j hr hj).exists

def xUnit (j : ℕ) : (ArithmeticThetaIndexedOverlapsR0058.Open k j true)ˣ :=
  ArithmeticThetaIndexedOverlapsR0058.xUnit k j

end ArithmeticThetaCorrectedGammaR0061
