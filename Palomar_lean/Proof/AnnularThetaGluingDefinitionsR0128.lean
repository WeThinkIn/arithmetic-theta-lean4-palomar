module

public import CorrectedGammaDefinitionsR0061
public import ScaledThetaLimitExactSpecializationR0050
public import AllSolutionsAnnularEvaluationR0119
public import ScaledThetaCompletedLimitR0050

@[expose] public section

/-! Literal theta sums on the existing completed nodes and their actual
coordinate-open maps. These definitions assert no proper model, algebraization,
line bundle, or compatibility theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAnnularThetaR0128

abbrev Chart (k : Type u) [Field k] [CharZero k] :=
  ArithmeticThetaAnnularTorsionPrereqR0053.Chart k

def shift (j : ℕ) : ℕ := ArithmeticThetaScaledAnnularR0050.thetaShift 1 j

def thetaSection (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (he : Even m) (j : ℕ) (ν : Fin m) : Chart k :=
  Classical.choose (ArithmeticThetaScaledAnnularR0050.theta_completed_limit
    k 1 m 1 j (ν.val : ℤ) (by decide) hm he (by decide))

def specialize (k : Type u) [Field k] [CharZero k] (a : kˣ) :
    Chart k →+* PowerSeries k :=
  ArithmeticThetaScaledAnnularR0050.specialization k 1 0 (by decide) (by decide)
    (a : k) a.ne_zero

def restriction (k : Type u) [Field k] [CharZero k] (j : ℕ) (side : Bool) :=
  ArithmeticThetaCorrectedGammaR0061.restrict k j side

def adjacent (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (j : ℕ) (hj : j < 2*m) :=
  ArithmeticThetaCorrectedGammaR0061.overlap k (2*m) j
    (Nat.mul_pos (by decide) hm) hj

def interiorAdjacent (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (j : ℕ) (hj : j+1 < 2*m) :
    ArithmeticThetaIndexedOverlapsR0058.OpenHat k j false ≃+*
      ArithmeticThetaIndexedOverlapsR0058.OpenHat k (j+1) true := by
  have hn : ArithmeticThetaIndexedOverlapsR0058.next (2*m) j = j+1 :=
    Nat.mod_eq_of_lt hj
  exact hn ▸ (adjacent k m hm j (Nat.lt_of_succ_lt hj))

def targetT (k : Type u) [Field k] [CharZero k] (j : ℕ) :=
  restriction k j true (ArithmeticThetaAnnularTorsionPrereqR0053.tau k)

def targetX (k : Type u) [Field k] [CharZero k] (j : ℕ) :=
  restriction k j true (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)

def InteriorEquation (k : Type u) [Field k] [CharZero k] (m : ℕ)
    (hm : 0 < m) (j : ℕ) (hj : j+1 < 2*m) (s s' : Chart k) : Prop :=
  targetT k (j+1) ^ shift (j+1) * interiorAdjacent k m hm j hj (restriction k j false s) =
    targetT k (j+1) ^ shift j * restriction k (j+1) true s'

def lastIndex (m : ℕ) (hm : 0 < m) : Fin (2*m) :=
  ⟨2*m-1, Nat.sub_lt (Nat.mul_pos (by decide) hm) (by decide)⟩

def firstIndex (m : ℕ) (hm : 0 < m) : Fin (2*m) :=
  ⟨0, Nat.mul_pos (by decide) hm⟩

def boundaryAdjacent (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) :
    ArithmeticThetaIndexedOverlapsR0058.OpenHat k (lastIndex m hm).val false ≃+*
      ArithmeticThetaIndexedOverlapsR0058.OpenHat k 0 true := by
  have hp : 0 < 2*m := Nat.mul_pos (by decide) hm
  have hn : ArithmeticThetaIndexedOverlapsR0058.next (2*m) (lastIndex m hm).val = 0 := by
    simp [ArithmeticThetaIndexedOverlapsR0058.next, lastIndex, Nat.sub_add_cancel hp]
  exact hn ▸ (adjacent k m hm (lastIndex m hm).val (lastIndex m hm).isLt)

def PeriodEquation (k : Type u) [Field k] [CharZero k] (m : ℕ)
    (hm : 0 < m) (sLast sZero : Chart k) : Prop :=
  targetT k 0 ^ (shift 0 + m*m) * targetX k 0 ^ m *
      boundaryAdjacent k m hm
        (restriction k (lastIndex m hm).val false sLast) =
    targetT k 0 ^ shift (lastIndex m hm).val * restriction k 0 true sZero

def combine (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (he : Even m) (j : ℕ) (w : Fin m → PowerSeries k) : Chart k :=
  ∑ ν : Fin m, ArithmeticThetaAnnularTorsionPrereqR0053.base k (w ν) *
    thetaSection k m hm he j ν

def commonShift (m : ℕ) : ℕ := (2*m)^2

def uniformSection (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (he : Even m) (w : Fin m → PowerSeries k) (j : Fin (2*m)) : Chart k :=
  ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (commonShift m - shift j.val) *
    combine k m hm he j.val w

/-- Explicit gluing equations after a single vertical denominator has been
cleared. This is a predicate on actual chart elements and actual maps, not a
claim that an algebraic proper model or a Hodge line has been constructed. -/
def UniformCompatible (k : Type u) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m)
    (S : Fin (2*m) → Chart k) : Prop :=
  (∀ (j : Fin (2*m)) (h : j.val+1 < 2*m),
    interiorAdjacent k m hm j.val h (restriction k j.val false (S j)) =
      restriction k (j.val+1) true (S ⟨j.val+1,h⟩)) ∧
  targetT k 0 ^ (m*m) * targetX k 0 ^ m *
      boundaryAdjacent k m hm
        (restriction k (lastIndex m hm).val false (S (lastIndex m hm))) =
    restriction k 0 true (S (firstIndex m hm))

end ArithmeticThetaAnnularThetaR0128
