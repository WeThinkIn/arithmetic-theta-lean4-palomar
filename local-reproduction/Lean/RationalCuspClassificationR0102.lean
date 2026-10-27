import RationalBoundaryCoordinatesR0102
import CongruenceLabelFibersR0102
import IntegralPrimitiveLiftR0102
import FiniteFullLevelCount

noncomputable section
namespace ArithmeticThetaIntegralCuspsR0102

/-- Choose an integral representative of an actual rational boundary point. -/
def boundaryMarking (x : WithTop ℚ) : Marking :=
  Classical.choose (rational_boundary_coordinates.1 x)

lemma boundary_boundaryMarking (x : WithTop ℚ) : boundary (boundaryMarking x) = x :=
  Classical.choose_spec (rational_boundary_coordinates.1 x)

/-- The signed residue label of a rational boundary point. -/
def boundaryLabel (L : ℕ) (x : WithTop ℚ) :
    ArithmeticThetaLevelCount.SignedPrimitivePair L := signedLabel L (boundaryMarking x)

lemma boundaryLabel_boundary (L : ℕ) (hL : 3 ≤ L) (A : Marking) :
    boundaryLabel L (boundary A) = signedLabel L A := by
  apply (congruence_label_fibers L hL _ _).2
  obtain ⟨p, hp, he⟩ := (rational_boundary_coordinates.2
    (boundaryMarking (boundary A)) A).1 (boundary_boundaryMarking (boundary A))
  exact ⟨1, (CongruenceSubgroup.Gamma L).one_mem, p, hp, by simpa using he⟩

lemma boundaryLabel_respects (L : ℕ) (hL : 3 ≤ L) {x y : WithTop ℚ}
    (h : BoundaryRel L x y) : boundaryLabel L x = boundaryLabel L y := by
  obtain ⟨A, B, rfl, rfl, hAB⟩ := h
  rw [boundaryLabel_boundary L hL, boundaryLabel_boundary L hL]
  exact (congruence_label_fibers L hL A B).2 hAB

/-- The canonical signed-label map on the quotient of the rational boundary. -/
def cuspLabel (L : ℕ) (hL : 3 ≤ L) :
    RationalCusps L → ArithmeticThetaLevelCount.SignedPrimitivePair L :=
  Quot.lift (boundaryLabel L) (fun _ _ h => boundaryLabel_respects L hL h)

lemma cuspLabel_cusp_boundary (L : ℕ) (hL : 3 ≤ L) (A : Marking) :
    cuspLabel L hL (cusp L (boundary A)) = signedLabel L A :=
  boundaryLabel_boundary L hL A

/-- Equality of labels already identifies the actual rational-boundary orbits. -/
lemma cuspLabel_injective (L : ℕ) (hL : 3 ≤ L) :
    Function.Injective (cuspLabel L hL) := by
  intro x y
  induction x using Quot.inductionOn with
  | h x =>
    induction y using Quot.inductionOn with
    | h y =>
      intro hxy
      apply Quot.sound
      refine ⟨boundaryMarking x, boundaryMarking y,
        boundary_boundaryMarking x, boundary_boundaryMarking y, ?_⟩
      exact (congruence_label_fibers L hL _ _).1 hxy

/-- Finiteness needs injectivity into the finite signed-label carrier only. -/
lemma rationalCusps_finite (L : ℕ) (hL : 3 ≤ L) : Finite (RationalCusps L) := by
  have : NeZero L := ⟨by omega⟩
  let : Finite (ArithmeticThetaLevelCount.PrimitivePair L) :=
    inferInstanceAs (Finite {v : ZMod L × ZMod L // IsCoprime v.1 v.2})
  let : Finite (ArithmeticThetaLevelCount.SignedPrimitivePair L) :=
    inferInstanceAs (Finite (Quot (fun a b : ArithmeticThetaLevelCount.PrimitivePair L =>
      b.val = -a.val)))
  exact Finite.of_injective (cuspLabel L hL) (cuspLabel_injective L hL)

lemma cuspLabel_surjective (L : ℕ) (hL : 3 ≤ L) :
    Function.Surjective (cuspLabel L hL) := by
  intro v
  induction v using Quot.inductionOn with
  | h v =>
    obtain ⟨A, hA⟩ := integral_primitive_lift L hL v
    refine ⟨cusp L (boundary A), ?_⟩
    rw [cuspLabel_cusp_boundary]
    exact congrArg (Quot.mk _) hA

/-- Rational boundary cusp classes are exactly signed primitive residue labels. -/
theorem rational_cusp_classification : ∀ L : ℕ, 3 ≤ L →
    ∃ e : RationalCusps L ≃ ArithmeticThetaLevelCount.SignedPrimitivePair L,
      (∀ A : Marking, e (cusp L (boundary A)) = signedLabel L A) ∧
      Finite (RationalCusps L) ∧
      (2 * L : ℚ) * (Nat.card (RationalCusps L) : ℚ) =
        ArithmeticThetaLevelCount.levelIndex L := by
  intro L hL
  let e := Equiv.ofBijective (cuspLabel L hL)
    ⟨cuspLabel_injective L hL, cuspLabel_surjective L hL⟩
  refine ⟨e, cuspLabel_cusp_boundary L hL, rationalCusps_finite L hL, ?_⟩
  rw [Nat.card_congr e]
  exact (ArithmeticThetaGlobalization.finite_full_level_count L hL).2

end ArithmeticThetaIntegralCuspsR0102
