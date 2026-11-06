module

public import SchemeFourMarkingActionR0215
public import SchemeMillerPhaseR0215
public import ArbitraryPhaseMarkingInvarianceR0214
public import RelativeMarkingActionR0211

@[expose] public section

/-! Determinant-one marking invariance of the actual global Miller phase. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemePhaseMarkingInvariance
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open MarkedAffineTestComparison

variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

/-- The two multiple operations use the same actual group law. -/
lemma multiple_eq (P : AffineTest E M) {T : Scheme.{u}} (t : T ⟶ Base P.ring)
    (n : ℕ) (x : SchemeHomOver t (family E M P).p) :
    multiple (family E M P) t n x = P.law.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P.law.mul t (multiple (family E M P) t n x) x =
      P.law.mul t (P.law.nsmul t n x) x
    rw [ih]

/-- Change the marking on the same affine test, preserving its base and curve maps. -/
lemma changed_test (P : AffineTest E M) (N : FullLevel E 4)
    (A : ArithmeticThetaFourTorsion.Mat4) (hA : A.det = 1)
    (hN : Changes E M N A) :
    ∃ Q : AffineTest E N, ∀ z z' : Γ(S, ⊤),
      ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase
        P.ring P.equation P.law P.level (affineScalar E M P z) →
      ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase
        Q.ring Q.equation Q.law Q.level (affineScalar E N Q z') →
      affineScalar E M P z' = affineScalar E M P z := by
  letI := P.elliptic
  obtain ⟨L, hL, _⟩ :=
    (ArithmeticThetaRelativeFourCharacterR0211.relative_marking_action
      P.ring P.equation P.law P.originLaw (Base P.ring) (𝟙 _)).1 P.level A hA
  have hz : (family E M P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [family_zero]
    exact P.zero_eq
  have hn (x : SchemeHomOver (𝟙 (Base P.ring)) (family E M P).p)
      (y : SchemeHomOver (𝟙 S) E.p)
      (h : x.val ≫ P.comparison = P.base ≫ y.val) (n : ℕ) :
      (P.law.nsmul (𝟙 _) n x).val ≫ P.comparison =
        P.base ≫ (multiple E (𝟙 S) n y).val := by
    rw [← multiple_eq E M P]
    exact CartesianFullMarking.multiple_comp E (family E M P) P.base P.comparison
      hz P.mul_eq x y h n
  have hx : L.x.val ≫ P.comparison = P.base ≫ N.x.val := by
    rw [hL.1, hN.1]
    exact CartesianFullMarking.mul_comp E (family E M P) P.base P.comparison P.mul_eq
      _ _ _ _ (hn _ _ P.x_eq _) (hn _ _ P.y_eq _)
  have hy : L.y.val ≫ P.comparison = P.base ≫ N.y.val := by
    rw [hL.2, hN.2]
    exact CartesianFullMarking.mul_comp E (family E M P) P.base P.comparison P.mul_eq
      _ _ _ _ (hn _ _ P.x_eq _) (hn _ _ P.y_eq _)
  let Q : AffineTest E N :=
    { ring := P.ring, equation := P.equation, elliptic := P.elliptic
      law := P.law, originLaw := P.originLaw, base := P.base
      comparison := P.comparison, cartesian := P.cartesian
      zero_eq := P.zero_eq, mul_eq := P.mul_eq, level := L, x_eq := hx, y_eq := hy }
  refine ⟨Q, ?_⟩
  intro z z' hz hz'
  exact ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_phase_marking_invariance
    P.ring P.equation P.law P.originLaw P.level L A hA hL _ _ hz hz'

end SchemePhaseMarkingInvariance
open CategoryTheory AlgebraicGeometry

/-- Equality of the full regular functions, tested over the original affine rings. -/
theorem scheme_phase_marking_invariance :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4), A.det = 1 → ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A → ∀ z z' : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M' z' → z' = z := by
  intro k _ _ S σ E M N A hA hN z z' hz hz'
  apply SchemeMillerPhase.section_ext E M k σ
  intro P
  obtain ⟨Q, hQ⟩ := SchemePhaseMarkingInvariance.changed_test E M P N A hA hN
  exact hQ z z' (hz P) (hz' Q)

#print axioms scheme_phase_marking_invariance
end ArithmeticThetaSchemeFourCharacterR0215
