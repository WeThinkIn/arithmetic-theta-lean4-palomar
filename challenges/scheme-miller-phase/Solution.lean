module
public import SchemeMillerPhaseR0215
public import ArbitrarySplitFiberBasisR0214
public import GeometricFourCharacterR0118
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
universe u
namespace ArithmeticThetaPalomarSchemePhase433
theorem localDataExists (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k) (he : Function.Injective e) : Nonempty (ArithmeticThetaGeometricPairingR0118.LocalData k e) := by
  obtain ⟨D, _⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character k e he
  exact ⟨D⟩
theorem arbitrarySplitFiberBasis :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (∃ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y) ∧ (∀ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y → ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F),  Function.Injective (ι ∘ e) ∧ (∃! b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b) ∧ (∀ b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b → ArithmeticThetaMarkingR0115.IsBasis F (ι ∘ e) b ∧ ArithmeticThetaMarkingR0115.labels F (ι ∘ e) b = ι ∘ e)) := by
  exact ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_split_fiber_basis
theorem schemeMillerPhase :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∃! z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z) ∧ (∀ z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → IsUnit z ∧ z^2 = -1 ∧ (Nontrivial (S.presheaf.obj (Opposite.op ⊤)) → IsPrimitiveRoot z 4) ∧ (∀ P : ArithmeticThetaSchemeFourCharacterR0215.AffineTest E M, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase P.ring P.equation P.law P.level (ArithmeticThetaSchemeFourCharacterR0215.affineScalar E M P z))) := by
  exact ArithmeticThetaSchemeFourCharacterR0215.scheme_miller_phase
theorem recover_original_051 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∃! z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z) ∧ (∀ z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → IsUnit z ∧ z^2 = -1 ∧ (Nontrivial (S.presheaf.obj (Opposite.op ⊤)) → IsPrimitiveRoot z 4) ∧ (∀ P : ArithmeticThetaSchemeFourCharacterR0215.AffineTest E M, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase P.ring P.equation P.law P.level (ArithmeticThetaSchemeFourCharacterR0215.affineScalar E M P z))) := by
  exact schemeMillerPhase
end ArithmeticThetaPalomarSchemePhase433
