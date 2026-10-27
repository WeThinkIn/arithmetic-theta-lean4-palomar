import SchemeAlphaNaturalityR0215
import SchemePhaseMarkingInvarianceR0215

/-! The even-stabilizer character on the actual global cotangent section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeFourCharacterR0215
namespace SchemeAlphaCharacter
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open MarkedAffineTestComparison SchemeAlphaSection

variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)

/-- Pullback of the scalar action uses precisely the structural map of the test. -/
lemma affineAlpha_smul (P : AffineTest E M)
    (z : Γ(S, ⊤)) (n : ℕ) (a : Γ(Cotangent E, ⊤)) :
    affineAlpha E M P (idealIso E M P) (z^n • a) =
      ArithmeticThetaOpenHodgeR0180.scalar P.ring ((affineScalar E M P z)^n) •
        affineAlpha E M P (idealIso E M P) a := by
  have hs : ArithmeticThetaOpenHodgeR0180.scalar P.ring ((affineScalar E M P z)^n) =
      P.base.appTop (z^n) := by
    unfold ArithmeticThetaOpenHodgeR0180.scalar affineScalar
    rw [← map_pow, ← map_pow]
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of P.ring)).hom_inv_id _
  rw [hs]
  change (affineHodgeMap E M P (idealIso E M P)).app ⊤
      (Scheme.Modules.pullbackLocalSection P.base (z^n • a)) = _
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  rfl

/-- Change only the full marking of a test; the curve, origin, maps and ideal
comparison are literally retained. The accepted arbitrary-ring character then
compares the two intrinsic sections in this same Hodge module. -/
lemma affine_character (P : AffineTest E M) (N : FullLevel E 4)
    (A : ArithmeticThetaFourTorsion.Mat4) (hA : ArithmeticThetaFourTorsion.PreservesEven A)
    (hN : Changes E M N A) (z : Γ(S, ⊤)) (hz : MillerPhase E M z)
    (a a' : Γ(Cotangent E, ⊤)) (ha : RealizesAlpha E M a) (ha' : RealizesAlpha E N a') :
    affineAlpha E M P (idealIso E M P) a' =
      ArithmeticThetaOpenHodgeR0180.scalar P.ring
        ((affineScalar E M P z)^(ArithmeticThetaFourTorsion.characterExponent A).val) •
          affineAlpha E M P (idealIso E M P) a := by
  letI := P.elliptic
  obtain ⟨w, hw, _, _, _, _, hc⟩ :=
    ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_alpha_character
      P.ring P.equation P.law P.originLaw P.level
  have hwz : w = affineScalar E M P z := by
    obtain ⟨v, hv, hu⟩ :=
      (ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase
        P.ring P.equation P.law P.originLaw P.level).1
    exact (hu w hw).trans (hu _ (hz P)).symm
  subst w
  obtain ⟨L, hL, _, hchar⟩ := hc A hA
  have hzero : (family E M P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [family_zero]
    exact P.zero_eq
  have hn (x : SchemeHomOver (𝟙 (ArithmeticThetaLocalWeierstrassR0203.Base P.ring))
      (family E M P).p) (y : SchemeHomOver (𝟙 S) E.p)
      (h : x.val ≫ P.comparison = P.base ≫ y.val) (n : ℕ) :
      (P.law.nsmul (𝟙 _) n x).val ≫ P.comparison =
        P.base ≫ (multiple E (𝟙 S) n y).val := by
    rw [← SchemePhaseMarkingInvariance.multiple_eq E M P]
    exact CartesianFullMarking.multiple_comp E (family E M P) P.base P.comparison
      hzero P.mul_eq x y h n
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
  exact hchar _ _ ((ha P).2 _ (idealIso_compatible E M P))
    ((ha' Q).2 (idealIso E M P) (idealIso_compatible E M P))

/-- Equality is checked on the actual open affine tests, with no nonemptiness
or finiteness condition on the base. -/
lemma section_character (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (N : FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4)
    (hA : ArithmeticThetaFourTorsion.PreservesEven A) (hN : Changes E M N A)
    (z : Γ(S, ⊤)) (hz : MillerPhase E M z)
    (a a' : Γ(Cotangent E, ⊤)) (ha : RealizesAlpha E M a) (ha' : RealizesAlpha E N a') :
    a' = z^(ArithmeticThetaFourTorsion.characterExponent A).val • a := by
  let P : S → AffineTest E M := fun s => (coverage E M k σ s).choose
  have ho : ∀ s, IsOpenImmersion (P s).base := fun s =>
    (coverage E M k σ s).choose_spec.1
  apply sections_ext_cover (fun s => ArithmeticThetaLocalWeierstrassR0203.Base (P s).ring)
    (fun s => (P s).base) ho
    (fun s => ⟨s, (coverage E M k σ s).choose_spec.2⟩) (Cotangent E) a' _
  intro s
  apply (ConcreteCategory.bijective_of_isIso ((hodgeIso E M (P s)).hom.app ⊤)).1
  exact (affine_character E M (P s) N A hA hN z hz a a' ha ha').trans
    (affineAlpha_smul E M (P s) z _ a).symm

end SchemeAlphaCharacter

/-- The full source character, using the same global Miller phase and signed
cotangent alpha for every even-stabilizer marking change. -/
theorem scheme_alpha_character :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (z : S.presheaf.obj (Opposite.op ⊤)) (a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a → ∀ (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A ∧ ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M' z ∧ (∀ a' : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M' a' → a' = z ^ (ArithmeticThetaFourTorsion.characterExponent A).val • a) := by
  intro k _ _ S σ E M z a hz ha A hA
  obtain ⟨N, hN, _⟩ := (scheme_four_marking_action k S σ E M).1 A hA.1
  obtain ⟨w, hw, _⟩ := (scheme_miller_phase k S σ E N).1
  have heq := scheme_phase_marking_invariance k S σ E M N A hA.1 hN z w hz hw
  refine ⟨N, hN, heq ▸ hw, ?_⟩
  intro a' ha'
  exact SchemeAlphaCharacter.section_character E M k σ N A hA hN z hz a a' ha ha'

#print axioms scheme_alpha_character
end ArithmeticThetaSchemeFourCharacterR0215
