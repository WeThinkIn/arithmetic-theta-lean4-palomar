module

public import TateSchemeExactCommutatorR0263
public import TateSchemeInversionLiftR0263
public import TateSchemeSectionEvaluationR0263
public import SchemeGlobalSignAlignmentR0262
public import SchemeFullLevelThetaMarkingR0259

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaTateSchemeMarkingR0263
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
namespace GlobalLiteralMarking

/-- Transfer the given full marking using the actual origin and multiplication. -/
def fullLevel (k : Type) [Field k] [CharZero k] {m : ℕ} (V : TateLevel k (2*m)) :
    ArithmeticThetaSchemeLevelR0204.FullLevel (family k V) (2*m) := by
  letI := V.elliptic
  refine { x := V.marking.x, y := V.marking.y,
           killed_x := ?_, killed_y := ?_, avoids := ?_ }
  · exact (ArithmeticThetaSchemeKatoUnitR0250.SchemeMultiplicationDegree.weierstrass_multiple
      (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw _ _ _).trans V.marking.killed_x
  · exact (ArithmeticThetaSchemeKatoUnitR0250.SchemeMultiplicationDegree.weierstrass_multiple
      (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw _ _ _).trans V.marking.killed_y
  · intro i j hij
    dsimp only [family]
    rw [ArithmeticThetaSchemeKatoUnitR0250.SchemeMultiplicationDegree.weierstrass_multiple,
      ArithmeticThetaSchemeKatoUnitR0250.SchemeMultiplicationDegree.weierstrass_multiple,
      ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero]
    exact V.marking.avoids i j hij

end GlobalLiteralMarking

/-- Literal Tate lifts and unique original-base constant signs for every pointed
Cartesian group comparison. The comparison itself remains a hypothesis. -/
theorem global_literal_tate_marking :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (V : ArithmeticThetaTateCuspsR0181.TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) V → ∃ (Q : ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k m hm V ζ) (N : ArithmeticThetaSchemeLevelR0204.FullLevel (ArithmeticThetaTateSchemeMarkingR0263.family k V) (2*m)), N.x = ArithmeticThetaTateSchemeMarkingR0263.pointX k V ∧ N.y = ArithmeticThetaTateSchemeMarkingR0263.pointY k V ∧ ∃ (i : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k V) m (ArithmeticThetaSchemeThetaMarkingR0259.inverse (ArithmeticThetaTateSchemeMarkingR0263.family k V))) (a : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k V) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointX k V))) (b : ArithmeticThetaSchemeThetaMarkingR0259.Lift (ArithmeticThetaTateSchemeMarkingR0263.family k V) m (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointY k V))), ArithmeticThetaTateSchemeMarkingR0263.inversionLiftFacts k V Q he i ∧ ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k V Q he hζ a ∧ ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k V Q he b ∧ ArithmeticThetaTateSchemeMarkingR0263.ExactValues k V Q he ∧ ArithmeticThetaSchemeThetaMarkingR0259.Commutator (ArithmeticThetaTateSchemeMarkingR0263.family k V) m (ArithmeticThetaTateSchemeMarkingR0263.pointX k V) (ArithmeticThetaTateSchemeMarkingR0263.pointY k V) a b (ArithmeticThetaTateSchemeMarkingR0263.phase k (ζ := ζ)) ∧ ∀ (S : AlgebraicGeometry.Scheme) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m)) (t : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Puncture k) S) (f : Quiver.Hom (ArithmeticThetaTateSchemeMarkingR0263.family k V).curve E.curve) (hc : CategoryTheory.IsPullback f (ArithmeticThetaTateSchemeMarkingR0263.family k V).p E.p t) (hz : CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateSchemeMarkingR0263.family k V).zero f = CategoryTheory.CategoryStruct.comp t E.zero), ArithmeticThetaSchemeLevelR0204.Multiplicative E (ArithmeticThetaTateSchemeMarkingR0263.family k V) t f → CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateSchemeMarkingR0263.pointX k V).val f = CategoryTheory.CategoryStruct.comp t M.x.val → CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateSchemeMarkingR0263.pointY k V).val f = CategoryTheory.CategoryStruct.comp t M.y.val → ∃ (I : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.inverse E)) (A : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x)) (B : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y)), ArithmeticThetaSchemeThetaMarkingR0259.NormalizedInversion E m I ∧ ArithmeticThetaSchemeThetaMarkingR0259.MidpointNormalized E m M.x I A ∧ ArithmeticThetaSchemeThetaMarkingR0259.MidpointNormalized E m M.y I B ∧ ArithmeticThetaSchemeThetaMarkingR0259.Symmetric E m M.x I A ∧ ArithmeticThetaSchemeThetaMarkingR0259.Symmetric E m M.y I B ∧ (∃! signs : Bool × Bool, ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E (ArithmeticThetaTateSchemeMarkingR0263.family k V) t f hc hz m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x) (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointX k V)) (ArithmeticThetaSchemeThetaMarkingR0259.scaled E m (ArithmeticThetaSchemeThetaNaturalityR0262.signUnit S signs.1) A) a ∧ ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E (ArithmeticThetaTateSchemeMarkingR0263.family k V) t f hc hz m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y) (ArithmeticThetaSchemeThetaMarkingR0259.translation (ArithmeticThetaTateSchemeMarkingR0263.family k V) (ArithmeticThetaTateSchemeMarkingR0263.pointY k V)) (ArithmeticThetaSchemeThetaMarkingR0259.scaled E m (ArithmeticThetaSchemeThetaNaturalityR0262.signUnit S signs.2) B) b) := by
  intro k _ _ m hm he V ζ hζ hmark
  obtain ⟨Q⟩ := LocalTheta.markedModel_exists k m hm he V ζ hζ hmark
  let N := GlobalLiteralMarking.fullLevel k V
  obtain ⟨i, hi, _⟩ := tate_scheme_inversion_lift k m hm he V ζ hζ Q
  obtain ⟨a, ha, _⟩ := tate_scheme_scalar_lift k m hm he V ζ hζ Q
  obtain ⟨b, hb, _⟩ := tate_scheme_shift_lift k m hm he V ζ hζ Q
  have hv := (tate_scheme_section_evaluation k m hm he V ζ hζ Q).2
  have hcmt := (tate_scheme_exact_commutator k m hm he V ζ hζ Q a b ha hb).1
  refine ⟨Q, N, rfl, rfl, i, a, b, hi, ha, hb, hv, hcmt, ?_⟩
  intro S σ E M t f hc hz hmul hx hy
  obtain ⟨_, I, hI, _, _, A, B, hA, hsA, hB, hsB, _⟩ :=
    scheme_full_level_theta_marking k S σ E m hm he M
  refine ⟨I, A, B, hI, hA, hB, hsA, hsB, ?_⟩
  exact ArithmeticThetaSchemeThetaNaturalityR0262.scheme_global_sign_alignment
    k S σ E (Puncture k) (family k V) t f hc hz m hm he hmul M N hx hy
    I i hI hi.2 A B a b hsA hsB (ha.2 i hi.2) (hb.2 i hi.2)
    isPreconnected_univ inferInstance

#print axioms global_literal_tate_marking
end ArithmeticThetaTateSchemeMarkingR0263
