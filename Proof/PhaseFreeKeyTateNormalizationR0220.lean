module

public import SchemeAlphaTateComparisonR0220
public import CompactHodgeLatticeExtensionR0182

@[expose] public section

/-! Complete Tate normalization of the supplied phase-free key in its specified frames. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaKeyTateR0220
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaMultiplierKeyR0217 ArithmeticThetaPullback ArithmeticThetaSheafTensor
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

/-- The same key image, transported by the given comparisons, has the full
integral Tate coefficient and the positive canonical theta-square coefficient. -/
theorem phase_free_key_tate_normalization : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ), 0 < N → 4 ∣ N → ∀ (T : ArithmeticThetaTateCuspsR0181.TateLevel k N), ∀ (S : AlgebraicGeometry.Scheme) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ → ∀ (A : ArithmeticThetaPhaseFreeKeyR0219.MarkedTest E P) (B : ArithmeticThetaKeyTateR0220.TateTest k N T A.family A.marking) (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback A.map).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent A.family)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c → ∀ (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k N), ArithmeticThetaBoundaryHodgeR0182.Normalized k N δ → ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaKeyTateR0220.tateProduct k N T E P L A B) ⊤ (ArithmeticThetaKeyTateR0220.productFrame k N T E P L m A B δ) ∧ ArithmeticThetaKeyTateR0220.Expansion k N T E P L m A B δ (ArithmeticThetaKeyTateR0220.productAt k N T E P L A B c (κ.hom.app ⊤ (ArithmeticThetaMultiplierKeyR0217.evaluationSquare E P e))) := by
  intro k _ _ N hN h4 T S E P L m hm β hβ e _he κ hκ A B c hc δ hδ
  obtain ⟨a, ha⟩ := (hβ A).2.1
  have hfirst := (hβ A).2.2 c hc a ha
  have htransport : productAt k N T E P L A B c β =
      tensorSection (ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries k))
        (Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k N))
        (tateMultiplier k N T E P L A B) ⊤
        (alphaAt k N T A.family A.marking B a)
        (tateMultiplierFrame k N T E P L m A B) := by
    unfold productAt
    rw [hfirst]
    change (sheafTensorCongr (ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries k))
      (SchemeAlphaSection.hodgeIso A.family A.marking (B.affine k N T))
      (Iso.refl _)).hom.app ⊤
        ((pullback_sheafTensor_iso (ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries k)) A.base B.base
          (Cotangent A.family) ((Scheme.Modules.pullback A.map).obj L)).hom.app ⊤
          (pullbackGlobalSection B.base _
            (tensorSection A.base (Cotangent A.family)
              ((Scheme.Modules.pullback A.map).obj L) ⊤ a (m A)))) = _
    have ht := pullback_sheafTensor_section
      (ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries k)) A.base B.base
      (Cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) a (m A)
    exact (congrArg ((sheafTensorCongr
      (ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries k))
      (SchemeAlphaSection.hodgeIso A.family A.marking (B.affine k N T))
      (Iso.refl _)).hom.app ⊤) ht).trans
        (sheafTensorCongr_section _ _ _ ⊤ _ _)
  constructor
  · exact tensor_section_frame _ _ (hodgeGenerator_frame k N δ)
      (HodgeBaseChange.pullback_frame B.base _ _ (hm.2.1 A))
  · change κ.hom.app ⊤ (evaluationSquare E P e) = β at hκ
    rw [hκ, htransport]
    obtain ⟨⟨v, j, hj, haj⟩, hcanonical⟩ :=
      scheme_alpha_tate_comparison k N hN h4 T A.base A.family A.marking B δ hδ a ha
    constructor
    · refine ⟨v, j, hj, ?_⟩
      rw [haj]
      exact tensor_smul_left _ _ _ _ _ _
    · intro ζ hζ hmark
      rw [hcanonical ζ hζ hmark]
      exact tensor_smul_left _ _ _ _ _ _

end ArithmeticThetaKeyTateR0220

#print axioms ArithmeticThetaKeyTateR0220.phase_free_key_tate_normalization
