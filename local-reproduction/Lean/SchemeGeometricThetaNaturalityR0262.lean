import SchemeThetaComparisonCoherenceR0262
import SchemeNormalizationTransportR0262
import SchemePushforwardIntertwiningR0262
import SchemeEvaluationNaturalityR0262
import SchemeInvariantComponentNaturalityR0262
import SchemeCommutatorNaturalityR0262
import SchemeGlobalSignAlignmentR0262

/-! Assembly of canonical geometric theta naturality from the accepted providers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261

theorem scheme_geometric_theta_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hc : CategoryTheory.IsPullback f F.p E.p b) (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), ∀ (m : ℕ), 0 < m → Even m → ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f → ∀ (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m)) (N : ArithmeticThetaSchemeLevelR0204.FullLevel F (2*m)), CategoryTheory.CategoryStruct.comp N.x.val f = CategoryTheory.CategoryStruct.comp b M.x.val → CategoryTheory.CategoryStruct.comp N.y.val f = CategoryTheory.CategoryStruct.comp b M.y.val → ((∀ (hc : CategoryTheory.IsPullback (CategoryTheory.CategoryStruct.id E.curve) E.p E.p (CategoryTheory.CategoryStruct.id S)) (hz : CategoryTheory.CategoryStruct.comp E.zero (CategoryTheory.CategoryStruct.id E.curve) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id S) E.zero), ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E E (CategoryTheory.CategoryStruct.id S) (CategoryTheory.CategoryStruct.id E.curve) hc hz m = (AlgebraicGeometry.Scheme.Modules.pullbackId E.curve).app (ArithmeticThetaSchemeThetaMarkingR0259.thetaLine E m)) ∧ (∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hc : CategoryTheory.IsPullback f F.p E.p b) (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), ∀ (U : AlgebraicGeometry.Scheme.{u}) (H : ArithmeticThetaLocalWeierstrassR0203.Family U) (c : Quiver.Hom U T) (g : Quiver.Hom H.curve F.curve) (hd : CategoryTheory.IsPullback g H.p F.p c) (hw : CategoryTheory.CategoryStruct.comp H.zero g = CategoryTheory.CategoryStruct.comp c F.zero) (he : CategoryTheory.IsPullback (CategoryTheory.CategoryStruct.comp g f) H.p E.p (CategoryTheory.CategoryStruct.comp c b)) (hv : CategoryTheory.CategoryStruct.comp H.zero (CategoryTheory.CategoryStruct.comp g f) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp c b) E.zero), ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E H (CategoryTheory.CategoryStruct.comp c b) (CategoryTheory.CategoryStruct.comp g f) he hv m = CategoryTheory.Iso.trans ((AlgebraicGeometry.Scheme.Modules.pullbackComp g f).app (ArithmeticThetaSchemeThetaMarkingR0259.thetaLine E m)).symm (CategoryTheory.Iso.trans ((AlgebraicGeometry.Scheme.Modules.pullback g).mapIso (ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E F b f hc hz m)) (ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison F H c g hd hw m)))) ∧ ArithmeticThetaSchemeThetaNaturalityR0262.GeometricNaturality E F b f hc hz m M N := by
  intro k _ _ S σ E T F b f hc hz m hm he hmul M N hx hy
  refine ⟨scheme_theta_comparison_coherence k S σ E m, ?_⟩
  obtain ⟨ι, α, β, c, A, B, hi, ha, hsa, hb, hsb, hcomm, hprim,
    hA, hB, hrel, hrank, hline, horbit, hrest⟩ :=
    scheme_geometric_schrodinger k S σ E m hm he M
  obtain ⟨ι', α', β', c', A', B', hi', ha', hsa', hb', hsb', hcomm', hprim',
    hA', hB', hrel', hrank', hline', horbit', hrest'⟩ :=
    scheme_geometric_schrodinger k T (b ≫ σ) F m hm he N
  have hn := scheme_normalization_transport k S σ E T F b f hc hz m hmul
  have hι := hn.1 ι hi ι' hi'
  have hα := (hn.2 M.x N.x hx ι ι' hi hi' α α').2 ha ha'
  have hβ := (hn.2 M.y N.y hy ι ι' hi hi' β β').2 hb hb'
  obtain ⟨hcommF, hprimF⟩ := scheme_commutator_naturality k S σ E T F b f hc hz m
    hmul M N hx hy α β α' β' c hα hβ hcomm
  have hpF := hprimF hprim
  have hrF := scheme_theta_action_relations k T (b ≫ σ) F m hm he N ι' α' β'
    hi' ha' hb' A' B' (baseUnit b c) hcommF hA' hB'
  have hoF := scheme_schrodinger_orbit k T (b ≫ σ) (V F m) m hm A' B'
    (baseUnit b c) hrF hpF
  have hpush := scheme_pushforward_intertwining k S σ E T F b f hc hz m hm
  have hAA := hpush.2 (translation E M.x) (translation F N.x) α α' A A' hα hA hA'
  have hBB := hpush.2 (translation E M.y) (translation F N.y) β β' B B' hβ hB hB'
  have hcomponents := scheme_invariant_component_naturality k S σ E T F b f hc hz m hm
    A B A' B' hrel.1 hAA hBB
  refine ⟨ι, ι', α, β, α', β', c, A, B, A', B', hi, hi', ha, hb, ha', hb',
    hsa, hsb, hsa', hsb', hι, hα, hβ, hprim, hpF, hcomm, hcommF,
    hA, hB, hA', hB', hrel, hrF, hpush.1, hAA, hBB, hline, hline',
    horbit, hoF, hcomponents, ?_⟩
  intro a d hT hne hsaTest hsbTest
  exact scheme_global_sign_alignment k S σ E T F b f hc hz m hm he hmul M N hx hy
    ι ι' hi hi' α β a d hsa hsb hsaTest hsbTest hT hne

#print axioms scheme_geometric_theta_naturality
end ArithmeticThetaSchemeThetaNaturalityR0262
