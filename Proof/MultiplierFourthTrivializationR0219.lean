module

public import PhaseFreeMultiplierR0219

@[expose] public section

/-! The fourth powers of the actual level frames descend to a normalized
trivialization. Helpers are confined to this module's namespace. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace ArithmeticThetaPhaseFreeKeyR0219.FourthProof
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaMultiplierKeyR0217
open ArithmeticThetaPullback ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open InverseCharacterMultiplier InverseCharacterMultiplier.Transport Scheme.Modules AlphaTensorCoherence
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- A pure power in the pullback of the original tensor power. -/
def power {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :=
  (pullback_tensorPower_iso X Y f M n).inv.app ⊤
    (tensorPowerSection X ((Scheme.Modules.pullback f).obj M) n ⊤ s)

lemma power_frame {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) (hs : IsFrame _ ⊤ s) :
    IsFrame ((Scheme.Modules.pullback f).obj (tensorPower Y M n)) ⊤ (power f M n s) :=
  frame_iso (pullback_tensorPower_iso X Y f M n).symm _
    (HodgeBaseChange.tensorPower_frame _ s hs n)

lemma power_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) (a : Γ(X, ⊤)) :
    power f M n (a • s) = a ^ n • power f M n s := by
  unfold power
  rw [ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.tensor_smul,
    Hom.app_smul]

lemma power_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    power f M 0 s = pullbackGlobalSection f (𝟙_ Y.Modules) (1 : Γ(Y, ⊤)) := by
  apply (ConcreteCategory.bijective_of_isIso ((pullback_unit_iso X Y f).hom.app ⊤)).1
  change (pullback_unit_iso X Y f).hom.app ⊤
    ((pullback_unit_iso X Y f).inv.app ⊤ (1 : Γ(X, ⊤))) = _
  exact (MultiplierBaseChange.iso_hom_inv_section (pullback_unit_iso X Y f)
    (1 : Γ(X, ⊤))).trans (pullback_unit_section X Y f).symm

lemma power_succ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    power f M (n+1) s = (pullback_sheafTensor_iso X Y f (tensorPower Y M n) M).inv.app ⊤
      (tensorSection X _ _ ⊤ (power f M n s) s) := by
  change (pullback_sheafTensor_iso X Y f (tensorPower Y M n) M).inv.app ⊤
    ((sheafTensorCongr X (pullback_tensorPower_iso X Y f M n) (Iso.refl _)).inv.app ⊤
      (tensorSection X _ _ ⊤ (tensorPowerSection X _ n ⊤ s) s)) = _
  congr 1
  exact sheafTensorCongr_section X (pullback_tensorPower_iso X Y f M n).symm
    (Iso.refl _) ⊤ _ s

lemma tensor_comp_sections {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) (s : Γ((Scheme.Modules.pullback g).obj M, ⊤))
    (t : Γ((Scheme.Modules.pullback g).obj N, ⊤)) :
    ((pullbackComp f g).app (sheafTensor Z M N)).hom.app ⊤
      (pullbackGlobalSection f _ ((pullback_sheafTensor_iso Y Z g M N).inv.app ⊤
        (tensorSection Y _ _ ⊤ s t))) =
    (pullback_sheafTensor_iso X Z (f ≫ g) M N).inv.app ⊤
      (tensorSection X _ _ ⊤
        (((pullbackComp f g).app M).hom.app ⊤ (pullbackGlobalSection f _ s))
        (((pullbackComp f g).app N).hom.app ⊤ (pullbackGlobalSection f _ t))) := by
  apply (ConcreteCategory.bijective_of_isIso ((pullback_sheafTensor_iso X Z (f ≫ g) M N).hom.app ⊤)).1
  have h := congrArg (fun v => v.app ⊤
    (pullbackGlobalSection f _ ((pullback_sheafTensor_iso Y Z g M N).inv.app ⊤
      (tensorSection Y _ _ ⊤ s t)))) (tensor_comp X Y Z f g M N)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at h
  have hn := MultiplierBaseChange.global_app f (pullback_sheafTensor_iso Y Z g M N).hom
    ((pullback_sheafTensor_iso Y Z g M N).inv.app ⊤ (tensorSection Y _ _ ⊤ s t))
  rw [MultiplierBaseChange.iso_hom_inv_section] at hn
  have hp := pullback_sheafTensor_section X Y f
    ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) s t
  have hc := sheafTensorCongr_section X ((pullbackComp f g).app M)
    ((pullbackComp f g).app N) ⊤ (pullbackGlobalSection f _ s) (pullbackGlobalSection f _ t)
  have hz := MultiplierBaseChange.iso_hom_inv_section
    (pullback_sheafTensor_iso X Z (f ≫ g) M N)
    (tensorSection X _ _ ⊤
      (((pullbackComp f g).app M).hom.app ⊤ (pullbackGlobalSection f _ s))
      (((pullbackComp f g).app N).hom.app ⊤ (pullbackGlobalSection f _ t)))
  exact h.trans ((congrArg (fun v =>
    (sheafTensorCongr X ((pullbackComp f g).app M) ((pullbackComp f g).app N)).hom.app ⊤
      ((pullback_sheafTensor_iso X Y f ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N)).hom.app ⊤ v)) hn).trans
    ((congrArg (fun v => (sheafTensorCongr X ((pullbackComp f g).app M)
      ((pullbackComp f g).app N)).hom.app ⊤ v) hp).trans (hc.trans hz.symm)))

lemma power_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (n : ℕ) (s : Γ((Scheme.Modules.pullback g).obj M, ⊤)) :
    ((pullbackComp f g).app (tensorPower Z M n)).hom.app ⊤
      (pullbackGlobalSection f _ (power g M n s)) =
    power (f ≫ g) M n (((pullbackComp f g).app M).hom.app ⊤
      (pullbackGlobalSection f _ s)) := by
  induction n with
  | zero =>
    rw [power_zero, power_zero]
    exact comp_global f g (𝟙_ Z.Modules) (1 : Γ(Z, ⊤))
  | succ n ih =>
    rw [power_succ, power_succ]
    erw [tensor_comp_sections]
    rw [ih]

variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
  (k : Type u) [Field k] [CharZero k] (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
  {L : S.Modules} (m : Frames E P L) (hm : IsMultiplier E P L m)

def frames : Frames E P (tensorPower S L 4) := fun A => power A.map L 4 (m A)

def units : Frames E P (𝟙_ S.Modules) := fun A =>
  pullbackGlobalSection A.map (𝟙_ S.Modules) (1 : Γ(S, ⊤))

include hm in
lemma frames_frame (A : MarkedTest E P) : IsFrame _ ⊤ (frames E P m A) :=
  power_frame A.map L 4 (m A) (hm.2.1 A)

lemma units_frame (A : MarkedTest E P) : IsFrame _ ⊤ (units E P A) :=
  HodgeBaseChange.pullback_frame A.map _ _ (unit_frame S)

include hm in
lemma frames_natural (A B : MarkedTest E P) (H : TestMap E P A B) :
    testPull E P (tensorPower S L 4) H (frames E P m B) = frames E P m A := by
  unfold frames
  rw [← hm.2.2.1 A B H]
  have aux {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (p : X ⟶ S)
      (h : f ≫ g = p) (s : Γ((Scheme.Modules.pullback g).obj L, ⊤)) :
      (((pullbackComp f g).app (tensorPower S L 4)) ≪≫
        (pullbackCongr h).app (tensorPower S L 4)).hom.app ⊤
          (pullbackGlobalSection f _ (power g L 4 s)) =
        power p L 4 ((((pullbackComp f g).app L) ≪≫ (pullbackCongr h).app L).hom.app ⊤
          (pullbackGlobalSection f _ s)) := by
    subst p
    simpa only [pullbackCongr, eqToIso_refl, Iso.refl_hom, Iso.trans_hom,
      Iso.app_hom, NatTrans.id_app, Category.comp_id] using power_comp f g L 4 s
  exact aux H.map B.map A.map H.commutes (m B)

lemma units_natural (A B : MarkedTest E P) (H : TestMap E P A B) :
    testPull E P (𝟙_ S.Modules) H (units E P B) = units E P A := by
  unfold testPull units
  simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [comp_global, congr_global]

#print axioms power_comp
#print axioms frames_natural


include hm in
lemma frames_character (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)) (hz : z ^ 4 = 1)
    (hp : MillerPhase A.family A.marking z)
    (g : ArithmeticThetaFourTorsion.Mat4) (hg : ArithmeticThetaFourTorsion.PreservesEven g)
    (hchange : Changes A.family A.marking N g) :
    frames E P m (remark E P A N hN) = frames E P m A := by
  unfold frames
  rw [hm.2.2.2.1 A N hN z hp g hg hchange]
  change power A.map L 4 (z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val) • m A) = _
  rw [power_smul]
  have hpow : (z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val)) ^ 4 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  rw [hpow, one_smul]

include hm in
lemma frames_reversal (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val)
    (hchange : Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal) :
    frames E P m (remark E P A N hN) = frames E P m A := by
  unfold frames
  rw [hm.2.2.2.2 A N hN hchange]
  rfl

def testIso (A : MarkedTest E P) :
    (Scheme.Modules.pullback A.map).obj (tensorPower S L 4) ≅
      (Scheme.Modules.pullback A.map).obj (𝟙_ S.Modules) :=
  (existsUnique_frame_iso _ _ (frames E P m A) (units E P A)
    (frames_frame E P m hm A) (units_frame E P A)).choose

lemma testIso_spec (A : MarkedTest E P) :
    (testIso E P m hm A).hom.app ⊤ (frames E P m A) = units E P A :=
  (existsUnique_frame_iso _ _ (frames E P m A) (units E P A)
    (frames_frame E P m hm A) (units_frame E P A)).choose_spec.1

lemma testIso_character (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)) (hz : z ^ 4 = 1)
    (hp : MillerPhase A.family A.marking z)
    (g : ArithmeticThetaFourTorsion.Mat4) (hg : ArithmeticThetaFourTorsion.PreservesEven g)
    (hchange : Changes A.family A.marking N g) :
    testIso E P m hm (remark E P A N hN) = testIso E P m hm A := by
  apply Iso.ext
  apply hom_ext_of_frame (frames E P m (remark E P A N hN)) (frames_frame E P m hm _)
  rw [testIso_spec, frames_character E P m hm A N hN z hz hp g hg hchange]
  exact (testIso_spec E P m hm A).symm

lemma testIso_reversal (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val)
    (hchange : Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal) :
    testIso E P m hm (remark E P A N hN) = testIso E P m hm A := by
  apply Iso.ext
  apply hom_ext_of_frame (frames E P m (remark E P A N hN)) (frames_frame E P m hm _)
  rw [testIso_spec, frames_reversal E P m hm A N hN hchange]
  exact (testIso_spec E P m hm A).symm

lemma testIso_natural (A B : MarkedTest E P) (H : TestMap E P A B) :
    (Scheme.Modules.pullback H.map).map (testIso E P m hm B).hom ≫
      (((pullbackComp H.map B.map).app (𝟙_ S.Modules)) ≪≫
        (pullbackCongr H.commutes).app (𝟙_ S.Modules)).hom =
    (((pullbackComp H.map B.map).app (tensorPower S L 4)) ≪≫
      (pullbackCongr H.commutes).app (tensorPower S L 4)).hom ≫
      (testIso E P m hm A).hom := by
  apply hom_ext_of_frame (pullbackGlobalSection H.map _ (frames E P m B))
    (HodgeBaseChange.pullback_frame H.map _ _ (frames_frame E P m hm B))
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [MultiplierBaseChange.global_app, testIso_spec]
  change testPull E P (𝟙_ S.Modules) H (units E P B) =
    (testIso E P m hm A).hom.app ⊤ (testPull E P (tensorPower S L 4) H (frames E P m B))
  rw [frames_natural E P m hm, units_natural, testIso_spec]

#print axioms testIso_natural


open ArithmeticThetaUniversalEvaluationR0213 ArithmeticThetaPhaseSwitchR0218
open MultiplierProof (restrictTest restrictionMap restrictedFamily restrictedMarking
  restrictedMarked restrictedChanged phases_locally_signed coverTest)

lemma testIso_restrict_eq (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    {T : Scheme.{u}} (b : T ⟶ A.base)
    (he : testIso E P m hm (restrictTest E P A b) =
      testIso E P m hm (restrictTest E P (remark E P A N hN) b)) :
    (Scheme.Modules.pullback b).map (testIso E P m hm A).hom =
      (Scheme.Modules.pullback b).map (testIso E P m hm (remark E P A N hN)).hom := by
  have h1 := testIso_natural E P m hm _ A (restrictionMap E P A b)
  have h2 := testIso_natural E P m hm _ (remark E P A N hN)
    (restrictionMap E P (remark E P A N hN) b)
  apply (cancel_mono (((pullbackComp b A.map).app (𝟙_ S.Modules)) ≪≫ (pullbackCongr rfl).app (𝟙_ S.Modules)).hom).mp
  change (Scheme.Modules.pullback b).map (testIso E P m hm A).hom ≫
    (((pullbackComp b A.map).app (𝟙_ S.Modules)) ≪≫ (pullbackCongr rfl).app (𝟙_ S.Modules)).hom =
    (((pullbackComp b A.map).app (tensorPower S L 4)) ≪≫ (pullbackCongr rfl).app (tensorPower S L 4)).hom ≫
      (testIso E P m hm (restrictTest E P A b)).hom at h1
  change (Scheme.Modules.pullback b).map (testIso E P m hm (remark E P A N hN)).hom ≫
    (((pullbackComp b A.map).app (𝟙_ S.Modules)) ≪≫ (pullbackCongr rfl).app (𝟙_ S.Modules)).hom =
    (((pullbackComp b A.map).app (tensorPower S L 4)) ≪≫ (pullbackCongr rfl).app (tensorPower S L 4)).hom ≫
      (testIso E P m hm (restrictTest E P (remark E P A N hN) b)).hom at h2
  rw [h1, h2, he]

include k σ in
lemma testIso_samePhase (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (hzN : MillerPhase A.family N z) :
    testIso E P m hm A = testIso E P m hm (remark E P A N hN) := by
  have hp : evenPoint A.family A.marking = evenPoint A.family N := by
    apply A.cartesian.1.hom_ext
    · exact A.characteristic.trans hN.symm
    · rw [SchemeThetaEvaluation.evenPoint_over, SchemeThetaEvaluation.evenPoint_over]
  apply Iso.ext
  apply hom_ext_local_pullback (frames E P m A) (frames_frame E P m hm A)
  intro s
  obtain ⟨g, U, hs, hx, hy⟩ := LocallyConstantMarkingComparison.localWitness_exists
    A.family A.marking k (A.map ≫ σ) N z hz hzN hp s
  refine ⟨U, hs, testIso_restrict_eq E P m hm A N hN U.ι ?_⟩
  change testIso E P m hm (restrictTest E P A U.ι) =
    testIso E P m hm (remark E P (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N)
      (restrictTest E P (remark E P A N hN) U.ι).characteristic)
  symm
  exact testIso_character E P m hm (restrictTest E P A U.ι)
    (restrictedMarking E P A U.ι N) _ (U.ι.appTop z)
    (by
      change (U.ι.appTop z) ^ 4 = (1 : Γ(U.toScheme, ⊤))
      rw [← map_pow, phase_four z
      (((scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).2 z hz).2.1), map_one])
    (SchemePhaseNaturality.pullback_phase A.family (restrictedFamily E P A U.ι)
      A.marking (restrictedMarking E P A U.ι A.marking) U.ι (pullback.fst A.family.p U.ι)
      (restrictedMarked E P A U.ι A.marking) z hz)
    g.val g.property (restrictedChanged E P A N U.ι g.val hx hy)

include k σ in
lemma testIso_oppositePhase (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val)
    (z : Γ(A.base, ⊤)) (hz : MillerPhase A.family A.marking z)
    (hzN : MillerPhase A.family N (-z)) :
    testIso E P m hm A = testIso E P m hm (remark E P A N hN) := by
  obtain ⟨R, hR, _⟩ := (scheme_pairing_reversal k A.base (A.map ≫ σ) A.family N).1
  have hr := (scheme_pairing_reversal k A.base (A.map ≫ σ) A.family N).2 R hR
  have hRchar : evenPoint A.family R ≫ A.comparison = A.map ≫ P.point.val := by
    rw [hr.2.1, hN]
  have hphase : MillerPhase A.family R z := by simpa only [neg_neg] using hr.2.2.1 (-z) hzN
  have h1 := testIso_samePhase E P k σ m hm A R hRchar z hz hphase
  have h2 := testIso_reversal E P m hm (remark E P A N hN) R hRchar hR
  exact h1.trans h2

include k σ in
/-- Comparisons are independent of the marking, including locally varying phase signs. -/
lemma testIso_marking_independent (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val) :
    testIso E P m hm A = testIso E P m hm (remark E P A N hN) := by
  obtain ⟨z, hz, _⟩ := (scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).1
  obtain ⟨w, hw, _⟩ := (scheme_miller_phase k A.base (A.map ≫ σ) A.family N).1
  have hz2 := ((scheme_miller_phase k A.base (A.map ≫ σ) A.family A.marking).2 z hz).2.1
  have hw2 := ((scheme_miller_phase k A.base (A.map ≫ σ) A.family N).2 w hw).2.1
  apply Iso.ext
  apply hom_ext_local_pullback (frames E P m A) (frames_frame E P m hm A)
  intro s
  obtain ⟨U, hs, hsign⟩ := phases_locally_signed k (A.map ≫ σ) z w hz2 hw2 s
  refine ⟨U, hs, testIso_restrict_eq E P m hm A N hN U.ι ?_⟩
  change testIso E P m hm (restrictTest E P A U.ι) =
    testIso E P m hm (remark E P (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N)
      (restrictTest E P (remark E P A N hN) U.ι).characteristic)
  have hza := SchemePhaseNaturality.pullback_phase A.family (restrictedFamily E P A U.ι)
    A.marking (restrictedMarking E P A U.ι A.marking) U.ι (pullback.fst A.family.p U.ι)
    (restrictedMarked E P A U.ι A.marking) z hz
  have hwa := SchemePhaseNaturality.pullback_phase A.family (restrictedFamily E P A U.ι)
    N (restrictedMarking E P A U.ι N) U.ι (pullback.fst A.family.p U.ι)
    (restrictedMarked E P A U.ι N) w hw
  rcases hsign with hpos | hneg
  · rw [← hpos] at hwa
    exact testIso_samePhase E P k σ m hm (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N) _ (U.ι.appTop z) hza hwa
  · have he : U.ι.appTop w = -(U.ι.appTop z) := by rw [hneg, neg_neg]
    rw [he] at hwa
    exact testIso_oppositePhase E P k σ m hm (restrictTest E P A U.ι)
      (restrictedMarking E P A U.ι N) _ (U.ι.appTop z) hza hwa


#print axioms testIso_marking_independent


open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2

lemma testIso_pullHom (A B : MarkedTest E P) (H : TestMap E P A B) :
    pullHom (F := Transport.FF) (M₁ := tensorPower S L 4) (M₂ := 𝟙_ S.Modules) (f₁ := B.map) (f₂ := B.map)
      (testIso E P m hm B).hom H.map A.map A.map H.commutes H.commutes =
      (testIso E P m hm A).hom := by
  rw [pullHom_eq₂]
  have h := congrArg (fun v =>
    (((pullbackComp H.map B.map).app (tensorPower S L 4)) ≪≫ (pullbackCongr H.commutes).app (tensorPower S L 4)).inv ≫ v)
    (testIso_natural E P m hm A B H)
  simp only [Iso.inv_hom_id_assoc] at h
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc] at h
  exact h

include k σ in
lemma testIso_pair_eq (D : Cover E) (hD : RepresentsUnphased E P D) :
    pullHom (F := Transport.FF) (M₁ := tensorPower S L 4) (M₂ := 𝟙_ S.Modules)
      (f₁ := D.projection) (f₂ := D.projection)
      (testIso E P m hm (coverTest E P D hD)).hom
      (first E D) (first E D ≫ D.projection) (first E D ≫ D.projection) rfl rfl =
    pullHom (F := Transport.FF) (M₁ := tensorPower S L 4) (M₂ := 𝟙_ S.Modules)
      (f₁ := D.projection) (f₂ := D.projection)
      (testIso E P m hm (coverTest E P D hD)).hom
      (second E D) (first E D ≫ D.projection) (first E D ≫ D.projection)
      pullback.condition.symm pullback.condition.symm := by
  let T := overlap E D
  let b := first E D ≫ D.projection
  obtain ⟨F, f, hpb, hz, hmul⟩ := scheme_family_base_change S T E b
  have hc : Cartesian E F b f := ⟨hpb, hz, hmul⟩
  obtain ⟨M, g, hg, hgf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ D F b f hc
    (first E D) rfl
  obtain ⟨N, j, hj, hjf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ D F b f hc
    (second E D) pullback.condition.symm
  have char (Q : FullLevel F 4) (a : T ⟶ D.space) (ha : a ≫ D.projection = b)
      (v : F.curve ⟶ D.family.curve) (hv : MarkedCartesian D.family F D.marking Q a v)
      (hvc : v ≫ D.comparison = f) : evenPoint F Q ≫ f = b ≫ P.point.val := by
    rw [← hvc, ← Category.assoc, SchemeThetaEvaluation.evenPoint_natural D.family D.marking F Q a v hv,
      Category.assoc, hD.1, ← Category.assoc, ha]
  have hM := char M (first E D) rfl g hg hgf
  have hN := char N (second E D) pullback.condition.symm j hj hjf
  let A : MarkedTest E P := ⟨T, F, M, b, f, hc, hM⟩
  let B : MarkedTest E P := remark E P A N hN
  let H₁ : TestMap E P A (coverTest E P D hD) := ⟨first E D, rfl, g, hg, hgf⟩
  let H₂ : TestMap E P B (coverTest E P D hD) :=
    ⟨second E D, pullback.condition.symm, j, hj, hjf⟩
  exact (testIso_pullHom E P m hm A _ H₁).trans
    ((congrArg Iso.hom (testIso_marking_independent E P k σ m hm A N hN)).trans
      (testIso_pullHom E P m hm B _ H₂).symm)


/-- Tensor powers of the unit with their actual recursive tensor presentation. -/
def unitPower (X : Scheme.{u}) : (n : ℕ) → tensorPower X (𝟙_ X.Modules) n ≅ 𝟙_ X.Modules
  | 0 => Iso.refl _
  | n+1 => sheafTensorCongr X (unitPower X n) (Iso.refl _) ≪≫ tensorLeftUnitIso X _

lemma power_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    Scheme.Modules.IsInvertible (tensorPower X M n) := by
  constructor
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
  exact ⟨U, hx, ⟨pullback_tensorPower_iso U.toScheme X U.ι M n ≪≫
    EvenKeyBaseChange.powerIso e n ≪≫ unitPower U.toScheme n⟩⟩

include hm in
lemma preserves_of_cover (D : Cover E) (hD : RepresentsUnphased E P D)
    (v : tensorPower S L 4 ≅ 𝟙_ S.Modules)
    (hv : ((Scheme.Modules.pullback D.projection).map v.hom).app ⊤
      (frames E P m (coverTest E P D hD)) = units E P (coverTest E P D hD)) :
    ∀ A : MarkedTest E P, ((Scheme.Modules.pullback A.map).map v.hom).app ⊤
      (frames E P m A) = units E P A := by
  intro A
  obtain ⟨q, ⟨f, hf, ht⟩, _⟩ := hD.2 A
  let H : TestMap E P A (coverTest E P D hD) := ⟨q.val, q.property, f, hf, ht⟩
  rw [← frames_natural E P m hm A _ H]
  have h := MultiplierPhaseSwitch.along_natural
    A.map D.projection q.val q.property v.hom (frames E P m (coverTest E P D hD))
  change ((Scheme.Modules.pullback A.map).map v.hom).app ⊤
    (testPull E P (tensorPower S L 4) H (frames E P m (coverTest E P D hD))) =
    testPull E P (𝟙_ S.Modules) H (((Scheme.Modules.pullback D.projection).map v.hom).app ⊤
      (frames E P m (coverTest E P D hD))) at h
  rw [h, hv]
  exact units_natural E P A _ H

include k σ hm in
lemma normalized_exists : ∃ t : tensorPower S L 4 ≅ 𝟙_ S.Modules,
    ∀ A : MarkedTest E P, ((Scheme.Modules.pullback A.map).map t.hom).app ⊤
      (frames E P m A) = units E P A := by
  obtain ⟨D, hD, hgeom⟩ := (unphased_marking_cover k S σ E P).1
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  let η := testIso E P m hm (coverTest E P D hD)
  have hη := compatible_of_pair_eq E D η (testIso_pair_eq E P k σ m hm D hD)
  obtain ⟨v, hv, _⟩ :=
    P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one.KcDescAlong.existsUnique_of_comm
      D.projection (first E D) (second E D) (IsPullback.of_hasPullback _ _)
      (power_invertible L hm.1 4) (Scheme.Modules.isInvertible_unit S) η hη
  refine ⟨v, preserves_of_cover E P m hm D hD v ?_⟩
  have h := congrArg (fun e => e.hom.app ⊤ (frames E P m (coverTest E P D hD))) hv
  exact h.trans (testIso_spec E P m hm (coverTest E P D hD))

lemma normalized_iff (t : tensorPower S L 4 ≅ 𝟙_ S.Modules) :
    FourthNormalized E P L m t ↔
    ∀ A : MarkedTest E P, ((Scheme.Modules.pullback A.map).map t.hom).app ⊤
      (frames E P m A) = units E P A := by
  constructor
  · intro ht A
    have h := congrArg (fun v => (Scheme.Modules.pullbackUnitIso A.map).inv.app ⊤ v) (ht A)
    change (Scheme.Modules.pullbackUnitIso A.map).inv.app ⊤
      ((Scheme.Modules.pullbackUnitIso A.map).hom.app ⊤
        (((Scheme.Modules.pullback A.map).map t.hom).app ⊤ (frames E P m A))) = _ at h
    rw [MultiplierBaseChange.iso_inv_hom_section, unit_inv_one] at h
    exact h
  · intro ht A
    change (Scheme.Modules.pullbackUnitIso A.map).hom.app ⊤
      (((Scheme.Modules.pullback A.map).map t.hom).app ⊤ (frames E P m A)) = (1 : Γ(A.base, ⊤))
    rw [ht A]
    exact (MultiplierBaseChange.iso_hom_inv_section (Scheme.Modules.pullbackUnitIso A.map)
      (1 : Γ(A.base, ⊤))).symm ▸ congrArg (fun v => (Scheme.Modules.pullbackUnitIso A.map).hom.app ⊤ v)
        (unit_inv_one A.map).symm

include k σ hm in
lemma normalized_unique (v w : tensorPower S L 4 ≅ 𝟙_ S.Modules)
    (hv : FourthNormalized E P L m v) (hw : FourthNormalized E P L m w) : v = w := by
  obtain ⟨D, hD, hgeom⟩ := (unphased_marking_cover k S σ E P).1
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  apply Iso.ext
  apply AlphaDescentFaithfulness.pullback_hom_injective D.projection
    (power_invertible L hm.1 4) (Scheme.Modules.isInvertible_unit S)
  apply hom_ext_of_frame (frames E P m (coverTest E P D hD)) (frames_frame E P m hm _)
  exact ((normalized_iff E P m v).mp hv _).trans ((normalized_iff E P m w).mp hw _).symm

#print axioms normalized_exists
#print axioms normalized_unique
end ArithmeticThetaPhaseFreeKeyR0219.FourthProof

namespace ArithmeticThetaPhaseFreeKeyR0219
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaTensorPower

/-- The fourth power of the phase-free multiplier has the unique trivialization
normalized to one in every prescribed actual level frame. -/
theorem multiplier_fourth_trivialization :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
      (E : Family S) (P : EvenPoint E), ∀ (L : S.Modules) (m : Frames E P L),
      IsMultiplier E P L m → ∃! t : tensorPower S L 4 ≅ SheafOfModules.unit S.ringCatSheaf,
        FourthNormalized E P L m t := by
  intro k _ _ S σ E P L m hm
  obtain ⟨t, ht⟩ := FourthProof.normalized_exists E P k σ m hm
  exact ⟨t, (FourthProof.normalized_iff E P m t).mpr ht,
    fun v hv => FourthProof.normalized_unique E P k σ m hm v t hv
      ((FourthProof.normalized_iff E P m t).mpr ht)⟩

#print axioms multiplier_fourth_trivialization
end ArithmeticThetaPhaseFreeKeyR0219
