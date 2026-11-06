module
public import AlternationRecovery
public import LiftTransportRecovery
import all AlternationRecovery
import all LiftTransportRecovery
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768
noncomputable section
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaTateSchemeMarkingR0263 ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
namespace PalomarTateInversion1331
open PalomarAlternation1305 PalomarLift1168
def Normalization : Prop := ∀ {F : Type} [Field F]
    (E : ArithmeticThetaLocalWeierstrassR0203.Family (Spec (CommRingCat.of F)))
    (d : ℕ) (i : Lift E d (inverse E)) (v : Γ(thetaLine E d, ⊤))
    (hv : SectionAction.globalAct _ i v = v)
    (hne : Scheme.Modules.pullbackLocalSection E.zero v ≠ 0),
    NormalizedInversion E d i
variable (ht : Transport.{0}) (hg : GenericDualAction)
variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
 (V : TateLevel k (2*m)) {ζ : kˣ} (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)
include ht in
lemma matching_exists_unique :
    ∃! i : Lift (family k V) m (inverse (family k V)),
      Matches k V Q he _ Q.mapS i (Q.canonicalS he) := by
  let h := Q.inversion_commutes.symm
  obtain ⟨i, hi, hu⟩ := ht Q.cubic (inverse (family k V)) Q.mapS h
    (thetaLine (family k V) m) _ (modelComparison k V Q he)
    (LocalTheta.dualLift Q.mapS _ (Q.ideal_invertible he) (Q.canonicalS he).symm)
  exact ⟨i, ⟨h, hi⟩, fun j hj => hu j hj.choose_spec⟩
include hg in
lemma matching_action
    (i : Lift (family k V) m (inverse (family k V)))
    (hi : Matches k V Q he _ Q.mapS i (Q.canonicalS he))
    (v : Γ(thetaLine (family k V) m, ⊤)) :
    sectionEquiv k V Q he (SectionAction.globalAct _ i v) =
      ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m Q.mapS
        (Q.canonicalS he) (sectionEquiv k V Q he v) := by
  obtain ⟨h, hi⟩ := hi
  change LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ _ _ =
    ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m Q.mapS
      (Q.canonicalS he) (LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _ _ v)
  unfold LocalTheta.modelFunctional
  rw [← hg k Q.model Q.origin m (Q.ideal_invertible he)]
  rw [← hi, SectionAction.globalAct_changeLine, SectionAction.globalAct_baseChanged]
  rfl

include hg in
lemma matching_fixes_zero_basis
    (i : Lift (family k V) m (inverse (family k V)))
    (hi : Matches k V Q he _ Q.mapS i (Q.canonicalS he)) :
    SectionAction.globalAct _ i (basisSection k V Q he ⟨0, hm⟩) =
      basisSection k V Q he ⟨0, hm⟩ := by
  apply (sectionEquiv k V Q he).injective
  rw [matching_action hg k V Q he i hi]
  simp only [basisSection, Equiv.apply_symm_apply]
  rw [Q.canonicalS_reverses he]
  congr 1
  apply Fin.ext
  simp [ArithmeticThetaModelSymmetriesR0137.negIndex]

lemma zero_basis_identity_nonzero :
    Scheme.Modules.pullbackLocalSection (family k V).zero
      (basisSection k V Q he ⟨0, hm⟩) ≠ 0 := by
  letI := V.elliptic
  obtain ⟨_, ⟨frame⟩, hframe⟩ := ArithmeticThetaGenericEvaluationR0140.generic_projective_evaluation
    k m hm he Q.tower Q.model Q.isModel Q.origin Q.markedOrigin
  intro hz
  have ho : ArithmeticThetaGenericEvaluationR0140.genericPoint k Q.model Q.origin
      Q.markedOrigin.1 ≫ Q.cubic.hom = (family k V).zero := by
    rw [Q.cubic_origin]
    exact (ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero
      (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw).symm
  have hzero := LocalTheta.genericValue_modelFunctional_zero k Q.model Q.origin
    Q.markedOrigin.1 m Q.cubic (thetaLine (family k V) m) (modelComparison k V Q he)
    frame (basisSection k V Q he ⟨0, hm⟩) (by rw [ho]; exact hz)
  change ArithmeticThetaGenericEvaluationR0140.genericValue k Q.model Q.origin Q.markedOrigin.1 m frame
    (sectionEquiv k V Q he (basisSection k V Q he ⟨0, hm⟩)) = 0 at hzero
  simp only [basisSection, Equiv.apply_symm_apply] at hzero
  exact (hframe frame).1 hzero

theorem tate_inversion (ht : Transport.{0}) (hg : GenericDualAction) (hn : Normalization) : ∀ (k : Type) [inst : Field.{0} k] [inst_1 : @CharZero.{0} k (@AddGroupWithOne.toAddMonoidWithOne.{0} k (@Ring.toAddGroupWithOne.{0} k (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst))))] (m : Nat) (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) (he : @Even.{0} Nat instAddNat m) (V : @ArithmeticThetaTateCuspsR0181.TateLevel.{0} k inst (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) (ζ : @Units.{0} k (@Semiring.toMonoid.{0} k (@CommSemiring.toSemiring.{0} k (@Semifield.toCommSemiring.{0} k (@Field.toSemifield.{0} k inst))))) (hζ : @IsPrimitiveRoot.{0} k (@CommRing.toCommMonoid.{0} k (@Field.toCommRing.{0} k inst)) (@Units.val.{0} k (@Semiring.toMonoid.{0} k (@CommSemiring.toSemiring.{0} k (@Semifield.toCommSemiring.{0} k (@Field.toSemifield.{0} k inst)))) ζ) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) (Q : @ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.MarkedModel k inst inst_1 m hm V ζ), @ExistsUnique.{1} (@ArithmeticThetaSchemeThetaMarkingR0259.Lift.{0} (@ArithmeticThetaTateCuspsR0181.Puncture.{0} k inst) (@ArithmeticThetaTateSchemeMarkingR0263.family k inst m V) m (@ArithmeticThetaSchemeThetaMarkingR0259.inverse.{0} (@ArithmeticThetaTateCuspsR0181.Puncture.{0} k inst) (@ArithmeticThetaTateSchemeMarkingR0263.family k inst m V))) fun (i : @ArithmeticThetaSchemeThetaMarkingR0259.Lift.{0} (@ArithmeticThetaTateCuspsR0181.Puncture.{0} k inst) (@ArithmeticThetaTateSchemeMarkingR0263.family k inst m V) m (@ArithmeticThetaSchemeThetaMarkingR0259.inverse.{0} (@ArithmeticThetaTateCuspsR0181.Puncture.{0} k inst) (@ArithmeticThetaTateSchemeMarkingR0263.family k inst m V))) => @ArithmeticThetaTateSchemeMarkingR0263.inversionLiftFacts k inst inst_1 m hm V ζ Q he i := by
  intro k _ _ m hm he V ζ hζ Q
  obtain ⟨i, hi, hu⟩ := matching_exists_unique ht k V Q he
  refine ⟨i, ⟨hi, ?_⟩, fun j hj => hu j hj.1⟩
  exact hn (family k V) m i
    (basisSection k V Q he ⟨0, hm⟩)
    (matching_fixes_zero_basis hg k V Q he i hi)
    (zero_basis_identity_nonzero k V Q he)

end PalomarTateInversion1331
