module

public import GeneralEllipticKatoDefinitionsR0168
public import ActualMultiplicationFieldNormR0150

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
open CategoryTheory AlgebraicGeometry NeronModelInfra
open WeierstrassProjModel
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaGeometricNormR0150.ActualMultiplicationFieldNorm

namespace GeneralMultiplicationDegree

lemma kernel_rank (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G) (n : ℕ) (hn : 0 < n)
    [IsFinite (G.schemeNsmul n)] [Etale (G.schemeNsmul n)] :
    ∀ z, (G.schemeKerStr n).finrank z = n^2 := by
  classical
  have ho : (G.one (𝟙 _)).val = (kwZeroSect F W).val := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  obtain ⟨ev, hev, _, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G ho
  let K := AlgebraicClosure F
  letI : CharZero K := Algebra.charZero_of_charZero F K
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F K))
  have heone : ev K (G.one t) = 0 := by
    have H := hev.1 K (G.one t) (G.one t)
    change ev K (G.mul t (G.one t) (G.one t)) = _ at H
    rw [G.one_mul] at H
    exact (add_left_cancel (a := ev K (G.one t)) ((add_zero _).trans H)).symm
  have hens (P : SchemeHomOver t (structureMap F W)) (m : ℕ) :
      ev K (G.nsmul t m P) = m • ev K P := by
    induction m with
    | zero => simpa only [G.nsmul_zero, zero_smul] using heone
    | succ m ih =>
      rw [G.nsmul_succ]
      have H := hev.1 K (G.nsmul t m P) P
      change ev K (G.mul t (G.nsmul t m P) P) =
        ev K (G.nsmul t m P) + ev K P at H
      rw [H, ih, succ_nsmul]
  let e : SchemeHomOver t (G.schemeKerStr n) ≃
      Submodule.torsionBy ℤ (W.toProjective.baseChange K).toAffine.Point (n : ℤ) :=
    (kernelPointsEquiv G t n).trans (Equiv.subtypeEquiv (ev K) (by
      intro z
      rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
      constructor
      · intro hz
        exact (hens z n).symm.trans ((congrArg (fun P => ev K P) hz).trans heone)
      · intro hz
        apply (ev K).injective
        exact (hens z n).trans (hz.trans heone.symm)))
  intro z
  have hz : z = t (IsLocalRing.closedPoint K) := Subsingleton.elim _ _
  apply (congrArg (G.schemeKerStr n).finrank hz).trans
  apply (finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    (G.schemeKerStr n) K (algebraMap F K)).trans
  exact (Nat.card_congr e).trans
    (WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (by norm_num))

end GeneralMultiplicationDegree

/-- Multiplication on an arbitrary characteristic-zero elliptic curve, with
its actual induced field action and scalar norm. -/
theorem general_multiplication_degree :
∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (G : ArithmeticThetaGeneralEllipticKatoR0168.Law F W) (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)], ∀ (n : ℕ), 0 < n → AlgebraicGeometry.IsFinite (G.schemeNsmul n) ∧ AlgebraicGeometry.Etale (G.schemeNsmul n) ∧ AlgebraicGeometry.Surjective (G.schemeNsmul n) ∧ (∀ x, (G.schemeNsmul n).finrank x = n^2) ∧ ∃ φ : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField →+* (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField, ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul n) φ ∧ ArithmeticThetaGeneralEllipticKatoR0168.HasFieldDegree φ (n^2) ∧ ∀ a : F, ArithmeticThetaGeometricNormR0150.fieldNorm φ (ArithmeticThetaGeometricNormR0150.baseScalar F (ArithmeticThetaGeneralEllipticKatoR0168.structureMap F W) a) = ArithmeticThetaGeometricNormR0150.baseScalar F (ArithmeticThetaGeneralEllipticKatoR0168.structureMap F W) (a^(n^2)) := by
  intro F _ _ W _ G hG _ _ n hn
  letI : SmoothOfRelativeDimension 1 (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : Etale (G.schemeNsmul n) := etale_nsmul G hG.2 n hn
  letI : IsProper (G.schemeNsmul n) :=
    MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated)
      (G.schemeNsmul n) (structureMap F W) inferInstance
      (by rw [G.schemeNsmul_over]; infer_instance)
  letI : LocallyQuasiFinite (G.schemeNsmul n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  letI : IsFinite (G.schemeNsmul n) := .of_isProper_of_locallyQuasiFinite _
  have hrank : ∀ x, (G.schemeNsmul n).finrank x = n^2 :=
    rank_from_identity G n (n^2) (GeneralMultiplicationDegree.kernel_rank F W G hG n hn)
  letI : Surjective (G.schemeNsmul n) :=
    (G.schemeNsmul n).one_le_finrank_iff_surjective.mp (by
      intro x
      rw [hrank x]
      exact Nat.one_le_pow 2 n hn)
  obtain ⟨φ, hφ⟩ := exists_fieldMap (G.schemeNsmul n)
  obtain ⟨hfin, hdeg, _⟩ := finite_etale_local_norm _ _ (G.schemeNsmul n) φ hφ
  have hd : fieldDegree φ = n^2 :=
    (hdeg (genericPoint (Curve F W))).symm.trans (hrank _)
  refine ⟨inferInstance, inferInstance, inferInstance, hrank, φ, hφ, ?_, ?_⟩
  · exact ⟨hfin, hd⟩
  · intro a
    rw [fieldNorm_baseScalar F (structureMap F W) (G.schemeNsmul n)
      (G.schemeNsmul_over n) φ hφ hfin a, hd]

#print axioms general_multiplication_degree
end ArithmeticThetaGeneralEllipticKatoR0168
