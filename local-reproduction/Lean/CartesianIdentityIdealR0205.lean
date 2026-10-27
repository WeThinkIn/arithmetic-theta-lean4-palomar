import SchemeHodgeDefinitionsR0205

/-! The normalized identity ideal comparison over arbitrary test schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaSchemeHodgeR0205
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203

namespace CartesianIdentityIdeal

lemma zero_section {S : Scheme.{u}} (E : Family S) : E.zero ≫ E.p = 𝟙 S :=
  (E.law.one (𝟙 S)).property

lemma zero_cartesian {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) :
    IsPullback F.zero b f E.zero := by
  have houter : IsPullback (F.zero ≫ F.p) b b (E.zero ≫ E.p) := by
    rw [zero_section, zero_section]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact houter.of_right hz hc.flip

lemma ideal_comap {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) :
    E.zero.ker.comap f = F.zero.ker := by
  letI : IsProper E.p := E.proper
  letI : IsClosedImmersion (E.zero ≫ E.p) := by rw [zero_section]; infer_instance
  letI : IsClosedImmersion E.zero := IsClosedImmersion.of_comp E.zero E.p
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion E.zero f]
  rw [← Scheme.Hom.ker_comp_of_isIso (zero_cartesian E F b f hc hz).isoPullback.hom]
  rw [IsPullback.isoPullback_hom_fst]

lemma zero_ideal_invertible {S : Scheme.{u}} (E : Family S) : E.zero.ker.IsInvertible := by
  letI : IsProper E.p := E.proper
  letI : SmoothOfRelativeDimension 1 E.p := E.dimension
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id E.zero (zero_section E)

end CartesianIdentityIdeal

/-- Arbitrary Cartesian base change preserves the actual identity ideal, with
the unique isomorphism respecting its inclusion in the structure sheaf. -/
theorem cartesian_identity_ideal :
    ∀ (S T : Scheme.{u}) (E : Family S) (F : Family T)
      (b : T ⟶ S) (f : F.curve ⟶ E.curve),
      IsPullback f F.p E.p b → F.zero ≫ f = b ≫ E.zero →
      ∃! i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module,
        IdealCompatible E F f i := by
  intro S T E F b f hc hz
  let h := CartesianIdentityIdeal.ideal_comap E F b f hc hz
  let hE := CartesianIdentityIdeal.zero_ideal_invertible E
  let hF := CartesianIdentityIdeal.zero_ideal_invertible F
  let i := ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.idealPullbackIso
    f E.zero.ker F.zero.ker hE hF h
  have hi : IdealCompatible E F f i :=
    ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.idealPullbackIso_inclusion
      f E.zero.ker F.zero.ker hE hF h
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Iso.ext
  letI : Mono F.zero.ker.moduleι := inferInstanceAs (Mono (kernel.ι _))
  apply (cancel_mono F.zero.ker.moduleι).mp
  exact hj.trans hi.symm

end ArithmeticThetaSchemeHodgeR0205

#print axioms ArithmeticThetaSchemeHodgeR0205.cartesian_identity_ideal
