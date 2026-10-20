module

public import CartesianFullMarkingR0204
public import ArbitraryClassifyingUniquenessR0202

@[expose] public section

/-! Uniqueness of the two classifying morphisms on arbitrary schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra

namespace SchemeClassifyingUniqueness
variable {k : Type u} [Field k] {S : Scheme.{u}} {σ : S ⟶ Base k}
  {E : Family S} (P : LocalPresentation k S σ E)

/-- Lift a section through the actual local Cartesian comparison. -/
def lift (x : SchemeHomOver (𝟙 S) E.p) :
    SchemeHomOver (𝟙 (Base P.ring))
      (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation) :=
  ⟨P.cartesian.lift (P.base ≫ x.val) (𝟙 _) (by rw [Category.assoc, x.property]; simp),
    P.cartesian.lift_snd _ _ _⟩

lemma lift_comp (x : SchemeHomOver (𝟙 S) E.p) :
    (lift P x).val ≫ P.comparison = P.base ≫ x.val := P.cartesian.lift_fst _ _ _

lemma mul_comp
    (x y : SchemeHomOver (𝟙 (Base P.ring))
      (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation))
    (x' y' : SchemeHomOver (𝟙 S) E.p)
    (hx : x.val ≫ P.comparison = P.base ≫ x'.val)
    (hy : y.val ≫ P.comparison = P.base ≫ y'.val) :
    (P.law.mul (𝟙 _) x y).val ≫ P.comparison =
      P.base ≫ (E.law.mul (𝟙 S) x' y').val := by
  have h := P.mul_eq _ (𝟙 _) x y
    (CartesianFullMarking.restrict E P.base x')
    (CartesianFullMarking.restrict E P.base y') hx.symm hy.symm
  have hn := congrArg Subtype.val
    (E.law.mul_natural (𝟙 S) ((𝟙 _) ≫ P.base) P.base (by simp) x' y')
  exact h.symm.trans hn.symm

lemma nsmul_comp
    (x : SchemeHomOver (𝟙 (Base P.ring))
      (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation))
    (x' : SchemeHomOver (𝟙 S) E.p)
    (hx : x.val ≫ P.comparison = P.base ≫ x'.val) (n : ℕ) :
    (P.law.nsmul (𝟙 _) n x).val ≫ P.comparison =
      P.base ≫ (multiple E (𝟙 S) n x').val := by
  induction n with
  | zero =>
    change (P.law.one (𝟙 _)).val ≫ P.comparison = P.base ≫ E.zero
    rw [P.originLaw.1, Category.id_comp, P.zero_eq]
  | succ n ih => exact mul_comp P _ _ _ _ ih hx

lemma lift_killed (L : ℕ) (x : SchemeHomOver (𝟙 S) E.p)
    (hx : multiple E (𝟙 S) L x = E.law.one (𝟙 S)) :
    P.law.nsmul (𝟙 _) L (lift P x) = P.law.one (𝟙 _) := by
  apply Subtype.ext
  apply P.cartesian.hom_ext
  · rw [nsmul_comp P _ x (lift_comp P x), hx, P.originLaw.1,
      Category.id_comp, P.zero_eq]
    rfl
  · exact (P.law.nsmul (𝟙 _) L (lift P x)).property.trans
      (P.law.one (𝟙 _)).property.symm

/-- The original marking in the accepted affine interface. -/
def level {L : ℕ} (M : FullLevel E L) :
    ArithmeticThetaFullLevelCoverR0175.FullLevel P.ring P.equation P.law L (𝟙 _) where
  x := lift P M.x
  y := lift P M.y
  killed_x := lift_killed P L M.x M.killed_x
  killed_y := lift_killed P L M.y M.killed_y
  avoids := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ ⟨t, ht⟩
    have hc := mul_comp P _ _ _ _
      (nsmul_comp P _ M.x (lift_comp P M.x) i.val)
      (nsmul_comp P _ M.y (lift_comp P M.y) j.val)
    apply Set.disjoint_left.mp (M.avoids i j hij) (Set.mem_range_self (P.base z))
    refine ⟨P.base t, ?_⟩
    have H := congrArg (fun a => P.comparison a) ht
    change (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation ≫ P.comparison) t = _ at H
    rw [P.zero_eq] at H
    exact H.trans (congrArg (fun a : Base P.ring ⟶ E.curve => a z) hc)

variable [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
  (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
  (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
  (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
  (M : FullLevel E L)

lemma restrict_classifies
    (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve)
    (h : Classifies k L A B C Q σ E M b f) :
    ArithmeticThetaCompatibleLevelR0178.Classifies k L A B C Q
      P.ring P.equation P.law (level P M) (P.base ≫ b) (P.comparison ≫ f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, h.1, P.base_eq]
  · simpa only [Category.assoc] using P.cartesian.paste_horiz h.2.1
  · rw [← Category.assoc, P.zero_eq, Category.assoc, h.2.2.1]
    simp only [Category.assoc]
  · change (lift P M.x).val ≫ (P.comparison ≫ f) = _
    rw [← Category.assoc, lift_comp, Category.assoc, h.2.2.2.1]
    simp only [Category.assoc]
  · change (lift P M.y).val ≫ (P.comparison ≫ f) = _
    rw [← Category.assoc, lift_comp, Category.assoc, h.2.2.2.2.1]
    simp only [Category.assoc]

lemma local_unique (hL : 3 ≤ L) (heven : Even L)
    (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B)
    (b₁ b₂ : S ⟶ Base Q.quotient.ring)
    (f₁ f₂ : E.curve ⟶ A.descent.family.curve)
    (h₁ : Classifies k L A B C Q σ E M b₁ f₁)
    (h₂ : Classifies k L A B C Q σ E M b₂ f₂) :
    P.base ≫ b₁ = P.base ≫ b₂ ∧ P.comparison ≫ f₁ = P.comparison ≫ f₂ := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  letI : P.equation.IsElliptic := P.elliptic
  exact ArithmeticThetaArbitraryAffineR0202.arbitrary_classifying_uniqueness
    k L hL heven A B hB C Q P.ring P.equation P.law P.originLaw
    (level P M) (P.base ≫ b₁) (P.base ≫ b₂) (P.comparison ≫ f₁) (P.comparison ≫ f₂)
    (restrict_classifies P L A B C Q M b₁ f₁ h₁)
    (restrict_classifies P L A B C Q M b₂ f₂ h₂)

end SchemeClassifyingUniqueness

/-- Open-chart affine rigidity detects both original morphisms, including nilpotents. -/
theorem scheme_classifying_uniqueness :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A), ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B → ∀ (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E L) (b₁ b₂ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring)) (f₁ f₂ : Quiver.Hom E.curve A.descent.family.curve), ArithmeticThetaSchemeLevelR0204.Classifies k L A B C Q σ E M b₁ f₁ → ArithmeticThetaSchemeLevelR0204.Classifies k L A B C Q σ E M b₂ f₂ → b₁ = b₂ ∧ f₁ = f₂ := by
  intro k _ _ L hL heven A B hB C Q S σ E M b₁ b₂ f₁ f₂ h₁ h₂
  classical
  choose P hP using scheme_local_weierstrass k S σ E
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S
    (fun s => Base (P s).ring) (fun s => (P s).base)
    (fun s => ⟨s, hP s⟩) (fun s => (P s).openImmersion)
  have hu (s : S) := SchemeClassifyingUniqueness.local_unique (P s) L A B C Q M
    hL heven hB b₁ b₂ f₁ f₂ h₁ h₂
  refine ⟨𝒰.hom_ext b₁ b₂ (fun s => (hu s).1), ?_⟩
  apply (𝒰.pullback₁ E.p).hom_ext
  intro s
  change pullback.fst E.p (P s).base ≫ f₁ = pullback.fst E.p (P s).base ≫ f₂
  apply (cancel_epi (P s).cartesian.isoPullback.hom).mp
  simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst] using (hu s).2

#print axioms scheme_classifying_uniqueness
end ArithmeticThetaSchemeLevelR0204
