module

public import GenericThetaBasisR0140
public import AlgebraicIdentityEvaluationR0140

@[expose] public section

/-! Projective evaluation of the actual generic theta sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140
namespace GenericProjectiveEvaluationR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
open NormalizedIdentityFrameR0140
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma point_square (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) :
    genericPoint k M s hs ≫ genericInclusion k M = genericBase k ≫ s :=
  pullback.lift_fst _ _ _

def baseFrame (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (d : ℕ) (e : IdentityFrame k M s d) :
    GenericFrame k M s hs d := by
  let α := pullFrame (genericBase k) e.inv ≫
    (squareIso (genericInclusion k M) (genericPoint k M s hs) s (genericBase k)
      (point_square k M s hs) (powerModule k M s d)).hom
  letI : IsIso (pullFrame (genericBase k) e.inv) := pullFrame_isIso _ _
  exact (asIso α).symm

lemma baseFrame_value (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (d : ℕ) (e : IdentityFrame k M s d)
    (φ : Dual k M s d) :
    genericValue k M s hs d (baseFrame k M s hs d e) (restrictDual k M s d φ) =
      algebraMap (PowerSeries k) (LaurentSeries k) (frameValue k M s d e φ) := by
  have hh : (baseFrame k M s hs d e).inv ≫
      pulledInclusion (genericPoint k M s hs) (restrictDual k M s d φ) =
      fromSection (SheafOfModules.unit (Spec (.of (LaurentSeries k))).ringCatSheaf)
        ((genericBase k).appTop ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv
          (frameValue k M s d e φ))) := by
    change (pullFrame (genericBase k) e.inv ≫ _) ≫ _ = _
    change (pullFrame (genericBase k) e.inv ≫ _) ≫
      pulledInclusion (genericPoint k M s hs) (pulledInclusion (genericInclusion k M) φ) = _
    rw [Category.assoc, squareIso_inclusion]
    exact pullFrame_evaluation _ _ _ _ (frameValue_morphism k M s d e φ)
  have hv := ConcreteCategory.congr_hom
    (congrArg (fun q => Scheme.Modules.Hom.app q ⊤) hh) (1 : Γ(Spec (.of (LaurentSeries k)), ⊤))
  apply_fun (Scheme.ΓSpecIso (.of (LaurentSeries k))).hom at hv
  simp only [fromSection_apply, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, one_smul] at hv
  dsimp only [genericBase] at hv
  erw [affine_pullback_inv] at hv
  simpa only [genericValue, map_one, pulledInclusion, CommRingCat.hom_ofHom] using hv

/-- Evaluation of a structure-module endomorphism as a scalar. -/
def endValue {A : Type u} [CommRing A]
    (f : (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules) ⟶
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules)) : A :=
  (Scheme.ΓSpecIso (.of A)).hom ((Scheme.Modules.Hom.app f) ⊤ (1 : Γ(Spec (.of A), ⊤)))

lemma endValue_comp {A : Type u} [CommRing A]
    (f g : (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules) ⟶
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules)) :
    endValue (f ≫ g) = endValue f * endValue g := by
  unfold endValue
  change (Scheme.ΓSpecIso (.of A)).hom ((Scheme.Modules.Hom.app g) ⊤ ((Scheme.Modules.Hom.app f) ⊤ (1 : Γ(Spec (.of A), ⊤)))) = _
  rw [unit_hom_apply]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]
  change (Scheme.ΓSpecIso (.of A)).hom (_ * _) = _
  exact (Scheme.ΓSpecIso (.of A)).hom.hom.map_mul _ _

lemma endValue_nonzero {A : Type u} [Field A]
    (e : (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules) ≅
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules)) :
    endValue e.hom ≠ 0 := by
  have h : endValue e.hom * endValue e.inv = 1 := by
    rw [← endValue_comp, e.hom_inv_id]
    change (Scheme.ΓSpecIso (.of A)).hom (1 : Γ(Spec (.of A), ⊤)) = 1
    exact map_one _
  exact left_ne_zero_of_mul_eq_one h

lemma changeFrame_value (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (d : ℕ) (e e₀ : GenericFrame k M s hs d)
    (φ : GenericDual k M s d) :
    genericValue k M s hs d e φ = endValue (e.inv ≫ e₀.hom) *
      genericValue k M s hs d e₀ φ := by
  simp only [genericValue, map_one]
  change endValue (e.inv ≫ pulledInclusion _ φ) =
    endValue (e.inv ≫ e₀.hom) * endValue (e₀.inv ≫ pulledInclusion _ φ)
  rw [← endValue_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

lemma unary_zero_nonzero (m : ℕ) (hm : 0 < m) :
    ArithmeticThetaSchrodingerR0119.unary k m (zeroIndex m hm) ≠ 0 := by
  have hc : Nat.card {a : ℤ // Int.ModEq (m : ℤ) a (0 : ℤ) ∧ a^2 = (0 : ℤ)} = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0, ⟨Int.ModEq.refl _, by simp⟩⟩, ?_⟩
    intro a
    apply Subtype.ext
    exact (sq_eq_zero_iff).mp a.property.2
  have hv : PowerSeries.coeff 0 (ArithmeticThetaSchrodingerR0119.unary k m
      (zeroIndex m hm)) = 1 := by
    simpa only [ArithmeticThetaSchrodingerR0119.unary, PowerSeries.coeff_mk,
      zeroIndex, Nat.cast_zero, hc, Nat.cast_one]
  intro h
  rw [h, map_zero] at hv
  exact zero_ne_one hv

lemma theta_value (m : ℕ) (hm : 0 < m) (he : Even m)
    {T : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k T) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (e : IdentityFrame k M s m)
    (he' : NormalizedFrame k (thetaChartBound m hm he) M hM s hs m e) (ν : Fin m) :
    frameValue k M s m e (thetaSection k m hm he M hM s hs ν) =
      PowerSeries.X^((2*m)^2) * (↑(commonUnit k m hm) : PowerSeries k) *
        ArithmeticThetaSchrodingerR0119.unary k m ν := by
  classical
  have hv := algebraic_identity_evaluation k m hm he T M hM s hs e he' 0
    (thetaVector k m ν) (thetaSection k m hm he M hM s hs ν)
    (Classical.choose_spec (algebraized_theta_sections k m hm he T M hM s hs
      (thetaVector k m ν))).1
  simpa [thetaVector] using hv

end GenericProjectiveEvaluationR0140

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138 GenericProjectiveEvaluationR0140

/-- The actual generic theta basis has the full unary projective identity value
in every frame of its identity fiber. -/
theorem generic_projective_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s), (∀ φ : ArithmeticThetaGenericEvaluationR0140.GenericDual k M s m, ∃! c : Fin m → LaurentSeries k, ArithmeticThetaGenericEvaluationR0140.Combines k M s m m (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) c φ) ∧ Nonempty (ArithmeticThetaGenericEvaluationR0140.GenericFrame k M s hs.1 m) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.GenericFrame k M s hs.1 m, ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m e (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm)) ≠ 0 ∧ ∀ ν : Fin m, ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m e (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs ν) / ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m e (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm)) = (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ν)) / (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm))) := by
  intro k _ _ m hm he T M hM s hs
  refine ⟨generic_theta_basis k m hm he T M hM s hs, ?_⟩
  obtain ⟨e, he'⟩ := normalized_identity_frame k (2*m)
    (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) T M hM s hs m
  let e₀ := baseFrame k M s hs.1 m e
  refine ⟨⟨e₀⟩, ?_⟩
  intro e'
  let a : LaurentSeries k := endValue (e'.inv ≫ e₀.hom)
  have ha : a ≠ 0 := endValue_nonzero (e'.symm ≪≫ e₀)
  let C : PowerSeries k := PowerSeries.X^((2*m)^2) * (↑(commonUnit k m hm) : PowerSeries k)
  have hC : C ≠ 0 := mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
    (Units.ne_zero (commonUnit k m hm))
  have hinj := IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  have hmapC : algebraMap (PowerSeries k) (LaurentSeries k) C ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hC
  have hu : algebraMap (PowerSeries k) (LaurentSeries k)
      (ArithmeticThetaSchrodingerR0119.unary k m (zeroIndex m hm)) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (unary_zero_nonzero k m hm)
  have hv (ν : Fin m) :
      genericValue k M s hs.1 m e' (genericTheta k m hm he M hM s hs ν) =
        (a * algebraMap (PowerSeries k) (LaurentSeries k) C) *
          algebraMap (PowerSeries k) (LaurentSeries k)
            (ArithmeticThetaSchrodingerR0119.unary k m ν) := by
    rw [changeFrame_value k M s hs.1 m e' e₀]
    change a * genericValue k M s hs.1 m (baseFrame k M s hs.1 m e)
      (restrictDual k M s m (thetaSection k m hm he M hM s hs ν)) = _
    rw [baseFrame_value, theta_value k m hm he M hM s hs e he', map_mul]
    exact (mul_assoc _ _ _).symm
  constructor
  · rw [hv]
    exact mul_ne_zero (mul_ne_zero ha hmapC) hu
  · intro ν
    rw [hv, hv]
    exact mul_div_mul_left _ _ (mul_ne_zero ha hmapC)

end ArithmeticThetaGenericEvaluationR0140
#print axioms ArithmeticThetaGenericEvaluationR0140.generic_projective_evaluation
