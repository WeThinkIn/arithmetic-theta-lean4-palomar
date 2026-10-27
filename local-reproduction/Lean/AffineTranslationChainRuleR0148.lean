import InverseDifferentialSignR0147
import ActualFourTorsionHodgeRootR0147

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaDifferentialRecoveryR0148.AffineTranslationChainRule
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign
open ArithmeticThetaCompactifiedDifferentialR0145

section Translation
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
variable (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
variable (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaGenericEvaluationR0140

lemma translation_over (p : Point k M) :
    translation k M G p ≫ genericStructure k M = genericStructure k M :=
  (G.mul _ (universalPoint k M) (constantPoint k M p)).property

lemma comp_translation {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (z : SchemeHomOver t (genericStructure k M)) (p : Point k M) :
    z.val ≫ translation k M G p =
      (G.mul t z (schemeHomOverComp t (Category.comp_id t) p)).val := by
  have h := G.mul_natural (genericStructure k M) t z.val z.property
    (universalPoint k M) (constantPoint k M p)
  have h1 : schemeHomOverComp z.val z.property (universalPoint k M) = z :=
    Subtype.ext (Category.comp_id _)
  have h2 : schemeHomOverComp z.val z.property (constantPoint k M p) =
      schemeHomOverComp t (Category.comp_id t) p := by
    apply Subtype.ext
    change z.val ≫ (genericStructure k M ≫ p.val) = t ≫ p.val
    rw [← Category.assoc, z.property]
  exact (congrArg Subtype.val h).trans (congrArg Subtype.val (by rw [h1, h2]))

lemma translation_one : translation k M G (G.one (𝟙 _)) = 𝟙 _ := by
  have h : constantPoint k M (G.one (𝟙 _)) = G.one (genericStructure k M) :=
    G.one_natural (𝟙 _) (genericStructure k M) (genericStructure k M) (Category.comp_id _)
  change (G.mul _ (universalPoint k M) (constantPoint k M (G.one (𝟙 _)))).val = _
  rw [h, G.mul_one]
  rfl

lemma translation_mul (p q : Point k M) :
    translation k M G (G.mul (𝟙 _) p q) = translation k M G p ≫ translation k M G q := by
  have h := comp_translation k M G (genericStructure k M)
    ⟨translation k M G p, translation_over k M G p⟩ q
  have hn := G.mul_natural (𝟙 _) (genericStructure k M) (genericStructure k M)
    (Category.comp_id _) p q
  change constantPoint k M (G.mul (𝟙 _) p q) =
    G.mul _ (constantPoint k M p) (constantPoint k M q) at hn
  rw [h]
  change (G.mul _ (universalPoint k M) (constantPoint k M (G.mul (𝟙 _) p q))).val = _
  rw [hn, ← G.mul_assoc]
  rfl

lemma translation_isIso (p : Point k M) : IsIso (translation k M G p) := by
  let q := G.inv (𝟙 _) p
  have h1 : translation k M G p ≫ translation k M G q = 𝟙 _ := by
    rw [← translation_mul]
    have hp : G.mul (𝟙 _) p (G.inv (𝟙 _) p) = G.one (𝟙 _) := by
      letI := G.pointGroup (𝟙 _)
      exact mul_inv_cancel p
    rw [hp, translation_one]
  have h2 : translation k M G q ≫ translation k M G p = 𝟙 _ := by
    rw [← translation_mul, G.inv_mul_cancel, translation_one]
  exact ⟨⟨translation k M G q, h1, h2⟩⟩
/-- Identity translation satisfies the chain rule on every open. -/
lemma identity_chain_rule (e : Frame k M) (U : (genericScheme k M).Opens)
    (a : (genericScheme k M).presheaf.obj (Opposite.op U)) :
    frameDerivative k M e ((translation k M G (G.one (𝟙 _))) ⁻¹ᵁ U)
      ((translation k M G (G.one (𝟙 _))).app U a) =
      (translation k M G (G.one (𝟙 _))).app U (frameDerivative k M e U a) := by
  rw [translation_one k M G]
  rfl
end Translation

section RationalAddition
variable {F : Type u} [Field F]

/-- The differentiated chord slope on a monic Weierstrass cubic.
The second point is fixed; only the denominator x-a must be nonzero. -/
lemma chord_slope_identity (A B C x y a b : F)
    (hy : y^2 = x^3 + A*x^2 + B*x + C)
    (hb : b^2 = a^3 + A*a^2 + B*a + C) (hxa : x-a ≠ 0) :
    ((3*x^2 + 2*A*x + B)*(x-a) - (y-b)*(2*y)) / (x-a)^2 =
      x - (((y-b)/(x-a))^2 - A - x - a) := by
  field_simp
  linear_combination -hy + hb

/-- The X-coordinate of chord addition has derivative twice the Y-coordinate.
This is valid at the generic point even when the fixed point is two-torsion. -/
lemma chord_derivative {R : Type u} [CommRing R] [Algebra R F]
    (D : Derivation R F F) (A B C x y a b : F)
    (hy : y^2 = x^3 + A*x^2 + B*x + C)
    (hb : b^2 = a^3 + A*a^2 + B*a + C) (hxa : x-a ≠ 0)
    (hDx : D x = 2*y) (hDy : D y = 3*x^2 + 2*A*x + B)
    (hDA : D A = 0) (hDa : D a = 0) (hDb : D b = 0) :
    D (((y-b)/(x-a))^2 - A - x - a) =
      2 * (-y + ((y-b)/(x-a)) * (x - (((y-b)/(x-a))^2 - A - x - a))) := by
  have hs : D ((y-b)/(x-a)) = x - (((y-b)/(x-a))^2 - A - x - a) := by
    rw [D.leibniz_div, D.map_sub, D.map_sub, hDy, hDb, hDx, hDa]
    simp only [sub_zero, smul_eq_mul]
    calc
      (x-a)⁻¹^2 * ((x-a)*(3*x^2 + 2*A*x + B) - (y-b)*(2*y)) =
        ((3*x^2 + 2*A*x + B)*(x-a) - (y-b)*(2*y)) / (x-a)^2 := by rw [div_eq_mul_inv, inv_pow]; ring
      _ = _ := chord_slope_identity A B C x y a b hy hb hxa
  rw [D.map_sub, D.map_sub, D.map_sub, D.leibniz_pow, hDA, hDx, hDa, hs]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  ring

/-- The rational calculation agrees with mathlib's actual affine addition formulas. -/
lemma weierstrass_addX_derivative {R : Type u} [CommRing R] [Algebra R F]
    [DecidableEq F] (D : Derivation R F F) (W : WeierstrassCurve.Affine F)
    (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (x y a b : F)
    (hy : W.Equation x y) (hb : W.Equation a b) (hxa : x ≠ a)
    (hDx : D x = 2*y) (hDy : D y = 3*x^2 + 2*W.a₂*x + W.a₄)
    (hDA : D W.a₂ = 0) (hDa : D a = 0) (hDb : D b = 0) :
    D (W.addX x a (W.slope x a y b)) = 2 * W.addY x a y (W.slope x a y b) := by
  have hy' : y^2 = x^3 + W.a₂*x^2 + W.a₄*x + W.a₆ := by
    simpa only [WeierstrassCurve.Affine.equation_iff, h1, h3, zero_mul, add_zero] using hy
  have hb' : b^2 = a^3 + W.a₂*a^2 + W.a₄*a + W.a₆ := by
    simpa only [WeierstrassCurve.Affine.equation_iff, h1, h3, zero_mul, add_zero] using hb
  have H := chord_derivative D W.a₂ W.a₄ W.a₆ x y a b hy' hb' (sub_ne_zero.mpr hxa)
    hDx hDy hDA hDa hDb
  rw [W.slope_of_X_ne hxa]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    h1, h3, zero_mul, add_zero, sub_zero]
  rw [H]
  ring

end RationalAddition

section RingChord
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A chord calculation on a regular open, using a unit denominator and no field extension. -/
lemma chord_derivative_of_unit (D : Derivation R B B)
    (A B₄ C x y a b l : B)
    (hy : y^2 = x^3 + A*x^2 + B₄*x + C)
    (hb : b^2 = a^3 + A*a^2 + B₄*a + C)
    (hu : IsUnit (x-a)) (hl : (x-a)*l = y-b)
    (hDx : D x = 2*y) (hDy : D y = 3*x^2 + 2*A*x + B₄)
    (hDA : D A = 0) (hDa : D a = 0) (hDb : D b = 0) :
    D (l^2 - A - x - a) = 2 * (-y + l * (x - (l^2 - A - x - a))) := by
  have hd := congrArg D hl
  rw [D.leibniz, D.map_sub, D.map_sub, hDx, hDy, hDa, hDb] at hd
  simp only [sub_zero, smul_eq_mul] at hd
  have hc : (x-a) * ((3*x^2 + 2*A*x + B₄ - 2*y*l) -
      (x-a)*(x-(l^2-A-x-a))) = 0 := by
    linear_combination -hy + hb + ((x-a)*l-y-b)*hl
  have hc' : 3*x^2 + 2*A*x + B₄ - 2*y*l = (x-a)*(x-(l^2-A-x-a)) := by
    apply sub_eq_zero.mp
    exact hu.mul_left_cancel (hc.trans (mul_zero (x-a)).symm)
  have hs : D l = x-(l^2-A-x-a) := by
    apply hu.mul_left_cancel
    linear_combination hd + hc'
  rw [D.map_sub, D.map_sub, D.map_sub, D.leibniz_pow, hDA, hDx, hDa, hs]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  ring

/-- The cubic equation and the nonzero 2Y determine the Y derivative. -/
lemma derivative_y_of_equation [IsDomain B] (D : Derivation R B B)
    (A B₄ C x y : B) (hy : y^2 = x^3 + A*x^2 + B₄*x + C)
    (h2y : 2*y ≠ 0) (hDx : D x = 2*y)
    (hDA : D A = 0) (hDB : D B₄ = 0) (hDC : D C = 0) :
    D y = 3*x^2 + 2*A*x + B₄ := by
  have H := congrArg D hy
  simp only [map_add, D.leibniz, D.leibniz_pow, hDA, hDB, hDC, hDx,
    smul_eq_mul, nsmul_eq_mul] at H
  apply mul_left_cancel₀ h2y
  simp only [Nat.reduceSub, pow_one, mul_zero, zero_mul, add_zero] at H
  linear_combination H

end RingChord

section CoefficientDerivation
variable {F : Type u} [CommRing F] {C : Scheme.{u}}
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)

/-- The coefficient in the actual frame is a derivation for the specified base map. -/
def coefficientDerivation (U : C.Opens) :
    letI := p.sectionsAlgebra U
    Derivation F Γ(C,U) Γ(C,U) := by
  letI := p.sectionsAlgebra U
  exact {
    toFun := coefficient p e U
    map_add' := coefficient_add p e U
    map_smul' := fun c a => by
      change coefficient p e U (algebraMap F Γ(C,U) c * a) =
        algebraMap F Γ(C,U) c * coefficient p e U a
      have hc : coefficient p e U (algebraMap F Γ(C,U) c) = 0 := coefficient_constant p e U c
      rw [coefficient_mul, hc, mul_zero, add_zero]
    map_one_eq_zero' := coefficient_one p e U
    leibniz' := fun a b => coefficient_mul p e U a b }
end CoefficientDerivation

section CubicReduction
open ArithmeticThetaCubicModelR0144
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} (p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable (f : C ⟶ C) (hf : f ≫ p = p)
variable (U : C.Opens)

/-- The translation defect is a derivation twisted by the actual pullback. -/
def translationDefect : Γ(C,U) →+ Γ(C,f ⁻¹ᵁ U) where
  toFun a := coefficient p e (f ⁻¹ᵁ U) (f.app U a) - f.app U (coefficient p e U a)
  map_zero' := by simp only [map_zero, coefficient_zero, sub_self]
  map_add' a b := by
    simp only [map_add, coefficient_add]
    abel

lemma translationDefect_mul (a b : Γ(C,U)) :
    translationDefect k p e f U (a*b) =
      f.app U a * translationDefect k p e f U b + f.app U b * translationDefect k p e f U a := by
  simp only [translationDefect, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_mul, coefficient_mul, map_add]
  ring

include hf in
lemma translationDefect_constant (c : LaurentSeries k) :
    translationDefect k p e f U ((p.constToPresheaf.app (Opposite.op U)).hom c) = 0 := by
  change coefficient p e _ (f.app U _) - f.app U (coefficient p e U _) = 0
  rw [app_constant p f hf, coefficient_constant, coefficient_constant, map_zero, sub_self]

include hf in
/-- For a cubic chart, the actual chain rule reduces to the X-coordinate.
The nonzero condition on the pulled-back 2Y is stated explicitly. -/
lemma chainRule_of_cubic_x [IsDomain Γ(C,f ⁻¹ᵁ U)]
    (q : CubicRing k r →+* Γ(C,U)) (hq : Function.Surjective q)
    (hqc : ∀ c, q (algebraMap (LaurentSeries k) (CubicRing k r) c) =
      (p.constToPresheaf.app (Opposite.op U)).hom c)
    (hx : coefficient p e (f ⁻¹ᵁ U) (f.app U (q (cubicCoordinate k r false))) =
      f.app U (coefficient p e U (q (cubicCoordinate k r false))))
    (hy : f.app U (q (2*cubicCoordinate k r true)) ≠ 0) :
    ∀ a : Γ(C,U), coefficient p e (f ⁻¹ᵁ U) (f.app U a) =
      f.app U (coefficient p e U a) := by
  let E := translationDefect k p e f U
  have H := cubic_twisted_ext k r ((f.app U).hom.comp q) (E.comp q.toAddMonoidHom)
    (fun a b => by
      change E (q (a*b)) = _
      rw [map_mul]
      exact translationDefect_mul k p e f U (q a) (q b))
    (fun c => by
      change translationDefect k p e f U (q (algebraMap _ _ c)) = 0
      rw [hqc, translationDefect_constant k p e f hf])
    (sub_eq_zero.mpr hx) hy
  intro a
  obtain ⟨b,rfl⟩ := hq a
  exact sub_eq_zero.mp (H b)

end CubicReduction

section ActualCubicReduction
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
variable (k : Type u) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- The exact geometric obligation reduces to the actual pulled-back X-coordinate.
This helper does not assert the missing X-coordinate equation. -/
lemma actual_chainRule_of_x (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (G : Law k M) (e : Frame k M) (heN : IsGlobalDifferentialFrame k M s X Y e)
    (P : Point k M)
    (hx : frameDerivative k M e ((translation k M G P) ⁻¹ᵁ complement k M s)
      ((translation k M G P).app (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 2 X))) =
      2 * (translation k M G P).app (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 3 Y))) :
    ∀ a, frameDerivative k M e ((translation k M G P) ⁻¹ᵁ complement k M s)
      ((translation k M G P).app (complement k M s) a) =
      (translation k M G P).app (complement k M s)
        (frameDerivative k M e (complement k M s) a) := by
  let C := genericScheme k M
  let p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)) := genericStructure k M
  let f : C ⟶ C := translation k M G P
  let W := complement k M s
  letI : IsIntegral C := generic_integral k h3 M hM
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  letI : IsIso f := translation_isIso k M G P
  letI : Nonempty (f ⁻¹ᵁ W : C.Opens) := by
    let x : W := Classical.choice (complement_nonempty k h3 M hM s hs)
    refine ⟨⟨(inv f) x.val, ?_⟩⟩
    change f ((inv f) x.val) ∈ W
    have h : f ((inv f) x.val) = x.val := by
      exact congrArg (fun g : C ⟶ C => g x.val) (IsIso.inv_hom_id f)
    rw [h]
    exact x.property
  obtain ⟨a,ha,_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  let q : CubicRing k r →+* Γ(C,W) := W.topIso.hom.hom.comp
    (a.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv.hom)
  have hq (odd : Bool) : q (cubicCoordinate k r odd) =
      W.topIso.hom (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X)) :=
    congrArg W.topIso.hom (coordinateIso_values k M s X Y a ha odd)
  have hqc (c : LaurentSeries k) : q (algebraMap _ _ c) =
      (p.constToPresheaf.app (Opposite.op W)).hom c := by
    change W.topIso.hom (a.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
      (algebraMap _ _ c))) = _
    rw [← spec_constant]
    have ht : a.hom.appTop = a.hom.appLE ⊤ ⊤ le_top := by
      simp [Scheme.Hom.appTop, Scheme.Hom.appLE]
    rw [ht]
    erw [appLE_constant]
    change W.topIso.hom (((a.hom ≫ cubicStructure k r).constToPresheaf.app (Opposite.op ⊤)).hom c) = _
    rw [ha.1]
    exact topIso_constant p W c
  have hnorm : coefficient p e W (q (cubicCoordinate k r false)) = 2*q (cubicCoordinate k r true) := by
    rw [hq false, hq true]
    exact coefficient_normalization p e W _ _ (normalization_from_predicate k M s X Y e heN)
  have hsurj : Function.Surjective q :=
    (ConcreteCategory.bijective_of_isIso W.topIso.hom).2.comp
      ((ConcreteCategory.bijective_of_isIso a.hom.appTop).2.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv).2)
  apply chainRule_of_cubic_x k r p e f (translation_over k M G P) W q hsurj hqc
  · rw [hnorm, map_mul, map_ofNat, hq false, hq true]
    exact hx
  · have hy0 : q (cubicCoordinate k r true) ≠ 0 := by
      rw [hq true]
      exact complement_y_nonzero k h3 he M hM s hs X Y hX hY
    have h2 : (2 : Γ(C,W)) ≠ 0 := by
      letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
      have hu : IsUnit (2 : Γ(C,W)) := by
        simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
          ((p.constToPresheaf.app (Opposite.op W)).hom)
      exact hu.ne_zero
    intro H
    have HH : q (2*cubicCoordinate k r true) = 0 :=
      (ConcreteCategory.bijective_of_isIso (f.app W)).1 (H.trans (map_zero (f.app W).hom).symm)
    rw [map_mul, map_ofNat] at HH
    exact (mul_ne_zero h2 hy0) HH

/-- The actual X-coordinate is never a base constant. Hence the generic chord
has a nonzero denominator for every fixed finite point, including two-torsion. -/
lemma actual_x_ne_constant (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (e : Frame k M) (heN : IsGlobalDifferentialFrame k M s X Y e)
    (c : LaurentSeries k) :
    (complement k M s).topIso.hom (complementCoordinate k M s 2 X) ≠
      ((genericStructure k M).constToPresheaf.app (Opposite.op (complement k M s))).hom c := by
  let W := complement k M s
  let p := genericStructure k M
  letI := generic_integral k h3 M hM
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  have hn := coefficient_normalization p e W _ _
    (normalization_from_predicate k M s X Y e heN)
  have hy := complement_y_nonzero k h3 he M hM s hs X Y hX hY
  have h2 : (2 : Γ(genericScheme k M,W)) ≠ 0 := by
    letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
    exact (show IsUnit (2 : Γ(genericScheme k M,W)) from by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
        ((p.constToPresheaf.app (Opposite.op W)).hom)).ne_zero
  intro H
  have HH := congrArg (coefficient p e W) H
  rw [hn, coefficient_constant] at HH
  exact mul_ne_zero h2 hy HH

end ActualCubicReduction

section ChartAddition
open ArithmeticThetaMarkedGroupLawR0146
open WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)

/-- Field-valued chord coordinates follow from the accepted evaluation of the actual law. -/
lemma field_chord_coordinates
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra (LaurentSeries k) F]
    (P Q R : SchemeHomOver (extensionBase k F) (projectiveStructure k r))
    (χ ψ ρ : ChartRing k r →+* F)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r)
    (hQ : Q.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion k r)
    (hR : R.val = Spec.map (CommRingCat.ofHom ρ) ≫ chartInclusion k r)
    (hPQ : G.mul (extensionBase k F) P Q = R)
    (hne : χ (xOverZ (curve k r).toProjective) ≠ ψ (xOverZ (curve k r).toProjective)) :
    let W := ((curve k r).toProjective.baseChange F).toAffine
    let x := χ (xOverZ (curve k r).toProjective)
    let y := χ (yOverZ (curve k r).toProjective)
    let a := ψ (xOverZ (curve k r).toProjective)
    let b := ψ (yOverZ (curve k r).toProjective)
    ρ (xOverZ (curve k r).toProjective) = W.addX x a ((y-b)/(x-a)) ∧
    ρ (yOverZ (curve k r).toProjective) = W.addY x a y ((y-b)/(x-a)) := by
  obtain ⟨h₁,e₁⟩ := hev.2 F P χ hP
  obtain ⟨h₂,e₂⟩ := hev.2 F Q ψ hQ
  obtain ⟨h₃,e₃⟩ := hev.2 F R ρ hR
  have H := hev.1.1 F P Q
  change ev F (G.mul (extensionBase k F) P Q) = ev F P + ev F Q at H
  rw [hPQ,e₁,e₂,e₃,WeierstrassCurve.Affine.Point.add_of_X_ne hne] at H
  have h := WeierstrassCurve.Affine.Point.some.inj H
  simpa only [WeierstrassCurve.Affine.slope_of_X_ne hne] using h

/-- The group law's coordinate comparison descends to any domain, on the chord open. -/
lemma ring_chord_coordinates
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra (LaurentSeries k) B]
    (P Q R : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B)))
      (projectiveStructure k r))
    (χ ψ ρ : ChartRing k r →+* B)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r)
    (hQ : Q.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion k r)
    (hR : R.val = Spec.map (CommRingCat.ofHom ρ) ≫ chartInclusion k r)
    (hPQ : G.mul (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B))) P Q = R)
    (l : B)
    (hu : IsUnit (χ (xOverZ (curve k r).toProjective) - ψ (xOverZ (curve k r).toProjective)))
    (hl : (χ (xOverZ (curve k r).toProjective) - ψ (xOverZ (curve k r).toProjective))*l =
      χ (yOverZ (curve k r).toProjective) - ψ (yOverZ (curve k r).toProjective)) :
    let x := χ (xOverZ (curve k r).toProjective)
    let y := χ (yOverZ (curve k r).toProjective)
    let a := ψ (xOverZ (curve k r).toProjective)
    let A := algebraMap (LaurentSeries k) B (curve k r).a₂
    ρ (xOverZ (curve k r).toProjective) = l^2 - A - x - a ∧
    ρ (yOverZ (curve k r).toProjective) = -y + l*(x - ρ (xOverZ (curve k r).toProjective)) := by
  classical
  let F := FractionRing B
  let β := Spec.map (CommRingCat.ofHom (algebraMap B F))
  let t := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B))
  have ht : β ≫ t = extensionBase k F := by
    change Spec.map (CommRingCat.ofHom (algebraMap B F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rfl
  let PF := schemeHomOverComp β ht P
  let QF := schemeHomOverComp β ht Q
  let RF := schemeHomOverComp β ht R
  let χF := (algebraMap B F).comp χ
  let ψF := (algebraMap B F).comp ψ
  let ρF := (algebraMap B F).comp ρ
  have fac (P : SchemeHomOver t (projectiveStructure k r)) (χ : ChartRing k r →+* B)
      (h : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r) :
      (schemeHomOverComp β ht P).val =
        Spec.map (CommRingCat.ofHom ((algebraMap B F).comp χ)) ≫ chartInclusion k r := by
    change β ≫ P.val = _
    rw [h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hsum : G.mul (extensionBase k F) PF QF = RF := by
    rw [← G.mul_natural]
    exact congrArg (schemeHomOverComp β ht) hPQ
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  have hne : χF (xOverZ (curve k r).toProjective) ≠ ψF (xOverZ (curve k r).toProjective) := by
    intro H
    exact hu.ne_zero (sub_eq_zero.mpr (hinj H))
  have hxy := field_chord_coordinates k r G ev hev F PF QF RF χF ψF ρF
    (fac P χ hP) (fac Q ψ hQ) (fac R ρ hR) hsum hne
  have hlF : (χF (yOverZ (curve k r).toProjective) - ψF (yOverZ (curve k r).toProjective)) /
      (χF (xOverZ (curve k r).toProjective) - ψF (xOverZ (curve k r).toProjective)) = algebraMap B F l := by
    apply (div_eq_iff (sub_ne_zero.mpr hne)).mpr
    have H := congrArg (algebraMap B F) hl
    simpa only [χF, ψF, RingHom.comp_apply, map_mul, map_sub, mul_comm] using H.symm
  dsimp only at hxy ⊢
  rw [hlF] at hxy
  have hx : ρ (xOverZ (curve k r).toProjective) =
      l^2 - algebraMap (LaurentSeries k) B (curve k r).a₂ -
        χ (xOverZ (curve k r).toProjective) - ψ (xOverZ (curve k r).toProjective) := by
    apply hinj
    have H := hxy.1
    change algebraMap B F (ρ _) =
      (algebraMap B F l)^2 + algebraMap (LaurentSeries k) F 0 * algebraMap B F l -
        algebraMap (LaurentSeries k) F (curve k r).a₂ - algebraMap B F (χ _) - algebraMap B F (ψ _) at H
    simpa only [map_zero, zero_mul, add_zero, map_sub, map_pow,
      ← IsScalarTower.algebraMap_apply (LaurentSeries k) B F] using H
  refine ⟨hx, ?_⟩
  apply hinj
  have H := hxy.2
  have hxx := hxy.1
  change algebraMap B F (ρ _) =
    -(algebraMap B F l * (_ - algebraMap B F (χ _)) + algebraMap B F (χ _)) -
      algebraMap (LaurentSeries k) F 0 * _ - algebraMap (LaurentSeries k) F 0 at H
  rw [← hxx, map_zero, zero_mul, sub_zero, sub_zero] at H
  simp only [map_add, map_neg, map_mul, map_sub]
  linear_combination H

/-- Every actual affine-chart point over a domain satisfies the same scalar cubic equation. -/
lemma ring_chart_equation
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra (LaurentSeries k) B]
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B)))
      (projectiveStructure k r)) (χ : ChartRing k r →+* B)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r) :
    let x := χ (xOverZ (curve k r).toProjective)
    let y := χ (yOverZ (curve k r).toProjective)
    y^2 = x^3 + algebraMap (LaurentSeries k) B (curve k r).a₂*x^2 +
      algebraMap (LaurentSeries k) B (curve k r).a₄*x + algebraMap (LaurentSeries k) B (curve k r).a₆ := by
  classical
  let F := FractionRing B
  let β := Spec.map (CommRingCat.ofHom (algebraMap B F))
  let t := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B))
  have ht : β ≫ t = extensionBase k F := by
    change Spec.map (CommRingCat.ofHom (algebraMap B F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rfl
  let PF := schemeHomOverComp β ht P
  let χF := (algebraMap B F).comp χ
  have hf : PF.val = Spec.map (CommRingCat.ofHom χF) ≫ chartInclusion k r := by
    change β ≫ P.val = _
    rw [hP, show CommRingCat.ofHom χF = CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap B F) from rfl,
      Spec.map_comp, Category.assoc]
  obtain ⟨hxy,_⟩ := hev.2 F PF χF hf
  have H := (WeierstrassCurve.Affine.equation_iff ..).mp hxy.1
  change (algebraMap B F (χ _))^2 + algebraMap (LaurentSeries k) F 0 * _ * _ +
      algebraMap (LaurentSeries k) F 0 * _ =
      (algebraMap B F (χ _))^3 + algebraMap (LaurentSeries k) F (curve k r).a₂*(algebraMap B F (χ _))^2 +
      algebraMap (LaurentSeries k) F (curve k r).a₄*algebraMap B F (χ _) +
      algebraMap (LaurentSeries k) F (curve k r).a₆ at H
  apply IsFractionRing.injective B F
  simpa only [map_zero, zero_mul, add_zero, map_add, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply (LaurentSeries k) B F] using H

end ChartAddition

section AffineMapComparison
variable {C : Scheme.{u}} (U : C.Opens)
variable {B : Type u} [CommRing B]

/-- The chart ring map on actual sections. -/
def chartSections (E : U.toScheme ≅ Spec (CommRingCat.of B)) : B →+* Γ(C,U) :=
  U.topIso.hom.hom.comp (E.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)

lemma chartSections_spec (hU : IsAffineOpen U) (E : U.toScheme ≅ Spec (CommRingCat.of B)) :
    Spec.map (CommRingCat.ofHom (chartSections U E)) = hU.isoSpec.inv ≫ E.hom := by
  letI : IsAffine U := hU
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ E.hom.appTop ≫ U.topIso.hom) = _
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    Category.assoc, Scheme.isoSpec_inv_naturality]
  rfl

lemma chartSections_factor {D : Scheme.{u}} (hU : IsAffineOpen U)
    (E : U.toScheme ≅ Spec (CommRingCat.of B)) (j : Spec (CommRingCat.of B) ⟶ D)
    (g : C ⟶ D) (hg : U.ι ≫ g = E.hom ≫ j)
    (f : C ⟶ C) (V : C.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom ((f.appLE U V hVU).hom.comp (chartSections U E))) ≫ j =
      hV.fromSpec ≫ f ≫ g := by
  change Spec.map (CommRingCat.ofHom (chartSections U E) ≫ f.appLE U V hVU) ≫ j = _
  rw [Spec.map_comp, chartSections_spec U hU E]
  simp only [Category.assoc]
  rw [← hg, ← Category.assoc hU.isoSpec.inv, IsAffineOpen.isoSpec_inv_ι,
    ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec]
  exact Category.assoc _ _ _

lemma affine_structural {F : Type u} [CommRing F] (p : C ⟶ Spec (CommRingCat.of F))
    (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = Spec.map (p.constToPresheaf.app (Opposite.op U)) := by
  change hU.fromSpec ≫ p = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appLE ⊤ U le_top)
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU le_top).symm

lemma identity_appLE (V : C.Opens) (hVU : V ≤ U) :
    (𝟙 C : C ⟶ C).appLE U V hVU = C.presheaf.map (homOfLE hVU).op := by
  simp [Scheme.Hom.appLE, Scheme.Hom.id_app]

lemma constant_restrict {F : Type u} [CommRing F] (p : C ⟶ Spec (CommRingCat.of F))
    (V : C.Opens) (hVU : V ≤ U) (c : F) :
    C.presheaf.map (homOfLE hVU).op ((p.constToPresheaf.app (Opposite.op U)).hom c) =
      (p.constToPresheaf.app (Opposite.op V)).hom c := by
  have H := p.constToPresheaf.naturality (homOfLE hVU).op
  exact (ConcreteCategory.congr_hom H c).symm

/-- A nonzero denominator becomes a unit on a nonempty affine open inside
any prescribed nonempty open of the integral curve. -/
lemma exists_affine_unit_open [IsIntegral C] (V : C.Opens) [Nonempty V]
    (a : Γ(C,U)) (ha : a ≠ 0) :
    ∃ (W : C.Opens) (hW : IsAffineOpen W), Nonempty W ∧
      ∃ (hWU : W ≤ U), W ≤ V ∧ IsUnit (C.presheaf.map (homOfLE hWU).op a) := by
  let Z := C.basicOpen a
  have hnZ : Nonempty Z := by
    by_contra H
    have hZ : C.basicOpen a = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => H ⟨⟨x,hx⟩⟩)
    exact ha ((basicOpen_eq_bot_iff a).mp hZ)
  letI : Nonempty Z := hnZ
  let z : (Z ⊓ V : C.Opens) := Classical.choice
    (ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.nonempty_inter Z V)
  obtain ⟨W,⟨W,hW,rfl⟩,hz,hWN⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    z.property (Z ⊓ V).isOpen
  have hWZ : W ≤ Z := hWN.trans inf_le_left
  have hWU : W ≤ U := hWZ.trans (C.basicOpen_le a)
  refine ⟨W,hW,⟨⟨z.val,hz⟩⟩,hWU,hWN.trans inf_le_right,?_⟩
  have H := (C.toRingedSpace.isUnit_res_basicOpen a).map
    (C.presheaf.map (homOfLE hWZ).op).hom
  change IsUnit (C.presheaf.map (homOfLE hWZ).op
    (C.presheaf.map (homOfLE (C.basicOpen_le a)).op a)) at H
  rw [← CommRingCat.comp_apply, ← Functor.map_comp] at H
  exact H

end AffineMapComparison

section LocalActualAddition
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- A typed presentation of the original structural map. -/
def structureMap (M : Model k T) : genericScheme k M ⟶ Spec (CommRingCat.of (LaurentSeries k)) :=
  genericStructure k M

lemma structureMap_eq (M : Model k T) : structureMap k M = genericStructure k M := rfl

/-- The actual translation has the chord formulas on each affine chord open. -/
lemma local_actual_chord (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (G : Law k M) (P : Point k M)
    (E : genericScheme k M ≅ projectiveCurve k r)
    (hE : E.hom ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r = structureMap k M)
    (hG : (G.one (𝟙 _)).val ≫ E.hom = origin k r)
    (U : (genericScheme k M).Opens) (hU : IsAffineOpen U)
    (E₀ : U.toScheme ≅ Spec (CommRingCat.of (ChartRing k r)))
    (hE₀ : U.ι ≫ E.hom = E₀.hom ≫ chartInclusion k r)
    (χP : ChartRing k r →+* LaurentSeries k)
    (hP : P.val ≫ E.hom = Spec.map (CommRingCat.ofHom χP) ≫ chartInclusion k r)
    (V : (genericScheme k M).Opens) (hV : IsAffineOpen V) [Nonempty V]
    [IsIntegral (genericScheme k M)]
    (hVU : V ≤ U) (hVt : V ≤ (translation k M G P) ⁻¹ᵁ U)
    (l : Γ(genericScheme k M,V))
    (hu : IsUnit ((genericScheme k M).presheaf.map (homOfLE hVU).op
      (chartSections U E₀ (xOverZ (curve k r).toProjective)) -
      ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom
        (χP (xOverZ (curve k r).toProjective))))
    (hl : ((genericScheme k M).presheaf.map (homOfLE hVU).op
      (chartSections U E₀ (xOverZ (curve k r).toProjective)) -
      ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom
        (χP (xOverZ (curve k r).toProjective)))*l =
      (genericScheme k M).presheaf.map (homOfLE hVU).op
        (chartSections U E₀ (yOverZ (curve k r).toProjective)) -
      ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom
        (χP (yOverZ (curve k r).toProjective))) :
    let x := (genericScheme k M).presheaf.map (homOfLE hVU).op
      (chartSections U E₀ (xOverZ (curve k r).toProjective))
    let y := (genericScheme k M).presheaf.map (homOfLE hVU).op
      (chartSections U E₀ (yOverZ (curve k r).toProjective))
    let a := ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom
      (χP (xOverZ (curve k r).toProjective))
    let A := ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom (curve k r).a₂
    let xt := (translation k M G P).appLE U V hVt (chartSections U E₀ (xOverZ (curve k r).toProjective))
    let yt := (translation k M G P).appLE U V hVt (chartSections U E₀ (yOverZ (curve k r).toProjective))
    let b := ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom
      (χP (yOverZ (curve k r).toProjective))
    let B₄ := ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom (curve k r).a₄
    let B₆ := ((structureMap k M).constToPresheaf.app (Opposite.op V)).hom (curve k r).a₆
    y^2 = x^3+A*x^2+B₄*x+B₆ ∧ b^2 = a^3+A*a^2+B₄*a+B₆ ∧
      xt = l^2-A-x-a ∧ yt = -y+l*(x-xt) := by
  classical
  let C := genericScheme k M
  let p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)) := structureMap k M
  let f := translation k M G P
  letI := p.sectionsAlgebra V
  let B := Γ(C,V)
  let t := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) B))
  have ht : hV.fromSpec ≫ p = t := affine_structural V p hV
  have hei : E.inv ≫ p = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    change E.inv ≫ structureMap k M = _
    rw [← hE, E.inv_hom_id_assoc]
  let H := transport E.symm hei G
  have hH : (H.one (𝟙 _)).val = origin k r := hG
  obtain ⟨ev,hev⟩ := projective_points_evaluation k r h3 he H hH
  let z : SchemeHomOver t p := ⟨hV.fromSpec, ht⟩
  let q : SchemeHomOver t p := schemeHomOverComp t (Category.comp_id _) P
  have hf : f ≫ p = p := translation_over k M G P
  let zt : SchemeHomOver t p := ⟨hV.fromSpec ≫ f, by
    rw [Category.assoc, hf, ht]⟩
  let Z := pointsEquiv E hE t z
  let Q := pointsEquiv E hE t q
  let R := pointsEquiv E hE t zt
  let χ := (C.presheaf.map (homOfLE hVU).op).hom.comp (chartSections U E₀)
  let ψ := (algebraMap (LaurentSeries k) B).comp χP
  let ρ := (f.appLE U V hVt).hom.comp (chartSections U E₀)
  have hZ : Z.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r := by
    have hh := chartSections_factor U hU E₀ (chartInclusion k r) E.hom hE₀ (𝟙 C) V hV hVU
    rw [identity_appLE] at hh
    have hid : (𝟙 C : C ⟶ C) ≫ E.hom = E.hom := Category.id_comp _
    rw [hid] at hh
    exact hh.symm
  have hQ : Q.val = Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion k r := by
    change (t ≫ P.val) ≫ E.hom = _
    rw [Category.assoc, hP]
    change t ≫ Spec.map (CommRingCat.ofHom χP) ≫ chartInclusion k r = _
    rw [show CommRingCat.ofHom ψ = CommRingCat.ofHom χP ≫
      CommRingCat.ofHom (algebraMap (LaurentSeries k) B) from rfl, Spec.map_comp, Category.assoc]
  have hR : R.val = Spec.map (CommRingCat.ofHom ρ) ≫ chartInclusion k r := by
    exact (Category.assoc _ _ _).trans
      (chartSections_factor U hU E₀ (chartInclusion k r) E.hom hE₀ f V hV hVt).symm
  have hsum : H.mul t Z Q = R := by
    have hback (z : SchemeHomOver t p) :
        pointsEquiv E.symm hei t (pointsEquiv E hE t z) = z := by
      apply Subtype.ext
      simp [pointsEquiv]
    have htrans : G.mul t z q = zt := by
      apply Subtype.ext
      exact (comp_translation k M G t z P).symm
    change (pointsEquiv E.symm hei t).symm (G.mul t
      (pointsEquiv E.symm hei t (pointsEquiv E hE t z))
      (pointsEquiv E.symm hei t (pointsEquiv E hE t q))) = R
    rw [hback, hback, htrans]
    rfl
  exact ⟨ring_chart_equation k r H ev hev B Z χ hZ,
    ring_chart_equation k r H ev hev B Q ψ hQ,
    ring_chord_coordinates k r H ev hev B Z Q R χ ψ ρ hZ hQ hR hsum l hu hl⟩

end LocalActualAddition


section FiniteTranslation
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma finite_translation_x (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (e : Frame k M) (heN : IsGlobalDifferentialFrame k M s X Y e)
    (P : Point k M) (hPone : P ≠ G.one (𝟙 _)) :
    frameDerivative k M e ((translation k M G P) ⁻¹ᵁ complement k M s)
      ((translation k M G P).app (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 2 X))) =
      2 * (translation k M G P).app (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) := by
  classical
  let C := genericScheme k M
  let p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)) := structureMap k M
  let W := complement k M s
  let f : C ⟶ C := translation k M G P
  letI : IsIntegral C := generic_integral k h3 M hM
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  letI : IsIso f := translation_isIso k M G P
  letI : Nonempty (f ⁻¹ᵁ W : C.Opens) := by
    let x : W := Classical.choice (complement_nonempty k h3 M hM s hs)
    refine ⟨⟨(inv f) x.val, ?_⟩⟩
    change f ((inv f) x.val) ∈ W
    have H : f ((inv f) x.val) = x.val := congrArg (fun g : C ⟶ C => g x.val) (IsIso.inv_hom_id f)
    rw [H]
    exact x.property
  obtain ⟨a,ha,_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c,hc,_⟩ := projective_cubic_chart k r
  obtain ⟨E,hE,_⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  have hOrigin : (G.one (𝟙 _)).val ≫ E.hom = origin k r := by
    rw [hG.1]
    simpa only [pointOver, Category.id_comp] using hE.2.2
  have hPne : P ≠ pointOver k M (𝟙 _) s hs.1 := by
    intro H
    exact hPone (H.trans (hG.1 _).symm)
  obtain ⟨xp,yp,χP,hPfac,_,_⟩ := ActualFourTorsionHodgeRoot.coordinates_of_ne k M hM s hs.1 a c E hE P hPne
  let q := chartSections W (a ≪≫ c)
  have hq (odd : Bool) :
      q (if odd then yOverZ (curve k r).toProjective else xOverZ (curve k r).toProjective) =
      W.topIso.hom (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X)) := by
    change W.topIso.hom (a.hom.appTop (c.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv _))) = _
    rw [hc.2 odd]
    exact congrArg W.topIso.hom (coordinateIso_values k M s X Y a ha odd)
  have hqx : q (xOverZ (curve k r).toProjective) = W.topIso.hom (complementCoordinate k M s 2 X) := hq false
  have hqy : q (yOverZ (curve k r).toProjective) = W.topIso.hom (complementCoordinate k M s 3 Y) := hq true
  let xW := q (xOverZ (curve k r).toProjective)
  let yW := q (yOverZ (curve k r).toProjective)
  have hnorm : coefficient p e W xW = 2*yW := by
    change coefficient p e W (q _) = 2*q _
    rw [hqx,hqy]
    exact coefficient_normalization p e W _ _ (normalization_from_predicate k M s X Y e heN)
  let aP := χP (xOverZ (curve k r).toProjective)
  let bP := χP (yOverZ (curve k r).toProjective)
  have hden : xW - (p.constToPresheaf.app (Opposite.op W)).hom aP ≠ 0 := by
    apply sub_ne_zero.mpr
    change q _ ≠ _
    rw [hqx]
    exact actual_x_ne_constant k h3 he M hM s hs X Y hX hY e heN aP
  obtain ⟨V,hV,hnV,hVW,hVt,hu⟩ := exists_affine_unit_open W (f ⁻¹ᵁ W)
    (xW - (p.constToPresheaf.app (Opposite.op W)).hom aP) hden
  letI : Nonempty V := hnV
  letI := p.sectionsAlgebra V
  let R := Γ(C,V)
  let res := (C.presheaf.map (homOfLE hVW).op).hom
  let x : R := res xW
  let y : R := res yW
  let aa : R := algebraMap (LaurentSeries k) R aP
  let bb : R := algebraMap (LaurentSeries k) R bP
  let A : R := algebraMap (LaurentSeries k) R (curve k r).a₂
  let B₄ : R := algebraMap (LaurentSeries k) R (curve k r).a₄
  let B₆ : R := algebraMap (LaurentSeries k) R (curve k r).a₆
  have hunit : IsUnit (x-aa) := by
    rw [map_sub, constant_restrict W p V hVW] at hu
    exact hu
  obtain ⟨u,huv⟩ := hunit
  have hunit : IsUnit (x-aa) := by rw [← huv]; exact u.isUnit
  let l : R := (↑u⁻¹ : R)*(y-bb)
  have hl : (x-aa)*l = y-bb := by
    rw [← huv]
    simp [l, ← mul_assoc]
  have hlocal := local_actual_chord k h3 he M G P E hE.1 hOrigin W
    (complement_isAffineOpen k h3 M hM s hs X hX) (a ≪≫ c) hE.2.1 χP hPfac V hV hVW hVt l hunit hl
  let xt : R := f.appLE W V hVt xW
  let yt : R := f.appLE W V hVt yW
  change y^2 = x^3+A*x^2+B₄*x+B₆ ∧ bb^2 = aa^3+A*aa^2+B₄*aa+B₆ ∧
    xt = l^2-A-x-aa ∧ yt = -y+l*(x-xt) at hlocal
  let D := coefficientDerivation p e V
  have hDx : D x = 2*y := by
    change coefficient p e V (res xW) = 2*res yW
    rw [← coefficient_restrict p e W V hVW, hnorm, map_mul, map_ofNat]
  have hnonzero : 2*y ≠ 0 := by
    have hyW : yW ≠ 0 := by
      change q _ ≠ 0
      rw [hqy]
      exact complement_y_nonzero k h3 he M hM s hs X Y hX hY
    have h2 : (2 : Γ(C,W)) ≠ 0 := by
      letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
      have H : IsUnit (2 : Γ(C,W)) := by
        simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
          ((p.constToPresheaf.app (Opposite.op W)).hom)
      exact H.ne_zero
    intro H
    apply mul_ne_zero h2 hyW
    apply map_injective_of_isIntegral C (homOfLE hVW)
    simpa only [map_mul, map_ofNat, map_zero] using H
  have hDA : D A = 0 := D.map_algebraMap _
  have hDB : D B₄ = 0 := D.map_algebraMap _
  have hDC : D B₆ = 0 := D.map_algebraMap _
  have hDa : D aa = 0 := D.map_algebraMap _
  have hDb : D bb = 0 := D.map_algebraMap _
  have hDy := derivative_y_of_equation D A B₄ B₆ x y hlocal.1 hnonzero hDx hDA hDB hDC
  have hd := chord_derivative_of_unit D A B₄ B₆ x y aa bb l hlocal.1 hlocal.2.1 hunit hl
    hDx hDy hDA hDa hDb
  have hDxt : D xt = 2*yt := by
    rw [hlocal.2.2.2, hlocal.2.2.1]
    exact hd
  change coefficient p e (f ⁻¹ᵁ W) (f.app W (W.topIso.hom (complementCoordinate k M s 2 X))) =
    2*f.app W (W.topIso.hom (complementCoordinate k M s 3 Y))
  rw [← hqx, ← hqy]
  apply map_injective_of_isIntegral C (homOfLE hVt)
  rw [coefficient_restrict, map_mul, map_ofNat]
  exact hDxt

end FiniteTranslation

#print axioms translation_over
#print axioms comp_translation
#print axioms translation_one
#print axioms translation_mul
#print axioms translation_isIso
#print axioms identity_chain_rule
#print axioms chord_slope_identity
#print axioms chord_derivative
#print axioms weierstrass_addX_derivative
#print axioms chord_derivative_of_unit
#print axioms coefficientDerivation
#print axioms translationDefect_mul
#print axioms translationDefect_constant
#print axioms chainRule_of_cubic_x
#print axioms actual_chainRule_of_x
#print axioms actual_x_ne_constant

end ArithmeticThetaDifferentialRecoveryR0148.AffineTranslationChainRule

namespace ArithmeticThetaDifferentialRecoveryR0148
open CategoryTheory AlgebraicGeometry
open AffineTranslationChainRule

/-- The normalized actual affine translation chain rule, for every rational point
and every regular function on the fixed complement. -/
theorem affine_translation_chain_rule :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ∀ (p : ArithmeticThetaHodgeFourTorsionR0147.Point k M), ∀ (a : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).presheaf.obj (Opposite.op (ArithmeticThetaCubicModelR0144.complement k M s))), ArithmeticThetaHodgeFourTorsionR0147.frameDerivative k M δ ((TopologicalSpace.Opens.map (ArithmeticThetaHodgeFourTorsionR0147.translation k M G p).base).obj (ArithmeticThetaCubicModelR0144.complement k M s)) ((ArithmeticThetaHodgeFourTorsionR0147.translation k M G p).app (ArithmeticThetaCubicModelR0144.complement k M s) a) = (ArithmeticThetaHodgeFourTorsionR0147.translation k M G p).app (ArithmeticThetaCubicModelR0144.complement k M s) (ArithmeticThetaHodgeFourTorsionR0147.frameDerivative k M δ (ArithmeticThetaCubicModelR0144.complement k M s) a) := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY G hG e heN P a
  by_cases hP : P = G.one (𝟙 _)
  · subst P
    exact identity_chain_rule k M G e (ArithmeticThetaCubicModelR0144.complement k M s) a
  · exact actual_chainRule_of_x k h3 he M hM s hs X Y hX hY G e heN P
      (finite_translation_x k h3 he M hM s hs X Y hX hY G hG e heN P hP) a

#print axioms affine_translation_chain_rule
end ArithmeticThetaDifferentialRecoveryR0148
