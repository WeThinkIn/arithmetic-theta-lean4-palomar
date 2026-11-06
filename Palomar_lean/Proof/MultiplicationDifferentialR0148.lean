module

public import TranslationInvariantDifferentialR0148
public import AffineTranslationChainRuleR0148
public import WeightedAffineExtensionR0148

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaDifferentialRecoveryR0148.AffineTranslationChainRule
open InverseDifferentialSign

section MovingChord
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Differentiating the chord slope with both points moving. -/
lemma moving_chord_slope_derivative (D : Derivation R B B)
    (A B₄ C x y a b l α β : B)
    (hy : y^2 = x^3 + A*x^2 + B₄*x + C)
    (hb : b^2 = a^3 + A*a^2 + B₄*a + C)
    (hu : IsUnit (x-a)) (hl : (x-a)*l = y-b)
    (hDx : D x = α*(2*y)) (hDy : D y = α*(3*x^2 + 2*A*x + B₄))
    (hDa : D a = β*(2*b)) (hDb : D b = β*(3*a^2 + 2*A*a + B₄))
    (hDA : D A = 0) :
    D l = α*(x-(l^2-A-x-a)) + β*(a-(l^2-A-x-a)) := by
  have hx : 3*x^2+2*A*x+B₄-2*y*l = (x-a)*(x-(l^2-A-x-a)) := by
    apply sub_eq_zero.mp
    apply hu.mul_left_cancel
    rw [mul_zero]
    linear_combination -hy + hb + ((x-a)*l-y-b)*hl
  have ha : 3*a^2+2*A*a+B₄-2*b*l = (a-x)*(a-(l^2-A-x-a)) := by
    apply sub_eq_zero.mp
    apply hu.mul_left_cancel
    rw [mul_zero]
    linear_combination -hy + hb + (-(x-a)*l-y-b)*hl
  have hd := congrArg D hl
  rw [D.leibniz, D.map_sub, D.map_sub, hDx, hDa, hDy, hDb] at hd
  simp only [smul_eq_mul] at hd
  have hDl : D l = α*(x-(l^2-A-x-a)) + β*(a-(l^2-A-x-a)) := by
    apply hu.mul_left_cancel
    linear_combination hd + α*hx - β*ha
  exact hDl

/-- The two moving points contribute additively to the normalized differential.
The denominator is a unit on the chord open. -/
lemma moving_chord_derivative (D : Derivation R B B)
    (A B₄ C x y a b l α β : B)
    (hy : y^2 = x^3 + A*x^2 + B₄*x + C)
    (hb : b^2 = a^3 + A*a^2 + B₄*a + C)
    (hu : IsUnit (x-a)) (hl : (x-a)*l = y-b)
    (hDx : D x = α*(2*y)) (hDy : D y = α*(3*x^2 + 2*A*x + B₄))
    (hDa : D a = β*(2*b)) (hDb : D b = β*(3*a^2 + 2*A*a + B₄))
    (hDA : D A = 0) :
    D (l^2-A-x-a) = (α+β)*2*(-y+l*(x-(l^2-A-x-a))) := by
  have hDl := moving_chord_slope_derivative D A B₄ C x y a b l α β
    hy hb hu hl hDx hDy hDa hDb hDA
  rw [D.map_sub, D.map_sub, D.map_sub, D.leibniz_pow, hDA, hDx, hDa, hDl]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  linear_combination -2*β*hl

/-- The Y-coordinate satisfies the same sum-of-weights law, even if the output Y is zero. -/
lemma moving_chord_derivative_y (D : Derivation R B B)
    (A B₄ C x y a b l α β : B)
    (hy : y^2 = x^3+A*x^2+B₄*x+C)
    (hb : b^2 = a^3+A*a^2+B₄*a+C)
    (hu : IsUnit (x-a)) (hl : (x-a)*l = y-b)
    (hDx : D x = α*(2*y)) (hDy : D y = α*(3*x^2+2*A*x+B₄))
    (hDa : D a = β*(2*b)) (hDb : D b = β*(3*a^2+2*A*a+B₄))
    (hDA : D A = 0) :
    D (-y+l*(x-(l^2-A-x-a))) =
      (α+β)*(3*(l^2-A-x-a)^2+2*A*(l^2-A-x-a)+B₄) := by
  have hx : 3*x^2+2*A*x+B₄-2*y*l = (x-a)*(x-(l^2-A-x-a)) := by
    apply sub_eq_zero.mp
    apply hu.mul_left_cancel
    rw [mul_zero]
    linear_combination -hy + hb + ((x-a)*l-y-b)*hl
  have hs := moving_chord_slope_derivative D A B₄ C x y a b l α β
    hy hb hu hl hDx hDy hDa hDb hDA
  have hz := moving_chord_derivative D A B₄ C x y a b l α β
    hy hb hu hl hDx hDy hDa hDb hDA
  rw [map_add, map_neg, D.leibniz, D.map_sub, hDy, hDx, hs, hz]
  simp only [smul_eq_mul]
  linear_combination -(2*α+β)*hx

/-- A weighted X derivative determines the Y derivative away from two-torsion. -/
lemma weighted_derivative_y [IsDomain B] (D : Derivation R B B)
    (A B₄ C x y α : B) (hy : y^2 = x^3+A*x^2+B₄*x+C)
    (h2y : 2*y ≠ 0) (hDx : D x = α*(2*y))
    (hDA : D A = 0) (hDB : D B₄ = 0) (hDC : D C = 0) :
    D y = α*(3*x^2+2*A*x+B₄) := by
  have H := congrArg D hy
  simp only [map_add, D.leibniz, D.leibniz_pow, hDA, hDB, hDC, hDx,
    smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one, mul_zero, zero_mul, add_zero] at H
  apply mul_left_cancel₀ h2y
  linear_combination H

/-- Tangent addition doubles the differential weight; the denominator is 2Y. -/
lemma tangent_derivative (D : Derivation R B B)
    (A B₄ C x y l α : B)
    (hy : y^2 = x^3+A*x^2+B₄*x+C)
    (hu : IsUnit (2*y)) (hl : (2*y)*l = 3*x^2+2*A*x+B₄)
    (hDx : D x = α*(2*y)) (hDy : D y = α*(3*x^2+2*A*x+B₄))
    (hDA : D A = 0) (hDB : D B₄ = 0) :
    D (l^2-A-x-x) = (α+α)*2*(-y+l*(x-(l^2-A-x-x))) := by
  have hD2 : D (2 : B) = 0 := by simpa using D.map_natCast 2
  have hD3 : D (3 : B) = 0 := by simpa using D.map_natCast 3
  have hd := congrArg D hl
  simp only [D.leibniz, map_add, D.leibniz_pow, hDx, hDy, hDA, hDB,
    hD2, hD3, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one,
    mul_zero, zero_mul, add_zero, zero_add] at hd
  have hDl : D l = α*(6*x+2*A-2*l^2) := by
    apply hu.mul_left_cancel
    linear_combination hd + 2*α*l*hl
  rw [D.map_sub, D.map_sub, D.map_sub, D.leibniz_pow, hDA, hDx, hDl]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  ring
/-- The tangent Y formula is valid without inverting the output Y-coordinate. -/
lemma tangent_derivative_y (D : Derivation R B B)
    (A B₄ C x y l α : B)
    (hy : y^2 = x^3+A*x^2+B₄*x+C)
    (hu : IsUnit (2*y)) (hl : (2*y)*l = 3*x^2+2*A*x+B₄)
    (hDx : D x = α*(2*y)) (hDy : D y = α*(3*x^2+2*A*x+B₄))
    (hDA : D A = 0) (hDB : D B₄ = 0) :
    D (-y+l*(x-(l^2-A-x-x))) =
      (α+α)*(3*(l^2-A-x-x)^2+2*A*(l^2-A-x-x)+B₄) := by
  have hD2 : D (2 : B) = 0 := by simpa using D.map_natCast 2
  have hD3 : D (3 : B) = 0 := by simpa using D.map_natCast 3
  have hd := congrArg D hl
  simp only [D.leibniz, map_add, D.leibniz_pow, hDx, hDy, hDA, hDB,
    hD2, hD3, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one,
    mul_zero, zero_mul, add_zero, zero_add] at hd
  have hs : D l = α*(6*x+2*A-2*l^2) := by
    apply hu.mul_left_cancel
    linear_combination hd + 2*α*l*hl
  have hz := tangent_derivative D A B₄ C x y l α hy hu hl hDx hDy hDA hDB
  rw [map_add, map_neg, D.leibniz, D.map_sub, hDy, hDx, hs, hz]
  simp only [smul_eq_mul]
  linear_combination 3*α*hl

end MovingChord

section FractionDerivation
variable {R B K : Type u} [CommRing R] [CommRing B] [CommRing K]
variable [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]
variable [Algebra.FormallyEtale B K]

/-- Extend the actual coefficient derivation through an étale localization. -/
def extendDerivation (D : Derivation R B B) : Derivation R K K :=
  let d := (Algebra.linearMap B K).compDer D
  let L := (LinearMap.liftBaseChange K d.liftKaehlerDifferential).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B K).symm.toLinearMap
  L.compDer (KaehlerDifferential.D R K)

lemma extendDerivation_algebraMap (D : Derivation R B B) (b : B) :
    extendDerivation (K := K) D (algebraMap B K b) = algebraMap B K (D b) := by
  change (LinearMap.liftBaseChange K ((Algebra.linearMap B K).compDer D).liftKaehlerDifferential)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B K).symm
      (KaehlerDifferential.D R K (algebraMap B K b))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]
  simp only [one_smul]
  rfl
end FractionDerivation

section RationalCompatibility
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
variable {F : Type u} [CommRing F] {C : Scheme.{u}} [IsIntegral C]
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable [Algebra F C.functionField]

/-- Agreement on a nonempty affine chart forces agreement with the actual
coefficient derivation on every nonempty open. -/
lemma derivation_germ_compatibility (D : Derivation F C.functionField C.functionField)
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hD : ∀ a : Γ(C,W), D (C.germToFunctionField W a) =
      C.germToFunctionField W (coefficient p e W a))
    (U : C.Opens) [Nonempty U] (a : Γ(C,U)) :
    D (C.germToFunctionField U a) = C.germToFunctionField U (coefficient p e U a) := by
  let V := U ⊓ W
  letI : Nonempty V := nonempty_inter U W
  obtain ⟨b,c,hc,heq⟩ := section_fraction W hW U a
  have eqg : C.germToFunctionField U a * C.germToFunctionField W c =
      C.germToFunctionField W b := by
    have H := congrArg (C.germToFunctionField V) heq
    simpa only [V, map_mul, Scheme.germToFunctionField, C.presheaf.germ_res_apply] using H
  have eqd : C.germToFunctionField U a * C.germToFunctionField W (coefficient p e W c) +
      C.germToFunctionField W c * C.germToFunctionField U (coefficient p e U a) =
      C.germToFunctionField W (coefficient p e W b) := by
    have H := congrArg (fun z => C.germToFunctionField V (coefficient p e V z)) heq
    rw [coefficient_mul, ← coefficient_restrict, ← coefficient_restrict,
      ← coefficient_restrict, map_add, map_mul, map_mul] at H
    simpa only [V, Scheme.germToFunctionField, C.presheaf.germ_res_apply] using H
  have H := congrArg D eqg
  rw [D.leibniz, hD b, hD c] at H
  simp only [smul_eq_mul] at H
  have hcg : C.germToFunctionField W c ≠ 0 := by
    intro hz
    exact hc (C.germToFunctionField_injective W (hz.trans (map_zero _).symm))
  apply mul_left_cancel₀ hcg
  linear_combination H - eqd
end RationalCompatibility

section RationalFrame
variable {F : Type u} [CommRing F] {C : Scheme.{u}} [IsIntegral C]
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)

/-- The base action on the function field comes from the actual structure map. -/
def rationalBaseAlgebra (W : C.Opens) [Nonempty W] : Algebra F C.functionField :=
  ((C.germToFunctionField W).hom.comp
    (p.constToPresheaf.app (Opposite.op W)).hom).toAlgebra

lemma exists_rational_derivation (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    letI := rationalBaseAlgebra p W
    ∃ D : Derivation F C.functionField C.functionField,
      ∀ (U : C.Opens) [Nonempty U] (a : Γ(C,U)),
      D (C.germToFunctionField U a) = C.germToFunctionField U (coefficient p e U a) := by
  letI := p.sectionsAlgebra W
  letI := rationalBaseAlgebra p W
  letI : IsScalarTower F Γ(C,W) C.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI := functionField_isFractionRing_of_isAffineOpen C W hW
  letI : Algebra.FormallyEtale Γ(C,W) C.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(C,W))
  let D := extendDerivation (K := C.functionField) (coefficientDerivation p e W)
  have hD (a : Γ(C,W)) : D (C.germToFunctionField W a) =
      C.germToFunctionField W (coefficient p e W a) :=
    extendDerivation_algebraMap (coefficientDerivation p e W) a
  exact ⟨D, fun U _ a => derivation_germ_compatibility p e D W hW hD U a⟩

lemma rational_point_structure (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    letI := rationalBaseAlgebra p W
    C.fromSpecStalk (_root_.genericPoint C) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F C.functionField)) := by
  let hx : _root_.genericPoint C ∈ W :=
    ((_root_.genericPoint_spec C).mem_open_set_iff W.isOpen).mpr (by simpa using (inferInstance : Nonempty W))
  rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
  change (Spec.map (C.germToFunctionField W) ≫ hW.fromSpec) ≫ p = _
  rw [Category.assoc, affine_structural W p hW, ← Spec.map_comp]
  rfl

lemma rational_germ_constant (W U : C.Opens) [Nonempty W] [Nonempty U] (c : F) :
    letI := rationalBaseAlgebra p W
    C.germToFunctionField U ((p.constToPresheaf.app (Opposite.op U)).hom c) =
      algebraMap F C.functionField c := by
  let V := U ⊓ W
  letI : Nonempty V :=
    ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.nonempty_inter U W
  have hU := congrArg (C.germToFunctionField V) (constant_restrict U p V inf_le_left c)
  have hW := congrArg (C.germToFunctionField V) (constant_restrict W p V inf_le_right c)
  simp only [Scheme.germToFunctionField, C.presheaf.germ_res_apply] at hU hW
  exact hU.trans hW.symm

/-- Equality of germs is preserved by the actual frame coefficient derivation. -/
lemma coefficient_germ_eq (x : C) (U V : C.Opens) (hU : x ∈ U) (hV : x ∈ V)
    (a : Γ(C,U)) (b : Γ(C,V))
    (hab : C.presheaf.germ U x hU a = C.presheaf.germ V x hV b) :
    C.presheaf.germ U x hU (coefficient p e U a) =
      C.presheaf.germ V x hV (coefficient p e V b) := by
  obtain ⟨Z,hZ,i,j,h⟩ := C.presheaf.germ_eq x hU hV a b hab
  have H := congrArg (fun z => C.presheaf.germ Z x hZ (coefficient p e Z z)) h
  have hi : i = homOfLE i.le := Subsingleton.elim _ _
  have hj : j = homOfLE j.le := Subsingleton.elim _ _
  rw [hi, hj] at H
  rw [← coefficient_restrict p e U Z i.le, ← coefficient_restrict p e V Z j.le] at H
  simpa only [C.presheaf.germ_res_apply] using H

/-- Differentiate a product relation between germs represented on different opens. -/
lemma coefficient_germ_product (x : C) (U W : C.Opens) (hxU : x ∈ U) (hxW : x ∈ W)
    (a : Γ(C,U)) (b c : Γ(C,W))
    (h : C.presheaf.germ U x hxU a * C.presheaf.germ W x hxW c =
      C.presheaf.germ W x hxW b) :
    C.presheaf.germ U x hxU a * C.presheaf.germ W x hxW (coefficient p e W c) +
      C.presheaf.germ W x hxW c * C.presheaf.germ U x hxU (coefficient p e U a) =
      C.presheaf.germ W x hxW (coefficient p e W b) := by
  let V := U ⊓ W
  have hxV : x ∈ V := ⟨hxU,hxW⟩
  let ra := C.presheaf.map (homOfLE (show V ≤ U from inf_le_left)).op a
  let rc := C.presheaf.map (homOfLE (show V ≤ W from inf_le_right)).op c
  have H : C.presheaf.germ V x hxV (ra*rc) = C.presheaf.germ W x hxW b := by
    simpa only [ra, rc, map_mul, C.presheaf.germ_res_apply] using h
  have H' := coefficient_germ_eq p e x V W hxV hxW (ra*rc) b H
  rw [coefficient_mul] at H'
  dsimp only [ra, rc] at H'
  rw [← coefficient_restrict, ← coefficient_restrict, map_add, map_mul, map_mul] at H'
  simpa only [C.presheaf.germ_res_apply] using H'

/-- A weighted chain rule at a field-valued point extends from one affine
neighborhood to every neighborhood, without assuming the point is generic. -/
lemma chain_rule_at_point_of_affine {K : Type u} [Field K] [Algebra F K]
    (x : C) (φ : C.presheaf.stalk x →+* K) (D : Derivation F K K) (weight : K)
    (W : C.Opens) (hW : IsAffineOpen W) (hxW : x ∈ W)
    (hD : ∀ b : Γ(C,W), D (φ (C.presheaf.germ W x hxW b)) =
      weight * φ (C.presheaf.germ W x hxW (coefficient p e W b)))
    (U : C.Opens) (hxU : x ∈ U) (a : Γ(C,U)) :
    D (φ (C.presheaf.germ U x hxU a)) =
      weight * φ (C.presheaf.germ U x hxU (coefficient p e U a)) := by
  letI := C.presheaf.algebra_section_stalk ⟨x,hxW⟩
  letI := hW.isLocalization_stalk ⟨x,hxW⟩
  obtain ⟨⟨b,c⟩,hbc⟩ := IsLocalization.surj (hW.primeIdealOf ⟨x,hxW⟩).asIdeal.primeCompl
    (C.presheaf.germ U x hxU a)
  change C.presheaf.germ U x hxU a * C.presheaf.germ W x hxW c =
    C.presheaf.germ W x hxW b at hbc
  have hc : φ (C.presheaf.germ W x hxW c) ≠ 0 := by
    have hu := IsLocalization.map_units (C.presheaf.stalk x) c
    exact (hu.map φ).ne_zero
  have H := congrArg D (congrArg φ hbc)
  rw [map_mul, D.leibniz, hD b, hD c] at H
  simp only [smul_eq_mul] at H
  have H' := congrArg φ (coefficient_germ_product p e x U W hxU hxW a b c hbc)
  simp only [map_add, map_mul] at H'
  apply mul_left_cancel₀ hc
  linear_combination H - weight*H'

/-- All-open extension for natural-number weights. Only the inverse image of
the chosen chart must be nonempty; the morphism need not be invertible. -/
lemma nat_chain_rule_of_affine (f : C ⟶ C) (n : ℕ)
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W] [Nonempty (f ⁻¹ᵁ W : C.Opens)]
    (hchain : ∀ b : Γ(C,W), coefficient p e (f ⁻¹ᵁ W) (f.app W b) =
      (n : Γ(C,f ⁻¹ᵁ W))*f.app W (coefficient p e W b)) :
    ∀ (U : C.Opens) (a : Γ(C,U)),
      coefficient p e (f ⁻¹ᵁ U) (f.app U a) =
        (n : Γ(C,f ⁻¹ᵁ U))*f.app U (coefficient p e U a) := by
  letI := rationalBaseAlgebra p W
  obtain ⟨D,hD⟩ := exists_rational_derivation p e W hW
  let η := _root_.genericPoint C
  let x := f η
  let φ : C.presheaf.stalk x →+* C.functionField := (f.stalkMap η).hom
  have hx (U : C.Opens) [Nonempty (f ⁻¹ᵁ U : C.Opens)] : x ∈ U :=
    ((_root_.genericPoint_spec C).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ U : C.Opens)))
  have heval (U : C.Opens) [Nonempty (f ⁻¹ᵁ U : C.Opens)] (a : Γ(C,U)) :
      φ (C.presheaf.germ U x (hx U) a) = C.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) := by
    exact ConcreteCategory.congr_hom (Scheme.Hom.germ_stalkMap f U η (hx U)) a
  have hDW (b : Γ(C,W)) : D (φ (C.presheaf.germ W x (hx W) b)) =
      (n : C.functionField)*φ (C.presheaf.germ W x (hx W) (coefficient p e W b)) := by
    rw [heval, heval, hD, hchain, map_mul, map_natCast]
  intro U a
  by_cases hu : Nonempty (f ⁻¹ᵁ U : C.Opens)
  · letI := hu
    apply C.germToFunctionField_injective (f ⁻¹ᵁ U)
    rw [map_mul, map_natCast, ← hD]
    have H := chain_rule_at_point_of_affine p e x φ D (n : C.functionField)
      W hW (hx W) hDW U (hx U) a
    simpa only [heval] using H
  · have hu' : f ⁻¹ᵁ U = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => hu ⟨⟨x,hx⟩⟩)
    letI : Subsingleton Γ(C,f ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hu')
    exact Subsingleton.elim _ _

/-- The generic point in a target chart is given by the actual pullback on
sections followed by the source germ. No dominance is assumed. -/
lemma generic_chart_factor {B : Type u} [CommRing B] {Y : Scheme.{u}}
    (U : C.Opens) (hU : IsAffineOpen U) (E : U.toScheme ≅ Spec (CommRingCat.of B))
    (j : Spec (CommRingCat.of B) ⟶ Y) (g : C ⟶ Y)
    (hg : U.ι ≫ g = E.hom ≫ j) (f : C ⟶ C) [Nonempty (f ⁻¹ᵁ U : C.Opens)] :
    Spec.map (CommRingCat.ofHom ((C.germToFunctionField (f ⁻¹ᵁ U)).hom.comp
      ((f.app U).hom.comp (chartSections U E)))) ≫ j =
      C.fromSpecStalk (_root_.genericPoint C) ≫ f ≫ g := by
  let x := _root_.genericPoint C
  have hx : f x ∈ U := ((_root_.genericPoint_spec C).mem_open_set_iff
    (f ⁻¹ᵁ U).isOpen).mpr (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ U : C.Opens)))
  have hh := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx] at hh
  unfold IsAffineOpen.fromSpecStalk at hh
  rw [← Category.assoc, ← Spec.map_comp, Scheme.Hom.germ_stalkMap] at hh
  change Spec.map (CommRingCat.ofHom (chartSections U E) ≫ f.app U ≫
    C.germToFunctionField (f ⁻¹ᵁ U)) ≫ j = _
  rw [Spec.map_comp, chartSections_spec U hU E]
  simp only [Category.assoc]
  rw [← hg, ← Category.assoc hU.isoSpec.inv, IsAffineOpen.isoSpec_inv_ι]
  rw [← Category.assoc, hh]
  exact Category.assoc _ _ _
lemma generic_chart_factor_id {B : Type u} [CommRing B] {Y : Scheme.{u}}
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (E : U.toScheme ≅ Spec (CommRingCat.of B))
    (j : Spec (CommRingCat.of B) ⟶ Y) (g : C ⟶ Y)
    (hg : U.ι ≫ g = E.hom ≫ j) :
    C.fromSpecStalk (_root_.genericPoint C) ≫ g =
      Spec.map (CommRingCat.ofHom ((C.germToFunctionField U).hom.comp (chartSections U E))) ≫ j := by
  letI : Nonempty ((𝟙 C) ⁻¹ᵁ U : C.Opens) := by
    simpa only [Scheme.Hom.id_preimage] using (inferInstance : Nonempty U)
  have H := generic_chart_factor U hU E j g hg (𝟙 C)
  simpa only [Category.id_comp, Scheme.Hom.id_app, CommRingCat.hom_id,
    RingHom.id_comp, Category.comp_id, Scheme.Hom.id_preimage] using H.symm
end RationalFrame

section NoninvertibleExtension
open ArithmeticThetaDifferentialRecoveryR0148.WeightedAffineExtension
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
variable {F : Type u} [CommRing F] {C : Scheme.{u}} [IsIntegral C]
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable (f : C ⟶ C) (c : F)

/-- The fraction argument does not require an automorphism: nonempty inverse
images and injectivity of section pullbacks suffice. These conditions must be
proved for the actual multiplication map before this lemma can be applied. -/
lemma weighted_extension_of_injective
    (hne : ∀ (U : C.Opens), Nonempty U → Nonempty (f ⁻¹ᵁ U : C.Opens))
    (hinj : ∀ (U : C.Opens), Function.Injective (f.app U))
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hzero : ∀ a, weightedDefect p e f c W a = 0) :
    ∀ (U : C.Opens) (a : Γ(C,U)), weightedDefect p e f c U a = 0 := by
  intro U a
  by_cases hU : Nonempty U
  · letI := hU
    let V := U ⊓ W
    letI : Nonempty V := nonempty_inter U W
    letI : Nonempty (f ⁻¹ᵁ V : C.Opens) := hne V inferInstance
    apply map_injective_of_isIntegral C
      (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => hx.1))
    rw [map_zero, weightedDefect_restrict p e f c U V inf_le_left]
    obtain ⟨b,d,hd,heq⟩ := section_fraction W hW U a
    let res := C.presheaf.map (homOfLE (show V ≤ W from inf_le_right)).op
    have hz (z : Γ(C,W)) : weightedDefect p e f c V (res z) = 0 := by
      rw [← weightedDefect_restrict, hzero, map_zero]
    have hh := congrArg (weightedDefect p e f c V) heq
    rw [weightedDefect_mul, hz b, hz d, mul_zero, zero_add] at hh
    apply (mul_eq_zero.mp hh).resolve_left
    have hr : res d ≠ 0 := by
      intro H
      apply hd
      exact map_injective_of_isIntegral C (homOfLE (show V ≤ W from inf_le_right))
        (H.trans (map_zero res.hom).symm)
    intro H
    apply hr
    exact hinj V (H.trans (map_zero (f.app V).hom).symm)
  · have hv : f ⁻¹ᵁ U = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => hU ⟨⟨f x,hx⟩⟩)
    letI : Subsingleton Γ(C,f ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hv)
    exact Subsingleton.elim _ _
end NoninvertibleExtension

section EvaluationNaturality
open NeronModelInfra ArithmeticThetaCompactifiedDifferentialR0145
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
variable (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
variable (F : Type u) [Field F] [DecidableEq F] [Algebra (LaurentSeries k) F]

include hev

lemma evaluation_one : ev F (G.one (extensionBase k F)) = 0 := by
  have H := hev.1.1 F (G.one (extensionBase k F)) (G.one (extensionBase k F))
  change ev F (G.mul (extensionBase k F) (G.one _) (G.one _)) = _ at H
  rw [G.one_mul] at H
  exact (add_left_cancel (a := ev F (G.one (extensionBase k F)))
    ((add_zero _).trans H)).symm

lemma evaluation_nsmul
    (P : SchemeHomOver (extensionBase k F) (projectiveStructure k r)) (n : ℕ) :
    ev F (G.nsmul (extensionBase k F) n P) = n • ev F P := by
  induction n with
  | zero => simpa only [G.nsmul_zero, zero_smul] using evaluation_one k r G ev hev F
  | succ n ih =>
    rw [G.nsmul_succ]
    have H := hev.1.1 F (G.nsmul (extensionBase k F) n P) P
    change ev F (G.mul (extensionBase k F) (G.nsmul (extensionBase k F) n P) P) =
      ev F (G.nsmul (extensionBase k F) n P) + ev F P at H
    rw [H, ih, succ_nsmul]
end EvaluationNaturality

section FieldPoints
variable {R F : Type u} [CommRing R] [Field F] [Algebra R F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F) (D : Derivation R F F)

/-- The normalized velocity is specified by both actual coordinate derivatives.
At the identity it is zero. -/
def HasVelocity (α : F) : W.Point → Prop
  | .zero => α = 0
  | .some x y _ => D x = α*(2*y) ∧ D y = α*(3*x^2+2*W.a₂*x+W.a₄)

lemma short_addX (h1 : W.a₁ = 0) (x a l : F) :
    W.addX x a l = l^2-W.a₂-x-a := by
  simp [WeierstrassCurve.Affine.addX, h1]

lemma short_addY (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (x a y l : F) :
    W.addY x a y l = -y+l*(x-(l^2-W.a₂-x-a)) := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, short_addX W h1, h1, h3]
  ring

lemma velocity_add (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (hDA : D W.a₂ = 0) (hDB : D W.a₄ = 0)
    (P Q : W.Point) (α β : F)
    (hP : HasVelocity W D α P) (hQ : HasVelocity W D β Q) :
    HasVelocity W D (α+β) (P+Q) := by
  cases P with
  | zero =>
    change α = 0 at hP
    subst α
    change HasVelocity W D (0+β) ((0 : W.Point)+Q)
    simpa using hQ
  | some x y hp =>
    cases Q with
    | zero =>
      change β = 0 at hQ
      subst β
      change HasVelocity W D (α+0) ((.some x y hp : W.Point)+0)
      simpa using hP
    | some a b hq =>
      change D x = α*(2*y) ∧ D y = α*(3*x^2+2*W.a₂*x+W.a₄) at hP
      change D a = β*(2*b) ∧ D b = β*(3*a^2+2*W.a₂*a+W.a₄) at hQ
      have hy : y^2 = x^3+W.a₂*x^2+W.a₄*x+W.a₆ := by
        simpa only [WeierstrassCurve.Affine.equation_iff, h1, h3, zero_mul, add_zero] using hp.1
      have hb : b^2 = a^3+W.a₂*a^2+W.a₄*a+W.a₆ := by
        simpa only [WeierstrassCurve.Affine.equation_iff, h1, h3, zero_mul, add_zero] using hq.1
      by_cases hxa : x = a
      · subst a
        by_cases hinv : y = W.negY x b
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hinv]
          change α+β = 0
          have hib : y = -b := by simpa [WeierstrassCurve.Affine.negY, h1, h3] using hinv
          have hd : (α+β)*(2*y) = 0 := by linear_combination -hP.1 + hQ.1 + 2*β*hib
          by_cases h2y : 2*y = 0
          · have hf : 3*x^2+2*W.a₂*x+W.a₄ ≠ 0 := by
              have hn := (WeierstrassCurve.Affine.nonsingular_iff' ..).mp hp
              simpa only [h1, h3, zero_mul, zero_add, add_zero, h2y,
                ne_eq, not_true_eq_false, or_false, neg_ne_zero, zero_sub] using hn.2
            have hd' : (α+β)*(3*x^2+2*W.a₂*x+W.a₄) = 0 := by
              have he := congrArg D hib
              rw [map_neg] at he
              linear_combination -hP.2 - hQ.2 + he
            exact (mul_eq_zero.mp hd').resolve_right hf
          · exact (mul_eq_zero.mp hd).resolve_right h2y
        · have heq : y = b := WeierstrassCurve.Affine.Y_eq_of_Y_ne hp.1 hq.1 rfl hinv
          subst b
          have h2y : 2*y ≠ 0 := by
            intro heq
            apply hinv
            simp only [WeierstrassCurve.Affine.negY, h1, h3, zero_mul, sub_zero]
            linear_combination heq
          have hab : α = β := mul_right_cancel₀ h2y (hP.1.symm.trans hQ.1)
          subst β
          rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hinv]
          change D (W.addX x x (W.slope x x y y)) = _ ∧
            D (W.addY x x y (W.slope x x y y)) = _
          have hs : W.slope x x y y = (3*x^2+2*W.a₂*x+W.a₄)/(2*y) := by
            simp [WeierstrassCurve.Affine.slope_of_Y_ne rfl hinv, h1, h3, two_mul]
          rw [hs, short_addX W h1, short_addY W h1 h3]
          have hl : (2*y)*((3*x^2+2*W.a₂*x+W.a₄)/(2*y)) = 3*x^2+2*W.a₂*x+W.a₄ :=
            mul_div_cancel₀ _ h2y
          constructor
          · simpa only [mul_assoc] using tangent_derivative D W.a₂ W.a₄ W.a₆ x y _ α hy
              (isUnit_iff_ne_zero.mpr h2y) hl hP.1 hP.2 hDA hDB
          · exact tangent_derivative_y D W.a₂ W.a₄ W.a₆ x y _ α hy
              (isUnit_iff_ne_zero.mpr h2y) hl hP.1 hP.2 hDA hDB
      · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxa]
        change D (W.addX x a (W.slope x a y b)) = _ ∧
          D (W.addY x a y (W.slope x a y b)) = _
        rw [WeierstrassCurve.Affine.slope_of_X_ne hxa, short_addX W h1, short_addY W h1 h3]
        have hu : IsUnit (x-a) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxa)
        have hl : (x-a)*((y-b)/(x-a)) = y-b := mul_div_cancel₀ _ (sub_ne_zero.mpr hxa)
        constructor
        · simpa only [mul_assoc] using moving_chord_derivative D W.a₂ W.a₄ W.a₆ x y a b _ α β hy hb hu hl
            hP.1 hP.2 hQ.1 hQ.2 hDA
        · exact moving_chord_derivative_y D W.a₂ W.a₄ W.a₆ x y a b _ α β hy hb hu hl
            hP.1 hP.2 hQ.1 hQ.2 hDA

lemma velocity_unique (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (P : W.Point) (α β : F) (hP : HasVelocity W D α P) (hQ : HasVelocity W D β P) :
    α = β := by
  cases P with
  | zero => exact hP.trans hQ.symm
  | some x y hp =>
    change D x = α*(2*y) ∧ D y = α*(3*x^2+2*W.a₂*x+W.a₄) at hP
    change D x = β*(2*y) ∧ D y = β*(3*x^2+2*W.a₂*x+W.a₄) at hQ
    have hn : 3*x^2+2*W.a₂*x+W.a₄ ≠ 0 ∨ 2*y ≠ 0 := by
      have H := (WeierstrassCurve.Affine.nonsingular_iff' ..).mp hp
      simpa only [h1, h3, zero_mul, zero_add, add_zero, zero_sub, neg_ne_zero] using H.2
    rcases hn with hn | hn
    · exact mul_right_cancel₀ hn (hP.2.symm.trans hQ.2)
    · exact mul_right_cancel₀ hn (hP.1.symm.trans hQ.1)

/-- The complete field-point multiplication law, including the identity and all exceptional sums. -/
lemma velocity_nsmul (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (hDA : D W.a₂ = 0) (hDB : D W.a₄ = 0)
    (P : W.Point) (α : F) (hP : HasVelocity W D α P) (n : ℕ) :
    HasVelocity W D ((n : F)*α) (n • P) := by
  induction n with
  | zero =>
    simp only [zero_smul, Nat.cast_zero, zero_mul]
    rfl
  | succ n ih =>
    rw [succ_nsmul, Nat.cast_succ, add_mul, one_mul]
    exact velocity_add W D h1 h3 hDA hDB (n • P) P _ α ih hP

lemma nsmul_ne_zero_of_velocity_one [CharZero F]
    (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (hDA : D W.a₂ = 0) (hDB : D W.a₄ = 0)
    (P : W.Point) (hP : HasVelocity W D 1 P) (n : ℕ) (hn : 0 < n) :
    n • P ≠ 0 := by
  intro he
  have H := velocity_nsmul W D h1 h3 hDA hDB P 1 hP n
  rw [he, mul_one] at H
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) H
end FieldPoints

section ChartVelocity
open NeronModelInfra ArithmeticThetaCompactifiedDifferentialR0145
open WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
variable (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
variable (K : Type u) [Field K] [DecidableEq K] [Algebra (LaurentSeries k) K]
include hev

lemma chart_point_velocity (D : Derivation (LaurentSeries k) K K)
    (P : SchemeHomOver (extensionBase k K) (projectiveStructure k r))
    (χ : ChartRing k r →+* K)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r)
    (hx : D (χ (xOverZ (curve k r).toProjective)) = 2*χ (yOverZ (curve k r).toProjective))
    (hy : 2*χ (yOverZ (curve k r).toProjective) ≠ 0) :
    HasVelocity ((curve k r).toProjective.baseChange K).toAffine D 1 (ev K P) := by
  obtain ⟨hxy,heq⟩ := hev.2 K P χ hP
  rw [heq]
  change D (χ (xOverZ (curve k r).toProjective)) = 1*(2*χ (yOverZ (curve k r).toProjective)) ∧ _
  refine ⟨by simpa only [one_mul] using hx, ?_⟩
  have eqc := ring_chart_equation k r G ev hev K P χ hP
  have hd := weighted_derivative_y D
    (algebraMap (LaurentSeries k) K (curve k r).a₂)
    (algebraMap (LaurentSeries k) K (curve k r).a₄)
    (algebraMap (LaurentSeries k) K (curve k r).a₆)
    (χ (xOverZ (curve k r).toProjective)) (χ (yOverZ (curve k r).toProjective)) 1
    eqc hy (by simpa only [one_mul] using hx)
    (D.map_algebraMap _) (D.map_algebraMap _) (D.map_algebraMap _)
  exact hd
lemma chart_velocity_coordinates (D : Derivation (LaurentSeries k) K K)
    (P : SchemeHomOver (extensionBase k K) (projectiveStructure k r))
    (χ : ChartRing k r →+* K)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r)
    (weight : K)
    (hvel : HasVelocity ((curve k r).toProjective.baseChange K).toAffine D weight (ev K P)) :
    D (χ (xOverZ (curve k r).toProjective)) = weight*(2*χ (yOverZ (curve k r).toProjective)) ∧
    D (χ (yOverZ (curve k r).toProjective)) = weight*
      (3*(χ (xOverZ (curve k r).toProjective))^2 +
        2*(algebraMap (LaurentSeries k) K (curve k r).a₂)*χ (xOverZ (curve k r).toProjective) +
        algebraMap (LaurentSeries k) K (curve k r).a₄) := by
  obtain ⟨hp,heq⟩ := hev.2 K P χ hP
  rw [heq] at hvel
  exact hvel
end ChartVelocity

section GenericPointVelocity
open NeronModelInfra ArithmeticThetaCompactifiedDifferentialR0145
open WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} [IsIntegral C]
variable (p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable [Algebra (LaurentSeries k) C.functionField] [DecidableEq C.functionField]

lemma generic_point_velocity (D : Derivation (LaurentSeries k) C.functionField C.functionField)
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (E₀ : W.toScheme ≅ Spec (CommRingCat.of (ChartRing k r)))
    (g : C ⟶ projectiveCurve k r) (hg : W.ι ≫ g = E₀.hom ≫ chartInclusion k r)
    (hD : ∀ a : Γ(C,W), D (C.germToFunctionField W a) =
      C.germToFunctionField W (coefficient p e W a))
    (hnorm : coefficient p e W (chartSections W E₀ (xOverZ (curve k r).toProjective)) =
      2*chartSections W E₀ (yOverZ (curve k r).toProjective))
    (hy : chartSections W E₀ (yOverZ (curve k r).toProjective) ≠ 0)
    (H : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r H ev)
    (P : SchemeHomOver (extensionBase k C.functionField) (projectiveStructure k r))
    (hP : P.val = C.fromSpecStalk (_root_.genericPoint C) ≫ g) :
    HasVelocity ((curve k r).toProjective.baseChange C.functionField).toAffine D 1 (ev C.functionField P) := by
  let χ : ChartRing k r →+* C.functionField := (C.germToFunctionField W).hom.comp (chartSections W E₀)
  have hfac : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r := by
    rw [hP]
    letI : Nonempty ((𝟙 C) ⁻¹ᵁ W : C.Opens) := by simpa only [Scheme.Hom.id_preimage] using (inferInstance : Nonempty W)
    have H := generic_chart_factor W hW E₀ (chartInclusion k r) g hg (𝟙 C)
    simpa only [Category.id_comp, Scheme.Hom.id_app, CommRingCat.hom_id,
      RingHom.id_comp, Category.comp_id, Scheme.Hom.id_preimage] using H.symm
  apply chart_point_velocity k r H ev hev C.functionField D P χ hfac
  · change D (C.germToFunctionField W (chartSections W E₀ _)) = _
    rw [hD, hnorm, map_mul, map_ofNat]
    rfl
  · have h2 : (2 : C.functionField) ≠ 0 := by
      letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
      letI : CharZero C.functionField := Algebra.charZero_of_charZero (LaurentSeries k) C.functionField
      exact two_ne_zero
    apply mul_ne_zero h2
    intro hh
    exact hy (C.germToFunctionField_injective W (hh.trans (map_zero _).symm))
end GenericPointVelocity

section VelocityToSections
variable {F : Type u} [CommRing F] {C : Scheme.{u}} [IsIntegral C]
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)

lemma velocity_to_sections (f : C ⟶ C) (hf : f ≫ p = p) (n : ℕ)
    (W : C.Opens) [Nonempty W] [Nonempty (f ⁻¹ᵁ W : C.Opens)]
    (x y : Γ(C,W)) (A B : F)
    (hnorm : coefficient p e W x = 2*y) :
    letI := rationalBaseAlgebra p W
    ∀ (D : Derivation F C.functionField C.functionField),
    (∀ (U : C.Opens) [Nonempty U] (a : Γ(C,U)),
      D (C.germToFunctionField U a) = C.germToFunctionField U (coefficient p e U a)) →
    D (C.germToFunctionField W y) =
      3*(C.germToFunctionField W x)^2 + 2*algebraMap F C.functionField A*C.germToFunctionField W x +
        algebraMap F C.functionField B →
    D (C.germToFunctionField (f ⁻¹ᵁ W) (f.app W x)) =
      (n : C.functionField)*(2*C.germToFunctionField (f ⁻¹ᵁ W) (f.app W y)) →
    D (C.germToFunctionField (f ⁻¹ᵁ W) (f.app W y)) =
      (n : C.functionField)*(3*(C.germToFunctionField (f ⁻¹ᵁ W) (f.app W x))^2 +
        2*algebraMap F C.functionField A*C.germToFunctionField (f ⁻¹ᵁ W) (f.app W x) +
        algebraMap F C.functionField B) →
    (coefficient p e (f ⁻¹ᵁ W) (f.app W x) =
      (n : Γ(C,f ⁻¹ᵁ W))*f.app W (coefficient p e W x)) ∧
    (coefficient p e (f ⁻¹ᵁ W) (f.app W y) =
      (n : Γ(C,f ⁻¹ᵁ W))*f.app W (coefficient p e W y)) := by
  letI := rationalBaseAlgebra p W
  intro D hD hdy hnx hny
  have hy : coefficient p e W y = 3*x^2 +
      2*(p.constToPresheaf.app (Opposite.op W)).hom A*x +
      (p.constToPresheaf.app (Opposite.op W)).hom B := by
    apply C.germToFunctionField_injective W
    rw [← hD, hdy]
    simp only [map_add, map_mul, map_pow, map_ofNat, rational_germ_constant p W W]
  constructor
  · apply C.germToFunctionField_injective (f ⁻¹ᵁ W)
    rw [← hD, hnx, hnorm, map_mul, map_natCast, map_mul, map_ofNat, map_mul, map_ofNat]
  · apply C.germToFunctionField_injective (f ⁻¹ᵁ W)
    rw [← hD, hny, hy]
    simp only [map_mul, map_add, map_pow, map_natCast, map_ofNat,
      app_constant p f hf, rational_germ_constant p W (f ⁻¹ᵁ W)]
end VelocityToSections

section CubicBothCoordinates
open ArithmeticThetaCubicModelR0144 MvPolynomial
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)

/-- Both coordinates determine a twisted derivation without any nonvanishing
hypothesis on the image of Y. -/
lemma cubic_twisted_ext_xy {B : Type u} [CommRing B]
    (φ : CubicRing k r →+* B) (E : CubicRing k r →+ B)
    (hprod : ∀ a b, E (a*b) = φ a*E b + φ b*E a)
    (hconst : ∀ c, E (algebraMap (LaurentSeries k) (CubicRing k r) c) = 0)
    (hx : E (cubicCoordinate k r false) = 0)
    (hy : E (cubicCoordinate k r true) = 0) : ∀ a, E a = 0 := by
  intro z
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective z
  induction q using MvPolynomial.induction_on with
  | C c => exact hconst c
  | add a b ha hb => rw [map_add, map_add, ha, hb, zero_add]
  | mul_X a i ha =>
    rw [map_mul, hprod, ha, mul_zero, add_zero]
    have hi : E (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
      fin_cases i
      · exact hx
      · exact hy
    rw [hi, mul_zero]

open ArithmeticThetaDifferentialRecoveryR0148.WeightedAffineExtension
lemma nat_chainRule_of_cubic_xy {C : Scheme.{u}}
    (p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
    (f : C ⟶ C) (hf : f ≫ p = p) (n : ℕ) (U : C.Opens)
    (q : CubicRing k r →+* Γ(C,U)) (hq : Function.Surjective q)
    (hqc : ∀ c, q (algebraMap (LaurentSeries k) (CubicRing k r) c) =
      (p.constToPresheaf.app (Opposite.op U)).hom c)
    (hxy : ∀ odd : Bool, coefficient p e (f ⁻¹ᵁ U) (f.app U (q (cubicCoordinate k r odd))) =
      (n : Γ(C,f ⁻¹ᵁ U))*f.app U (coefficient p e U (q (cubicCoordinate k r odd)))) :
    ∀ a : Γ(C,U), coefficient p e (f ⁻¹ᵁ U) (f.app U a) =
      (n : Γ(C,f ⁻¹ᵁ U))*f.app U (coefficient p e U a) := by
  let E := weightedDefect p e f (n : LaurentSeries k) U
  have hE (a : Γ(C,U)) : E a = coefficient p e (f ⁻¹ᵁ U) (f.app U a) -
      (n : Γ(C,f ⁻¹ᵁ U))*f.app U (coefficient p e U a) := by
    simp only [E, weightedDefect, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_natCast]
  have H := cubic_twisted_ext_xy k r ((f.app U).hom.comp q) (E.comp q.toAddMonoidHom)
    (fun a b => by
      change E (q (a*b)) = _
      rw [map_mul]
      exact weightedDefect_mul p e f (n : LaurentSeries k) U (q a) (q b))
    (fun c => by
      change E (q (algebraMap _ _ c)) = 0
      rw [hE, hqc, app_constant p f hf, coefficient_constant,
        coefficient_constant, map_zero, mul_zero, sub_self])
    (by change E (q (cubicCoordinate k r false)) = 0; rw [hE, hxy, sub_self])
    (by change E (q (cubicCoordinate k r true)) = 0; rw [hE, hxy, sub_self])
  intro a
  obtain ⟨b,rfl⟩ := hq a
  exact sub_eq_zero.mp ((hE _).symm.trans (H b))
end CubicBothCoordinates

section GroupTransport
open NeronModelInfra WeierstrassProjModel
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
variable {F : Type u} [CommRing F] {A B : Scheme.{u}}
variable {p : A ⟶ Spec (CommRingCat.of F)} {q : B ⟶ Spec (CommRingCat.of F)}

lemma transport_nsmul (E : A ≅ B) (hE : E.hom ≫ q = p) (G : RelativeGroupLaw F q)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F)) (z : SchemeHomOver t p) (n : ℕ) :
    pointsEquiv E hE t ((transport E hE G).nsmul t n z) =
      G.nsmul t n (pointsEquiv E hE t z) := by
  induction n with
  | zero => exact (pointsEquiv E hE t).apply_symm_apply _
  | succ n ih =>
    change pointsEquiv E hE t ((pointsEquiv E hE t).symm
      (G.mul t (pointsEquiv E hE t ((transport E hE G).nsmul t n z)) (pointsEquiv E hE t z))) = _
    rw [Equiv.apply_symm_apply, ih]
    rfl

lemma transport_symm_nsmul (E : A ≅ B) (hE : E.hom ≫ q = p)
    (hi : E.inv ≫ p = q) (G : RelativeGroupLaw F p)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F)) (z : SchemeHomOver t p) (n : ℕ) :
    (transport E.symm hi G).nsmul t n (pointsEquiv E hE t z) =
      pointsEquiv E hE t (G.nsmul t n z) := by
  have hback (w : SchemeHomOver t p) :
      pointsEquiv E.symm hi t (pointsEquiv E hE t w) = w := by
    apply Subtype.ext
    simp [pointsEquiv]
  apply (pointsEquiv E.symm hi t).injective
  rw [transport_nsmul, hback, hback]

lemma comp_schemeNsmul (G : RelativeGroupLaw F p) {V : Scheme.{u}}
    (t : V ⟶ Spec (CommRingCat.of F)) (z : SchemeHomOver t p) (n : ℕ) :
    z.val ≫ G.schemeNsmul n = (G.nsmul t n z).val := by
  have H := G.nsmul_natural p t z.val z.property n (⟨𝟙 A, Category.id_comp p⟩ : SchemeHomOver p p)
  have hz : schemeHomOverComp z.val z.property (⟨𝟙 A, Category.id_comp p⟩ : SchemeHomOver p p) = z :=
    Subtype.ext (Category.comp_id _)
  exact (congrArg Subtype.val H).trans (congrArg (fun z => (G.nsmul t n z).val) hz)

/-- A field-valued point supported on a closed base section equals that section
composed with its specified structure map. -/
lemma field_point_eq_section {K : Type u} [Field K]
    (z : Spec (CommRingCat.of K) ⟶ A) (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    (e : Spec (CommRingCat.of F) ⟶ A) [IsClosedImmersion e]
    (hz : z ≫ p = t) (he : e ≫ p = 𝟙 _)
    (x : Spec (CommRingCat.of K)) (y : Spec (CommRingCat.of F)) (hxy : z x = e y) :
    z = t ≫ e := by
  obtain ⟨v,hv,_⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  letI : Surjective (CategoryTheory.Limits.pullback.fst z e) :=
    ⟨fun w => ⟨v,hv.trans (Subsingleton.elim x w)⟩⟩
  letI : IsIso (CategoryTheory.Limits.pullback.fst z e) :=
    isIso_of_isClosedImmersion_of_surjective _
  apply (cancel_epi (CategoryTheory.Limits.pullback.fst z e)).mp
  have H := congrArg (fun a => a ≫ p) (CategoryTheory.Limits.pullback.condition (f := z) (g := e))
  simp only [Category.assoc, hz, he, Category.comp_id] at H
  rw [← Category.assoc, H, CategoryTheory.Limits.pullback.condition]
end GroupTransport

section ConstantMap
variable {F : Type u} [Field F] {C : Scheme.{u}}
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)

lemma coefficient_structure_app (U : (Spec (CommRingCat.of F)).Opens)
    (a : Γ(Spec (CommRingCat.of F),U)) :
    coefficient p e (p ⁻¹ᵁ U) (p.app U a) = 0 := by
  by_cases hU : Nonempty U
  · have hu : U = ⊤ := by
      obtain ⟨x⟩ := hU
      ext z
      change z ∈ U ↔ True
      apply iff_true_intro
      exact (Subsingleton.elim x.val z) ▸ x.property
    subst U
    obtain ⟨c,rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
    have hc := coefficient_constant p e (p ⁻¹ᵁ ⊤) c
    simpa [Scheme.Hom.constToPresheaf, Scheme.Hom.appLE] using hc
  · have hu : p ⁻¹ᵁ U = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => hU ⟨⟨p x,hx⟩⟩)
    letI : Subsingleton Γ(C,p ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hu)
    exact Subsingleton.elim _ _

lemma coefficient_constant_map (q : Spec (CommRingCat.of F) ⟶ C)
    (U : C.Opens) (a : Γ(C,U)) :
    coefficient p e ((p ≫ q) ⁻¹ᵁ U) ((p ≫ q).app U a) = 0 := by
  exact coefficient_structure_app p e (q ⁻¹ᵁ U) (q.app U a)
end ConstantMap

section ActualMaps
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
variable (M : Model k T) (G : Law k M)

lemma multiplication_over (n : ℕ) :
    multiplication k M G n ≫ genericStructure k M = genericStructure k M :=
  (G.nsmul _ n (universalPoint k M)).property

lemma multiplication_one : multiplication k M G 1 = 𝟙 _ := by
  unfold multiplication
  rw [G.nsmul_one_apply]
  rfl

lemma multiplication_zero :
    multiplication k M G 0 = genericStructure k M ≫ (G.one (𝟙 _)).val := by
  unfold multiplication
  rw [G.nsmul_zero]
  exact (congrArg Subtype.val (G.one_natural (𝟙 _) (genericStructure k M)
    (genericStructure k M) (Category.comp_id _))).symm

lemma multiplication_one_differential (e : Frame k M) :
    DifferentialWeight k M e (multiplication k M G 1) 1 := by
  rw [multiplication_one]
  refine ⟨Category.id_comp _, ?_⟩
  intro U a
  simp only [scalarAt, map_one, one_mul]
  rfl

lemma multiplication_zero_differential (e : Frame k M) :
    DifferentialWeight k M e (multiplication k M G 0) 0 := by
  refine ⟨multiplication_over k M G 0, ?_⟩
  intro U a
  rw [multiplication_zero]
  simp only [scalarAt, map_zero, zero_mul]
  exact coefficient_constant_map (genericStructure k M) e (G.one (𝟙 _)).val U a

open NeronModelInfra ArithmeticThetaCubicModelR0144
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

lemma multiplication_preimage_nonempty (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) (hG : IsOriginLaw k M s hs G)
    {K : Type u} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (z : SchemeHomOver t (genericStructure k M)) (n : ℕ)
    (hn : G.nsmul t n z ≠ G.one t) :
    Nonempty ((multiplication k M G n) ⁻¹ᵁ complement k M s : (genericScheme k M).Opens) := by
  classical
  let x : Spec (CommRingCat.of K) := Classical.choice inferInstance
  let q : Spec (CommRingCat.of (LaurentSeries k)) := Classical.choice inferInstance
  let f := multiplication k M G n
  by_cases hx : f (z.val x) ∈ complement k M s
  · exact ⟨⟨z.val x,hx⟩⟩
  · exfalso
    have hsupport : f (z.val x) = genericPoint k M s hs q := by
      have H : f (z.val x) ∈ (s.ker.comap (genericInclusion k M)).support := by
        exact not_not.mp hx
      exact (Set.ext_iff.mp (generic_identity_support_singleton k M hM s hs q) _).mp H
    have hcomp : z.val ≫ f = (G.nsmul t n z).val := comp_schemeNsmul G t z n
    letI := genericPoint_closed k M hM s hs
    have H := field_point_eq_section (p := genericStructure k M) (z.val ≫ f) t
      (genericPoint k M s hs)
      (by rw [Category.assoc, multiplication_over, z.property])
      (genericPoint_structure k M s hs) x q hsupport
    apply hn
    rw [hG.1]
    apply Subtype.ext
    exact hcomp.symm.trans H

end ActualMaps

#print axioms generic_point_velocity
#print axioms chart_point_velocity
#print axioms cubic_twisted_ext_xy
#print axioms transport_nsmul
#print axioms comp_schemeNsmul
#print axioms field_point_eq_section
#print axioms nat_chain_rule_of_affine
#print axioms chain_rule_at_point_of_affine
#print axioms coefficient_germ_eq
#print axioms generic_chart_factor
#print axioms exists_rational_derivation
#print axioms rational_point_structure
#print axioms weighted_extension_of_injective
#print axioms derivation_germ_compatibility
#print axioms extendDerivation_algebraMap
#print axioms evaluation_nsmul
#print axioms velocity_unique
#print axioms velocity_nsmul
#print axioms nsmul_ne_zero_of_velocity_one
#print axioms velocity_add
#print axioms moving_chord_slope_derivative
#print axioms moving_chord_derivative_y
#print axioms tangent_derivative_y
#print axioms moving_chord_derivative
#print axioms weighted_derivative_y
#print axioms tangent_derivative
#print axioms coefficient_structure_app
#print axioms coefficient_constant_map
#print axioms multiplication_zero_differential
#print axioms multiplication_over
#print axioms multiplication_zero
#print axioms multiplication_one_differential
end ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory AlgebraicGeometry NeronModelInfra
open MultiplicationDifferential
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaDifferentialRecoveryR0148.AffineTranslationChainRule
open InverseDifferentialSign WeierstrassCurve.DrinfeldGlobal

/-- Multiplication by every natural number scales the actual normalized relative
frame by that number on every open and every regular function. -/
theorem multiplication_differential :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ∀ (n : ℕ), ArithmeticThetaHodgeFourTorsionR0147.DifferentialWeight k M δ (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G n) (n : LaurentSeries k) := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY G hG e heN n
  classical
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using multiplication_zero_differential k M G e
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let C := genericScheme k M
  let p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)) := genericStructure k M
  let W := complement k M s
  let f : C ⟶ C := multiplication k M G n
  have hf : f ≫ p = p := multiplication_over k M G n
  letI : IsIntegral C := generic_integral k h3 M hM
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  have hW : IsAffineOpen W := complement_isAffineOpen k h3 M hM s hs X hX
  obtain ⟨a,ha,_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c,hc,_⟩ := projective_cubic_chart k r
  obtain ⟨E,hE,_⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  let qchart := chartSections W (a ≪≫ c)
  have hqchart (odd : Bool) :
      qchart (if odd then yOverZ (curve k r).toProjective else xOverZ (curve k r).toProjective) =
      W.topIso.hom (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X)) := by
    change W.topIso.hom (a.hom.appTop (c.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv _))) = _
    rw [hc.2 odd]
    exact congrArg W.topIso.hom (coordinateIso_values k M s X Y a ha odd)
  have hqx : qchart (xOverZ (curve k r).toProjective) = W.topIso.hom (complementCoordinate k M s 2 X) := hqchart false
  have hqy : qchart (yOverZ (curve k r).toProjective) = W.topIso.hom (complementCoordinate k M s 3 Y) := hqchart true
  let xW := qchart (xOverZ (curve k r).toProjective)
  let yW := qchart (yOverZ (curve k r).toProjective)
  have hnorm : coefficient p e W xW = 2*yW := by
    change coefficient p e W (qchart _) = 2*qchart _
    rw [hqx,hqy]
    exact coefficient_normalization p e W _ _ (normalization_from_predicate k M s X Y e heN)
  have hyW : yW ≠ 0 := by
    change qchart _ ≠ 0
    rw [hqy]
    exact complement_y_nonzero k h3 he M hM s hs X Y hX hY
  letI := rationalBaseAlgebra p W
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : CharZero C.functionField := Algebra.charZero_of_charZero (LaurentSeries k) C.functionField
  obtain ⟨D,hD⟩ := exists_rational_derivation p e W hW
  let t := extensionBase k C.functionField
  let z : SchemeHomOver t p := ⟨C.fromSpecStalk (_root_.genericPoint C), rational_point_structure p W hW⟩
  have hEp : E.hom ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r = p := hE.1
  have hei : E.inv ≫ p = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by rw [← hEp, E.inv_hom_id_assoc]
  let H := transport E.symm hei G
  have hH : (H.one (𝟙 _)).val = origin k r := by
    change (G.one (𝟙 _)).val ≫ E.hom = _
    rw [hG.1]
    simpa only [pointOver, Category.id_comp] using hE.2.2
  obtain ⟨ev,hev⟩ := projective_points_evaluation k r h3 he H hH
  let P := pointsEquiv E hEp t z
  let Pn := pointsEquiv E hEp t (G.nsmul t n z)
  have hvel : HasVelocity ((curve k r).toProjective.baseChange C.functionField).toAffine D 1
      (ev C.functionField P) :=
    generic_point_velocity k r p e D W hW (a ≪≫ c) E.hom hE.2.1 (hD W) hnorm hyW H ev hev P rfl
  have hpn : ev C.functionField Pn = n • ev C.functionField P := by
    have hh : H.nsmul t n P = Pn := transport_symm_nsmul E hEp hei G t z n
    exact (congrArg (ev C.functionField) hh.symm).trans
      (evaluation_nsmul k r H ev hev C.functionField P n)
  have hnv : HasVelocity ((curve k r).toProjective.baseChange C.functionField).toAffine D (n : C.functionField)
      (ev C.functionField Pn) := by
    rw [hpn]
    simpa only [mul_one] using velocity_nsmul _ D (map_zero _) (map_zero _)
      (D.map_algebraMap _) (D.map_algebraMap _) _ 1 hvel n
  have hne : ev C.functionField Pn ≠ 0 := by
    rw [hpn]
    exact nsmul_ne_zero_of_velocity_one _ D (map_zero _) (map_zero _)
      (D.map_algebraMap _) (D.map_algebraMap _) _ hvel n hnpos
  have hzne : G.nsmul t n z ≠ G.one t := by
    intro hh
    apply hne
    change ev C.functionField (pointsEquiv E hEp t (G.nsmul t n z)) = 0
    rw [hh]
    exact evaluation_one k r H ev hev C.functionField
  letI : Nonempty (f ⁻¹ᵁ W : C.Opens) :=
    multiplication_preimage_nonempty k M G hM s hs.1 hG t z n hzne
  let χ : ChartRing k r →+* C.functionField := (C.germToFunctionField W).hom.comp qchart
  let χn : ChartRing k r →+* C.functionField :=
    (C.germToFunctionField (f ⁻¹ᵁ W)).hom.comp ((f.app W).hom.comp qchart)
  have hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r := by
    exact generic_chart_factor_id W hW (a ≪≫ c) (chartInclusion k r) E.hom hE.2.1
  have hPn : Pn.val = Spec.map (CommRingCat.ofHom χn) ≫ chartInclusion k r := by
    change (G.nsmul t n z).val ≫ E.hom = _
    rw [← comp_schemeNsmul G t z n, Category.assoc]
    exact (generic_chart_factor W hW (a ≪≫ c) (chartInclusion k r) E.hom hE.2.1 f).symm
  have hv0 := chart_velocity_coordinates k r H ev hev C.functionField D P χ hP 1 hvel
  have hvn := chart_velocity_coordinates k r H ev hev C.functionField D Pn χn hPn (n : C.functionField) hnv
  have hxy := velocity_to_sections p e f hf n W xW yW (curve k r).a₂ (curve k r).a₄ hnorm D hD
    (by simpa only [one_mul, χ, RingHom.comp_apply, xW, yW] using hv0.2) hvn.1 hvn.2
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
  have hsurj : Function.Surjective q :=
    (ConcreteCategory.bijective_of_isIso W.topIso.hom).2.comp
      ((ConcreteCategory.bijective_of_isIso a.hom.appTop).2.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv).2)
  have hqxC : q (cubicCoordinate k r false) = qchart (xOverZ (curve k r).toProjective) :=
    (show q (cubicCoordinate k r false) = W.topIso.hom (complementCoordinate k M s 2 X) from hq false).trans hqx.symm
  have hqyC : q (cubicCoordinate k r true) = qchart (yOverZ (curve k r).toProjective) :=
    (show q (cubicCoordinate k r true) = W.topIso.hom (complementCoordinate k M s 3 Y) from hq true).trans hqy.symm
  have hchain : ∀ b : Γ(C,W), coefficient p e (f ⁻¹ᵁ W) (f.app W b) =
      (n : Γ(C,f ⁻¹ᵁ W))*f.app W (coefficient p e W b) := by
    apply nat_chainRule_of_cubic_xy k r p e f hf n W q hsurj hqc
    intro odd
    cases odd
    · rw [hqxC]
      exact hxy.1
    · rw [hqyC]
      exact hxy.2
  refine ⟨hf, ?_⟩
  intro U b
  simpa only [scalarAt, map_natCast, coefficient, frameDerivative, differentialAt] using nat_chain_rule_of_affine p e f n W hW hchain U b

#print axioms multiplication_differential
end ArithmeticThetaHodgeFourTorsionR0147
