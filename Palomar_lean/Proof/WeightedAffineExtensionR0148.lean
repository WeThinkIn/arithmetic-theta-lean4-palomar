module

public import InverseDifferentialSignR0147

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaDifferentialRecoveryR0148
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign

namespace WeightedAffineExtension
variable {F : Type u} [CommRing F] {C : Scheme.{u}}
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable (f : C ⟶ C) (c : F)

/-- Difference between the two scalar-weighted chain-rule expressions. -/
def weightedDefect (U : C.Opens) : Γ(C,U) →+ Γ(C,f ⁻¹ᵁ U) where
  toFun a := coefficient p e (f ⁻¹ᵁ U) (f.app U a) -
    (p.constToPresheaf.app (Opposite.op (f ⁻¹ᵁ U))).hom c *
      f.app U (coefficient p e U a)
  map_zero' := by simp only [map_zero, coefficient_zero, mul_zero, sub_self]
  map_add' a b := by
    simp only [map_add, coefficient_add, mul_add]
    abel

lemma weightedDefect_mul (U : C.Opens) (a b : Γ(C,U)) :
    weightedDefect p e f c U (a*b) =
      f.app U a * weightedDefect p e f c U b +
      f.app U b * weightedDefect p e f c U a := by
  simp only [weightedDefect, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_mul, coefficient_mul, map_add]
  ring

lemma scalar_restrict (U V : C.Opens) (h : V ≤ U) :
    C.presheaf.map (homOfLE h).op ((p.constToPresheaf.app (Opposite.op U)).hom c) =
      (p.constToPresheaf.app (Opposite.op V)).hom c := by
  exact (ConcreteCategory.congr_hom (p.constToPresheaf.naturality (homOfLE h).op) c).symm

lemma weightedDefect_restrict (U V : C.Opens) (h : V ≤ U) (a : Γ(C,U)) :
    C.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op
      (weightedDefect p e f c U a) =
      weightedDefect p e f c V (C.presheaf.map (homOfLE h).op a) := by
  change C.presheaf.map _ (_ - _ * _) = _
  rw [map_sub, map_mul, coefficient_restrict, app_restrict,
    scalar_restrict, app_restrict, coefficient_restrict]
  rfl

/-- A scalar-weighted twisted derivation vanishing on one affine open
vanishes everywhere, by clearing a denominator in the function field. -/
lemma weightedDefect_zero_of_affine [IsIntegral C] [IsIso f]
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hzero : ∀ a, weightedDefect p e f c W a = 0) :
    ∀ (U : C.Opens) (a : Γ(C,U)), weightedDefect p e f c U a = 0 := by
  intro U a
  by_cases hU : Nonempty U
  · letI := hU
    let V := U ⊓ W
    letI : Nonempty V := nonempty_inter U W
    have hne : Nonempty (f ⁻¹ᵁ V : C.Opens) := by
      obtain ⟨x,hx⟩ := Set.nonempty_coe_sort.mp (inferInstance : Nonempty V)
      obtain ⟨y,hy⟩ := f.homeomorph.surjective x
      refine ⟨⟨y,?_⟩⟩
      change f y ∈ V
      simpa only [Scheme.Hom.homeomorph_apply] using hy ▸ hx
    letI := hne
    apply map_injective_of_isIntegral C
      (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => hx.1))
    rw [map_zero, weightedDefect_restrict p e f c U V inf_le_left]
    obtain ⟨b,d,hd,heq⟩ := section_fraction W hW U a
    let R := C.presheaf.map (homOfLE (show V ≤ W from inf_le_right)).op
    have hz (z : Γ(C,W)) : weightedDefect p e f c V (R z) = 0 := by
      rw [← weightedDefect_restrict, hzero, map_zero]
    have hh := congrArg (weightedDefect p e f c V) heq
    rw [weightedDefect_mul, hz b, hz d, mul_zero, zero_add] at hh
    apply (mul_eq_zero.mp hh).resolve_left
    have hr : R d ≠ 0 := by
      intro H
      apply hd
      exact map_injective_of_isIntegral C (homOfLE (show V ≤ W from inf_le_right))
        (H.trans (map_zero R.hom).symm)
    intro H
    apply hr
    exact (ConcreteCategory.bijective_of_isIso (f.app V)).1 (H.trans (map_zero (f.app V).hom).symm)
  · have hv : f ⁻¹ᵁ U = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => hU ⟨⟨f x,hx⟩⟩)
    letI : Subsingleton Γ(C,f ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hv)
    exact Subsingleton.elim _ _
end WeightedAffineExtension

/-- Extend the actual scalar-weighted differential chain rule from a
nonempty affine open to all opens, including the empty open. -/
theorem weighted_affine_extension
    (F : Type u) [CommRing F] (C : Scheme.{u}) [IsIntegral C]
    (p : C ⟶ Spec (CommRingCat.of F))
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
    (f : C ⟶ C) [IsIso f] (c : F)
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (h : ∀ a : Γ(C,W), coefficient p e (f ⁻¹ᵁ W) (f.app W a) =
      (p.constToPresheaf.app (Opposite.op (f ⁻¹ᵁ W))).hom c *
        f.app W (coefficient p e W a)) :
    ∀ (U : C.Opens) (a : Γ(C,U)),
      coefficient p e (f ⁻¹ᵁ U) (f.app U a) =
      (p.constToPresheaf.app (Opposite.op (f ⁻¹ᵁ U))).hom c *
        f.app U (coefficient p e U a) := by
  intro U a
  apply sub_eq_zero.mp
  exact WeightedAffineExtension.weightedDefect_zero_of_affine p e f c W hW
    (fun b => sub_eq_zero.mpr (h b)) U a

end ArithmeticThetaDifferentialRecoveryR0148
