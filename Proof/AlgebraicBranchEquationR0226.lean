module

public import AlgebraicBranchDefinitionsR0226

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaAlgebraicBranchesR0226
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Base Sections)
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaValuativeRootsR0223
open ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185

namespace AlgebraicBranchEquationR0226

private lemma along_heq {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ Z) (hab : a ≫ b = c) (J : Z.Modules)
    (h : Sections ((Scheme.Modules.pullback b).obj J)) :
    HEq (((Scheme.Modules.pullbackComp a b).app J).hom.app ⊤
      (pullbackGlobalSection a _ h))
      ((along a b c hab J).hom.app ⊤ (pullbackGlobalSection a _ h)) := by
  subst c
  simp [along, Scheme.Modules.pullbackCongr]

/-- Associativity of the accepted transport applied to the given section. -/
private lemma frame_comp_heq {W X Y Z : Scheme.{0}}
    (q : W ⟶ X) (p : X ⟶ Y) (f : Y ⟶ Z) (d : W ⟶ Y)
    (hd : q ≫ p = d) (J : Z.Modules)
    (h : Sections ((Scheme.Modules.pullback f).obj J)) :
    HEq (((Scheme.Modules.pullbackComp q (p ≫ f)).app J).hom.app ⊤
      (pullbackGlobalSection q _
        (((Scheme.Modules.pullbackComp p f).app J).hom.app ⊤
          (pullbackGlobalSection p _ h))))
      (((Scheme.Modules.pullbackComp d f).app J).hom.app ⊤
        (pullbackGlobalSection d _ h)) := by
  have ht : q ≫ (p ≫ f) = d ≫ f := by rw [← Category.assoc, hd]
  have hc := along_comp_section f p q (p ≫ f) d (d ≫ f)
    rfl hd rfl ht J h
  simp only [transport_as_app] at hc
  have hi : (along p f (p ≫ f) rfl J) = (Scheme.Modules.pullbackComp p f).app J := by
    apply Iso.ext
    simp [along, Scheme.Modules.pullbackCongr]
  have ho : (along d f (d ≫ f) rfl J) = (Scheme.Modules.pullbackComp d f).app J := by
    apply Iso.ext
    simp [along, Scheme.Modules.pullbackCongr]
  rw [hi, ho] at hc
  exact (along_heq q (p ≫ f) (d ≫ f) ht J _).trans (heq_of_eq hc)

/-- Equality of the actual maps and heterogeneous equality of their frames
identify the entire equation, including its scalar action and tensor power. -/
private lemma equation_congr (E : Type) [Field E] {Z : Scheme.{0}}
    (u v : Base E ⟶ Z) (hu : u = v) (J : Z.Modules) (n : ℕ)
    (F : Sections (tensorPower Z J n))
    (h₁ : Sections ((Scheme.Modules.pullback u).obj J))
    (h₂ : Sections ((Scheme.Modules.pullback v).obj J)) (hh : HEq h₁ h₂) (r : E) :
    (pullbackPowerSection u J n F = ArithmeticThetaOpenHodgeR0180.scalar E (r ^ n) •
      tensorPowerSection (Base E) ((Scheme.Modules.pullback u).obj J) n ⊤ h₁) ↔
    (pullbackPowerSection v J n F = ArithmeticThetaOpenHodgeR0180.scalar E (r ^ n) •
      tensorPowerSection (Base E) ((Scheme.Modules.pullback v).obj J) n ⊤ h₂) := by
  subst v
  cases eq_of_heq hh
  rfl

end AlgebraicBranchEquationR0226

/-- The direct field equation and the equation over the extended valuation
disk use the same original section and frame, for every exponent. -/
theorem algebraic_branch_equation :
    ∀ (k E : Type) [Field k] [Field E] [Algebra (LaurentSeries k) E]
      (V : ValuationExtension k E) (Z : Scheme.{0})
      (f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ Z) (J : Z.Modules) (n : ℕ)
      (F : Sections (tensorPower Z J n))
      (h : Sections ((Scheme.Modules.pullback f).obj J)) (r : E),
      Equation f J n F h r ↔
        FieldEquation E V.ring (extendedDisk k E V.ring V.inclusion f) J n F
          (extendedFrame k E V.ring V.inclusion f J h) r := by
  intro k E _ _ _ V Z f J n F h r
  have hd : genericInclusion E V.ring ≫ Spec.map (CommRingCat.ofHom V.inclusion) =
      Spec.map (CommRingCat.ofHom (seriesMap k E)) := by
    unfold genericInclusion
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap V.ring E).comp V.inclusion)) = _
    rw [V.compatible]
  have hm : genericInclusion E V.ring ≫ extendedDisk k E V.ring V.inclusion f =
      fieldDisk (E := E) f := by
    rw [ValuedExtensionPrescribedRootsR0223.generic_extended_disk k E V.ring V.inclusion
      (fun t => RingHom.congr_fun V.compatible t) f]
    unfold fieldDisk seriesMap ArithmeticThetaTateCuspsR0181.genericInclusion
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hh := AlgebraicBranchEquationR0226.frame_comp_heq
    (genericInclusion E V.ring) (Spec.map (CommRingCat.ofHom V.inclusion)) f
    (Spec.map (CommRingCat.ofHom (seriesMap k E))) hd J h
  exact AlgebraicBranchEquationR0226.equation_congr E _ _ hm.symm J n F
    (fieldFrame f J h) (genericFrame E V.ring _ J (extendedFrame k E V.ring V.inclusion f J h))
    hh.symm r

#print axioms algebraic_branch_equation
end ArithmeticThetaAlgebraicBranchesR0226
