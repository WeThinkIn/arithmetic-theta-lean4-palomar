module

public import FiniteEtaleNormSectionR0251

@[expose] public section

/-! Multiplicative determinant norms on the structure sheaf, with uniqueness
and restriction compatibility on every open of an arbitrary scheme. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150

namespace NormFamilyConstruction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma one (U : Y.Opens) : IsNormSection f U 1 1 := by
  intro V e hV
  simp [restrict, ArithmeticThetaArbitraryKatoUnitR0249.restrict, affineNorm]

lemma mul (U : Y.Opens) (a a' : Sections X (f ⁻¹ᵁ U))
    (b b' : Sections Y U) (h : IsNormSection f U a b)
    (h' : IsNormSection f U a' b') : IsNormSection f U (a * a') (b * b') := by
  intro V e hV
  have hn : ∀ x y : Sections X (f ⁻¹ᵁ V.1),
      affineNorm f V.1 (x * y) = affineNorm f V.1 x * affineNorm f V.1 y := by
    intro x y
    let := (f.app V.1).hom.toAlgebra
    exact map_mul (Algebra.norm (Sections Y V.1)) x y
  simpa only [restrict, ArithmeticThetaArbitraryKatoUnitR0249.restrict,
    map_mul, hn] using congrArg₂ (· * ·) (h V e hV) (h' V e hV)

lemma restriction (U V : Y.Opens) (e : V ≤ U)
    (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) (h : IsNormSection f U a b) :
    IsNormSection f V
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a)
      (restrict U V e b) := by
  intro W eW hW
  rw [NormSection.restrict_trans, NormSection.restrict_trans]
  exact h W (eW.trans e) hW

end NormFamilyConstruction

/-- The unique glued local determinants form the unique multiplicative norm
family, including its restriction law on arbitrary opens. -/
theorem finite_etale_norm_family
    (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] [Etale f] :
    ∃! N : NormFamily f, IsNormFamily f N := by
  classical
  let n : ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) → Sections Y U :=
    fun U a => (finite_etale_norm_section X Y f U a).exists.choose
  have hn : ∀ U a, IsNormSection f U a (n U a) :=
    fun U a => (finite_etale_norm_section X Y f U a).exists.choose_spec
  have unique : ∀ U a b, IsNormSection f U a b → b = n U a := by
    intro U a b hb
    exact (finite_etale_norm_section X Y f U a).unique hb (hn U a)
  let N : NormFamily f := fun U =>
    { toFun := n U
      map_one' := (unique U 1 1 (NormFamilyConstruction.one f U)).symm
      map_mul' := fun a a' =>
        (unique U (a * a') (n U a * n U a')
          (NormFamilyConstruction.mul f U a a' (n U a) (n U a')
            (hn U a) (hn U a'))).symm }
  refine ⟨N, ⟨hn, ?_⟩, ?_⟩
  · intro U V e a
    exact (unique V _ _ (NormFamilyConstruction.restriction f U V e a
      (n U a) (hn U a))).symm
  · intro N' hN'
    funext U
    apply MonoidHom.ext
    intro a
    exact unique U a (N' U a) (hN'.1 U a)

end ArithmeticThetaSchemeKatoNormR0251

#print axioms ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family
