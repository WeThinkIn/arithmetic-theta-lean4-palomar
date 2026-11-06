module

public import SchemeDiscriminantExistenceR0244
public import SchemeDiscriminantFrameUniquenessR0244

@[expose] public section

/-! Naturality of the normalized discriminant on arbitrary scheme families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaSchemeDiscriminantR0244
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203

namespace SchemeDiscriminantNaturality
open SchemeDiscriminantExistence

/-- The actual tensor comparison commutes with composition on global sections. -/
theorem pull_comp {S T U : Scheme.{u}} {E : Family S} {F : Family T}
    {H : Family U} {b : T ⟶ S} {a : U ⟶ T}
    (C : Comparison E F b) (D : Comparison F H a) (d : Sections E) :
    pull (comparisonComp C D) d = pull D (pull C d) :=
  localPull_comp C D ⊤ ⊤ ⊤ (by simp) (by simp) d

/-- Composing each affine test with the given Cartesian map preserves the
universal normalization predicate, with its specified coefficient algebra. -/
theorem isD2_pull (k : Type u) [Field k] [CharZero k]
    {S T : Scheme.{u}} (σ : S ⟶ Base k) (τ : T ⟶ Base k)
    (E : Family S) (F : Family T) (b : T ⟶ S) (hb : b ≫ σ = τ)
    (C : Comparison E F b) (d : Sections E) (hd : IsD2 k σ E d) :
    IsD2 k τ F (pull C d) := by
  intro R instR instAlg W instEll G hG a ha D
  have hcomp : (a ≫ b) ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [Category.assoc, hb, ha]
  have h := hd R W G hG (a ≫ b) hcomp (comparisonComp C D)
  rw [pull_comp] at h
  exact h

end SchemeDiscriminantNaturality

/-- The canonical section commutes with every actual pointed Cartesian base
change over the characteristic-zero field. -/
theorem scheme_discriminant_naturality
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ Base k) (E : Family S)
    (T : Scheme.{u}) (τ : T ⟶ Base k) (F : Family T) (b : T ⟶ S)
    (hb : b ≫ σ = τ) (C : Comparison E F b) (d : Sections E) (e : Sections F)
    (hd : IsD2 k σ E d) (he : IsD2 k τ F e) : pull C d = e := by
  exact (scheme_discriminant_frame_uniqueness k T τ F e he).2 (pull C d)
    (SchemeDiscriminantNaturality.isD2_pull k σ τ E F b hb C d hd)

#print axioms scheme_discriminant_naturality
end ArithmeticThetaSchemeDiscriminantR0244
