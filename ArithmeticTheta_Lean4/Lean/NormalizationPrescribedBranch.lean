import KummerCover
import NormalizedSectionDefinitions

open AlgebraicGeometry CategoryTheory
open ArithmeticThetaNormalization ArithmeticThetaKummerCover

namespace ArithmeticThetaCoverComparison

universe u

noncomputable section

/-- The proper root normalization has a unique valuative lift of the specified
branch.  The lift simultaneously satisfies the base triangle and the triangle
through the generated root field. -/
theorem normalization_prescribed_valuative_branch
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [CharZero X.functionField]
    (hX : ArithmeticThetaNormalizedSections.NormalAffine X)
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] (N s : ℕ) (hN : 0 < N)
    (r : Fin s → Ω) (a : Fin s → X.functionField)
    (hr : ∀ i, r i ^ N = algebraMap X.functionField Ω (a i))
    (A : ValuationSubring Ω) (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ f = genericExtensionMap X Ω) :
    ∃! g : Spec (CommRingCat.of A) ⟶ rootCover X Ω s r,
      g ≫ rootCoverMap X Ω s r = f ∧
      Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ g =
        Spec.map (CommRingCat.ofHom (generatedRootField X Ω s r).subtype) ≫
          extensionToNormalization X (generatedRootField X Ω s r) := by
  let E := generatedRootField X Ω s r
  let t : Spec (CommRingCat.of Ω) ⟶ rootCover X Ω s r :=
    Spec.map (CommRingCat.ofHom E.subtype) ≫ extensionToNormalization X E
  have ht : t ≫ rootCoverMap X Ω s r = genericExtensionMap X Ω := by
    dsimp only [t, rootCoverMap]
    rw [Category.assoc, extensionNormalization_factorization]
    unfold genericExtensionMap
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  let S : ValuativeCommSq (rootCoverMap X Ω s r) :=
    { R := A
      K := Ω
      i₁ := t
      i₂ := f
      commSq := ⟨ht.trans hf.symm⟩ }
  have hp : IsProper (rootCoverMap X Ω s r) :=
    (rootCover_geometry X Ω N s hN r a hr hX).2.2.1
  rw [IsProper.eq_valuativeCriterion] at hp
  obtain ⟨hU⟩ := hp.1.1.1 S
  let _ := hU
  refine ⟨(default : S.commSq.LiftStruct).l, ?_, ?_⟩
  · exact ⟨(default : S.commSq.LiftStruct).fac_right,
      (default : S.commSq.LiftStruct).fac_left⟩
  · intro g hg
    let l : S.commSq.LiftStruct := ⟨g, hg.2, hg.1⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l default)

end
end ArithmeticThetaCoverComparison
