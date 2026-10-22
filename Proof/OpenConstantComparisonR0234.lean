module

public import LevelConstantsDefinitionsR0234
public import MarkedCartesianReconstructionR0206
public import SchemeFullLevelUniversalR0204

@[expose] public section

/-! The canonical coefficient-field comparison of the actual full-level bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaLevelConstantsR0234
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

/-- Classify the target universal marked family after forgetting its coefficient
field, and recover compatibility on every test by marked Cartesian reconstruction. -/
theorem open_constant_comparison :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L →
      ∀ (D : LevelData k L) (E : LevelData l L),
      ∃! f : OpenBase l L E ⟶ OpenBase k L D, RespectsClassifiers ι D E f := by
  intro k l _ _ _ _ ι L hL heven D E
  obtain ⟨U, M, u, hu⟩ := SchemeFullLevelUniversal.converse E.atlas
    (B := E.two) (C := E.cover) (Q := E.quotient)
    (OpenBase l L E) (openStructure l L E) (𝟙 _) (Category.id_comp _)
  obtain ⟨f, a, ha⟩ := global_scheme_classifier k L hL heven
    D.atlas D.two D.canonical D.cover D.quotient (OpenBase l L E)
    (openStructure l L E ≫ constants ι) U M
  refine ⟨f, ⟨ha.1, ?_⟩, ?_⟩
  · intro S σ F N b g hg
    obtain ⟨q, hq, _⟩ :=
      ArithmeticThetaMetaplecticComparisonR0206.marked_cartesian_reconstruction
        l L hL heven E.atlas E.two E.cover E.quotient
        (OpenBase l L E) S (openStructure l L E) σ U F M N
        b (𝟙 _) b u g hg.1 hu hg (Category.comp_id _).symm
    exact ⟨q ≫ a, SchemeFullLevelUniversal.classifies_comp D.atlas
      (B := D.two) (C := D.cover) (Q := D.quotient)
      (by rw [← Category.assoc]; exact congrArg (fun t => t ≫ constants ι) hg.1)
      hq.1 ha⟩
  · intro f' hf'
    obtain ⟨a', ha'⟩ := hf'.2 (OpenBase l L E) (openStructure l L E)
      U M (𝟙 _) u hu
    have h := (scheme_classifying_uniqueness k L hL heven
      D.atlas D.two D.canonical D.cover D.quotient (OpenBase l L E)
      (openStructure l L E ≫ constants ι) U M (𝟙 _ ≫ f') f a' a ha' ha).1
    simpa only [Category.id_comp] using h

end ArithmeticThetaLevelConstantsR0234

#print axioms ArithmeticThetaLevelConstantsR0234.open_constant_comparison
