module

public import OpenConstantComparisonR0234

@[expose] public section

/-! The all-test universal property of coefficient extension of the level base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaLevelConstantsR0234
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204

private lemma cartesian_lift
    {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : LevelData l L)
    (f : OpenBase l L E ⟶ OpenBase k L D) (hf : RespectsClassifiers ι D E f)
    (S : Scheme.{0}) (b : S ⟶ OpenBase k L D) (σ : S ⟶ Base l)
    (hb : b ≫ openStructure k L D = σ ≫ constants ι) :
    ∃! c : S ⟶ OpenBase l L E,
      c ≫ f = b ∧ c ≫ openStructure l L E = σ := by
  obtain ⟨F, M, a, ha⟩ := SchemeFullLevelUniversal.converse D.atlas
    (B := D.two) (C := D.cover) (Q := D.quotient) S (σ ≫ constants ι) b hb
  obtain ⟨c, g, hg⟩ := global_scheme_classifier l L hL heven
    E.atlas E.two E.canonical E.cover E.quotient S σ F M
  obtain ⟨a', ha'⟩ := hf.2 S σ F M c g hg
  have hcf : c ≫ f = b := (scheme_classifying_uniqueness k L hL heven
    D.atlas D.two D.canonical D.cover D.quotient S (σ ≫ constants ι)
    F M (c ≫ f) b a' a ha' ha).1
  refine ⟨c, ⟨hcf, hg.1⟩, ?_⟩
  rintro m ⟨hmf, hmσ⟩
  obtain ⟨G, N, v, hv⟩ := SchemeFullLevelUniversal.converse E.atlas
    (B := E.two) (C := E.cover) (Q := E.quotient) S σ m hmσ
  obtain ⟨w, hw⟩ := hf.2 S σ G N m v hv
  rw [hmf] at hw
  obtain ⟨q, hq, _⟩ :=
    ArithmeticThetaMetaplecticComparisonR0206.marked_cartesian_reconstruction
      k L hL heven D.atlas D.two D.cover D.quotient S S
      (σ ≫ constants ι) (σ ≫ constants ι) F G M N (𝟙 S) b b a w
      (Category.id_comp _) ha hw (Category.id_comp _).symm
  have hc := SchemeFullLevelUniversal.classifies_comp E.atlas
    (B := E.two) (C := E.cover) (Q := E.quotient)
    (Category.id_comp σ) hq.1 hg
  have hu := (scheme_classifying_uniqueness l L hL heven
    E.atlas E.two E.canonical E.cover E.quotient S σ G N
    m (𝟙 S ≫ c) v (q ≫ g) hv hc).1
  simpa only [Category.id_comp] using hu

/-- The actual classifier-preserving comparison is scalar extension, including
arbitrary nonreduced and empty tests, and is surjective. -/
theorem open_constant_cartesian :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L →
      ∀ (D : LevelData k L) (E : LevelData l L),
      ∀ (f : OpenBase l L E ⟶ OpenBase k L D), RespectsClassifiers ι D E f →
      IsPullback f (openStructure l L E) (openStructure k L D) (constants ι) ∧
        Surjective f := by
  intro k l _ _ _ _ ι L hL heven D E f hf
  have hp : IsPullback f (openStructure l L E) (openStructure k L D) (constants ι) := by
    apply IsPullback.of_isLimit
      (c := PullbackCone.mk f (openStructure l L E) hf.1)
    apply PullbackCone.isLimitAux'
    intro s
    let h := cartesian_lift ι L hL heven D E f hf s.pt s.fst s.snd s.condition
    exact ⟨h.choose, h.choose_spec.1.1, h.choose_spec.1.2,
      fun hm hn => h.choose_spec.2 _ ⟨hm, hn⟩⟩
  exact ⟨hp, MorphismProperty.of_isPullback (P := @Surjective) hp.flip inferInstance⟩

end ArithmeticThetaLevelConstantsR0234

#print axioms ArithmeticThetaLevelConstantsR0234.open_constant_cartesian
