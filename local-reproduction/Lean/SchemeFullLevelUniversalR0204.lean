import GlobalSchemeClassifierR0204
import FullMarkingSignDescentR0176

/-! The fixed compatible quotient and its universal marked elliptic family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeLevelR0204
namespace SchemeFullLevelUniversal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 GlobalSchemeClassifier

variable {k : Type u} [Field k] {L : ℕ}
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)

/-- The recursive multiples use exactly the descended group operation. -/
lemma multiple_eq {T : Scheme.{u}} (t : T ⟶ Base A.quotient.ring)
    (n : ℕ) (x : SchemeHomOver t (universalFamily L A).p) :
    multiple (universalFamily L A) t n x = A.descent.family.law.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change A.descent.family.law.mul t (multiple (universalFamily L A) t n x) x =
      A.descent.family.law.mul t (A.descent.family.law.nsmul t n x) x
    rw [ih]

/-- The accepted marking, on the same family, with its actual killed and
identity-avoidance equations in the general-scheme interface. -/
def universalLevel : FullLevel (universalFamily L A) L where
  x := A.marking.x
  y := A.marking.y
  killed_x := by
    rw [multiple_eq]
    apply Subtype.ext
    rw [ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent.section_nsmul]
    exact A.marking.killed_x
  killed_y := by
    rw [multiple_eq]
    apply Subtype.ext
    rw [ArithmeticThetaLegendreAtlasR0176.FullMarkingSignDescent.section_nsmul]
    exact A.marking.killed_y
  avoids := by
    intro i j hij
    rw [multiple_eq, multiple_eq]
    exact A.marking.avoids i j hij

variable [CharZero k]
  {B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A}
  {C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B}
  {Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C}

/-- Pull back the actual descended family and its full marking along any map
to the compatible quotient. No restriction on the test scheme or map is used. -/
lemma converse (S : Scheme.{u}) (σ : S ⟶ Base k)
    (b : S ⟶ Base Q.quotient.ring)
    (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = σ) :
    ∃ (E : Family S) (M : FullLevel E L) (f : E.curve ⟶ A.descent.family.curve),
      Classifies k L A B C Q σ E M b f := by
  obtain ⟨E, f, hf, hz, hm⟩ := scheme_family_base_change
    (Base A.quotient.ring) S (universalFamily L A) (b ≫ Q.inclusion)
  obtain ⟨M, hM, _⟩ := cartesian_full_marking
    (Base A.quotient.ring) S (universalFamily L A) E (b ≫ Q.inclusion) f
    hf hz hm L (universalLevel A)
  exact ⟨E, M, f, hb, hf, hz, hM.1, hM.2, hm⟩

/-- Composing a marked Cartesian comparison with a classifier gives a
classifier over the composite base map, including the given structural k-map. -/
lemma classifies_comp {S T : Scheme.{u}} {σ : S ⟶ Base k} {τ : T ⟶ Base k}
    {E : Family S} {F : Family T} {M : FullLevel E L} {N : FullLevel F L}
    {a : T ⟶ S} {g : F.curve ⟶ E.curve} (ha : a ≫ σ = τ)
    (hg : MarkedCartesian E F M N a g)
    {b : S ⟶ Base Q.quotient.ring} {f : E.curve ⟶ A.descent.family.curve}
    (hc : Classifies k L A B C Q σ E M b f) :
    Classifies k L A B C Q τ F N (a ≫ b) (g ≫ f) := by
  have hp : IsPullback (g ≫ f) F.p A.descent.family.projection
      ((a ≫ b) ≫ Q.inclusion) := by
    simpa only [Category.assoc] using hg.1.paste_horiz hc.2.1
  have hz : F.zero ≫ (g ≫ f) =
      ((a ≫ b) ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val := by
    rw [← Category.assoc, hg.2.1, Category.assoc, hc.2.2.1]
    simp only [Category.assoc]
  refine ⟨?_, hp, hz, ?_, ?_, universal_multiplicative F _ _ hp hz⟩
  · rw [Category.assoc, hc.1, ha]
  · rw [← Category.assoc, hg.2.2.2.1, Category.assoc, hc.2.2.2.1]
    simp only [Category.assoc]
  · rw [← Category.assoc, hg.2.2.2.2, Category.assoc, hc.2.2.2.2.1]
    simp only [Category.assoc]

end SchemeFullLevelUniversal

open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203

/-- A single compatible quotient has the full universal-family property over
all characteristic-zero test schemes, with both comparison maps natural. -/
theorem scheme_full_level_universal :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L),
      ∃ (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
        (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B)
        (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
        (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C),
        Universal k L A B C Q := by
  intro k _ _ L hL heven A
  obtain ⟨B, hB⟩ :=
    ArithmeticThetaCompatibleLevelR0178.NormalAffineClassifyingConstruction.canonical_marking k L A
  obtain ⟨C⟩ := ArithmeticThetaCompatibleLevelR0178.compatible_level_subcover k L hL heven A B hB
  obtain ⟨Q⟩ := ArithmeticThetaCompatibleLevelR0178.compatible_sign_quotient k L hL heven A B hB C
  refine ⟨B, hB, C, Q, ?_, ?_, ?_⟩
  · intro S σ E M
    obtain ⟨b, f, hf⟩ := global_scheme_classifier k L hL heven A B hB C Q S σ E M
    refine ⟨b, ⟨f, hf, ?_⟩, ?_⟩
    · intro f' hf'
      exact (scheme_classifying_uniqueness k L hL heven A B hB C Q S σ E M
        b b f' f hf' hf).2
    · intro b' hb'
      obtain ⟨f', hf', _⟩ := hb'
      exact (scheme_classifying_uniqueness k L hL heven A B hB C Q S σ E M
        b' b f' f hf' hf).1
  · exact SchemeFullLevelUniversal.converse A
  · intro S T σ τ E F M N a g ha hg b c f h hf hh
    exact scheme_classifying_uniqueness k L hL heven A B hB C Q T τ F N
      c (a ≫ b) h (g ≫ f) hh (SchemeFullLevelUniversal.classifies_comp A ha hg hf)

#print axioms scheme_full_level_universal
end ArithmeticThetaSchemeLevelR0204
