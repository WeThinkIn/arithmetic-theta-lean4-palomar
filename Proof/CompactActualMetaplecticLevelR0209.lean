module

public import CompactInteriorLevelR0209
public import FiniteEtaleActualLevelR0208
public import ActualMetaplecticFPQCStackR0207

@[expose] public section

/-! The given compact Hodge root defines a level in the actual family stack. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaCompactModularityR0209
open CategoryTheory AlgebraicGeometry

namespace CompactActualMetaplecticLevelR0209

/-- Universality is proved for the specified quotient, without replacing it
by an existentially chosen provider. -/
private theorem fixed_quotient_universal
    (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
    (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
    (hB : ArithmeticThetaCompatibleLevelR0178.CanonicalTwo k L A B)
    (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
    (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) :
    ArithmeticThetaSchemeHodgeR0205.HodgeUniversal k L A B C Q := by
  refine ⟨?_, ArithmeticThetaSchemeHodgeR0205.classifying_cotangent_hodge
    k L hL heven A B C Q,
    ArithmeticThetaSchemeHodgeR0205.SchemeHodgeUniversal.classifier_natural k L A B C Q⟩
  refine ⟨?_, ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal.converse A, ?_⟩
  · intro S σ E M
    obtain ⟨b, f, hf⟩ := ArithmeticThetaSchemeLevelR0204.global_scheme_classifier
      k L hL heven A B hB C Q S σ E M
    refine ⟨b, ⟨f, hf, ?_⟩, ?_⟩
    · intro f' hf'
      exact (ArithmeticThetaSchemeLevelR0204.scheme_classifying_uniqueness
        k L hL heven A B hB C Q S σ E M b b f' f hf' hf).2
    · intro b' hb'
      obtain ⟨f', hf', _⟩ := hb'
      exact (ArithmeticThetaSchemeLevelR0204.scheme_classifying_uniqueness
        k L hL heven A B hB C Q S σ E M b' b f' f hf' hf).1
  · intro S T σ τ E F M N a g ha hg b c f h hf hh
    exact ArithmeticThetaSchemeLevelR0204.scheme_classifying_uniqueness
      k L hL heven A B hB C Q T τ F N c (a ≫ b) h (g ≫ f) hh
      (ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal.classifies_comp A ha hg hf)

end CompactActualMetaplecticLevelR0209

/-- The actual finite étale level retains the same compact cover, compatible
quotient, restricted Hodge square, and all-test geometric fiber property. -/
theorem compact_actual_metaplectic_level
    (k : Type) [Field k] [CharZero k] (L b : ℕ) (K : CompactRoot k L b)
    (hL : 3 ≤ L) (heven : Even L) (hK : Etale K.cover.map) : ActualLevel K := by
  have hInterior := compact_interior_level k L b K hK
  have h : Universal K :=
    CompactActualMetaplecticLevelR0209.fixed_quotient_universal k L hL heven
      K.data.atlas K.data.two K.data.canonical K.data.cover K.data.quotient
  obtain ⟨C, hforget, hstack⟩ :=
    ArithmeticThetaMetaplecticStackR0207.actual_metaplectic_fpqc_stack k L hL heven
  refine ⟨hInterior, h, C, hforget, hstack, ?_, ?_⟩
  · exact ArithmeticThetaActualLevelR0208.actual_anchored_pullback k L C
      (interiorBase K)
      (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K))
      (ArithmeticThetaActualLevelR0208.canonicalMap C (interiorBase K)
        (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K)))
  · exact ArithmeticThetaActualLevelR0208.finite_etale_actual_level k L hL heven
      (provider K h) C (interiorBase K) (levelMap K h) (openSquare K)
      (ArithmeticThetaActualLevelR0208.canonicalMap C (interiorBase K)
        (ArithmeticThetaActualLevelR0208.object (provider K h) (levelMap K h) (openSquare K)))
      hInterior.2.2.1 hInterior.2.2.2.1

end ArithmeticThetaCompactModularityR0209

#print axioms ArithmeticThetaCompactModularityR0209.compact_actual_metaplectic_level
