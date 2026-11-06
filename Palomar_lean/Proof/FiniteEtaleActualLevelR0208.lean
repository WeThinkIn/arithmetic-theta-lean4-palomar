module

public import ActualCategoricalRootFiberR0208

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaActualLevelR0208
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaMetaplecticComparisonR0206 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaMetaplecticTestsR0196 ArithmeticThetaStackLevelR0199
attribute [local instance] CategoryTheory.uliftCategory

namespace FiniteEtaleActualLevelProof
variable {k : Type} [Field k] [CharZero k] {L : ℕ}

/-- Reconstruct an anchor from the actual identity object of an arbitrary test map.
The accepted essential arrow preserves the marked curve and the entire square. -/
def anchorTest (hL : 3 ≤ L) (heven : Even L) (P : Provider k L)
    {C : Coherence L (Base k)} {T : Over (Base k)}
    (r : Pseudofunctor.StrongTrans (representable T) C.functor) :
    AnchoredMap C T (object P
      (Over.homMk (testRoot P r).map
        (ActualFamilyFPQCDescentProof.classifier P.universal
          ((r.app (.mk (.op T))).toFunctor.obj (point (𝟙 T)))).property)
      (testRoot P r).root) := by
  let X : (group L T.left).Objects :=
    (r.app (.mk (.op T))).toFunctor.obj (point (𝟙 T))
  let b : T ⟶ base P := Over.homMk (testRoot P r).map
    (ActualFamilyFPQCDescentProof.classifier P.universal X).property
  let a := Classical.choice (FiberEquivalenceProof.essential_arrow hL heven P.universal
    (model P b) (ActualFamilyFPQCDescentProof.classifiedModel P.universal X) X.root)
  let f : object P b (testRoot P r).root ⟶ X := ((group L T.left).arrow _ _).symm a
  exact ⟨r, (asIso f).symm⟩

lemma two_unit (P : Provider k L) :
    IsUnit (2 : (base P).left.presheaf.obj (Opposite.op ⊤)) := by
  let a : k →+* (base P).left.presheaf.obj (Opposite.op ⊤) :=
    (base P).hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have h : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map a
end FiniteEtaleActualLevelProof

/-- Finite étale representability against every strong test map, with pointwise
rank and conditional surjectivity for the original geometric level morphism. -/
theorem finite_etale_actual_level
    (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (P : Provider k L) (C : Coherence L (Base k))
    (Y : Over (Base k)) (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
    (j : AnchoredMap C Y (object P p H))
    (hfin : IsFinite p.left) (het : Etale p.left) : FiniteEtaleLevel P p H j := by
  let := hfin
  let := het
  intro T r
  let b : T ⟶ base P := Over.homMk (testRoot P r).map
    (ActualFamilyFPQCDescentProof.classifier P.universal
      ((r.app (.mk (.op T))).toFunctor.obj (point (𝟙 T)))).property
  let r' := FiniteEtaleActualLevelProof.anchorTest hL heven P r
  obtain ⟨F, hrep, hpair⟩ := relative_root_test_fiber
    (base P).left Y.left (hodge P) p.left H (FiniteEtaleActualLevelProof.two_unit P)
    T.left (testRoot P r)
  obtain ⟨G, hG⟩ := actual_categorical_root_fiber k L hL heven P C Y p H j
    T b (testRoot P r).root r' F hrep
  obtain ⟨e, heY, heT⟩ := hG
  obtain ⟨a, haY, haT, hafin, haet, hasur, harank⟩ := hpair
  let := hafin
  let := haet
  let := hasur
  refine ⟨F, G, hrep, ⟨a, haY, haT, hafin, haet, hasur, harank⟩,
    ⟨e, heY, heT⟩, ?_, ?_, ?_, ?_⟩
  · rw [← heT, ← haT]
    infer_instance
  · rw [← heT, ← haT]
    infer_instance
  · intro hsur
    let := hsur
    rw [← heT, ← haT]
    infer_instance
  · intro t
    rw [← heT, ← haT, Scheme.Hom.finrank_comp_left_of_isIso,
      Scheme.Hom.finrank_comp_of_finrank_eq_const a
        (Limits.pullback.snd p.left (testRoot P r).map) 2 harank,
      Scheme.Hom.finrank_pullback_snd]

end ArithmeticThetaActualLevelR0208
#print axioms ArithmeticThetaActualLevelR0208.FiniteEtaleActualLevelProof.anchorTest
#print axioms ArithmeticThetaActualLevelR0208.finite_etale_actual_level
