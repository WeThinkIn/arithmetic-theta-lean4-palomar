import ExtendedClassifierCartesianR0241
import ExtendedInteriorGeometryR0241
import ExtendedCompactSquareR0241

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaExtendedMetaplecticR0241
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaActualLevelR0208
open ArithmeticThetaMetaplecticStackR0207 ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaCoverComparison
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183

namespace ExtendedActualLevelProof

private lemma classified_arrow {k : Type} [Field k] [CharZero k] {L : ℕ}
    (hL : 3 ≤ L) (heven : Even L) (P : Provider k L)
    (S : Over (Base k)) (X : (group L S.left).Objects)
    (H : SquareLine S.left
      ((Scheme.Modules.pullback (classifiedMap P S X).left).obj (hodge P)))
    (e : H.line ≅ X.root.line)
    (hs : tensorPowerMap e.hom 2 ≫ X.root.square.hom =
      H.square.hom ≫ (ActualFamilyFPQCDescentProof.classifiedModel P.universal X).hodge.hom) :
    ∃ a : Arrow (object P (classifiedMap P S X) H) X, a.line.hom = e.hom := by
  let m := model P (classifiedMap P S X)
  let n := ActualFamilyFPQCDescentProof.classifiedModel P.universal (S := S) X
  obtain ⟨g, ⟨hg, ht⟩, _⟩ := marked_cartesian_reconstruction k L hL heven
    P.atlas P.two P.cover P.quotient
    S.left S.left S.hom S.hom n.family m.family n.marking m.marking (𝟙 S.left)
    (classifiedMap P S X).left (classifiedMap P S X).left n.curve m.curve
    (Category.id_comp _) n.classifies m.classifies (Category.id_comp _).symm
  letI : IsIso g := hg.1.isIso_fst_of_isIso
  let d := ActualGroupoidProof.backward g hg.1 hg.2.1
  have hd : n.hodge.hom ≫ d.hom = m.hodge.hom :=
    FiberEquivalenceProof.hodge_backward P.universal n m g hg ht
  refine ⟨{
    curve := asIso g
    marked := hg
    cotangent := d.symm
    canonical := ActualGroupoidProof.backward_canonical g hg.1 hg.2.1
    line := e
    square := ?_
  }, rfl⟩
  change tensorPowerMap e.hom 2 ≫ X.root.square.hom =
    (H.square.hom ≫ m.hodge.hom) ≫ d.inv
  rw [← hd]
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hs

end ExtendedActualLevelProof

/-- The literal extended compact half-line defines the actual target-field
metaplectic level, retaining its normalized family arrow and every test fiber. -/
theorem extended_actual_metaplectic_level :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (n h : ℕ), 0 < n → 0 < h →
      ∀ (A : Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A,
      ArithmeticThetaCompactModularityR0209.ActualLevel G.root → ExtendedLevel ι G := by
  intro k l _ _ _ _ ι n h hn hh A hA G hG
  have hN : 0 < commonN A := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have heven : Even (level (commonN A)) := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [level]
    omega
  obtain ⟨hs, hopen, hdense⟩ := extended_interior_geometry k l ι n h hn hh A hA G hG
  obtain ⟨u, _⟩ := hG.2
  obtain ⟨Q, C, hforget, hstack, hlevel⟩ :=
    standard_actual_metaplectic_level l (level (commonN A)) hL heven
  have hc : IsPullback (toOldInterior ι G) (targetMap ι G u Q).left
      (ArithmeticThetaCompactModularityR0209.levelMap G.root u).left
      (coefficientMap ι (oldProvider G u) Q) :=
    extended_classifier_cartesian k l ι _ hL heven (oldProvider G u) Q
      (ArithmeticThetaCompactModularityR0209.interiorBase G.root)
      (ArithmeticThetaCompactModularityR0209.levelMap G.root u)
      (ArithmeticThetaCompactModularityR0209.openSquare G.root)
      (interiorBase ι G) (toOldInterior ι G) hs
  letI : IsFinite (ArithmeticThetaCompactModularityR0209.levelMap G.root u).left :=
    hG.1.2.2.1
  letI : Etale (ArithmeticThetaCompactModularityR0209.levelMap G.root u).left :=
    hG.1.2.2.2.1
  have hfin : IsFinite (targetMap ι G u Q).left :=
    MorphismProperty.of_isPullback hc inferInstance
  have het : Etale (targetMap ι G u Q).left :=
    MorphismProperty.of_isPullback hc inferInstance
  obtain ⟨hpull, hfinite⟩ := hlevel (interiorBase ι G)
    (targetMap ι G u Q) (targetSquare ι G u Q) hfin het
  refine ⟨hopen, hdense, u, Q, C, hforget, hstack, ?_, hpull, hfinite, ?_⟩
  · apply ExtendedActualLevelProof.classified_arrow hL heven Q
      (interiorBase ι G) (pulledObject ι G u) (targetSquare ι G u Q)
      (actualLineComparison ι G u).symm
    have hsquare := extended_compact_square k l ι n h A G u
    rw [← hsquare]
    simp only [Iso.symm_hom, ← Category.assoc, ← tensorPowerMap_comp,
      Iso.inv_hom_id, tensorPowerMap_id, Category.id_comp]
    simp only [targetSquare, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · intro z
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hc]
    exact hG.1.2.2.2.2 _

#print axioms extended_actual_metaplectic_level
end ArithmeticThetaExtendedMetaplecticR0241
