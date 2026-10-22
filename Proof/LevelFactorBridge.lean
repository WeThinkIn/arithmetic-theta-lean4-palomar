module
public import ExtensionFactorBridge
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
noncomputable section
namespace PalomarLevel911
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaActualLevelR0208
open ArithmeticThetaMetaplecticStackR0207 ArithmeticThetaMetaplecticComparisonR0206
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower ArithmeticThetaCoverComparison
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaExtendedMetaplecticR0241

private lemma old_interior_over
    {k : Type} [Field k] [CharZero k] {n h : ℕ}
    {A : ArithmeticThetaLatticeSectionsR0188.Matrices n h}
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) :
    ArithmeticThetaCompactModularityR0209.interiorInclusion G.root ≫
        ArithmeticThetaArithmeticFieldR0231.structureMap G =
      (ArithmeticThetaCompactModularityR0209.interiorBase G.root).hom := by
  change ArithmeticThetaCompactModularityR0209.interiorInclusion G.root ≫
    (ArithmeticThetaCompactModularityR0209.compactMap G.root ≫ G.root.compact.projection) = _
  rw [← Category.assoc, pullback.condition, Category.assoc, G.root.compact.over_eq]
  rfl

def StandardLevel : Prop :=
∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L), ∃ (P : ArithmeticThetaActualLevelR0208.Provider k L) (C : ArithmeticThetaMetaplecticStackR0207.Coherence L (ArithmeticThetaLocalWeierstrassR0203.Base k)), Nonempty (ArithmeticThetaMetaplecticStackR0207.ForgetData L (ArithmeticThetaLocalWeierstrassR0203.Base k) C) ∧ CategoryTheory.Pseudofunctor.IsStack C.functor (ArithmeticThetaRootStackR0198.rootTopology (ArithmeticThetaLocalWeierstrassR0203.Base k)) ∧ ∀ (Y : CategoryTheory.Over (ArithmeticThetaLocalWeierstrassR0203.Base k)) (p : Quiver.Hom Y (ArithmeticThetaActualLevelR0208.base P)) (H : ArithmeticThetaSquareLinesR0192.SquareLine Y.left ((AlgebraicGeometry.Scheme.Modules.pullback p.left).obj (ArithmeticThetaActualLevelR0208.hodge P))), AlgebraicGeometry.IsFinite p.left → AlgebraicGeometry.Etale p.left → Nonempty (ArithmeticThetaActualLevelR0208.PullbackComparison (PalomarCyclotomic669.anchoredMap C Y (ArithmeticThetaActualLevelR0208.object P p H))) ∧ ArithmeticThetaActualLevelR0208.FiniteEtaleLevel P p H (PalomarCyclotomic669.anchoredMap C Y (ArithmeticThetaActualLevelR0208.object P p H))

def InteriorTransport : Prop :=
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
    (hI : ArithmeticThetaCompactModularityR0209.InteriorGeometry G.root),
    IsPullback (toOldInterior ι G) (interiorBase ι G).hom
      (ArithmeticThetaCompactModularityR0209.interiorBase G.root).hom
      (ArithmeticThetaScalarExtensionR0240.fieldMap ι) ∧
    IsOpenImmersion (inclusion ι G) ∧ DenseRange (inclusion ι G).base

def ClassifierTransport : Prop :=
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L →
      ∀ (P : ArithmeticThetaActualLevelR0208.Provider k L)
        (Q : ArithmeticThetaActualLevelR0208.Provider l L),
      ∀ (Y : Over (Base k)) (p : Y ⟶ base P)
        (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
        (Z : Over (Base l)) (a : Z.left ⟶ Y.left),
      IsPullback a Z.hom Y.hom (ArithmeticThetaScalarExtensionR0240.fieldMap ι) →
      IsPullback a (classifiedMap Q Z (extendedObject P Y p H Z a)).left p.left
        (coefficientMap ι P Q)

def SquareTransport : Prop :=
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
      (ι : k →+* l) (n h : ℕ) (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h)
      (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A)
      (u : ArithmeticThetaCompactModularityR0209.Universal G.root),
      tensorPowerMap (actualLineComparison ι G u).hom 2 ≫
        (restrictedCompactSquare ι G u).hom = (pulledObject ι G u).root.square.hom

def ArrowTransport : Prop :=
∀ {k : Type} [Field k] [CharZero k] {L : ℕ}
    (hL : 3 ≤ L) (heven : Even L) (P : Provider k L)
    (S : Over (Base k)) (X : (group L S.left).Objects)
    (H : SquareLine S.left
      ((Scheme.Modules.pullback (classifiedMap P S X).left).obj (hodge P)))
    (e : H.line ≅ X.root.line)
    (hs : tensorPowerMap e.hom 2 ≫ X.root.square.hom =
      H.square.hom ≫ (ActualFamilyFPQCDescentProof.classifiedModel P.universal X).hodge.hom),
    ∃ a : Arrow (object P (classifiedMap P S X) H) X, a.line.hom = e.hom

theorem standard_level : StandardLevel := by
 intro k _ _ L hL heven
 obtain ⟨P,C,hforget,hstack,hlevel⟩ := standard_actual_metaplectic_level k L hL heven
 refine ⟨P,C,hforget,hstack,?_⟩
 intro Y p H hfin het
 simpa only [PalomarCyclotomic669.anchoredMap_eq_original] using hlevel Y p H hfin het

theorem interior_transport : InteriorTransport := by
  intro k l _ _ _ _ ι n h hn hh A hA G hI
  have hs := (IsPullback.of_hasPullback
    (ArithmeticThetaScalarExtensionR0240.projection ι G)
    (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root)).flip.paste_vert
      (IsPullback.of_hasPullback
        (ArithmeticThetaArithmeticFieldR0231.structureMap G)
        (ArithmeticThetaScalarExtensionR0240.fieldMap ι))
  rw [old_interior_over G] at hs
  letI : IsOpenImmersion (ArithmeticThetaCompactModularityR0209.interiorInclusion G.root) :=
    hI.1
  letI : IsOpenImmersion (inclusion ι G) := inferInstance
  refine ⟨hs, inferInstance, ?_⟩
  have hg := ArithmeticThetaScalarExtensionR0240.scalar_extension_geometry
    k l ι n h hn hh A hA G
  letI : GeometricallyIntegral (ArithmeticThetaScalarExtensionR0240.structureMap ι G) :=
    hg.2.2.2.1
  letI : IsIntegral (ArithmeticThetaScalarExtensionR0240.Space ι G) :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (ArithmeticThetaScalarExtensionR0240.structureMap ι G)
  letI : IsIntegral G.root.cover.space := G.root.cover.integral
  haveI : Nonempty (ArithmeticThetaCompactModularityR0209.Interior G.root) :=
    hI.2.1.nonempty
  letI : Surjective (ArithmeticThetaScalarExtensionR0240.fieldMap ι) := inferInstance
  haveI : Nonempty (Interior ι G) :=
    (toOldInterior ι G).surjective.nonempty
  exact (inclusion ι G).isOpenMap.denseRange_of_isPreirreducibleSpace

theorem classifier_transport : ClassifierTransport := extended_classifier_cartesian

theorem square_transport : SquareTransport := extended_compact_square

theorem arrow_transport : ArrowTransport := by
  intro k _ _ L hL heven P S X H e hs
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

theorem recover_level (hi : InteriorTransport) (hc : ClassifierTransport)
 (hsq : SquareTransport) (ha : ArrowTransport) (hl : StandardLevel) :
 PalomarExtension908.LevelTransport := by
  intro k l _ _ _ _ ι n h hn hh A hA G hGn
  have hG := (PalomarCyclotomic669.actualLevel_iff_original G.root).mp hGn
  apply (PalomarRemaining861.extendedLevel_iff_original ι G).mpr
  have hN : 0 < commonN A := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : 3 ≤ level (commonN A) := by
    have hp := pow_pos hN 2
    dsimp [level]
    omega
  have heven : Even (level (commonN A)) := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [level]
    omega
  obtain ⟨hs, hopen, hdense⟩ := hi k l ι n h hn hh A hA G hG.1
  obtain ⟨u, _⟩ := hG.2
  obtain ⟨Q, C, hforget, hstack, hlevel⟩ :=
    hl l (level (commonN A)) hL heven
  have hc : IsPullback (toOldInterior ι G) (targetMap ι G u Q).left
      (ArithmeticThetaCompactModularityR0209.levelMap G.root u).left
      (coefficientMap ι (oldProvider G u) Q) :=
    hc k l ι _ hL heven (oldProvider G u) Q
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
  simp only [PalomarCyclotomic669.anchoredMap_eq_original] at hpull hfinite
  refine ⟨hopen, hdense, u, Q, C, hforget, hstack, ?_, hpull, hfinite, ?_⟩
  · apply ha hL heven Q
      (interiorBase ι G) (pulledObject ι G u) (targetSquare ι G u Q)
      (actualLineComparison ι G u).symm
    have hsquare := hsq k l ι n h A G u
    rw [← hsquare]
    simp only [Iso.symm_hom, ← Category.assoc, ← tensorPowerMap_comp,
      Iso.inv_hom_id, tensorPowerMap_id, Category.id_comp]
    simp only [targetSquare, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · intro z
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hc]
    exact hG.1.2.2.2.2 _

theorem level_transport : PalomarExtension908.LevelTransport :=
 recover_level interior_transport classifier_transport square_transport arrow_transport standard_level
end PalomarLevel911
