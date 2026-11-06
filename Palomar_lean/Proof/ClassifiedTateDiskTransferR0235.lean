module

public import TateHodgeGeneratorTransferR0235
public import OpenHodgeConstantComparisonR0234

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
noncomputable section
namespace ArithmeticThetaBoundaryConstantsR0235
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelConstantsR0234
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205
namespace ClassifiedTateDiskTransfer

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]

lemma laurent_power (ι : k →+* l) (a : PowerSeries k) :
    laurentMap ι (algebraMap (PowerSeries k) (LaurentSeries k) a) =
      algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι a) :=
  (Classical.choose_spec
    (ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι).1).1 a

lemma generic_square (ι : k →+* l) :
    genericInclusion l ≫ diskMap ι = punctureMap ι ≫ genericInclusion k := by
  simp only [genericInclusion, diskMap, punctureMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  exact (laurent_power ι a).symm

lemma disk_structure (ι : k →+* l) :
    diskMap ι ≫ diskStructure k = diskStructure l ≫ constants ι := by
  simp only [diskMap, diskStructure, constants, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  exact PowerSeries.map_C ι a

lemma puncture_structure (ι : k →+* l) :
    punctureMap ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))) =
      Spec.map (CommRingCat.ofHom (algebraMap l (LaurentSeries l))) ≫ constants ι := by
  have hk : (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (algebraMap k (PowerSeries k)) = algebraMap k (LaurentSeries k) := rfl
  have hl : (algebraMap (PowerSeries l) (LaurentSeries l)).comp
      (algebraMap l (PowerSeries l)) = algebraMap l (LaurentSeries l) := rfl
  have h := congrArg (fun t => genericInclusion l ≫ t) (disk_structure ι)
  rw [← Category.assoc, generic_square, Category.assoc] at h
  simpa only [genericInclusion, diskStructure, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hk, hl] using h

lemma disks_equal (ι : k →+* l) {L : ℕ}
    {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space)
    (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F)
    (T : DiskTest k L D X) (S : DiskTest l L E Y)
    (h : S.base ≫ f = punctureMap ι ≫ T.base) :
    S.disk ≫ F = diskMap ι ≫ T.disk := by
  have hl : genericInclusion l ≫ (S.disk ≫ F) =
      genericInclusion l ≫ (diskMap ι ≫ T.disk) := by
    rw [← Category.assoc, S.extends_eq.2.1, Category.assoc, hF.2,
      ← Category.assoc, h, Category.assoc, ← T.extends_eq.2.1,
      ← Category.assoc, ← generic_square, Category.assoc]
  have hr : (S.disk ≫ F) ≫ X.projection = diskStructure l ≫ constants ι := by
    rw [Category.assoc, hF.1, ← Category.assoc, S.extends_eq.1]
  have hr' : (diskMap ι ≫ T.disk) ≫ X.projection = diskStructure l ≫ constants ι := by
    rw [Category.assoc, T.extends_eq.1, disk_structure]
  let V : ValuativeCommSq X.projection :=
    { R := PowerSeries l, K := LaurentSeries l
      i₁ := genericInclusion l ≫ (S.disk ≫ F)
      i₂ := diskStructure l ≫ constants ι
      commSq := ⟨by rw [Category.assoc, hr]; rfl⟩ }
  have hv : ValuativeCriterion X.projection := by
    have hp := X.proper
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  obtain ⟨U⟩ := hv V
  exact congrArg CommSq.LiftStruct.l
    ((U.uniq ⟨S.disk ≫ F, rfl, hr⟩).trans
      (U.uniq ⟨diskMap ι ≫ T.disk, hl.symm, hr'⟩).symm)

/-- Retain the actual Tate cubic and law in the general family interface. -/
def family {L : ℕ} {D : LevelData k L} (T : Test k L D) : Family (Puncture k) where
  curve := Curve (LaurentSeries k) (TateCurve k L)
  p := structureMap (LaurentSeries k) (TateCurve k L)
  law :=
    { mul := T.level.law.mul, one := T.level.law.one, inv := T.level.law.inv
      mul_assoc := T.level.law.mul_assoc, one_mul := T.level.law.one_mul
      mul_one := T.level.law.mul_one, inv_mul_cancel := T.level.law.inv_mul_cancel
      mul_comm := T.level.originLaw.2, mul_natural := T.level.law.mul_natural }
  proper := MorphismProperty.of_isPullback T.classifies.2.1 D.atlas.descent.family.proper
  dimension := by
    letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.of_isPullback T.classifies.2.1 D.atlas.descent.family.smooth
  connected := MorphismProperty.of_isPullback T.classifies.2.1 D.atlas.descent.family.connected

lemma family_zero {L : ℕ} {D : LevelData k L} (T : Test k L D) :
    (family T).zero = origin (LaurentSeries k) (TateCurve k L) := by
  change (T.level.law.one (𝟙 (Puncture k))).val = _
  simpa only [Category.id_comp] using T.level.originLaw.1 (𝟙 (Puncture k))

lemma multiple_eq {L : ℕ} {D : LevelData k L} (T : Test k L D)
    {Z : Scheme} (t : Z ⟶ Puncture k) (n : ℕ)
    (x : NeronModelInfra.SchemeHomOver t (family T).p) :
    multiple (family T) t n x = T.level.law.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.level.law.mul t (multiple (family T) t n x) x =
      T.level.law.mul t (T.level.law.nsmul t n x) x
    rw [ih]

def level {L : ℕ} {D : LevelData k L} (T : Test k L D) : FullLevel (family T) L where
  x := T.level.marking.x
  y := T.level.marking.y
  killed_x := by rw [multiple_eq]; exact T.level.marking.killed_x
  killed_y := by rw [multiple_eq]; exact T.level.marking.killed_y
  avoids := by
    intro i j hij
    rw [multiple_eq, multiple_eq, family_zero]
    exact T.level.marking.avoids i j hij

lemma classifies {L : ℕ} {D : LevelData k L} (T : Test k L D) :
    Classifies D (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))))
      (family T) (level T) T.base T.map := by
  have hz : (family T).zero ≫ T.map =
      (T.base ≫ D.quotient.inclusion) ≫ (D.atlas.descent.family.law.one (𝟙 _)).val := by
    rw [family_zero]; exact T.classifies.2.2.1
  exact ⟨T.classifies.1, T.classifies.2.1, hz, T.classifies.2.2.2.1,
    T.classifies.2.2.2.2,
    GlobalSchemeClassifier.universal_multiplicative (family T) _ _ T.classifies.2.1 hz⟩

lemma marked {L : ℕ} (hL : 3 ≤ L) (ι : k →+* l)
    {D : LevelData k L} {E : LevelData l L} (T : Test k L D) (S : Test l L E)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b) (ht : Transfers ι T.level S.level b) :
    MarkedCartesian (family T) (family S) (level T) (level S) (punctureMap ι) b := by
  have hz : (family S).zero ≫ b = punctureMap ι ≫ (family T).zero := by
    rw [family_zero, family_zero]; exact hb.2.1
  refine ⟨hb.1, hz, ?_, ?_, ?_⟩
  · exact pointed_cartesian_group_law k _ _
      (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))))
      (family T) (family S) (punctureMap ι) b hb.1 hz
  · change S.level.marking.x.val ≫ b = punctureMap ι ≫ T.level.marking.x.val
    have h := ht.2 (⟨1, by omega⟩ : Fin L) (⟨0, by omega⟩ : Fin L)
    simpa only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint,
      S.level.law.nsmul_one_apply, S.level.law.nsmul_zero, S.level.law.mul_one,
      T.level.law.nsmul_one_apply, T.level.law.nsmul_zero, T.level.law.mul_one] using h
  · change S.level.marking.y.val ≫ b = punctureMap ι ≫ T.level.marking.y.val
    have h := ht.2 (⟨0, by omega⟩ : Fin L) (⟨1, by omega⟩ : Fin L)
    simpa only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint,
      S.level.law.nsmul_one_apply, S.level.law.nsmul_zero, S.level.law.one_mul,
      T.level.law.nsmul_one_apply, T.level.law.nsmul_zero, T.level.law.one_mul] using h

lemma classifiers {L : ℕ} (hL : 3 ≤ L) (he : Even L) (ι : k →+* l)
    {D : LevelData k L} {E : LevelData l L} (T : Test k L D) (S : Test l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (hf : RespectsClassifiers ι D E f)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b) (ht : Transfers ι T.level S.level b) :
    S.base ≫ f = punctureMap ι ≫ T.base ∧
      Classifies D
        (Spec.map (CommRingCat.ofHom (algebraMap l (LaurentSeries l))) ≫ constants ι)
        (family S) (level S) (S.base ≫ f) (b ≫ T.map) := by
  have hc := SchemeFullLevelUniversal.classifies_comp D.atlas (puncture_structure ι)
    (marked hL ι T S b hb ht) (classifies T)
  obtain ⟨a, ha⟩ := hf.2 _ _ (family S) (level S) S.base S.map (classifies S)
  obtain ⟨hbase, hmap⟩ := scheme_classifying_uniqueness k L hL he D.atlas D.two D.canonical
    D.cover D.quotient _ _ (family S) (level S) _ _ a (b ≫ T.map) ha hc
  exact ⟨hbase, hmap ▸ ha⟩

/-- Canonical affine differential comparison along a specified scheme map. -/
def affineComparison {R V : Type} [CommRing R] [CommRing V]
    (U : Family (ArithmeticThetaLocalWeierstrassR0203.Base R))
    (W : Family (ArithmeticThetaLocalWeierstrassR0203.Base V))
    (a : ArithmeticThetaLocalWeierstrassR0203.Base V ⟶ ArithmeticThetaLocalWeierstrassR0203.Base R)
    (g : W.curve ⟶ U.curve) (hc : IsPullback g W.p U.p a)
    (hz : W.zero ≫ g = a ≫ U.zero) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback U.zero).obj U.p.kaehler) ≅
      (Scheme.Modules.pullback W.zero).obj W.p.kaehler :=
  let ρ := (Spec.preimage a).hom
  let ha : Spec.map (CommRingCat.ofHom ρ) = a := Spec.map_preimage a
  pullbackEqIso ha.symm _ ≪≫
    affineHodgeComparison U W ρ g (by rw [ha]; exact hc) (by rw [ha]; exact hz)

lemma affine_normalization {R V : Type} [CommRing R] [CommRing V]
    (U : Family (ArithmeticThetaLocalWeierstrassR0203.Base R))
    (W : Family (ArithmeticThetaLocalWeierstrassR0203.Base V))
    (a : ArithmeticThetaLocalWeierstrassR0203.Base V ⟶ ArithmeticThetaLocalWeierstrassR0203.Base R)
    (g : W.curve ⟶ U.curve) (hc : IsPullback g W.p U.p a)
    (hz : W.zero ≫ g = a ≫ U.zero)
    (i : (Scheme.Modules.pullback g).obj U.zero.ker.module ≅ W.zero.ker.module)
    (hi : IdealCompatible U W g i) :
    (Scheme.Modules.pullback a).map (affineDifferential U) ≫
      (affineComparison U W a g hc hz).hom =
      (cotangentComparison U W a g hz i).hom ≫ affineDifferential W := by
  let ρ := (Spec.preimage a).hom
  have ha : Spec.map (CommRingCat.ofHom ρ) = a := Spec.map_preimage a
  have gen (a : ArithmeticThetaLocalWeierstrassR0203.Base V ⟶ ArithmeticThetaLocalWeierstrassR0203.Base R)
      (ha : a = Spec.map (CommRingCat.ofHom ρ))
      (hc : IsPullback g W.p U.p a) (hz : W.zero ≫ g = a ≫ U.zero) :
      (Scheme.Modules.pullback a).map (affineDifferential U) ≫
        (pullbackEqIso ha _).hom ≫
        (affineHodgeComparison U W ρ g (by rw [← ha]; exact hc)
          (by rw [← ha]; exact hz)).hom =
        (cotangentComparison U W a g hz i).hom ≫ affineDifferential W := by
    subst a
    simpa only [pullbackEqIso, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
      (affine_conormal_hodge_naturality R V U W ρ g hc hz).2.2 i hi
  exact gen a ha.symm hc hz

lemma classifier_derivative {R : Type} [CommRing R] {L : ℕ} (D : LevelData k L)
    (W : Family (ArithmeticThetaLocalWeierstrassR0203.Base R))
    (a : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶ OpenBase k L D)
    (g : W.curve ⟶ D.atlas.descent.family.curve)
    (hc : IsPullback g W.p D.atlas.descent.family.projection (a ≫ D.quotient.inclusion))
    (hz : W.zero ≫ g = (a ≫ D.quotient.inclusion) ≫
      (universalFamily k L D.atlas).zero)
    (e : (Scheme.Modules.pullback a).obj (weight D) ≅ Cotangent W)
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient W a g e) :
    e.hom ≫ affineDifferential W =
      ((Scheme.Modules.pullbackComp a D.quotient.inclusion).app _).hom ≫
        (affineComparison (universalFamily k L D.atlas) W
          (a ≫ D.quotient.inclusion) g hc hz).hom := by
  obtain ⟨hz', i, hi, hn⟩ := he
  let U := universalFamily k L D.atlas
  letI : IsIso (affineDifferential U) := AffineConormalHodgeNaturality.differential_isIso U
  apply (cancel_epi ((Scheme.Modules.pullback a).map
    ((Scheme.Modules.pullback D.quotient.inclusion).map (affineDifferential U)))).mp
  have hn' := affine_normalization U W (a ≫ D.quotient.inclusion) g hc hz i hi
  have h₁ := congrArg (fun q => q ≫ affineDifferential W) hn
  have h₂ := congrArg (fun q =>
    ((Scheme.Modules.pullbackComp a D.quotient.inclusion).app (Cotangent U)).hom ≫ q) hn'.symm
  have h₃ := congrArg (fun q => q ≫ (affineComparison U W _ g hc hz).hom)
    ((Scheme.Modules.pullbackComp a D.quotient.inclusion).hom.naturality
      (affineDifferential U)).symm
  simp only [Category.assoc] at h₁ h₃
  exact h₁.trans (h₂.trans h₃)

lemma pointed_zero_congr {R V : Type} [CommRing R] [CommRing V] [Algebra R V]
    {X Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R)) (q : X ⟶ Spec (CommRingCat.of V))
    (g : X ⟶ Y) (hc : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R V))))
    [SmoothOfRelativeDimension 1 p]
    (s : Spec (CommRingCat.of R) ⟶ Y) (t t' : Spec (CommRingCat.of V) ⟶ X)
    (ht : t = t')
    (hz : t ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R V)) ≫ s)
    (hz' : t' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R V)) ≫ s) :
    (pointedDifferentialIso p q g hc s t hz).hom ≫ (pullbackEqIso ht q.kaehler).hom =
      (pointedDifferentialIso p q g hc s t' hz').hom := by
  subst t'
  simp only [pullbackEqIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]

def derivative {L : ℕ} {D : LevelData k L} (T : Test k L D) :
    Cotangent (family T) ≅ Hodge (LaurentSeries k) (TateCurve k L) := by
  letI := AffineConormalHodgeNaturality.differential_isIso (family T)
  exact asIso (affineDifferential (family T)) ≪≫
    pullbackEqIso (family_zero T) (family T).p.kaehler

lemma test_derivative {L : ℕ} {D : LevelData k L} (T : Test k L D)
    (e : (Scheme.Modules.pullback T.base).obj (weight D) ≅ Cotangent (family T))
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient (family T) T.base T.map e) :
    e.hom ≫ (derivative T).hom = (openTestIso k L T).hom := by
  have hz := (classifies T).2.2.1
  have hn := classifier_derivative D (family T) T.base T.map T.classifies.2.1 hz e he
  have hh : (affineComparison (universalFamily k L D.atlas) (family T)
      (T.base ≫ D.quotient.inclusion) T.map T.classifies.2.1 hz).hom ≫
      (pullbackEqIso (family_zero T) (family T).p.kaehler).hom = (testIso k L T).hom := by
    unfold affineComparison
    dsimp only [Iso.trans_hom]
    rw [Category.assoc (pullbackEqIso _ _).hom]
    let ρ := (Spec.preimage (T.base ≫ D.quotient.inclusion)).hom
    letI : Algebra D.atlas.quotient.ring (LaurentSeries k) := ρ.toAlgebra
    letI : SmoothOfRelativeDimension 1 (universalFamily k L D.atlas).p := D.atlas.descent.family.smooth
    change (pullbackEqIso _ _).hom ≫
      (pointedDifferentialIso _ _ T.map _ _ _ _).hom ≫
        (pullbackEqIso (family_zero T) _).hom = _
    rw [pointed_zero_congr]
    rfl
  have h := congrArg (fun q => q ≫
    (pullbackEqIso (family_zero T) (family T).p.kaehler).hom) hn
  have h' : e.hom ≫ (derivative T).hom =
      ((Scheme.Modules.pullbackComp T.base D.quotient.inclusion).app _).hom ≫
      ((affineComparison (universalFamily k L D.atlas) (family T)
        (T.base ≫ D.quotient.inclusion) T.map T.classifies.2.1 hz).hom ≫
        (pullbackEqIso (family_zero T) (family T).p.kaehler).hom) := by
    simpa only [derivative, Iso.trans_hom, asIso_hom, Category.assoc] using h
  exact h'.trans (congrArg (fun q =>
    ((Scheme.Modules.pullbackComp T.base D.quotient.inclusion).app _).hom ≫ q) hh)


lemma pointed_sections_congr {R V : Type} [CommRing R] [CommRing V] [Algebra R V]
    {X Y : Scheme} (p : Y ⟶ Spec (CommRingCat.of R)) (q : X ⟶ Spec (CommRingCat.of V))
    (g : X ⟶ Y) (hc : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R V))))
    [SmoothOfRelativeDimension 1 p]
    (s s' : Spec (CommRingCat.of R) ⟶ Y) (t t' : Spec (CommRingCat.of V) ⟶ X)
    (hs : s = s') (ht : t = t')
    (hz : t ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R V)) ≫ s)
    (hz' : t' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R V)) ≫ s') :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R V)))).map
        (pullbackEqIso hs p.kaehler).hom ≫
      (pointedDifferentialIso p q g hc s' t' hz').hom =
    (pointedDifferentialIso p q g hc s t hz).hom ≫ (pullbackEqIso ht q.kaehler).hom := by
  subst s'; subst t'
  simp only [pullbackEqIso, eqToIso_refl, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

lemma cotangent_transfer {L : ℕ} (ι : k →+* l)
    {D : LevelData k L} {E : LevelData l L} (T : Test k L D) (S : Test l L E)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b)
    (hz : (family S).zero ≫ b = punctureMap ι ≫ (family T).zero)
    (i : (Scheme.Modules.pullback b).obj (family T).zero.ker.module ≅
      (family S).zero.ker.module)
    (hi : IdealCompatible (family T) (family S) b i) :
    (Scheme.Modules.pullback (punctureMap ι)).map (derivative T).hom ≫
      (tateHodgeIso ι T.level b hb).hom =
      (cotangentComparison (family T) (family S) (punctureMap ι) b hz i).hom ≫
        (derivative S).hom := by
  letI : Algebra (LaurentSeries k) (LaurentSeries l) := (laurentMap ι).toAlgebra
  letI : SmoothOfRelativeDimension 1 (family T).p := (family T).dimension
  have hn := (affine_conormal_hodge_naturality (LaurentSeries k) (LaurentSeries l)
    (family T) (family S) (laurentMap ι) b hb.1 hz).2.2 i hi
  have hp := pointed_sections_congr (family T).p (family S).p b hb.1
    (family T).zero (origin (LaurentSeries k) (TateCurve k L))
    (family S).zero (origin (LaurentSeries l) (TateCurve l L))
    (family_zero T) (family_zero S) hz hb.2.1
  change (Scheme.Modules.pullback (punctureMap ι)).map
      (pullbackEqIso (family_zero T) (family T).p.kaehler).hom ≫
      (tateHodgeIso ι T.level b hb).hom =
    (affineHodgeComparison (family T) (family S) (laurentMap ι) b hb.1 hz).hom ≫
      (pullbackEqIso (family_zero S) (family S).p.kaehler).hom at hp
  have h₁ := congrArg (fun q =>
    (Scheme.Modules.pullback (punctureMap ι)).map (affineDifferential (family T)) ≫ q) hp
  have h₂ := congrArg (fun q => q ≫
    (pullbackEqIso (family_zero S) (family S).p.kaehler).hom) hn
  simp only [Category.assoc] at h₂
  simpa only [derivative, Iso.trans_hom, asIso_hom, Functor.map_comp,
    Category.assoc, punctureMap] using h₁.trans h₂

lemma pullbackCongr_eq {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = (pullbackEqIso h M).hom := by
  subst g
  rfl

#print axioms cotangent_transfer

lemma comparison_hodge {L : ℕ} (hL : 3 ≤ L) (heven : Even L) (ι : k →+* l)
    {D : LevelData k L} {E : LevelData l L} (T : Test k L D) (S : Test l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (hf : RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (he : HodgeCompatible ι D E f e)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b) (ht : Transfers ι T.level S.level b) :
    ∃ h : S.base ≫ f = punctureMap ι ≫ T.base,
      (testComparison ι T S f e h).hom ≫ (openTestIso l L S).hom =
        (Scheme.Modules.pullback (punctureMap ι)).map (openTestIso k L T).hom ≫
          (tateHodgeIso ι T.level b hb).hom := by
  obtain ⟨hbase, hcls⟩ := classifiers hL heven ι T S f hf b hb ht
  obtain ⟨ekT, hekT, _⟩ := classifying_cotangent_hodge k L hL heven
    D.atlas D.two D.cover D.quotient _ _ (family T) (level T) T.base T.map (classifies T)
  obtain ⟨elS, helS, _⟩ := classifying_cotangent_hodge l L hL heven
    E.atlas E.two E.cover E.quotient _ _ (family S) (level S) S.base S.map (classifies S)
  obtain ⟨ekS, hekS, _⟩ := classifying_cotangent_hodge k L hL heven
    D.atlas D.two D.cover D.quotient _ _ (family S) (level S) (S.base ≫ f) (b ≫ T.map) hcls
  have hz : (family S).zero ≫ b = punctureMap ι ≫ (family T).zero := by
    rw [family_zero, family_zero]; exact hb.2.1
  obtain ⟨i, hi, _⟩ := cartesian_identity_ideal _ _ (family T) (family S)
    (punctureMap ι) b hb.1 hz
  let c := cotangentComparison (family T) (family S) (punctureMap ι) b hz i
  have hc : CotangentCompatible (family T) (family S) (punctureMap ι) b hz c := ⟨i, hi, rfl⟩
  have hn := OpenHodgeComparisonProof.natural_general D (family T) (family S)
    (punctureMap ι) b hz T.base (S.base ≫ f) hbase.symm T.map (b ≫ T.map) rfl
    ekT ekS c hekT hekS hc
  rw [pullbackCongr_eq] at hn
  have heq := he _ _ (family S) (level S) S.base S.map (b ≫ T.map)
    (classifies S) hcls elS ekS helS hekS
  have hcomp : (testComparison ι T S f e hbase).hom ≫ elS.hom =
      (Scheme.Modules.pullback (punctureMap ι)).map ekT.hom ≫ c.hom := by
    simpa only [testComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, heq, Iso.inv_hom_id_assoc, ← Iso.app_hom] using hn.symm
  have hd := cotangent_transfer ι T S b hb hz i hi
  have hT := test_derivative T ekT hekT
  have hS := test_derivative S elS helS
  have h₁ := congrArg (fun q => q ≫ (derivative S).hom) hcomp
  have h₂ := congrArg (fun q =>
    (Scheme.Modules.pullback (punctureMap ι)).map ekT.hom ≫ q) hd.symm
  have h₃ := congrArg (fun q =>
    (Scheme.Modules.pullback (punctureMap ι)).map q ≫ (tateHodgeIso ι T.level b hb).hom) hT
  simp only [Functor.map_comp, Category.assoc] at h₃
  simp only [Category.assoc, hS] at h₁
  exact ⟨hbase, h₁.trans (h₂.trans h₃)⟩

#print axioms comparison_hodge

lemma test_generator {L : ℕ} {D : LevelData k L} (T : Test k L D) :
    (openTestIso k L T).hom.app ⊤ (testGenerator T) = hodgeGenerator k L T.differential := by
  change Scheme.Modules.Hom.app ((openTestIso k L T).inv ≫ (openTestIso k L T).hom) ⊤ _ = _
  rw [Iso.inv_hom_id]
  rfl

lemma normalized_test {L : ℕ} (hL : 3 ≤ L) (heven : Even L) (ι : k →+* l)
    {D : LevelData k L} {E : LevelData l L} (T : Test k L D) (S : Test l L E)
    (f : OpenBase l L E ⟶ OpenBase k L D) (hf : RespectsClassifiers ι D E f)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E)
    (he : HodgeCompatible ι D E f e)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b) (ht : Transfers ι T.level S.level b) :
    TestCompatible ι T S f e := by
  obtain ⟨h, hc⟩ := comparison_hodge hL heven ι T S f hf e he b hb ht
  refine ⟨h, ?_⟩
  have hg := tate_hodge_generator_transfer k l ι L hL heven T.level b hb
    T.differential S.differential T.normalized S.normalized
  simp only [res_refl] at hg ⊢
  have hh := congrArg (fun q => q.app (punctureMap ι ⁻¹ᵁ ⊤)
    (Scheme.Modules.pullbackLocalSection (punctureMap ι) (testGenerator T))) hc
  change (openTestIso l L S).hom.app (punctureMap ι ⁻¹ᵁ ⊤)
      ((testComparison ι T S f e h).hom.app (punctureMap ι ⁻¹ᵁ ⊤)
        (Scheme.Modules.pullbackLocalSection (punctureMap ι) (testGenerator T))) =
    (tateHodgeIso ι T.level b hb).hom.app (punctureMap ι ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullback (punctureMap ι)).map (openTestIso k L T).hom).app (punctureMap ι ⁻¹ᵁ ⊤)
        (Scheme.Modules.pullbackLocalSection (punctureMap ι) (testGenerator T))) at hh
  rw [← Scheme.Modules.pullbackLocalSection_app, test_generator] at hh
  apply (ConcreteCategory.bijective_of_isIso
    ((openTestIso l L S).hom.app (punctureMap ι ⁻¹ᵁ ⊤))).1
  exact hh.trans (hg.trans (test_generator S).symm)

#print axioms normalized_test

#print axioms test_derivative

#print axioms classifiers
#print axioms disks_equal

end ClassifiedTateDiskTransfer
/-- Exact coefficient transport of the classified normalized Tate test and its entire disk. -/
theorem classified_tate_disk_transfer :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L), ∀ (f : Quiver.Hom (ArithmeticThetaLevelCompactificationR0179.OpenBase l L E) (ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)), ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (ArithmeticThetaLevelConstantsR0234.weight D)) (ArithmeticThetaLevelConstantsR0234.weight E)), ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e → ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (F : Quiver.Hom (Y.space) (X.space)) (hF : ArithmeticThetaLevelConstantsR0234.Extends ι D E X Y f F), ∀ (T : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X) (S : ArithmeticThetaBoundaryHodgeR0182.DiskTest l L E Y) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries l) (ArithmeticThetaTateCuspsR0181.TateCurve l L)) (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L))), ArithmeticThetaBoundaryConstantsR0235.CurveMap ι L b → ArithmeticThetaBoundaryConstantsR0235.Transfers ι T.level S.level b → ArithmeticThetaBoundaryConstantsR0235.TestCompatible ι T.toTest S.toTest f e ∧ CategoryTheory.CategoryStruct.comp S.disk F = CategoryTheory.CategoryStruct.comp (ArithmeticThetaBoundaryConstantsR0235.diskMap ι) T.disk := by
  intro k l _ _ _ _ ι L hL he D E f hf e heH X Y F hF T S b hb ht
  have h := ClassifiedTateDiskTransfer.normalized_test hL he ι T.toTest S.toTest f hf e heH b hb ht
  exact ⟨h, ClassifiedTateDiskTransfer.disks_equal ι f F hF T S h.choose⟩

#print axioms classified_tate_disk_transfer

end ArithmeticThetaBoundaryConstantsR0235
