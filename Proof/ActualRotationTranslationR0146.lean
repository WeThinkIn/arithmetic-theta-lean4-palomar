module

public import ActualGenericGroupLawR0146
public import MarkedSectionAlgebraizationR0136

@[expose] public section

/-! Single-rotation comparison on the actual generic curve.
The supporting lemmas below retain the specified structural map and all test schemes.
The difference morphism avoids the origin and is constant on its affine complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146.ActualRotationTranslation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141 WeierstrassProjModel
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma markedLift_unique (M : Model k T) (i : Fin r) (a : kˣ)
    (s p : baseScheme k ⟶ M.X) (hs : MarkedLift k M i a s)
    (hp : MarkedLift k M i a p) : s = p := by
  apply MarkedSectionAlgebraizationR0136.hom_ext k
  intro n
  exact (hs.2 n).trans (hp.2 n).symm

lemma origin_rotation (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (next r hr (zeroIndex r hr)) 1 p) :
    s ≫ rot.hom = p := by
  exact markedLift_unique k M _ _ _ _
    (algebraized_marked_transport k r hr h3 T M hM rot scal inv ha _ _ s hs).1 hp

lemma genericMap_structure (M : Model k T) (f : M.X ⟶ M.X)
    (hf : f ≫ M.p = M.p) :
    genericMap k M f hf ≫ genericStructure k M = genericStructure k M := by
  exact pullback.lift_snd _ _ _

lemma genericPoint_map (M : Model k T) (f : M.X ⟶ M.X)
    (hf : f ≫ M.p = M.p) (s p : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (hp : p ≫ M.p = 𝟙 _) (hsp : s ≫ f = p) :
    genericPoint k M s hs ≫ genericMap k M f hf = genericPoint k M p hp := by
  apply pullback.hom_ext
  · simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericMap, genericInclusion, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
    rw [hsp]
  · simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericMap, genericStructure, Category.assoc, pullback.lift_snd]

lemma generic_origin_rotation (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (next r hr (zeroIndex r hr)) 1 p) :
    genericPoint k M s hs.1 ≫ rotationMap k M rot scal inv ha =
      genericPoint k M p hp.1 := by
  exact genericPoint_map k M rot.hom _ s p hs.1 hp.1
    (origin_rotation k h3 M hM s hs rot scal inv ha p hp)

/-- A single stage rotation has no fixed topological point: a purported
fixed point would belong to both opposite, disjoint coordinate opens. -/
lemma stage_rotation_no_fixed {n : ℕ} {E : B k n false ≃+* B k n true}
    (D : Atlas k r n hr E) (g : D.X ≅ D.X)
    (hg : StageAction k D (next r hr) 1 false g) (x : D.X) : g.hom x ≠ x := by
  obtain ⟨i, a, rfl⟩ := D.covers x
  intro h
  obtain ⟨_, f, hf, hc⟩ := hg
  rw [TowerPeriodRotationR0137.coordinate_unique k n f hf] at hc
  have he : D.chart i a = D.chart (next r hr i) a := by
    have hh := congrArg (fun q : specA k n ⟶ D.X => q a) (hc i)
    simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp,
      Scheme.Hom.comp_apply, h] using hh
  obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent i) a a he
  exact Set.disjoint_left.mp (legs_disjoint k n E) ⟨z, hz⟩ ⟨z, hz'⟩

/-- A proper scheme mapping into the rotation equalizer is empty. Properness
forces a point into the special fiber, where the stage rotation is fixed-point-free. -/
lemma proper_rotation_fixed_empty (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) {Z : Scheme.{u}} (q : Z ⟶ M.X)
    [IsProper (q ≫ M.p)] (hq : q ≫ rot.hom = q) : IsEmpty Z := by
  refine ⟨fun z => ?_⟩
  obtain ⟨y, _, hy⟩ := (q ≫ M.p).isClosedMap.specializingMap
    (IsLocalRing.specializes_closedPoint ((q ≫ M.p) z))
  obtain ⟨b, hb⟩ := AlgebraizedGenericSmoothnessR0135.closedPoint_in_baseInclusion k
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback (hM.2.2.1 0) (q y) b
    (hy.trans hb.symm)
  obtain ⟨g, hg, hrot⟩ := ha.1
  have hi : IsClosedImmersion (M.inclusion 0) :=
    AlgebraizedGeometricConnectednessR0135.stage_closed k M hM 0
  let := hi
  have hfix : (g 0).hom w = w := by
    apply (Scheme.Hom.isClosedEmbedding (M.inclusion 0)).injective
    have hh := congrArg (fun f : (T.atlas 0).X ⟶ M.X => f w) (hrot.2 0)
    have hqy := congrArg (fun f : Z ⟶ M.X => f y) hq
    simp only [Scheme.Hom.comp_apply] at hh hqy
    exact hh.symm.trans ((congrArg rot.hom hw).trans (hqy.trans hw.symm))
  exact stage_rotation_no_fixed k (T.atlas 0) (g 0) (hg.2 0) w hfix

/-- The relative equalizer is proper, so fixed morphisms from arbitrary
test schemes have empty domain. This includes geometric points over all extensions. -/
lemma rotation_fixed_morphism_empty (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) {W : Scheme.{u}} (q : W ⟶ M.X)
    (hq : q ≫ rot.hom = q) : IsEmpty W := by
  let : IsProper M.p := hM.1
  let A : Over (baseScheme k) := Over.mk M.p
  let : IsSeparated A.hom := inferInstanceAs (IsSeparated M.p)
  let R : A ⟶ A := Over.homMk rot.hom (modelOver k M _ _ _ rot ha.1)
  let I : A ⟶ A := 𝟙 A
  let Z := equalizer R I
  let j : Z.left ⟶ M.X := (equalizer.ι R I).left
  have hj : j ≫ rot.hom = j := by
    have h := congrArg (fun f : Z ⟶ A => f.left) (equalizer.condition R I)
    simpa [R, I, j, Over.comp_left] using h
  let : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (equalizer.ι R I).left)
  let : IsProper (j ≫ M.p) := inferInstance
  have hZ : IsEmpty Z.left := proper_rotation_fixed_empty k M hM rot scal inv ha j hj
  let Q : Over.mk (q ≫ M.p) ⟶ A := Over.homMk q rfl
  have hQ : Q ≫ R = Q ≫ I := by
    apply Over.OverMorphism.ext
    simpa [Q, R, I, Over.comp_left] using hq
  let l := equalizer.lift Q hQ
  exact ⟨fun w => hZ.false (l.left w)⟩

/-- No geometric point of the actual generic curve is fixed by rotation. -/
lemma generic_rotation_fixed_morphism_empty (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) {W : Scheme.{u}} (q : W ⟶ genericScheme k M)
    (hq : q ≫ rotationMap k M rot scal inv ha = q) : IsEmpty W := by
  apply rotation_fixed_morphism_empty k M hM rot scal inv ha (q ≫ genericInclusion k M)
  have hh := congrArg (fun f => f ≫ genericInclusion k M) hq
  simpa only [rotationMap, genericMap, genericInclusion, Category.assoc,
    pullback.lift_fst] using hh

/-- Pullback on test points is a group homomorphism, including inversion. -/
lemma inv_natural {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {V W : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (t' : W ⟶ Spec (CommRingCat.of R)) (q : W ⟶ V) (hq : q ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp q hq (G.inv t x) = G.inv t' (schemeHomOverComp q hq x) := by
  let := G.pointGroup t'
  apply eq_inv_of_mul_eq_one_left
  change G.mul t' (schemeHomOverComp q hq (G.inv t x)) (schemeHomOverComp q hq x) = G.one t'
  rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]

/-- Any morphism into an affine scheme is constant when the source has only
base global functions. The constant is its value at the specified section. -/
lemma affine_map_constant {K : Type u} [Field K] {C A : Scheme.{u}} [IsAffine A]
    (π : C ⟶ Spec (CommRingCat.of K))
    (ε : Spec (CommRingCat.of K) ⟶ C) (hε : ε ≫ π = 𝟙 _)
    (hπ : Function.Surjective π.appTop) (q : C ⟶ A) : q = π ≫ ε ≫ q := by
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  ext a
  obtain ⟨b, hb⟩ := hπ (q.appTop a)
  have he : ε.appTop (π.appTop b) = b := by
    have hh := congrArg (fun f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) => f.appTop b) hε
    simpa using hh
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← hb, he]

open ArithmeticThetaCubicModelR0144 ArithmeticThetaAlgebraicCoordinatesR0143

def difference (M : Model k T) (G : Law k M)
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M) :
    SchemeHomOver (genericStructure k M) (genericStructure k M) :=
  G.mul (genericStructure k M) ⟨f, hf⟩
    (G.inv (genericStructure k M) ⟨𝟙 _, Category.id_comp _⟩)

lemma difference_natural (M : Model k T) (G : Law k M)
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (x : SchemeHomOver t (genericStructure k M)) :
    x.val ≫ (difference k M G f hf).val =
      (G.mul t ⟨x.val ≫ f, by rw [Category.assoc, hf, x.property]⟩ (G.inv t x)).val := by
  have hn := G.mul_natural (genericStructure k M) t x.val x.property
    ⟨f, hf⟩ (G.inv (genericStructure k M) ⟨𝟙 _, Category.id_comp _⟩)
  rw [inv_natural] at hn
  have hx : schemeHomOverComp x.val x.property
      (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (genericStructure k M) (genericStructure k M)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at hn
  exact congrArg Subtype.val hn

lemma difference_range_complement (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    (G : Law k M) (hG : IsOriginLaw k M s hs G)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) :
    Set.range (difference k M G (rotationMap k M rot scal inv ha)
      (genericMap_structure k M rot.hom _)).val ⊆ (complement k M s : Set (genericScheme k M)) := by
  let f := rotationMap k M rot scal inv ha
  have hf : f ≫ genericStructure k M = genericStructure k M := genericMap_structure k M rot.hom _
  let d := difference k M G f hf
  let ε := genericPoint k M s hs
  let W := pullback d.val ε
  let q : W ⟶ genericScheme k M := pullback.fst d.val ε
  let a : W ⟶ Spec (CommRingCat.of (LaurentSeries k)) := pullback.snd d.val ε
  let t := q ≫ genericStructure k M
  have ha' : a = t := by
    calc a = (a ≫ ε) ≫ genericStructure k M := by rw [Category.assoc, genericPoint_structure]; simp
         _ = (q ≫ d.val) ≫ genericStructure k M := by rw [pullback.condition]
         _ = t := by rw [Category.assoc, d.property]
  have hq : q ≫ f = q := by
    let x : SchemeHomOver t (genericStructure k M) := ⟨q, rfl⟩
    let y : SchemeHomOver t (genericStructure k M) := ⟨q ≫ f, by rw [Category.assoc, hf]⟩
    have hd : G.mul t y (G.inv t x) = G.one t := by
      apply Subtype.ext
      rw [← difference_natural k M G f hf t x, hG.1]
      change q ≫ d.val = t ≫ ε
      exact (pullback.condition (f := d.val) (g := ε)).trans (congrArg (fun a => a ≫ ε) ha')
    let := G.pointGroup t
    have hxy : y = x := mul_inv_eq_one.mp hd
    exact congrArg Subtype.val hxy
  have hW : IsEmpty W := generic_rotation_fixed_morphism_empty k M hM rot scal inv ha q hq
  rw [complement_eq_genericPoint_compl k M hM s hs]
  rintro _ ⟨x, rfl⟩ ⟨b, hb⟩
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x b hb.symm
  exact hW.false w

lemma difference_constant (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) :
    (difference k M G (rotationMap k M rot scal inv ha) (genericMap_structure k M rot.hom _)).val =
      genericStructure k M ≫ genericPoint k M s hs.1 ≫
        (difference k M G (rotationMap k M rot scal inv ha) (genericMap_structure k M rot.hom _)).val := by
  let d := difference k M G (rotationMap k M rot scal inv ha) (genericMap_structure k M rot.hom _)
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  let U := complement k M s
  let : IsAffine U := complement_isAffineOpen k h3 M hM s hs X hX
  have hrange : Set.range d.val ⊆ Set.range U.ι := by
    simpa only [Scheme.Opens.range_ι] using difference_range_complement k M hM s hs.1 G hG rot scal inv ha
  let q := IsOpenImmersion.lift U.ι d.val hrange
  have hq : q ≫ U.ι = d.val := IsOpenImmersion.lift_fac _ _ _
  let := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  let := generic_integral k h3 M hM
  have hb := P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral_of_section
    (LaurentSeries k) (X := genericScheme k M) (genericStructure k M) (genericPoint k M s hs.1) (genericPoint_structure k M s hs.1)
  have hsurj : Function.Surjective (genericStructure k M).appTop := by
    intro a
    obtain ⟨b, hb⟩ := hb.2 a
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv b, hb⟩
  have hh := affine_map_constant (genericStructure k M) (genericPoint k M s hs.1)
    (genericPoint_structure k M s hs.1) hsurj q
  have heq := congrArg (fun f => f ≫ U.ι) hh
  simpa only [Category.assoc, hq] using heq


end ArithmeticThetaMarkedGroupLawR0146.ActualRotationTranslation

namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ActualRotationTranslation

/-- The actual single rotation is translation by the actual marked point (1,1),
with equality on every test scheme in the original universe. -/
theorem actual_rotation_translation :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (p : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaInfinitesimalPolygonR0129.next r hr (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr)) 1 p), ArithmeticThetaMarkedGroupLawR0146.IsTranslation k M G p hp.1 (ArithmeticThetaMarkedGroupLawR0146.rotationMap k M rot scal inv ha) := by
  intro k _ _ r hr h3 T he M hM s hs G hG rot scal inv ha p hp
  let f := rotationMap k M rot scal inv ha
  have hf : f ≫ genericStructure k M = genericStructure k M :=
    genericMap_structure k M rot.hom
      (ArithmeticThetaGeometricLiftsR0141.modelOver k M _ _ _ rot ha.1)
  let d := difference k M G f hf
  have hεd : genericPoint k M s hs.1 ≫ d.val = genericPoint k M p hp.1 := by
    have hi : G.inv (𝟙 _) (G.one (𝟙 _)) = G.one (𝟙 _) := by
      let := G.pointGroup (𝟙 _)
      exact inv_one
    have hn := difference_natural k M G f hf (𝟙 _) (G.one (𝟙 _))
    rw [hi, G.mul_one, hG.1] at hn
    have hh : genericPoint k M s hs.1 ≫ d.val = genericPoint k M s hs.1 ≫ f := by
      simpa only [pointOver, Category.id_comp] using hn
    exact hh.trans (generic_origin_rotation k h3 M hM s hs rot scal inv ha p hp)
  have hd : d.val = genericStructure k M ≫ genericPoint k M p hp.1 := by
    have hh := difference_constant k h3 M hM s hs G hG rot scal inv ha
    exact hh.trans (congrArg (fun z => genericStructure k M ≫ z) hεd)
  intro V t x
  let y : SchemeHomOver t (genericStructure k M) :=
    ⟨x.val ≫ f, by rw [Category.assoc, hf, x.property]⟩
  have hh : G.mul t y (G.inv t x) = pointOver k M t p hp.1 := by
    apply Subtype.ext
    rw [← difference_natural k M G f hf t x]
    change x.val ≫ d.val = t ≫ genericPoint k M p hp.1
    rw [hd, ← Category.assoc, x.property]
  let := G.pointGroup t
  have hy : y = G.mul t (pointOver k M t p hp.1) x := mul_inv_eq_iff_eq_mul.mp hh
  rw [hG.2] at hy
  exact congrArg Subtype.val hy.symm

#print axioms actual_rotation_translation
end ArithmeticThetaMarkedGroupLawR0146
