module

public import ComponentDegreeDefinitionsR0184
public import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
public import Theorems.Thm_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
public import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_linComb_linComb_eq_zpow_det
public import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_map_algHom
public import P2M.Sol.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
public import Theorems.Thm_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
public import P2M.Sol.S_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq

@[expose] public section

/-! Geometric prerequisites for the component cusp bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaComponentDegreeR0184
namespace GeometricComponentCuspBoundR0184
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- Restriction of the finite actual boundary to an actual component. -/
theorem cusps_finite : Finite (Cusps k L D X x) := by
  have hf := (BoundaryGeometry.boundary_finite k L D X).preimage
    (inclusion k L D X x).isOpenEmbedding.injective.injOn
  exact hf.to_subtype

theorem inclusion_closed : IsClosedImmersion (inclusion k L D X x) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact compactComponent_closed k L D X x

/-- Each actual component has boundary: otherwise its inclusion factors as a
closed immersion into the affine open base, contradicting proper smooth
dimension one. This does not use connectedness of a pairing locus. -/
theorem cusps_nonempty : Nonempty (Cusps k L D X x) := by
  classical
  letI := X.openImmersion
  letI := X.proper
  letI := X.smooth
  letI := inclusion_closed k L D X x
  letI : IsProper (projection k L D X x) := inferInstance
  letI : SmoothOfRelativeDimension 1 (projection k L D X x) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  by_contra hn
  have hr : Set.range (inclusion k L D X x) ⊆ Set.range X.inclusion := by
    rintro _ ⟨y, rfl⟩
    by_contra hy
    exact hn ⟨⟨y, hy⟩⟩
  let f := IsOpenImmersion.lift X.inclusion (inclusion k L D X x) hr
  have hf : f ≫ X.inclusion = inclusion k L D X x :=
    IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (f ≫ X.inclusion) := hf.symm ▸ inferInstance
  letI : IsClosedImmersion f := IsClosedImmersion.of_comp f X.inclusion
  have ha : IsAffine (Component k L D X x) := isAffine_of_isAffineHom f
  exact not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
    (projection k L D X x) ha

#print axioms cusps_finite
#print axioms cusps_nonempty

open ArithmeticThetaTateCuspsR0181

variable (hL : 3 ≤ L) (heven : Even L)

/-- The classifying map of a specified actual marked Tate curve. -/
def tateClassifying (E : TateLevel k L) : Puncture k ⟶ OpenBase k L D :=
  (TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E).choose

theorem tateClassifying_spec (E : TateLevel k L) :
    ClassifiesTate k L D E (tateClassifying k L D hL heven E) :=
  (TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E).choose_spec.1

/-- Its unique extension to the actual compactification. -/
def tateDisk (E : TateLevel k L) : Disk k ⟶ X.space :=
  (tate_cusp_disk_extension k L hL heven D E X
    (tateClassifying k L D hL heven E)
    (tateClassifying_spec k L D hL heven E)).choose

theorem tateDisk_spec (E : TateLevel k L) :
    Extends k L D X (tateClassifying k L D hL heven E)
      (tateDisk k L D X hL heven E) :=
  (tate_cusp_disk_extension k L hL heven D E X
    (tateClassifying k L D hL heven E)
    (tateClassifying_spec k L D hL heven E)).choose_spec.1

/-- The center is a geometric boundary point, with its boundary proof supplied
by the actual extension theorem. -/
def tateCenter (E : TateLevel k L) : {z : X.space // z ∈ boundary k L D X} :=
  ⟨tateDisk k L D X hL heven E (closedPoint k),
    (tateDisk_spec k L D X hL heven E).2.2⟩

/-- Any classifying disk for this marked Tate curve has this same center. -/
theorem tateCenter_eq_of_extends (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space)
    (hb : ClassifiesTate k L D E b) (hd : Extends k L D X b d) :
    (tateCenter k L D X hL heven E).val = d (closedPoint k) := by
  have hb' : b = tateClassifying k L D hL heven E :=
    (TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D E).choose_spec.2 b hb
  subst b
  have hd' : d = tateDisk k L D X hL heven E :=
    (tate_cusp_disk_extension k L hL heven D E X
      (tateClassifying k L D hL heven E)
      (tateClassifying_spec k L D hL heven E)).choose_spec.2 d hd
  exact congrArg (fun f : Disk k ⟶ X.space => f (closedPoint k)) hd'.symm

/-- All actual boundary points are centers of actual marked Tate curves. This
does not identify the determinant-one marking locus or its stabilizer. -/
theorem tateCenter_surjective [IsAlgClosed k] :
    Function.Surjective (tateCenter k L D X hL heven) := by
  intro z
  obtain ⟨E, b, d, hb, hd, hz⟩ :=
    every_geometric_boundary_tate_disk k L hL heven D X z.val z.property
  exact ⟨E, Subtype.ext ((tateCenter_eq_of_extends k L D X hL heven E b d hb hd).trans hz)⟩

/-- Choose a marked Tate representative of each cusp on the selected component.
The choice is tied to its actual geometric center. -/
def cuspTateMarking [IsAlgClosed k] (c : Cusps k L D X x) : TateLevel k L :=
  (tateCenter_surjective k L D X hL heven
    ⟨inclusion k L D X x c.val, c.property⟩).choose

theorem cuspTateMarking_center [IsAlgClosed k] (c : Cusps k L D X x) :
    (tateCenter k L D X hL heven (cuspTateMarking k L D X x hL heven c)).val =
      inclusion k L D X x c.val :=
  congrArg Subtype.val (tateCenter_surjective k L D X hL heven
    ⟨inclusion k L D X x c.val, c.property⟩).choose_spec

theorem cuspTateMarking_injective [IsAlgClosed k] :
    Function.Injective (cuspTateMarking k L D X x hL heven) := by
  intro a b hab
  apply Subtype.ext
  apply (inclusion k L D X x).isOpenEmbedding.injective
  rw [← cuspTateMarking_center k L D X x hL heven a,
    ← cuspTateMarking_center k L D X x hL heven b, hab]

#print axioms tateCenter_surjective
#print axioms cuspTateMarking_injective

section Pairing
open WeierstrassCurve.Affine
open P2MW.S_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure.WeilPrimitiveSol

/-- Perfectness of the actual Weil pairing makes its value on any full
torsion basis primitive. No primality or oddness restriction is used. -/
theorem primitive_pairing_of_torsion_basis
    {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W.baseChange K).toAffine.CoordinateRing]
    (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (e : (ZMod n × ZMod n) ≃+
      Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point (n : ℤ)) :
    IsPrimitiveRoot (weilPairing0 W K n (e (1, 0)).val (e (0, 1)).val) n := by
  let P := (e (1, 0)).val
  let Q := (e (0, 1)).val
  have hP : (n : ℤ) • P = 0 := (e (1, 0)).property
  have hQ : (n : ℤ) • Q = 0 := (e (0, 1)).property
  refine ⟨pair_pow_eq_one W hn P Q hP hQ, ?_⟩
  intro m hm
  have hmq : m • Q = 0 := by
    apply eq_zero_of_forall_weilPairing0_eq_one W hn (m • Q) (torsion_nsmul hQ m)
    intro S hS
    let a := e.symm ⟨S, hS⟩
    have ha : (a.1.val • (1, 0) + a.2.val • (0, 1) : ZMod n × ZMod n) = a := by
      ext <;> simp
    have hspan : S = a.1.val • P + a.2.val • Q := by
      have hh : a.1.val • e (1, 0) + a.2.val • e (0, 1) = ⟨S, hS⟩ := by
        rw [← map_nsmul, ← map_nsmul, ← map_add, ha]
        exact e.apply_symm_apply _
      exact (congrArg (fun z : Submodule.torsionBy ℤ
        (W.baseChange K).toAffine.Point (n : ℤ) => z.val) hh).symm
    rw [hspan, weilPairing0_add_left W hn _ _ _
      (torsion_nsmul hP _) (torsion_nsmul hQ _) (torsion_nsmul hQ m),
      pair_nsmul_left W hn _ P _ hP (torsion_nsmul hQ m),
      pair_nsmul_left W hn _ Q _ hQ (torsion_nsmul hQ m),
      pair_nsmul_right W hn m P Q hP hQ,
      pair_nsmul_right W hn m Q Q hQ hQ,
      weilPairing0_self W hn Q hQ, one_pow, one_pow, mul_one]
    exact (congrArg (fun z => z ^ a.1.val) hm).trans (one_pow _)
  have hme : e (m • (0, 1)) = 0 := by
    rw [map_nsmul]
    exact Subtype.ext hmq
  have hz : (m : ZMod n) = 0 := by
    have hh := congrArg Prod.snd (e.injective (hme.trans e.map_zero.symm))
    simpa using hh
  exact (ZMod.natCast_eq_zero_iff m n).mp hz

#print axioms primitive_pairing_of_torsion_basis
end Pairing

section FullMarkingPairing
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175
open ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation
open WeierstrassCurve.Affine

variable {F K : Type} [Field F] [CharZero F] [Field K] [DecidableEq K] [Algebra F K]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W) (hG : IsOriginLaw F W G)

/-- Coordinate evaluation from the accepted projective Weierstrass model.
This is the evaluation supplied by the actual chart dictionary. -/
def fullLevelEvaluation :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W) ≃
      (W.baseChange K).toAffine.Point :=
  (coordinateEvaluationExists W G (by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _))).choose K

theorem fullLevelEvaluation_mul (a b : SchemeHomOver
    (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W)) :
    fullLevelEvaluation W G hG (G.mul _ a b) =
      fullLevelEvaluation W G hG a + fullLevelEvaluation W G hG b :=
  (coordinateEvaluationExists W G (by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _))).choose_spec.1.1 K a b

theorem fullLevelEvaluation_zero :
    fullLevelEvaluation W G hG (G.one
      (Spec.map (CommRingCat.ofHom (algebraMap F K)))) = 0 := by
  have h := fullLevelEvaluation_mul (K := K) W G hG (G.one _) (G.one _)
  rw [G.one_mul] at h
  exact (add_left_cancel (a := fullLevelEvaluation W G hG (G.one _))
    ((add_zero _).trans h)).symm

variable [IsAlgClosed K]

/-- The actual Weil pairing on the coordinate points of a geometric full marking. -/
def fullLevelPairing (n : ℕ) (A : FullLevel F W G n
    (Spec.map (CommRingCat.ofHom (algebraMap F K)))) : Kˣ :=
  weilPairing0 W K n (fullLevelEvaluation W G hG A.x) (fullLevelEvaluation W G hG A.y)

/-- General even and composite levels are included. The basis is constructed
from the killed sections and their avoidance property, using the actual
geometric torsion group and its proved order. -/
theorem fullLevelPairing_primitive (n : ℕ) (hn : 0 < n)
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    IsPrimitiveRoot (fullLevelPairing W G hG n A) n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : CharZero K := Algebra.charZero_of_charZero F K
  letI : (W.baseChange K).IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  letI : IsDedekindDomain (W.baseChange K).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)
  let T := Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point (n : ℤ)
  have hc : Nat.card T = n ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.baseChange K).toAffine (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (by norm_num)
  letI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 (Nat.ne_of_gt hn))
  have hk (z : T) : n • z = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using Submodule.smul_torsionBy (n : ℤ) z
  let B := fieldMarkToPair (L := n) hG _ (fullLevelEvaluation (K := K) W G hG)
    (fullLevelEvaluation_mul W G hG) (fullLevelEvaluation_zero W G hG) A
  let e : (ZMod n × ZMod n) ≃+ T := basisPairEquiv n hk hc B
  have heP : e (1, 0) = B.val.1 := pairHom_fst n hk B.val.1 B.val.2
  have heQ : e (0, 1) = B.val.2 := pairHom_snd n hk B.val.1 B.val.2
  have hp := primitive_pairing_of_torsion_basis W n
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) e
  rw [heP, heQ] at hp
  exact hp

#print axioms fullLevelPairing_primitive

/-- A primitive root in a field extension of an algebraically closed ground
field has a unique ground-field value. This is a field statement, not yet
specialization compatibility on the compactified curve. -/
theorem primitive_root_descends {k₀ K₀ : Type} [Field k₀] [IsAlgClosed k₀]
    [Field K₀] [Algebra k₀ K₀] (n : ℕ) (hn : 0 < n)
    (z : K₀) (hz : IsPrimitiveRoot z n) :
    ∃! ζ : k₀, IsPrimitiveRoot ζ n ∧ algebraMap k₀ K₀ ζ = z := by
  let p : Polynomial k₀ := Polynomial.X ^ n - Polynomial.C 1
  have hp : p ≠ 0 := (Polynomial.monic_X_pow_sub_C (1 : k₀) (Nat.ne_of_gt hn)).ne_zero
  have hr : (p.map (algebraMap k₀ K₀)).IsRoot z := by
    simpa only [p, Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_one, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.map_one,
      Polynomial.eval_one, sub_eq_zero] using hz.pow_eq_one
  obtain ⟨ζ, hζ⟩ := (IsAlgClosed.splits p).mem_range_of_isRoot hp hr
  refine ⟨ζ, ⟨?_, hζ⟩, ?_⟩
  · exact (hζ.symm ▸ hz).of_map_of_injective (algebraMap k₀ K₀).injective
  · intro ζ' hζ'
    exact (algebraMap k₀ K₀).injective (hζ'.2.trans hζ.symm)

/-- Ground-field descent of the pairing of an actual full marking. The
algebra maps to the geometric coefficient field are the specified tower. -/
theorem fullLevelPairing_descends
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [Algebra k₀ F] [Algebra k₀ K]
    [IsScalarTower k₀ F K] (n : ℕ) (hn : 0 < n)
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    ∃! ζ : k₀, IsPrimitiveRoot ζ n ∧
      algebraMap k₀ K ζ = (fullLevelPairing W G hG n A : K) := by
  apply primitive_root_descends n hn
  exact (fullLevelPairing_primitive W G hG n hn A).map_of_injective
    (f := Units.coeHom K) Units.val_injective

#print axioms fullLevelPairing_descends

/-- Integer relabeling preserves the actual full-marking pairing precisely
when its determinant is one modulo the level. -/
theorem fullLevelPairing_relabel_iff (n : ℕ) (hn : 0 < n)
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    (g : Matrix (Fin 2) (Fin 2) ℤ) :
    weilPairing0 W K n
      (g 0 0 • fullLevelEvaluation W G hG A.x + g 1 0 • fullLevelEvaluation W G hG A.y)
      (g 0 1 • fullLevelEvaluation W G hG A.x + g 1 1 • fullLevelEvaluation W G hG A.y) =
        fullLevelPairing W G hG n A ↔
      (g.map (Int.castRingHom (ZMod n))).det = 1 := by
  letI : CharZero K := Algebra.charZero_of_charZero F K
  letI : (W.baseChange K).IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  letI : IsDedekindDomain (W.baseChange K).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)
  have hP : (n : ℤ) • fullLevelEvaluation W G hG A.x = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), A.killed_x, fullLevelEvaluation_zero]
  have hQ : (n : ℤ) • fullLevelEvaluation W G hG A.y = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), A.killed_y, fullLevelEvaluation_zero]
  rw [weilPairing0_linComb_linComb_eq_zpow_det W
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) _ _ hP hQ g]
  change (fullLevelPairing W G hG n A) ^ g.det = fullLevelPairing W G hG n A ↔
    ((Int.castRingHom (ZMod n)).mapMatrix g).det = 1
  rw [← (Int.castRingHom (ZMod n)).map_det g]
  change (fullLevelPairing W G hG n A) ^ g.det = fullLevelPairing W G hG n A ↔
    (g.det : ZMod n) = 1
  have hz := fullLevelPairing_primitive W G hG n hn A
  calc
    (fullLevelPairing W G hG n A) ^ g.det = fullLevelPairing W G hG n A ↔
        (fullLevelPairing W G hG n A) ^ (g.det - 1) = 1 := by
      rw [zpow_sub, zpow_one, mul_inv_eq_one]
    _ ↔ (n : ℤ) ∣ g.det - 1 := hz.zpow_eq_one_iff_dvd _
    _ ↔ (g.det : ZMod n) = 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [Int.cast_sub, Int.cast_one, sub_eq_zero]

#print axioms fullLevelPairing_relabel_iff
end FullMarkingPairing

section FieldEvaluationNaturality
open NeronModelInfra WeierstrassProjModel
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175
open ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation
open ArithmeticThetaLegendreComparisonR0177.TwoTorsionAffineCoordinates

variable {F K K' : Type} [Field F] [CharZero F]
  [Field K] [Field K'] [DecidableEq K] [DecidableEq K']
  [Algebra F K] [Algebra F K']
  (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W) (hG : IsOriginLaw F W G)

/-- Precomposition by the specified coefficient-field embedding. -/
def fieldPointMap (f : K →ₐ[F] K')
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W)) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K'))) (structureMap F W) :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ P.val, by
    rw [Category.assoc, P.property, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext f.commutes)⟩

theorem fullLevelEvaluation_chart
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W))
    (χ : WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective →+* K)
    (hχ : P.val = Spec.map (CommRingCat.ofHom χ) ≫
      WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective) :
    ∃ hxy : (W.baseChange K).toAffine.Nonsingular
        (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective))
        (χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective)),
      fullLevelEvaluation W G hG P = WeierstrassCurve.Affine.Point.some _ _ hxy :=
  (coordinateEvaluationExists W G (by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _))).choose_spec.2.2 K P χ hχ

/-- The actual coordinate dictionary is natural for arbitrary embeddings of
coefficient fields, including embeddings into larger algebraic closures. -/
theorem fullLevelEvaluation_map (f : K →ₐ[F] K')
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W)) :
    fullLevelEvaluation W G hG (fieldPointMap W f P) =
      WeierstrassCurve.Affine.Point.map f (fullLevelEvaluation W G hG P) := by
  classical
  by_cases hp : P = G.one _
  · subst P
    have he : fieldPointMap W f (G.one _) = G.one _ := by
      apply Subtype.ext
      change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (G.one _).val = _
      rw [hG.1, hG.1, ← Category.assoc, ← Spec.map_comp]
      congr 2
      exact CommRingCat.hom_ext (RingHom.ext f.commutes)
    rw [he, fullLevelEvaluation_zero, fullLevelEvaluation_zero, map_zero]
  · have hd := (field_avoids_iff hG _ P).mpr hp
    have hr : Set.range P.val ⊆ Set.range
        (WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective) := by
      rintro _ ⟨z, rfl⟩
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
      by_contra hn
      exact Set.disjoint_left.mp hd ⟨z, rfl⟩
        ((not_mem_basicOpen_iff_mem_range_kwZeroSect W (P.val z)).mp hn)
    let q := IsOpenImmersion.lift (WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective) P.val hr
    let χ := (Spec.preimage q).hom
    have hχ : P.val = Spec.map (CommRingCat.ofHom χ) ≫
        WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective := by
      rw [show CommRingCat.ofHom χ = Spec.preimage q from rfl, Spec.map_preimage]
      exact (IsOpenImmersion.lift_fac _ _ hr).symm
    have hχ' : (fieldPointMap W f P).val = Spec.map
        (CommRingCat.ofHom (f.toRingHom.comp χ)) ≫
          WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective := by
      change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ P.val = _
      rw [hχ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    obtain ⟨hxy, he⟩ := fullLevelEvaluation_chart W G hG P χ hχ
    obtain ⟨hxy', he'⟩ := fullLevelEvaluation_chart W G hG
      (fieldPointMap W f P) (f.toRingHom.comp χ) hχ'
    rw [he, he', WeierstrassCurve.Affine.Point.map_some]
    rfl

#print axioms fullLevelEvaluation_map

/-- Scalar extension of the actual two full-level sections. -/
def fieldMarkingMap (f : K →ₐ[F] K') {n : ℕ}
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K'))) :=
  BaseChange.restrict A (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext f.commutes))

/-- Weil pairing commutes with extension of the geometric coefficient field.
Both points are obtained from the actual projective marking maps. -/
theorem fullLevelPairing_map [IsAlgClosed K] [IsAlgClosed K']
    (f : K →ₐ[F] K') (n : ℕ) (hn : 0 < n)
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    (fullLevelPairing W G hG n (fieldMarkingMap W G f A) : K') =
      f (fullLevelPairing W G hG n A : K) := by
  letI : CharZero K := Algebra.charZero_of_charZero F K
  letI : (W.baseChange K).IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  letI : (W.baseChange K').IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  letI : IsDedekindDomain (W.baseChange K).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)
  letI : IsDedekindDomain (W.baseChange K').toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K')
  have hx : (n : ℤ) • fullLevelEvaluation W G hG A.x = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), A.killed_x, fullLevelEvaluation_zero]
  have hy : (n : ℤ) • fullLevelEvaluation W G hG A.y = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), A.killed_y, fullLevelEvaluation_zero]
  change (WeierstrassCurve.Affine.weilPairing0 W K' n
      (fullLevelEvaluation W G hG (fieldPointMap W f A.x))
      (fullLevelEvaluation W G hG (fieldPointMap W f A.y)) : K') = _
  rw [fullLevelEvaluation_map, fullLevelEvaluation_map]
  exact WeierstrassCurve.Affine.weilPairing0_map_algHom W f
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) _ _ hx hy

#print axioms fullLevelPairing_map
end FieldEvaluationNaturality

section VariableEvaluationNaturality
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175
open ArithmeticThetaLegendreComparisonR0177
open TwoTorsionAffineCoordinates NormalFormConstruction
open WeierstrassCurve.Affine WeierstrassCurve.DrinfeldGlobal
open P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange.WeilIsoInvSol

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W) (hG : IsOriginLaw K W G)

theorem fullLevelEvaluation_coordinates
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) (structureMap K W))
    (a b : K) (hP : HasCoordinates K W P.val a b) :
    ∃ hxy : (W.baseChange K).toAffine.Nonsingular a b,
      fullLevelEvaluation W G hG P = Point.some a b hxy := by
  obtain ⟨_, χ, hχ, hx, hy⟩ := hP
  simpa only [hx, hy] using fullLevelEvaluation_chart W G hG P χ hχ

/-- The actual projective coordinate dictionary intertwines a variable-change
map with the affine point transformation used by the Weil pairing. -/
theorem fullLevelEvaluation_variable
    (C : WeierstrassCurve.VariableChange K) [(C • W).IsElliptic]
    (H : Law K (C • W)) (hH : IsOriginLaw K (C • W) H)
    (b : Curve K (C • W) ⟶ Curve K W)
    (hb : b ≫ structureMap K W = structureMap K (C • W))
    (ho : origin K (C • W) ≫ b = origin K W)
    (a : ChartRing K W →+* ChartRing K (C • W))
    (ha : Spec.map (CommRingCat.ofHom a) ≫ chartInclusion K W =
      chartInclusion K (C • W) ≫ b)
    (hx : a (xOverZ W.toProjective) = chartScalar K (C • W) ((C.u : K)^2) *
      xOverZ (C • W).toProjective + chartScalar K (C • W) C.r)
    (hy : a (yOverZ W.toProjective) = chartScalar K (C • W) ((C.u : K)^3) *
      yOverZ (C • W).toProjective + chartScalar K (C • W) ((C.u : K)^2 * C.s) *
      xOverZ (C • W).toProjective + chartScalar K (C • W) C.t)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) (structureMap K W))
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) (structureMap K (C • W)))
    (hPQ : Q.val ≫ b = P.val) :
    ψ W C (fullLevelEvaluation W G hG P) = fullLevelEvaluation (C • W) H hH Q := by
  by_cases hQ : Q = H.one _
  · have hP : P = G.one _ := by
      apply Subtype.ext
      rw [← hPQ, hQ, hH.1, Category.assoc, ho, hG.1]
    rw [hP, hQ, fullLevelEvaluation_zero, fullLevelEvaluation_zero, ψ_zero]
  · have hd := (field_avoids_iff hH _ Q).mpr hQ
    obtain ⟨χ, hχ⟩ := exists_chart_factorization (C • W) Q.val hd
    have hcoordQ : HasCoordinates K (C • W) Q.val
        (χ (xOverZ (C • W).toProjective)) (χ (yOverZ (C • W).toProjective)) := by
      refine ⟨?_, χ, hχ, rfl, rfl⟩
      simpa using Q.property
    have hcoordP := coordinates_under_map W (C • W) b hb a ha
      ((C.u : K)^2) C.r ((C.u : K)^3) ((C.u : K)^2 * C.s) C.t hx hy
      Q.val _ _ hcoordQ
    rw [hPQ] at hcoordP
    obtain ⟨hnsP, heP⟩ := fullLevelEvaluation_coordinates W G hG P _ _ hcoordP
    obtain ⟨hnsQ, heQ⟩ := fullLevelEvaluation_coordinates (C • W) H hH Q _ _ hcoordQ
    rw [heP, heQ]
    obtain ⟨hns, he⟩ := ψ_some W C hnsP
    rw [he]
    apply some_ext
    · exact vcXInv_vcX _
    · exact vcYInv_vcY _ _

/-- Pairing invariance for an actual pointed variable-change comparison,
including arbitrary positive composite levels. -/
theorem fullLevelPairing_variable [IsAlgClosed K]
    (C : WeierstrassCurve.VariableChange K) [(C • W).IsElliptic]
    (H : Law K (C • W)) (hH : IsOriginLaw K (C • W) H)
    (b : Curve K (C • W) ⟶ Curve K W)
    (hb : b ≫ structureMap K W = structureMap K (C • W))
    (ho : origin K (C • W) ≫ b = origin K W)
    (a : ChartRing K W →+* ChartRing K (C • W))
    (ha : Spec.map (CommRingCat.ofHom a) ≫ chartInclusion K W =
      chartInclusion K (C • W) ≫ b)
    (hx : a (xOverZ W.toProjective) = chartScalar K (C • W) ((C.u : K)^2) *
      xOverZ (C • W).toProjective + chartScalar K (C • W) C.r)
    (hy : a (yOverZ W.toProjective) = chartScalar K (C • W) ((C.u : K)^3) *
      yOverZ (C • W).toProjective + chartScalar K (C • W) ((C.u : K)^2 * C.s) *
      xOverZ (C • W).toProjective + chartScalar K (C • W) C.t)
    (n : ℕ)
    (M : FullLevel K W G n (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (N : FullLevel K (C • W) H n (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (hMx : N.x.val ≫ b = M.x.val) (hMy : N.y.val ≫ b = M.y.val) :
    fullLevelPairing (C • W) H hH n N = fullLevelPairing W G hG n M := by
  unfold fullLevelPairing
  rw [← fullLevelEvaluation_variable W G hG C H hH b hb ho a ha hx hy M.x N.x hMx,
    ← fullLevelEvaluation_variable W G hG C H hH b hb ho a ha hx hy M.y N.y hMy]
  exact weilPairing0_ψ W C n _ _

#print axioms fullLevelEvaluation_variable
#print axioms fullLevelPairing_variable

/-- Any pointed isomorphism of the actual projective curves preserves the
actual Weil pairing of full markings whose two sections it identifies. -/
theorem fullLevelPairing_pointed_iso [IsAlgClosed K]
    (V : WeierstrassCurve K) [V.IsElliptic]
    (H : Law K V) (hH : IsOriginLaw K V H)
    (e : Curve K W ≅ Curve K V)
    (hp : e.hom ≫ structureMap K V = structureMap K W)
    (ho : origin K W ≫ e.hom = origin K V)
    (n : ℕ)
    (M : FullLevel K W G n (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (N : FullLevel K V H n (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (hMx : M.x.val ≫ e.hom = N.x.val) (hMy : M.y.val ≫ e.hom = N.y.val) :
    fullLevelPairing V H hH n N = fullLevelPairing W G hG n M := by
  obtain ⟨C, hC, φ, hφ, hvc, hmap⟩ :=
    WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
      K W V (WeierstrassCurve.isUnit_Δ W) (WeierstrassCurve.isUnit_Δ V) e hp ho
  subst V
  simp only [eqToHom_refl, Category.id_comp] at hmap
  obtain ⟨a, ha, _, hx, hy⟩ :=
    WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
      W.toProjective C φ hφ hvc
  rw [hmap] at ha
  have hpi : e.inv ≫ structureMap K W = structureMap K (C • W) := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using hp.symm
  have hoi : origin K (C • W) ≫ e.inv = origin K W := by
    rw [← ho, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply fullLevelPairing_variable W G hG C H hH e.inv hpi hoi a ha.symm
  · simpa only [chartScalar_apply] using hx
  · simpa only [chartScalar_apply] using hy
  · rw [← hMx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [← hMy, Category.assoc, Iso.hom_inv_id, Category.comp_id]

#print axioms fullLevelPairing_pointed_iso
end VariableEvaluationNaturality

section CoefficientEvaluationNaturality
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175
open ArithmeticThetaLegendreComparisonR0177
open TwoTorsionAffineCoordinates NormalFormConstruction
open WeierstrassCurve.Affine WeierstrassCurve.DrinfeldGlobal
open P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange.WeilIsoInvSol

variable {F K : Type} [Field F] [CharZero F] [Field K] [CharZero K]
  [DecidableEq K] [Algebra F K]
  (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W) (hG : IsOriginLaw F W G)
  [(W.baseChange K).IsElliptic]
  (H : Law K (W.baseChange K)) (hH : IsOriginLaw K (W.baseChange K) H)
  (b : Curve K (W.baseChange K) ⟶ Curve F W)
  (ho : origin K (W.baseChange K) ≫ b =
    Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ origin F W)
  (a : ChartRing F W →+* ChartRing K (W.baseChange K))
  (ha : Spec.map (CommRingCat.ofHom a) ≫ chartInclusion F W =
    chartInclusion K (W.baseChange K) ≫ b)
  (hx : a (xOverZ W.toProjective) = xOverZ (W.baseChange K).toProjective)
  (hy : a (yOverZ W.toProjective) = yOverZ (W.baseChange K).toProjective)

include ho ha hx hy in
/-- Coefficient change preserves the evaluated coordinates of the actual
projective sections. The map and its chart equations are retained. -/
theorem fullLevelEvaluation_coefficient
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W))
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K)))
      (structureMap K (W.baseChange K)))
    (hPQ : Q.val ≫ b = P.val) :
    fullLevelEvaluation W G hG P = fullLevelEvaluation (W.baseChange K) H hH Q := by
  by_cases hQ : Q = H.one _
  · have hP : P = G.one _ := by
      apply Subtype.ext
      rw [← hPQ, hQ, hH.1, Category.assoc, ho, ← Category.assoc]
      simpa using (hG.1 (Spec.map (CommRingCat.ofHom (algebraMap F K)))).symm
    rw [hP, hQ, fullLevelEvaluation_zero, fullLevelEvaluation_zero]
  · have hd := (field_avoids_iff hH _ Q).mpr hQ
    obtain ⟨χ, hχ⟩ := exists_chart_factorization (W.baseChange K) Q.val hd
    have hχP : P.val = Spec.map (CommRingCat.ofHom (χ.comp a)) ≫ chartInclusion F W := by
      rw [← hPQ, hχ]
      simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha]
    obtain ⟨hnsP, heP⟩ := fullLevelEvaluation_chart W G hG P (χ.comp a) hχP
    obtain ⟨hnsQ, heQ⟩ := fullLevelEvaluation_chart (W.baseChange K) H hH Q χ hχ
    rw [heP, heQ]
    apply some_ext
    · simp only [RingHom.comp_apply, hx]
    · simp only [RingHom.comp_apply, hy]

include ho ha hx hy in
/-- Computing the actual pairing after coefficient change agrees with
computing it on the original equation over the same geometric field. -/
theorem fullLevelPairing_coefficient [IsAlgClosed K] (n : ℕ)
    (M : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    (N : FullLevel K (W.baseChange K) H n (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (hMx : N.x.val ≫ b = M.x.val) (hMy : N.y.val ≫ b = M.y.val) :
    fullLevelPairing (W.baseChange K) H hH n N = fullLevelPairing W G hG n M := by
  unfold fullLevelPairing
  rw [fullLevelEvaluation_coefficient W G hG H hH b ho a ha hx hy M.x N.x hMx,
    fullLevelEvaluation_coefficient W G hG H hH b ho a ha hx hy M.y N.y hMy]
  exact (P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq.BaseSol.weilPairing0_self
    W n _ _).symm

#print axioms fullLevelEvaluation_coefficient
#print axioms fullLevelPairing_coefficient
end CoefficientEvaluationNaturality

section CartesianPairingNaturality
open CategoryTheory.Limits NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreComparisonR0177
open NormalFormConstruction MarkedLegendreAtlasLocalCoverageR0177

/-- Actual pointed Cartesian comparisons preserve the Weil pairing. The
coefficient comparison and its group law are constructed, then the two
pullback presentations are compared by their unique pointed isomorphism. -/
theorem fullLevelPairing_cartesian
    {F K : Type} [Field F] [CharZero F] [Field K] [CharZero K]
    [DecidableEq K] [IsAlgClosed K] [Algebra F K]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W) (hG : IsOriginLaw F W G)
    (V : WeierstrassCurve K) [V.IsElliptic] (H : Law K V) (hH : IsOriginLaw K V H)
    (b : Curve K V ⟶ Curve F W)
    (hb : IsPullback b (structureMap K V) (structureMap F W)
      (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    (ho : origin K V ≫ b = Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ origin F W)
    (n : ℕ)
    (M : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    (N : FullLevel K V H n (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (hMx : N.x.val ≫ b = M.x.val) (hMy : N.y.val ≫ b = M.y.val) :
    fullLevelPairing V H hH n N = fullLevelPairing W G hG n M := by
  let W' := W.baseChange K
  letI : W'.IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  obtain ⟨c, a, hc, hco, ha, hax, hay, _⟩ := coefficient_comparison W (algebraMap F K)
  change IsPullback c (structureMap K W') (structureMap F W)
    (baseMap F K (algebraMap F K)) at hc
  change origin K W' ≫ c = baseMap F K (algebraMap F K) ≫ origin F W at hco
  obtain ⟨J, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      (algebraMap F K) (structureMap F W) (structureMap K W') c hc G
  have hJ : IsOriginLaw K W' J := by
    constructor
    · intro T t
      apply hc.hom_ext
      · simp only [hj, hG.1, Category.assoc, hco, baseMap]
      · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
        exact (J.one t).property
    · intro T t P Q
      apply Subtype.ext
      apply hc.hom_ext
      · rw [hm, hm, hG.2]
      · exact (J.mul t P Q).property.trans (J.mul t Q P).property.symm
  have hBC := pointed_base_change G J hG hJ (algebraMap F K) c hc hco
  let t := Spec.map (CommRingCat.ofHom (algebraMap K K))
  let M₀ : FullLevel F W G n (t ≫ baseMap F K (algebraMap F K)) :=
    BaseChange.restrict M (𝟙 _) (by simp [t, baseMap])
  let N₀ := BaseChange.up hBC hG hJ M₀
  have hN₀x : N₀.x.val ≫ c = M.x.val := by
    exact (BaseChange.up_x hBC hG hJ M₀).trans (Category.id_comp M.x.val)
  have hN₀y : N₀.y.val ≫ c = M.y.val := by
    exact (BaseChange.up_y hBC hG hJ M₀).trans (Category.id_comp M.y.val)
  let e : Curve K V ≅ Curve K W' := hb.isoIsPullback _ _ hc
  have hec : e.hom ≫ c = b := IsPullback.isoIsPullback_hom_fst _ _ hb hc
  have hep : e.hom ≫ structureMap K W' = structureMap K V :=
    IsPullback.isoIsPullback_hom_snd _ _ hb hc
  have heo : origin K V ≫ e.hom = origin K W' := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, ho, hco]
      rfl
    · rw [Category.assoc, hep, BaseChange.origin_over, BaseChange.origin_over]
  have hex : N.x.val ≫ e.hom = N₀.x.val := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hMx, hN₀x]
    · rw [Category.assoc, hep, N.x.property, N₀.x.property]
  have hey : N.y.val ≫ e.hom = N₀.y.val := by
    apply hc.hom_ext
    · rw [Category.assoc, hec, hMy, hN₀y]
    · rw [Category.assoc, hep, N.y.property, N₀.y.property]
  exact (fullLevelPairing_pointed_iso V H hH W' J hJ e hep heo n N N₀ hex hey).symm.trans
    (fullLevelPairing_coefficient W G hG J hJ c hco a ha hax hay n M N₀ hN₀x hN₀y)

#print axioms fullLevelPairing_cartesian
end CartesianPairingNaturality

section GeometricSign
open CategoryTheory.Limits NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaLegendreAtlasR0176.FullLevelFreeSignR0176

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

theorem comp_inversion {T : Scheme} (t : T ⟶ Base R)
    (P : SchemeHomOver t (structureMap R W)) :
    P.val ≫ inversion R W G = (G.inv t P).val := by
  have h := congrArg Subtype.val (inverse_natural G (structureMap R W) t
    P.val P.property ⟨𝟙 _, Category.id_comp _⟩)
  simpa only [inversion, WeierstrassProjModel.schemeHomOverComp, Category.comp_id] using h

theorem inversion_over : inversion R W G ≫ structureMap R W = structureMap R W :=
  (G.inv (structureMap R W) ⟨𝟙 _, Category.id_comp _⟩).property

theorem inversion_square : inversion R W G ≫ inversion R W G = 𝟙 _ := by
  change (G.inv (structureMap R W) ⟨𝟙 _, Category.id_comp _⟩).val ≫ inversion R W G = _
  rw [comp_inversion W G (structureMap R W)
    (G.inv (structureMap R W) ⟨𝟙 _, Category.id_comp _⟩), inverse_twice]

def inversionIso : Curve R W ≅ Curve R W where
  hom := inversion R W G
  inv := inversion R W G
  hom_inv_id := inversion_square W G
  inv_hom_id := inversion_square W G

theorem inversion_origin (hG : IsOriginLaw R W G) :
    origin R W ≫ inversion R W G = origin R W := by
  have ho : (G.one (𝟙 _)).val = origin R W := by
    simpa only [Category.id_comp] using hG.1 (𝟙 _)
  rw [← ho, comp_inversion]
  letI := G.pointGroup (𝟙 (Base R))
  exact congrArg Subtype.val (inv_one (G := SchemeHomOver (𝟙 (Base R)) (structureMap R W)))

/-- Simultaneous sign is absorbed by the actual inversion isomorphism of
the source curve, preserving the classifying base map and both section equations. -/
theorem classifies_negative [Algebra k R] (hpos : 0 < L)
    (hG : IsOriginLaw R W G) (A : FullLevel R W G L (𝟙 (Base R)))
    (b : Base R ⟶ OpenBase k L D)
    (f : Curve R W ⟶ D.atlas.descent.family.curve)
    (hf : Classifies k L D.atlas D.two D.cover D.quotient R W G A b f) :
    Classifies k L D.atlas D.two D.cover D.quotient R W G (negative G hpos A)
      b (inversion R W G ≫ f) := by
  let e := inversionIso W G
  have hi : IsPullback e.hom (structureMap R W) (structureMap R W) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [e, inversionIso, Category.comp_id] using inversion_over W G⟩
  refine ⟨hf.1, ?_, ?_, ?_, ?_⟩
  · simpa only [e, inversionIso, Category.id_comp] using hi.paste_horiz hf.2.1
  · rw [← Category.assoc, inversion_origin W G hG]
    exact hf.2.2.1
  · change (G.inv _ A.x).val ≫ (inversion R W G ≫ f) = _
    rw [← Category.assoc, comp_inversion, inverse_twice]
    exact hf.2.2.2.1
  · change (G.inv _ A.y).val ≫ (inversion R W G ≫ f) = _
    rw [← Category.assoc, comp_inversion, inverse_twice]
    exact hf.2.2.2.2

/-- The signed actual Tate marking uses the same curve and group law. -/
def negativeTate (hpos : 0 < L) (E : TateLevel k L) : TateLevel k L :=
  ⟨E.elliptic, E.law, E.originLaw, negative E.law hpos E.marking⟩

/-- Simultaneous sign acts freely on actual full Tate markings at level at
least three. The nonzero residue (2,0) supplies the contradiction. -/
theorem negativeTate_ne_self (E : TateLevel k L) :
    negativeTate k L (by omega) E ≠ E := by
  intro he
  have hx : E.law.inv (𝟙 _) E.marking.x = E.marking.x :=
    Subtype.ext (congrArg (fun A : TateLevel k L => A.marking.x.val) he)
  have htwo : E.law.nsmul (𝟙 _) 2 E.marking.x = E.law.one (𝟙 _) := by
    rw [E.law.nsmul_succ, E.law.nsmul_one_apply]
    calc
      E.law.mul _ E.marking.x E.marking.x =
          E.law.mul _ (E.law.inv _ E.marking.x) E.marking.x := by rw [hx]
      _ = _ := E.law.inv_mul_cancel _ _
  have ha := E.marking.avoids (⟨2, by omega⟩ : Fin L) (⟨0, by omega⟩ : Fin L)
    (show (2 : ℕ) ≠ 0 ∨ (0 : ℕ) ≠ 0 from Or.inl (Nat.succ_ne_zero 1))
  simp only [E.law.nsmul_zero, E.law.mul_one] at ha
  exact ((ArithmeticThetaFullLevelCoverR0175.CoverGeometryR0175.field_avoids_iff
    E.originLaw _ _).mp ha) htwo

theorem tateCenter_negative (E : TateLevel k L) :
    tateCenter k L D X hL heven (negativeTate k L (by omega) E) =
      tateCenter k L D X hL heven E := by
  obtain ⟨f, hf⟩ := tateClassifying_spec k L D hL heven E
  have hn : ClassifiesTate k L D (negativeTate k L (by omega) E)
      (tateClassifying k L D hL heven E) :=
    ⟨_, classifies_negative k L D (TateCurve k L) E.law (by omega) E.originLaw
      E.marking _ f hf⟩
  apply Subtype.ext
  exact tateCenter_eq_of_extends k L D X hL heven _ _ _ hn
    (tateDisk_spec k L D X hL heven E)

#print axioms classifies_negative
#print axioms tateCenter_negative
#print axioms negativeTate_ne_self
end GeometricSign

section ComponentGenericPoint
open NeronModelInfra

/-- Every point of a local Tate disk lies on the same actual open-and-closed
component as its center. -/
theorem disk_range_component (d : Disk k ⟶ X.space)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    Set.range d ⊆ (componentOpen k L D X x : Set X.space) := by
  rintro _ ⟨z, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint z).map d.continuous).mem_open
    (componentOpen k L D X x).isOpen hc

/-- Factor the specified disk through the specified component. -/
def componentDisk (d : Disk k ⟶ X.space)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    Disk k ⟶ Component k L D X x :=
  IsOpenImmersion.lift (inclusion k L D X x) d (by
    rw [Scheme.Opens.range_ι]
    exact disk_range_component k L D X x d hc)

theorem componentDisk_inclusion (d : Disk k ⟶ X.space)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    componentDisk k L D X x d hc ≫ inclusion k L D X x = d :=
  IsOpenImmersion.lift_fac _ _ _

/-- The punctured disk maps to the actual generic point of the component.
A nongeneric image would be closed on the smooth integral curve and would
equal its boundary specialization, contrary to the open restriction. -/
theorem componentDisk_generic (b : Puncture k ⟶ OpenBase k L D)
    (d : Disk k ⟶ X.space) (hd : Extends k L D X b d)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    (genericInclusion k ≫ componentDisk k L D X x d hc)
      (IsLocalRing.closedPoint (LaurentSeries k)) = genericPoint (Component k L D X x) := by
  letI := X.smooth
  letI : SmoothOfRelativeDimension 1 (projection k L D X x) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  let η := IsLocalRing.closedPoint (LaurentSeries k)
  let δ := componentDisk k L D X x d hc
  by_contra hn
  have hclosed := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
    (projection k L D X x) ((genericInclusion k ≫ δ) η) hn
  have hspec : (genericInclusion k ≫ δ) η ⤳ δ (closedPoint k) :=
    (IsLocalRing.specializes_closedPoint (genericInclusion k η)).map δ.continuous
  have he : δ (closedPoint k) = (genericInclusion k ≫ δ) η :=
    Set.mem_singleton_iff.mp (hspec.mem_closed hclosed (Set.mem_singleton _))
  have he' : d (closedPoint k) = (genericInclusion k ≫ d) η := by
    have hh := congrArg (inclusion k L D X x) he
    simpa only [← Scheme.Hom.comp_apply, Category.assoc,
      componentDisk_inclusion, δ] using hh
  apply hd.2.2
  refine ⟨b η, ?_⟩
  rw [he', hd.2.1]
  rfl

/-- A field-valued point with generic image factors through the actual
function field via the homomorphism induced on its stalk. -/
theorem generic_field_factor {Y : Scheme} [IsIntegral Y]
    {F : Type} [Field F] (g : Spec (CommRingCat.of F) ⟶ Y)
    (hg : g (IsLocalRing.closedPoint F) = genericPoint Y) :
    ∃ θ : Y.functionField →+* F,
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = g := by
  have hh : ∃ θ : Y.presheaf.stalk (genericPoint Y) ⟶ CommRingCat.of F,
      Spec.map θ ≫ Y.fromSpecStalk (genericPoint Y) = g := by
    rw [← hg]
    exact ⟨Scheme.stalkClosedPointTo g, Scheme.Spec_stalkClosedPointTo_fromSpecStalk g⟩
  obtain ⟨θ, hθ⟩ := hh
  exact ⟨θ.hom, hθ⟩

/-- All actual disks centered on this component use embeddings of its SAME
function field, with the defining factorization through the geometric map. -/
theorem componentDisk_functionField (b : Puncture k ⟶ OpenBase k L D)
    (d : Disk k ⟶ X.space) (hd : Extends k L D X b d)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    ∃ θ : (Component k L D X x).functionField →+* LaurentSeries k,
      Spec.map (CommRingCat.ofHom θ) ≫
        (Component k L D X x).fromSpecStalk (genericPoint (Component k L D X x)) ≫
          inclusion k L D X x = b ≫ X.inclusion := by
  obtain ⟨θ, hθ⟩ := generic_field_factor (genericInclusion k ≫ componentDisk k L D X x d hc)
    (componentDisk_generic k L D X x b d hd hc)
  refine ⟨θ, ?_⟩
  rw [← Category.assoc, hθ, Category.assoc, componentDisk_inclusion]
  exact hd.2.1

#print axioms componentDisk_generic
#print axioms componentDisk_functionField

/-- Density of the actual open base places the component's generic point
in that open base. -/
theorem component_generic_in_open :
    inclusion k L D X x (genericPoint (Component k L D X x)) ∈ Set.range X.inclusion := by
  letI := X.openImmersion
  obtain ⟨z, hzC, hzU⟩ := X.dense.inter_open_nonempty
    (componentOpen k L D X x) (componentOpen k L D X x).isOpen
    ⟨x, show x ∈ irreducibleComponent x from mem_irreducibleComponent⟩
  let U : (Component k L D X x).Opens :=
    (inclusion k L D X x) ⁻¹ᵁ X.inclusion.opensRange
  have hne : Nonempty U := ⟨⟨⟨z, hzC⟩, hzU⟩⟩
  exact ((genericPoint_spec (Component k L D X x)).mem_open_set_iff U.isOpen).mpr
    (by simpa using hne)

/-- The unique generic morphism to the actual affine open base. -/
def componentGenericOpen :
    Spec ((Component k L D X x).functionField) ⟶ OpenBase k L D := by
  letI := X.openImmersion
  let C := Component k L D X x
  let j := C.fromSpecStalk (genericPoint C) ≫ inclusion k L D X x
  apply IsOpenImmersion.lift X.inclusion j
  rintro _ ⟨z, rfl⟩
  have hz : z = IsLocalRing.closedPoint C.functionField := by
    change (z : PrimeSpectrum C.functionField) = _
    exact @Subsingleton.elim (PrimeSpectrum C.functionField) inferInstance _ _
  rw [hz, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  exact component_generic_in_open k L D X x

theorem componentGenericOpen_inclusion :
    componentGenericOpen k L D X x ≫ X.inclusion =
      (Component k L D X x).fromSpecStalk (genericPoint (Component k L D X x)) ≫
        inclusion k L D X x := by
  letI := X.openImmersion
  exact IsOpenImmersion.lift_fac _ _ _

/-- The structural map on the function field is the one induced by the
given geometric projection. -/
theorem generic_structure {K : Type} [Field K] {Y : Scheme} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) :
    Y.fromSpecStalk (genericPoint Y) ≫ p =
      Spec.map (CommRingCat.ofHom (AlgebraicCurve.baseToFunctionField p)) := by
  refine ext_of_isAffine ?_
  have h1 : (Spec.map (CommRingCat.ofHom (AlgebraicCurve.baseToFunctionField p))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
        CommRingCat.ofHom (AlgebraicCurve.baseToFunctionField p) ≫
          (Scheme.ΓSpecIso (Y.presheaf.stalk (genericPoint Y))).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom (AlgebraicCurve.baseToFunctionField p) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop ≫
        Y.presheaf.germ ⊤ (genericPoint Y) trivial := by
    ext a
    rfl
  have h3 : (Spec (Y.presheaf.stalk (genericPoint Y))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (Y.presheaf.stalk (genericPoint Y))).Opens) ≤ ⊤)).op =
        𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, h3,
    Category.comp_id, h1, h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem componentGenericOpen_over :
    componentGenericOpen k L D X x ≫ openStructure k L D =
      Spec.map (CommRingCat.ofHom (AlgebraicCurve.baseToFunctionField (projection k L D X x))) := by
  rw [← X.over_eq, ← Category.assoc, componentGenericOpen_inclusion, Category.assoc]
  exact generic_structure (projection k L D X x)

/-- Each classifying Tate puncture factors through the same generic map,
and its field embedding respects the actual k-structure. -/
theorem componentDisk_field_embedding (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (d : Disk k ⟶ X.space) (hd : Extends k L D X b d)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    ∃ θ : (Component k L D X x).functionField →+* LaurentSeries k,
      θ.comp (AlgebraicCurve.baseToFunctionField (projection k L D X x)) =
        algebraMap k (LaurentSeries k) ∧
      Spec.map (CommRingCat.ofHom θ) ≫ componentGenericOpen k L D X x = b := by
  letI := X.openImmersion
  obtain ⟨θ, hθ⟩ := componentDisk_functionField k L D X x b d hd hc
  have hfac : Spec.map (CommRingCat.ofHom θ) ≫ componentGenericOpen k L D X x = b := by
    apply (cancel_mono X.inclusion).mp
    rw [Category.assoc, componentGenericOpen_inclusion]
    exact hθ
  refine ⟨θ, ?_, hfac⟩
  obtain ⟨f, hf⟩ := hb
  have he : CommRingCat.ofHom
      (θ.comp (AlgebraicCurve.baseToFunctionField (projection k L D X x))) =
        CommRingCat.ofHom (algebraMap k (LaurentSeries k)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← componentGenericOpen_over,
      ← Category.assoc, hfac]
    exact hf.1
  exact congrArg CommRingCat.Hom.hom he

#print axioms componentDisk_field_embedding

/-- Extend a geometrically specified field embedding to algebraic closures,
retaining its restriction to the original field. -/
theorem algebraicClosure_embedding {F K : Type} [Field F] [Field K]
    (θ : F →+* K) :
    ∃ σ : AlgebraicClosure F →+* AlgebraicClosure K,
      σ.comp (algebraMap F (AlgebraicClosure F)) =
        (algebraMap K (AlgebraicClosure K)).comp θ := by
  letI : Algebra F (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp θ).toAlgebra
  let σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure K := IsAlgClosed.lift
  exact ⟨σ.toRingHom, RingHom.ext σ.commutes⟩

/-- All cusp punctures admit a comparison with one algebraic closure of the
component function field, with both the k-map and generic map checked. -/
theorem componentDisk_geometric_embedding (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (d : Disk k ⟶ X.space) (hd : Extends k L D X b d)
    (hc : d (closedPoint k) ∈ componentOpen k L D X x) :
    let F := (Component k L D X x).functionField
    ∃ σ : AlgebraicClosure F →+* AlgebraicClosure (LaurentSeries k),
      σ.comp ((algebraMap F (AlgebraicClosure F)).comp
        (AlgebraicCurve.baseToFunctionField (projection k L D X x))) =
          (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k))).comp
            (algebraMap k (LaurentSeries k)) ∧
      Spec.map (CommRingCat.ofHom σ) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) ≫
          componentGenericOpen k L D X x) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k)))) ≫ b := by
  obtain ⟨θ, hθk, hθ⟩ := componentDisk_field_embedding k L D X x E b hb d hd hc
  obtain ⟨σ, hσ⟩ := algebraicClosure_embedding θ
  refine ⟨σ, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, hσ, RingHom.comp_assoc, hθk]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hθ]

#print axioms componentDisk_geometric_embedding
end ComponentGenericPoint

section GenericMarkedCurve
open CategoryTheory.Limits NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaLegendreAtlasR0176 CompatibleClassifyingUniqueness

/-- An actual marked Weierstrass presentation of a specified geometric point
of the compatible quotient. Existence is proved below. -/
structure FieldPresentation (K : Type) [Field K] [Algebra k K]
    (b : Base K ⟶ OpenBase k L D) where
  equation : WeierstrassCurve K
  elliptic : equation.IsElliptic
  law : Law K equation
  originLaw : IsOriginLaw K equation law
  marking : FullLevel K equation law L (𝟙 (Base K))
  comparison : Curve K equation ⟶ D.atlas.descent.family.curve
  classifies : Classifies k L D.atlas D.two D.cover D.quotient
    K equation law marking b comparison

/-- The finite sign cover supplies a geometric lift; its accepted Legendre
presentation retains the same quotient map and both full-marking sections. -/
theorem fieldPresentation_exists (K : Type) [Field K] [IsAlgClosed K] [Algebra k K]
    (b : Base K ⟶ OpenBase k L D)
    (hb : b ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    Nonempty (FieldPresentation k L D K b) := by
  letI := D.quotient.quotient.finite
  letI := D.quotient.quotient.surjective
  obtain ⟨a₀, ha₀⟩ := lift_geometric_point D.quotient.quotient.q b
  let a := a₀ ≫ D.cover.inclusion
  let α := (Spec.preimage (a ≫ D.atlas.level.projection)).hom
  have ha : a ≫ D.atlas.level.projection = Spec.map (CommRingCat.ofHom α) :=
    (Spec.map_preimage _).symm
  obtain ⟨P⟩ := presentation_exists k L D.atlas K α a ha
  letI : (legendre k).IsElliptic := (legendre_family_geometry k).2.2.2.1
  letI : Algebra (LegendreRing k) K := α.toAlgebra
  letI : ((legendre k).map α).IsElliptic := inferInstance
  have hq : a ≫ D.atlas.quotient.q = b ≫ D.quotient.inclusion := by
    rw [show a = a₀ ≫ D.cover.inclusion from rfl, Category.assoc,
      D.quotient.cartesian.w, ← Category.assoc, ha₀]
  refine ⟨⟨(legendre k).map α, inferInstance, P.law, P.originLaw,
    P.marking, P.comparison, hb, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [hq] using P.cartesian
  · simpa only [hq] using P.origin_eq
  · simpa only [hq] using P.x_eq
  · simpa only [hq] using P.y_eq

/-- A single marked geometric generic curve for this actual component.
Every scalar action here is induced by its geometric projection. -/
theorem component_generic_presentation :
    let F := (Component k L D X x).functionField
    letI : Algebra k F := (AlgebraicCurve.baseToFunctionField (projection k L D X x)).toAlgebra
    let K := AlgebraicClosure F
    letI : Algebra k K := ((algebraMap F K).comp
      (AlgebraicCurve.baseToFunctionField (projection k L D X x))).toAlgebra
    Nonempty (FieldPresentation k L D K
      (Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ componentGenericOpen k L D X x)) := by
  let F := (Component k L D X x).functionField
  letI : Algebra k F := (AlgebraicCurve.baseToFunctionField (projection k L D X x)).toAlgebra
  let K := AlgebraicClosure F
  letI : Algebra k K := ((algebraMap F K).comp
    (AlgebraicCurve.baseToFunctionField (projection k L D X x))).toAlgebra
  change Nonempty (FieldPresentation k L D K
    (Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ componentGenericOpen k L D X x))
  apply fieldPresentation_exists
  rw [Category.assoc, componentGenericOpen_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

#print axioms fieldPresentation_exists
#print axioms component_generic_presentation

/-- Two actual presentations over compatible field points have a pointed
Cartesian comparison preserving both full-level sections. -/
theorem classification_comparison
    {F K : Type} [Field F] [Field K] [Algebra k F] [Algebra k K]
    {W : WeierstrassCurve F} {V : WeierstrassCurve K}
    {G : Law F W} {H : Law K V}
    (M : FullLevel F W G L (𝟙 (Base F)))
    (N : FullLevel K V H L (𝟙 (Base K)))
    (bF : Base F ⟶ OpenBase k L D) (bK : Base K ⟶ OpenBase k L D)
    (f : Curve F W ⟶ D.atlas.descent.family.curve)
    (g : Curve K V ⟶ D.atlas.descent.family.curve)
    (hf : Classifies k L D.atlas D.two D.cover D.quotient F W G M bF f)
    (hg : Classifies k L D.atlas D.two D.cover D.quotient K V H N bK g)
    (σ : F →+* K) (hσ : baseMap F K σ ≫ bF = bK) :
    ∃ j : Curve K V ⟶ Curve F W,
      IsPullback j (structureMap K V) (structureMap F W) (baseMap F K σ) ∧
      j ≫ f = g ∧
      origin K V ≫ j = baseMap F K σ ≫ origin F W ∧
      N.x.val ≫ j = baseMap F K σ ≫ M.x.val ∧
      N.y.val ≫ j = baseMap F K σ ≫ M.y.val := by
  have hbase : baseMap F K σ ≫ (bF ≫ D.quotient.inclusion) =
      bK ≫ D.quotient.inclusion := by rw [← Category.assoc, hσ]
  let j := hf.2.1.lift g (structureMap K V ≫ baseMap F K σ)
    (by rw [hg.2.1.w, Category.assoc, hbase])
  have hjf : j ≫ f = g := hf.2.1.lift_fst _ _ _
  have hjp : j ≫ structureMap F W = structureMap K V ≫ baseMap F K σ :=
    hf.2.1.lift_snd _ _ _
  have hj : IsPullback j (structureMap K V) (structureMap F W) (baseMap F K σ) := by
    have hout : IsPullback (j ≫ f) (structureMap K V)
        D.atlas.descent.family.projection
        (baseMap F K σ ≫ (bF ≫ D.quotient.inclusion)) := by
      rw [hjf, hbase]
      exact hg.2.1
    exact hout.of_right hjp hf.2.1
  refine ⟨j, hj, hjf, ?_, ?_, ?_⟩
  · apply hf.2.1.hom_ext
    · simp only [Category.assoc, hjf, hg.2.2.1, hf.2.2.1, ← hbase]
    · rw [Category.assoc, hjp, ← Category.assoc, BaseChange.origin_over,
        Category.id_comp, Category.assoc, BaseChange.origin_over, Category.comp_id]
  · apply hf.2.1.hom_ext
    · simp only [Category.assoc, hjf, hg.2.2.2.1, hf.2.2.2.1, ← hbase]
    · rw [Category.assoc, hjp, ← Category.assoc, N.x.property,
        Category.id_comp, Category.assoc, M.x.property, Category.comp_id]
  · apply hf.2.1.hom_ext
    · simp only [Category.assoc, hjf, hg.2.2.2.2, hf.2.2.2.2, ← hbase]
    · rw [Category.assoc, hjp, ← Category.assoc, N.y.property,
        Category.id_comp, Category.assoc, M.y.property, Category.comp_id]

/-- The Cartesian comparison respects the specified group laws, not just
the underlying unmarked projective curves. -/
theorem fieldPresentation_comparison
    {F K : Type} [Field F] [Field K] [Algebra k F] [Algebra k K]
    {bF : Base F ⟶ OpenBase k L D} {bK : Base K ⟶ OpenBase k L D}
    (P : FieldPresentation k L D F bF) (Q : FieldPresentation k L D K bK)
    (σ : F →+* K) (hσ : baseMap F K σ ≫ bF = bK) :
    ∃ j : Curve K Q.equation ⟶ Curve F P.equation,
      ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
        F P.equation P.law K Q.equation Q.law σ j ∧
      j ≫ P.comparison = Q.comparison ∧
      Q.marking.x.val ≫ j = baseMap F K σ ≫ P.marking.x.val ∧
      Q.marking.y.val ≫ j = baseMap F K σ ≫ P.marking.y.val := by
  letI := Q.elliptic
  obtain ⟨j, hj, hjf, hjo, hjx, hjy⟩ := classification_comparison k L D
    P.marking Q.marking bF bK P.comparison Q.comparison P.classifies Q.classifies σ hσ
  refine ⟨j, ?_, hjf, hjx, hjy⟩
  exact ArithmeticThetaLegendreComparisonR0177.MarkedLegendreAtlasLocalCoverageR0177.pointed_base_change
    P.law Q.law P.originLaw Q.originLaw σ j hj hjo

#print axioms classification_comparison
#print axioms fieldPresentation_comparison

/-- The actual Weil pairing of a marked geometric presentation. -/
def fieldPresentationPairing
    {K : Type} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K] [Algebra k K]
    {b : Base K ⟶ OpenBase k L D} (P : FieldPresentation k L D K b) : Kˣ := by
  letI := P.elliptic
  exact fullLevelPairing P.equation P.law P.originLaw L
    (BaseChange.restrict P.marking
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) (Category.comp_id _))

/-- A classifying comparison computes the same actual pairing after the
specified field embedding, even when the original field is not closed. -/
theorem classification_pairing
    {F K : Type} [Field F] [CharZero F] [Field K] [CharZero K]
    [DecidableEq K] [IsAlgClosed K] [Algebra k F] [Algebra k K]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W) (hG : IsOriginLaw F W G)
    (M : FullLevel F W G L (𝟙 (Base F)))
    (bF : Base F ⟶ OpenBase k L D) (bK : Base K ⟶ OpenBase k L D)
    (f : Curve F W ⟶ D.atlas.descent.family.curve)
    (hf : Classifies k L D.atlas D.two D.cover D.quotient F W G M bF f)
    (Q : FieldPresentation k L D K bK)
    (σ : F →+* K) (hσ : baseMap F K σ ≫ bF = bK) :
    letI : Algebra F K := σ.toAlgebra
    fieldPresentationPairing k L D Q = fullLevelPairing W G hG L
      (BaseChange.restrict M (baseMap F K σ) (Category.comp_id _)) := by
  letI : Algebra F K := σ.toAlgebra
  letI := Q.elliptic
  obtain ⟨j, hj, _, hjo, hjx, hjy⟩ := classification_comparison k L D
    M Q.marking bF bK f Q.comparison hf Q.classifies σ hσ
  apply fullLevelPairing_cartesian W G hG Q.equation Q.law Q.originLaw j hj hjo
  · simpa only [BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp,
      Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using hjx
  · simpa only [BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp,
      Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using hjy

/-- Naturality of the actual pairing on geometric presentations for the
specified embedding of algebraically closed coefficient fields. -/
theorem fieldPresentationPairing_natural
    {F K : Type} [Field F] [CharZero F] [DecidableEq F] [IsAlgClosed F]
    [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K] [Algebra k F] [Algebra k K]
    {bF : Base F ⟶ OpenBase k L D} {bK : Base K ⟶ OpenBase k L D}
    (P : FieldPresentation k L D F bF) (Q : FieldPresentation k L D K bK)
    (hn : 0 < L) (σ : F →+* K) (hσ : baseMap F K σ ≫ bF = bK) :
    (fieldPresentationPairing k L D Q : K) = σ (fieldPresentationPairing k L D P : F) := by
  letI := P.elliptic
  letI : Algebra F K := σ.toAlgebra
  have hc := classification_pairing k L D P.equation P.law P.originLaw P.marking
    bF bK P.comparison P.classifies Q σ hσ
  let M := BaseChange.restrict P.marking
    (Spec.map (CommRingCat.ofHom (algebraMap F F))) (Category.comp_id _)
  have hm : fieldMarkingMap P.equation P.law (Algebra.ofId F K) M =
      BaseChange.restrict P.marking (baseMap F K σ) (Category.comp_id _) := by
    apply CoverGeometryR0175.marking_ext
    · simp [fieldMarkingMap, M, BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp, baseMap]
      rfl
    · simp [fieldMarkingMap, M, BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp, baseMap]
      rfl
  have hp := fullLevelPairing_map P.equation P.law P.originLaw (Algebra.ofId F K) L hn M
  rw [hm] at hp
  exact (congrArg (fun z : Kˣ => (z : K)) hc).trans hp

#print axioms classification_pairing
#print axioms fieldPresentationPairing_natural

/-- A typed version retaining the existing scalar structure throughout the
actual Cartesian comparison. -/
theorem classification_pairing_algebra
    {F K : Type} [Field F] [CharZero F] [Field K] [CharZero K]
    [DecidableEq K] [IsAlgClosed K] [Algebra k F] [Algebra k K] [Algebra F K]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W) (hG : IsOriginLaw F W G)
    (M : FullLevel F W G L (𝟙 (Base F)))
    (bF : Base F ⟶ OpenBase k L D) (bK : Base K ⟶ OpenBase k L D)
    (f : Curve F W ⟶ D.atlas.descent.family.curve)
    (hf : Classifies k L D.atlas D.two D.cover D.quotient F W G M bF f)
    (Q : FieldPresentation k L D K bK)
    (hσ : baseMap F K (algebraMap F K) ≫ bF = bK) :
    fieldPresentationPairing k L D Q = fullLevelPairing W G hG L
      (BaseChange.restrict M (baseMap F K (algebraMap F K)) (Category.comp_id _)) := by
  letI := Q.elliptic
  obtain ⟨j, hj, _, hjo, hjx, hjy⟩ := classification_comparison k L D
    M Q.marking bF bK f Q.comparison hf Q.classifies (algebraMap F K) hσ
  apply fullLevelPairing_cartesian W G hG Q.equation Q.law Q.originLaw j hj hjo
  · simpa only [BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp,
      Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using hjx
  · simpa only [BaseChange.restrict, WeierstrassProjModel.schemeHomOverComp,
      Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using hjy

/-- The Weil pairing of the actual Tate marking over its geometric
coefficient field. -/
def tatePairing (E : TateLevel k L) : (AlgebraicClosure (LaurentSeries k))ˣ := by
  classical
  letI := E.elliptic
  exact fullLevelPairing (TateCurve k L) E.law E.originLaw L
    (BaseChange.restrict E.marking
      (Spec.map (CommRingCat.ofHom
        (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k)))))
      (Category.comp_id _))

/-- Comparison with a Tate presentation in a common geometric coefficient
field. The scalar equation and moduli-point equation are both explicit. -/
theorem tatePairing_of_common_presentation
    {A : Type} [Field A] [CharZero A] [DecidableEq A] [IsAlgClosed A] [Algebra k A]
    {bA : Base A ⟶ OpenBase k L D} (P : FieldPresentation k L D A bA)
    (hn : 0 < L) (ζ : k)
    (hζ : algebraMap k A ζ = (fieldPresentationPairing k L D P : A))
    (E : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D)
    (hb : ClassifiesTate k L D E b)
    (σ : A →+* AlgebraicClosure (LaurentSeries k))
    (hscalar : σ.comp (algebraMap k A) = algebraMap k (AlgebraicClosure (LaurentSeries k)))
    (hσ : baseMap A (AlgebraicClosure (LaurentSeries k)) σ ≫ bA =
      Spec.map (CommRingCat.ofHom
        (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k)))) ≫ b) :
    algebraMap k (AlgebraicClosure (LaurentSeries k)) ζ = (tatePairing k L E : _) := by
  classical
  let C := AlgebraicClosure (LaurentSeries k)
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : CharZero C := inferInstance
  let α := algebraMap (LaurentSeries k) C
  let bC := Spec.map (CommRingCat.ofHom α) ≫ b
  obtain ⟨f, hf⟩ := hb
  have hfb : b ≫ openStructure k L D =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))) := hf.1
  have hbC : bC ≫ openStructure k L D = Spec.map (CommRingCat.ofHom (algebraMap k C)) := by
    change (Spec.map (CommRingCat.ofHom α) ≫ b) ≫ openStructure k L D = _
    rw [Category.assoc, hfb, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq k (LaurentSeries k) C]
  obtain ⟨Q⟩ := fieldPresentation_exists k L D C bC hbC
  have hp := fieldPresentationPairing_natural k L D P Q hn σ hσ
  letI := E.elliptic
  have he : fieldPresentationPairing k L D Q = tatePairing k L E :=
    classification_pairing_algebra k L D (TateCurve k L) E.law E.originLaw E.marking
      b bC f hf Q rfl
  calc
    algebraMap k C ζ = σ (algebraMap k A ζ) := (RingHom.congr_fun hscalar ζ).symm
    _ = σ (fieldPresentationPairing k L D P : A) := congrArg σ hζ
    _ = (fieldPresentationPairing k L D Q : C) := hp.symm
    _ = (tatePairing k L E : C) := congrArg (fun z : Cˣ => (z : C)) he

#print axioms classification_pairing_algebra
#print axioms tatePairing_of_common_presentation

/-- A single primitive ground-field pairing value controls every actual
classifying Tate disk centered on the selected component. No connectedness
of a fixed-pairing locus is assumed. -/
theorem component_pairing_constant [IsAlgClosed k] (hn : 0 < L) :
    ∃ ζ : k, IsPrimitiveRoot ζ L ∧
      ∀ (E : TateLevel k L) (b : Puncture k ⟶ OpenBase k L D),
        ClassifiesTate k L D E b →
        ∀ (d : Disk k ⟶ X.space), Extends k L D X b d →
          d (closedPoint k) ∈ componentOpen k L D X x →
          algebraMap k (AlgebraicClosure (LaurentSeries k)) ζ = (tatePairing k L E : _) := by
  classical
  let F := (Component k L D X x).functionField
  let ρ := AlgebraicCurve.baseToFunctionField (projection k L D X x)
  letI : Algebra k F := ρ.toAlgebra
  let A := AlgebraicClosure F
  letI : Algebra k A := ((algebraMap F A).comp ρ).toAlgebra
  letI : CharZero A := Algebra.charZero_of_charZero k A
  let bA := Spec.map (CommRingCat.ofHom (algebraMap F A)) ≫ componentGenericOpen k L D X x
  obtain ⟨P⟩ := component_generic_presentation k L D X x
  change FieldPresentation k L D A bA at P
  letI := P.elliptic
  let M := BaseChange.restrict P.marking
    (Spec.map (CommRingCat.ofHom (algebraMap A A))) (Category.comp_id _)
  obtain ⟨ζ, hζ, _⟩ := fullLevelPairing_descends P.equation P.law P.originLaw k L hn M
  change IsPrimitiveRoot ζ L ∧ algebraMap k A ζ = (fieldPresentationPairing k L D P : A) at hζ
  refine ⟨ζ, hζ.1, ?_⟩
  intro E b hb d hd hc
  obtain ⟨σ, hσk, hσb⟩ := componentDisk_geometric_embedding k L D X x E b hb d hd hc
  let C := AlgebraicClosure (LaurentSeries k)
  have hscalar : σ.comp (algebraMap k A) = algebraMap k C :=
    hσk.trans (IsScalarTower.algebraMap_eq k (LaurentSeries k) C).symm
  exact tatePairing_of_common_presentation k L D P hn ζ hζ.2 E b hb σ hscalar hσb

#print axioms component_pairing_constant

include hL heven in
/-- The actual component cusps embed into one fixed-pairing set of actual
Tate markings. Its arithmetic orbit identification remains a separate step. -/
theorem cusps_fixed_pairing_embedding [IsAlgClosed k] :
    ∃ ζ : k, IsPrimitiveRoot ζ L ∧
      Nonempty ((Cusps k L D X x) ↪
        {E : TateLevel k L //
          algebraMap k (AlgebraicClosure (LaurentSeries k)) ζ = (tatePairing k L E : _)}) := by
  obtain ⟨ζ, hζ, hp⟩ := component_pairing_constant k L D X x (by omega)
  refine ⟨ζ, hζ, ⟨⟨fun c => ⟨cuspTateMarking k L D X x hL heven c, ?_⟩, ?_⟩⟩⟩
  · apply hp _ (tateClassifying k L D hL heven _)
      (tateClassifying_spec k L D hL heven _)
      (tateDisk k L D X hL heven _) (tateDisk_spec k L D X hL heven _)
    change (tateCenter k L D X hL heven (cuspTateMarking k L D X x hL heven c)).val ∈ _
    rw [cuspTateMarking_center]
    exact c.val.property
  · intro c c' hcc'
    exact cuspTateMarking_injective k L D X x hL heven (congrArg Subtype.val hcc')

#print axioms cusps_fixed_pairing_embedding
end GenericMarkedCurve

section ParameterRotation
open CategoryTheory.Limits NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality

variable (α : kˣ)

/-- The disk automorphism and its punctured restriction use the same
power-series coefficient map. -/
def rotateDisk : Disk k ⟶ Disk k :=
  Spec.map (CommRingCat.ofHom (powerRescale k α).toRingHom)

def rotatePuncture : Puncture k ⟶ Puncture k :=
  Spec.map (CommRingCat.ofHom (laurentRescale k α).toRingHom)

theorem rotateDisk_closedPoint : rotateDisk k α (closedPoint k) = closedPoint k := by
  letI : IsLocalHom (powerRescale k α).toRingHom :=
    IsLocalHom.of_surjective _ (powerRescale k α).surjective
  apply PrimeSpectrum.ext
  exact IsLocalRing.maximalIdeal_comap (powerRescale k α).toRingHom

theorem rotateDisk_generic :
    genericInclusion k ≫ rotateDisk k α = rotatePuncture k α ≫ genericInclusion k := by
  unfold genericInclusion rotateDisk rotatePuncture
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun f => (laurentRescale_powerSeries k α f).symm))

theorem rotateDisk_over : rotateDisk k α ≫ diskStructure k = diskStructure k := by
  unfold rotateDisk diskStructure
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change PowerSeries.rescale (α : k) (PowerSeries.C a) = PowerSeries.C a
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

theorem rotatePuncture_over :
    rotatePuncture k α ≫ Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k))) := by
  unfold rotatePuncture
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change laurentRescale k α (algebraMap k (LaurentSeries k) a) = algebraMap k (LaurentSeries k) a
  have ha : algebraMap k (LaurentSeries k) a =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C a) := by
    rw [HahnSeries.algebraMap_apply', LaurentSeries.coe_algebraMap]
    rfl
  rw [ha, laurentRescale_powerSeries]
  apply congrArg (algebraMap (PowerSeries k) (LaurentSeries k))
  change PowerSeries.rescale (α : k) (PowerSeries.C a) = PowerSeries.C a
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

/-- Reparametrizing an actual disk preserves its actual boundary center. -/
theorem extends_rotate (b : Puncture k ⟶ OpenBase k L D)
    (d : Disk k ⟶ X.space) (hd : Extends k L D X b d) :
    Extends k L D X (rotatePuncture k α ≫ b) (rotateDisk k α ≫ d) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, hd.1, rotateDisk_over]
  · rw [← Category.assoc, rotateDisk_generic, Category.assoc, hd.2.1, Category.assoc]
  · change d (rotateDisk k α (closedPoint k)) ∈ _
    rw [rotateDisk_closedPoint]
    exact hd.2.2

variable (hpos : 0 < L) (hα : (α : k)^L = 1)

/-- Pull back both full-level sections along the actual semilinear
Tate-curve automorphism, retaining the original group law. -/
def rotatedTate (E : TateLevel k L) : TateLevel k L := by
  letI := E.elliptic
  let hb := ParameterGeometry.isBaseChange k α L hpos heven hα E.law E.originLaw
  let A := BaseChange.restrict E.marking (rotatePuncture k α)
    (show rotatePuncture k α ≫ 𝟙 _ = 𝟙 _ ≫ rotatePuncture k α by simp)
  exact ⟨E.elliptic, E.law, E.originLaw, BaseChange.up hb E.originLaw E.originLaw A⟩

theorem rotatedTate_x (E : TateLevel k L) :
    (rotatedTate k L heven α hpos hα E).marking.x.val ≫
        ParameterGeometry.map k α L hpos heven hα =
      rotatePuncture k α ≫ E.marking.x.val := by
  letI := E.elliptic
  exact BaseChange.up_x _ E.originLaw E.originLaw _

theorem rotatedTate_y (E : TateLevel k L) :
    (rotatedTate k L heven α hpos hα E).marking.y.val ≫
        ParameterGeometry.map k α L hpos heven hα =
      rotatePuncture k α ≫ E.marking.y.val := by
  letI := E.elliptic
  exact BaseChange.up_y _ E.originLaw E.originLaw _

/-- Rotation acts on the prescribed actual classifying map, not merely on
an abstract set of labels. Both marking equations are preserved. -/
theorem classifies_rotatedTate (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b) :
    ClassifiesTate k L D (rotatedTate k L heven α hpos hα E) (rotatePuncture k α ≫ b) := by
  obtain ⟨f, hf⟩ := hb
  refine ⟨ParameterGeometry.map k α L hpos heven hα ≫ f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hf.1]
    exact rotatePuncture_over k α
  · simpa only [Category.assoc, rotatePuncture, baseMap] using
      (ParameterGeometry.cartesian k α L hpos heven hα).paste_horiz hf.2.1
  · rw [← Category.assoc, ParameterGeometry.origin_map, Category.assoc, hf.2.2.1]
    simp only [Category.assoc]
    rfl
  · rw [← Category.assoc, rotatedTate_x, Category.assoc, hf.2.2.2.1]
    simp only [Category.assoc]
  · rw [← Category.assoc, rotatedTate_y, Category.assoc, hf.2.2.2.2]
    simp only [Category.assoc]

/-- Every level-th-root parameter rotation lies in an actual disk-center
fiber. This supplies the geometric width action before finite labeling. -/
theorem tateCenter_rotatedTate (E : TateLevel k L) :
    tateCenter k L D X hL heven (rotatedTate k L heven α hpos hα E) =
      tateCenter k L D X hL heven E := by
  apply Subtype.ext
  have h := tateCenter_eq_of_extends k L D X hL heven
    (rotatedTate k L heven α hpos hα E)
    (rotatePuncture k α ≫ tateClassifying k L D hL heven E)
    (rotateDisk k α ≫ tateDisk k L D X hL heven E)
    (classifies_rotatedTate k L D heven α hpos hα E _ (tateClassifying_spec k L D hL heven E))
    (extends_rotate k L D X α _ _ (tateDisk_spec k L D X hL heven E))
  change _ = tateDisk k L D X hL heven E (closedPoint k)
  rw [h]
  change tateDisk k L D X hL heven E (rotateDisk k α (closedPoint k)) = _
  rw [rotateDisk_closedPoint]

#print axioms rotateDisk_closedPoint
#print axioms classifies_rotatedTate
#print axioms tateCenter_rotatedTate
end ParameterRotation

/-- The auxiliary law record does not change the center when the two actual
full-level section maps agree. -/
theorem tateCenter_eq_of_sections (E F : TateLevel k L)
    (hx : E.marking.x.val = F.marking.x.val)
    (hy : E.marking.y.val = F.marking.y.val) :
    tateCenter k L D X hL heven E = tateCenter k L D X hL heven F := by
  obtain ⟨f, hf⟩ := tateClassifying_spec k L D hL heven F
  have hE : ClassifiesTate k L D E (tateClassifying k L D hL heven F) := by
    refine ⟨f, hf.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
    · rw [hx]; exact hf.2.2.2.1
    · rw [hy]; exact hf.2.2.2.2
  apply Subtype.ext
  exact tateCenter_eq_of_extends k L D X hL heven E _ _ hE
    (tateDisk_spec k L D X hL heven F)

section FiniteLabelConvention
open ArithmeticThetaMarkingCuspsR0102

include hL in
/-- Inverting marking matrices converts the accepted right signed-translation
fibers to the left action used by geometric parameter rotation. -/
theorem inverse_label_fiber (A B : FiniteMarking L)
    (h : finiteLabel L A⁻¹ = finiteLabel L B⁻¹) :
    ∃ s : Bool × ZMod L, B = (signedTranslation L s)⁻¹ * A := by
  obtain ⟨e, he⟩ := signed_translation_fiber L hL
  let C : BaseFiber L := ⟨A * B⁻¹, by
    simpa using finiteLabel_mul_congr L A B⁻¹ A⁻¹ h.symm⟩
  obtain ⟨s, hs⟩ := e.surjective C
  have hc : signedTranslation L s = A * B⁻¹ := by
    rw [← he s, hs]
  refine ⟨s, ?_⟩
  rw [hc, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, inv_inv]

#print axioms inverse_label_fiber
end FiniteLabelConvention
#print axioms tateCenter_eq_of_sections

section RotationCoordinates
open CategoryTheory.Limits NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality

variable (α : kˣ) (hpos : 0 < L) (hα : (α : k)^L = 1)

/-- A coordinate presentation of the inverse parameter action suffices to
identify centers; no equality of auxiliary group-law records is assumed. -/
theorem tateCenter_eq_of_semilinear_sections (E F : TateLevel k L)
    (hx : baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).symm.toRingHom ≫
      E.marking.x.val ≫ ParameterGeometry.map k α L hpos heven hα = F.marking.x.val)
    (hy : baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).symm.toRingHom ≫
      E.marking.y.val ≫ ParameterGeometry.map k α L hpos heven hα = F.marking.y.val) :
    tateCenter k L D X hL heven E = tateCenter k L D X hL heven F := by
  letI := ParameterGeometry.map_isIso k α L hpos heven hα
  have hi : rotatePuncture k α ≫
      baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).symm.toRingHom = 𝟙 _ :=
    CoefficientMap.base_inverse (laurentRescale k α).symm
  have hx' : (rotatedTate k L heven α hpos hα F).marking.x.val = E.marking.x.val := by
    apply (cancel_mono (ParameterGeometry.map k α L hpos heven hα)).mp
    rw [rotatedTate_x, ← hx, ← Category.assoc, hi, Category.id_comp]
  have hy' : (rotatedTate k L heven α hpos hα F).marking.y.val = E.marking.y.val := by
    apply (cancel_mono (ParameterGeometry.map k α L hpos heven hα)).mp
    rw [rotatedTate_y, ← hy, ← Category.assoc, hi, Category.id_comp]
  exact (tateCenter_eq_of_sections k L D X hL heven _ E hx' hy').symm.trans
    (tateCenter_rotatedTate k L D X hL heven α hpos hα F)

include hpos hα in
/-- The literal Tate-coordinate formulas identify geometric centers after
one common root-of-unity rotation of both full-level sections. -/
theorem tateCenter_eq_of_rotated_coordinates (E F : TateLevel k L)
    (i j : Fin L) (a b : k)
    (hEx : HasCoordinates (LaurentSeries k) (TateCurve k L) E.marking.x.val
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L i.val a))
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L i.val a)))
    (hEy : HasCoordinates (LaurentSeries k) (TateCurve k L) E.marking.y.val
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L j.val b))
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L j.val b)))
    (hFx : HasCoordinates (LaurentSeries k) (TateCurve k L) F.marking.x.val
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX L i.val (a * ((α : k)^i.val)⁻¹)))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY L i.val (a * ((α : k)^i.val)⁻¹))))
    (hFy : HasCoordinates (LaurentSeries k) (TateCurve k L) F.marking.y.val
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX L j.val (b * ((α : k)^j.val)⁻¹)))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY L j.val (b * ((α : k)^j.val)⁻¹)))) :
    tateCenter k L D X hL heven E = tateCenter k L D X hL heven F := by
  apply tateCenter_eq_of_semilinear_sections k L D X hL heven α hpos hα E F
  · exact TwoTorsionSplitCubicR0177.coordinates_ext
      (ParameterGeometry.marked_coordinates k α L hpos heven hα i a E.marking.x.val hEx) hFx
  · exact TwoTorsionSplitCubicR0177.coordinates_ext
      (ParameterGeometry.marked_coordinates k α L hpos heven hα j b E.marking.y.val hEy) hFy

/-- Origin laws on the prescribed elliptic Tate cubic coincide. -/
theorem tateLaw_eq (E F : TateLevel k L) : E.law = F.law := by
  letI := E.elliptic
  have hone : (E.law.one (𝟙 _)).val = (F.law.one (𝟙 _)).val := by
    rw [E.originLaw.1, F.originLaw.1]
  apply ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext
  · intro T t P Q
    exact WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
      (TateCurve k L).toProjective E.law F.law hone t P Q
  · intro T t
    exact Subtype.ext ((E.originLaw.1 t).trans (F.originLaw.1 t).symm)

#print axioms tateCenter_eq_of_semilinear_sections
#print axioms tateCenter_eq_of_rotated_coordinates
#print axioms tateLaw_eq
end RotationCoordinates


section FixedPairingMatrices
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175

variable {F K : Type} [Field F] [CharZero F] [Field K] [DecidableEq K] [IsAlgClosed K]
    [Algebra F K] (W : WeierstrassCurve F) [W.IsElliptic]
    (G : Law F W) (hG : IsOriginLaw F W G) (n : ℕ) (hn : 0 < n)

abbrev GeometricTorsion := Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point (n : ℤ)

/-- Evaluation in the actual geometric torsion subgroup retains the killed-section proof. -/
def evalTorsionPoint
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) (structureMap F W))
    (hP : G.nsmul _ n P = G.one _) : GeometricTorsion (K := K) W n :=
  ⟨fullLevelEvaluation W G hG P, by
    change (n : ℤ) • fullLevelEvaluation W G hG P = 0
    rw [Nat.cast_smul_eq_nsmul, ← eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), hP, fullLevelEvaluation_zero]⟩

include hn in
theorem fullLevelBasis_exists
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    ∃ e : (ZMod n × ZMod n) ≃+ GeometricTorsion (K := K) W n,
      (e (1,0)).val = fullLevelEvaluation W G hG A.x ∧
      (e (0,1)).val = fullLevelEvaluation W G hG A.y := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : CharZero K := Algebra.charZero_of_charZero F K
  letI : (W.baseChange K).IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  let T := GeometricTorsion (K := K) W n
  have hc : Nat.card T = n ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.baseChange K).toAffine (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (by norm_num)
  letI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 hn.ne')
  have hk (z : T) : n • z = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using Submodule.smul_torsionBy (n : ℤ) z
  let B := fieldMarkToPair (L := n) hG _ (fullLevelEvaluation (K := K) W G hG)
    (fullLevelEvaluation_mul W G hG) (fullLevelEvaluation_zero W G hG) A
  let e : (ZMod n × ZMod n) ≃+ T := basisPairEquiv n hk hc B
  refine ⟨e, ?_, ?_⟩
  · exact congrArg Subtype.val (pairHom_fst n hk B.val.1 B.val.2)
  · exact congrArg Subtype.val (pairHom_snd n hk B.val.1 B.val.2)

/-- A basis constructed from the two actual full-level sections. -/
def fullLevelBasis
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    (ZMod n × ZMod n) ≃+ GeometricTorsion (K := K) W n :=
  (fullLevelBasis_exists W G hG n hn A).choose

theorem fullLevelBasis_fst
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    (fullLevelBasis W G hG n hn A (1,0)).val = fullLevelEvaluation W G hG A.x :=
  (fullLevelBasis_exists W G hG n hn A).choose_spec.1

theorem fullLevelBasis_snd
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    (fullLevelBasis W G hG n hn A (0,1)).val = fullLevelEvaluation W G hG A.y :=
  (fullLevelBasis_exists W G hG n hn A).choose_spec.2

theorem fullLevelBasis_apply
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    (v : ZMod n × ZMod n) :
    (fullLevelBasis W G hG n hn A v).val =
      v.1.val • fullLevelEvaluation W G hG A.x +
      v.2.val • fullLevelEvaluation W G hG A.y := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hv : v.1.val • (1,0) + v.2.val • (0,1) = v := by ext <;> simp
  have h := congrArg (fullLevelBasis W G hG n hn A) hv
  rw [map_add, map_nsmul, map_nsmul] at h
  have h' := congrArg Subtype.val h
  change v.1.val • (fullLevelBasis W G hG n hn A (1,0)).val +
    v.2.val • (fullLevelBasis W G hG n hn A (0,1)).val = _ at h'
  rw [fullLevelBasis_fst, fullLevelBasis_snd] at h'
  exact h'.symm

def fullLevelResidues
    (A B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    (ZMod n × ZMod n) × (ZMod n × ZMod n) :=
  ((fullLevelBasis W G hG n hn A).symm (evalTorsionPoint W G hG n B.x B.killed_x),
   (fullLevelBasis W G hG n hn A).symm (evalTorsionPoint W G hG n B.y B.killed_y))

/-- Columns record the two actual sections of B in the actual basis A. -/
def fullLevelTransitionInt
    (A B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  let v := fullLevelResidues W G hG n hn A B
  !![(v.1.1.val : ℤ), (v.2.1.val : ℤ); (v.1.2.val : ℤ), (v.2.2.val : ℤ)]

theorem fullLevelTransition_x
    (A B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    fullLevelEvaluation W G hG B.x =
      fullLevelTransitionInt W G hG n hn A B 0 0 • fullLevelEvaluation W G hG A.x +
      fullLevelTransitionInt W G hG n hn A B 1 0 • fullLevelEvaluation W G hG A.y := by
  have h := congrArg Subtype.val ((fullLevelBasis W G hG n hn A).apply_symm_apply
    (evalTorsionPoint W G hG n B.x B.killed_x))
  rw [fullLevelBasis_apply] at h
  simpa [fullLevelTransitionInt, fullLevelResidues, evalTorsionPoint, Nat.cast_smul_eq_nsmul]
    using h.symm

theorem fullLevelTransition_y
    (A B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    fullLevelEvaluation W G hG B.y =
      fullLevelTransitionInt W G hG n hn A B 0 1 • fullLevelEvaluation W G hG A.x +
      fullLevelTransitionInt W G hG n hn A B 1 1 • fullLevelEvaluation W G hG A.y := by
  have h := congrArg Subtype.val ((fullLevelBasis W G hG n hn A).apply_symm_apply
    (evalTorsionPoint W G hG n B.y B.killed_y))
  rw [fullLevelBasis_apply] at h
  simpa [fullLevelTransitionInt, fullLevelResidues, evalTorsionPoint, Nat.cast_smul_eq_nsmul]
    using h.symm

/-- Equal actual pairing is exactly the determinant-one condition on these
actual section coordinates, at every positive level. -/
theorem fullLevelTransition_det_iff
    (A B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    (fullLevelTransitionInt W G hG n hn A B |>.map (Int.castRingHom (ZMod n))).det = 1 ↔
      fullLevelPairing W G hG n B = fullLevelPairing W G hG n A := by
  rw [← fullLevelPairing_relabel_iff W G hG n hn A,
    ← fullLevelTransition_x, ← fullLevelTransition_y]
  rfl

#print axioms fullLevelBasis_exists
#print axioms fullLevelTransition_det_iff

/-- The residue columns recover both actual section maps. -/
theorem fullLevelResidues_injective
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    Function.Injective (fullLevelResidues W G hG n hn A) := by
  intro B C h
  have hx : (fullLevelBasis W G hG n hn A).symm (evalTorsionPoint W G hG n B.x B.killed_x) =
      (fullLevelBasis W G hG n hn A).symm (evalTorsionPoint W G hG n C.x C.killed_x) :=
    congrArg Prod.fst h
  have hy : (fullLevelBasis W G hG n hn A).symm (evalTorsionPoint W G hG n B.y B.killed_y) =
      (fullLevelBasis W G hG n hn A).symm (evalTorsionPoint W G hG n C.y C.killed_y) :=
    congrArg Prod.snd h
  apply marking_ext
  · exact congrArg Subtype.val ((fullLevelEvaluation W G hG).injective
      (congrArg Subtype.val ((fullLevelBasis W G hG n hn A).symm.injective hx)))
  · exact congrArg Subtype.val ((fullLevelEvaluation W G hG).injective
      (congrArg Subtype.val ((fullLevelBasis W G hG n hn A).symm.injective hy)))

theorem fullLevelTransition_mod_injective
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    Function.Injective (fun B =>
      (fullLevelTransitionInt W G hG n hn A B).map (Int.castRingHom (ZMod n))) := by
  letI : NeZero n := ⟨hn.ne'⟩
  intro B C h
  apply fullLevelResidues_injective W G hG n hn A
  have h00 := congrArg (fun M => M 0 0) h
  have h10 := congrArg (fun M => M 1 0) h
  have h01 := congrArg (fun M => M 0 1) h
  have h11 := congrArg (fun M => M 1 1) h
  simp only [fullLevelTransitionInt, Matrix.map_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_natCast, ZMod.natCast_zmod_val]
    at h00 h10 h01 h11
  exact Prod.ext (Prod.ext h00 h10) (Prod.ext h01 h11)

/-- One fixed actual pairing embeds into determinant-one finite markings. -/
def fixedPairingMatrixEmbedding
    (A : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    {B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K))) //
      fullLevelPairing W G hG n B = fullLevelPairing W G hG n A} ↪
        Matrix.SpecialLinearGroup (Fin 2) (ZMod n) where
  toFun B := ⟨(fullLevelTransitionInt W G hG n hn A B.val).map (Int.castRingHom (ZMod n)),
    (fullLevelTransition_det_iff W G hG n hn A B.val).mpr B.property⟩
  inj' B C h := Subtype.ext (fullLevelTransition_mod_injective W G hG n hn A
    (congrArg Subtype.val h))

#print axioms fullLevelTransition_mod_injective
#print axioms fixedPairingMatrixEmbedding

end FixedPairingMatrices


section ActualFixedPairing
local instance : DecidableEq (AlgebraicClosure (LaurentSeries k)) := Classical.typeDecidableEq _
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175

/-- Express a Tate marking using the proved common origin law. -/
def tateCommonMarking (E₀ E : TateLevel k L) :
    FullLevel (LaurentSeries k) (TateCurve k L) E₀.law L (𝟙 (Puncture k)) :=
  (tateLaw_eq k L E E₀) ▸ E.marking

theorem tateCommonMarking_points (E₀ E : TateLevel k L) :
    (tateCommonMarking k L E₀ E).x.val = E.marking.x.val ∧
    (tateCommonMarking k L E₀ E).y.val = E.marking.y.val := by
  cases E with
  | mk he G ho M =>
    cases E₀ with
    | mk he₀ H ho₀ M₀ =>
      have h : G = H := tateLaw_eq k L ⟨he, G, ho, M⟩ ⟨he₀, H, ho₀, M₀⟩
      subst H
      exact ⟨rfl, rfl⟩

theorem tateLevel_ext (E F : TateLevel k L)
    (hx : E.marking.x.val = F.marking.x.val)
    (hy : E.marking.y.val = F.marking.y.val) : E = F := by
  cases E with
  | mk he G ho M =>
    cases F with
    | mk hf H hp N =>
      have h : G = H := tateLaw_eq k L ⟨he, G, ho, M⟩ ⟨hf, H, hp, N⟩
      subst H
      have hm : M = N := marking_ext M N hx hy
      subst N
      rfl

/-- The actual two sections, extended along the prescribed geometric field map. -/
def tateGeometricMarking (E₀ E : TateLevel k L) :
    FullLevel (LaurentSeries k) (TateCurve k L) E₀.law L
      (Spec.map (CommRingCat.ofHom
        (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k))))) :=
  BaseChange.restrict (tateCommonMarking k L E₀ E)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k)))))
    (Category.comp_id _)

theorem tateGeometricMarking_points (E₀ E : TateLevel k L) :
    (tateGeometricMarking k L E₀ E).x.val =
      Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k)
        (AlgebraicClosure (LaurentSeries k)))) ≫ E.marking.x.val ∧
    (tateGeometricMarking k L E₀ E).y.val =
      Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k)
        (AlgebraicClosure (LaurentSeries k)))) ≫ E.marking.y.val := by
  constructor
  · exact congrArg (fun f => Spec.map (CommRingCat.ofHom
      (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k)))) ≫ f)
      (tateCommonMarking_points k L E₀ E).1
  · exact congrArg (fun f => Spec.map (CommRingCat.ofHom
      (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k)))) ≫ f)
      (tateCommonMarking_points k L E₀ E).2

theorem tateGeometricMarking_injective (E₀ : TateLevel k L) :
    Function.Injective (tateGeometricMarking k L E₀) := by
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k))))
  letI : Epi q := Flat.epi_of_flat_of_surjective _
  intro E F h
  apply tateLevel_ext k L E F
  · apply (cancel_epi q).mp
    exact (tateGeometricMarking_points k L E₀ E).1.symm.trans
      ((congrArg (fun M => M.x.val) h).trans (tateGeometricMarking_points k L E₀ F).1)
  · apply (cancel_epi q).mp
    exact (tateGeometricMarking_points k L E₀ E).2.symm.trans
      ((congrArg (fun M => M.y.val) h).trans (tateGeometricMarking_points k L E₀ F).2)

theorem tateGeometricMarking_pairing (E₀ E : TateLevel k L) :
    letI := E₀.elliptic
    fullLevelPairing (TateCurve k L) E₀.law E₀.originLaw L
      (tateGeometricMarking k L E₀ E) = tatePairing k L E := by
  classical
  cases E with
  | mk he G ho M =>
    cases E₀ with
    | mk he₀ H ho₀ M₀ =>
      have h : G = H := tateLaw_eq k L ⟨he, G, ho, M⟩ ⟨he₀, H, ho₀, M₀⟩
      subst H
      rfl

/-- The actual fixed-pairing Tate markings inject into SL₂, retaining the
geometric field map and both section coordinates. -/
def tateFixedPairingMatrixEmbedding (hn : 0 < L) (E₀ : TateLevel k L) :
    {E : TateLevel k L // tatePairing k L E = tatePairing k L E₀} ↪
      Matrix.SpecialLinearGroup (Fin 2) (ZMod L) := by
  classical
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := E₀.elliptic
  let A := tateGeometricMarking k L E₀ E₀
  let f : {E : TateLevel k L // tatePairing k L E = tatePairing k L E₀} ↪
      {B : FullLevel (LaurentSeries k) (TateCurve k L) E₀.law L
        (Spec.map (CommRingCat.ofHom
          (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k))))) //
        fullLevelPairing (TateCurve k L) E₀.law E₀.originLaw L B =
          fullLevelPairing (TateCurve k L) E₀.law E₀.originLaw L A} :=
    { toFun E := ⟨tateGeometricMarking k L E₀ E.val, by
        rw [tateGeometricMarking_pairing, tateGeometricMarking_pairing]
        exact E.property⟩
      inj' E F h := Subtype.ext (tateGeometricMarking_injective k L E₀
        (congrArg Subtype.val h)) }
  exact f.trans (fixedPairingMatrixEmbedding (TateCurve k L) E₀.law E₀.originLaw L hn A)

include hL heven in
/-- Actual cusps now have determinant-one finite marking representatives.
The signed-translation quotient is still required for the factor 2L. -/
theorem cusps_sl2_embedding [IsAlgClosed k] :
    Nonempty ((Cusps k L D X x) ↪ Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  classical
  obtain ⟨ζ, hζ, ⟨e⟩⟩ := cusps_fixed_pairing_embedding k L D X x hL heven
  let c₀ : Cusps k L D X x := Classical.choice (cusps_nonempty k L D X x)
  let E₀ := (e c₀).val
  let f : Cusps k L D X x ↪
      {E : TateLevel k L // tatePairing k L E = tatePairing k L E₀} :=
    { toFun c := ⟨(e c).val, Units.ext ((e c).property.symm.trans (e c₀).property)⟩
      inj' c d h := by
        apply e.injective
        apply Subtype.ext
        exact congrArg (fun z : {E : TateLevel k L //
          tatePairing k L E = tatePairing k L E₀} => z.val) h }
  exact ⟨f.trans (tateFixedPairingMatrixEmbedding k L (by omega) E₀)⟩

#print axioms tateGeometricMarking_injective
#print axioms tateGeometricMarking_pairing
#print axioms tateFixedPairingMatrixEmbedding
#print axioms cusps_sl2_embedding
end ActualFixedPairing


section CanonicalCoordinates
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 CoverGeometryR0175
open ArithmeticThetaLegendreComparisonR0177

variable {F K : Type} [Field F] [CharZero F] [Field K] [DecidableEq K] [IsAlgClosed K]
    [Algebra F K] (W : WeierstrassCurve F) [W.IsElliptic]
    (G : Law F W) (hG : IsOriginLaw F W G) (n : ℕ) (hn : 0 < n)

theorem fullLevelResidues_sections
    (A B : FullLevel F W G n (Spec.map (CommRingCat.ofHom (algebraMap F K)))) :
    let v := fullLevelResidues W G hG n hn A B
    B.x = G.mul _ (G.nsmul _ v.1.1.val A.x) (G.nsmul _ v.1.2.val A.y) ∧
    B.y = G.mul _ (G.nsmul _ v.2.1.val A.x) (G.nsmul _ v.2.2.val A.y) := by
  constructor
  · apply (fullLevelEvaluation W G hG).injective
    rw [fullLevelEvaluation_mul, eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG)]
    simpa [fullLevelTransitionInt, Nat.cast_smul_eq_nsmul] using
      fullLevelTransition_x W G hG n hn A B
  · apply (fullLevelEvaluation W G hG).injective
    rw [fullLevelEvaluation_mul, eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG), eval_nsmul _ _ (fullLevelEvaluation_mul W G hG)
      (fullLevelEvaluation_zero W G hG)]
    simpa [fullLevelTransitionInt, Nat.cast_smul_eq_nsmul] using
      fullLevelTransition_y W G hG n hn A B

local instance : DecidableEq (AlgebraicClosure (LaurentSeries k)) := Classical.typeDecidableEq _

/-- Coordinates of an actual marking relative to another actual Tate marking. -/
def tateResidues (hn : 0 < L) (C E : TateLevel k L) :
    (ZMod L × ZMod L) × (ZMod L × ZMod L) := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := C.elliptic
  exact fullLevelResidues (TateCurve k L) C.law C.originLaw L hn
    (tateGeometricMarking k L C C) (tateGeometricMarking k L C E)

theorem tateResidues_sections (hn : 0 < L) (C E : TateLevel k L) :
    letI : NeZero L := ⟨hn.ne'⟩
    let v := tateResidues k L hn C E
    E.marking.x.val = coordinatePoint (LaurentSeries k) (TateCurve k L) C.law C.marking
      ⟨v.1.1.val, ZMod.val_lt _⟩ ⟨v.1.2.val, ZMod.val_lt _⟩ ∧
    E.marking.y.val = coordinatePoint (LaurentSeries k) (TateCurve k L) C.law C.marking
      ⟨v.2.1.val, ZMod.val_lt _⟩ ⟨v.2.2.val, ZMod.val_lt _⟩ := by
  letI : NeZero L := ⟨hn.ne'⟩
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := C.elliptic
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap (LaurentSeries k) (AlgebraicClosure (LaurentSeries k))))
  letI : Epi q := Flat.epi_of_flat_of_surjective _
  let A := tateGeometricMarking k L C C
  let B := tateGeometricMarking k L C E
  have hA := tateGeometricMarking_points k L C C
  have hB := tateGeometricMarking_points k L C E
  have h := fullLevelResidues_sections (TateCurve k L) C.law C.originLaw L hn A B
  have hc (i j : Fin L) :
      q ≫ coordinatePoint (LaurentSeries k) (TateCurve k L) C.law C.marking i j =
      (C.law.mul q (C.law.nsmul q i.val A.x) (C.law.nsmul q j.val A.y)).val :=
    Representability.combination_comp (LaurentSeries k) (TateCurve k L) C.law
      (𝟙 _) q q (Category.comp_id _) C.marking.x C.marking.y A.x A.y
      hA.1.symm hA.2.symm i.val j.val
  constructor
  · apply (cancel_epi q).mp
    rw [hc]
    exact hB.1.symm.trans (congrArg Subtype.val h.1)
  · apply (cancel_epi q).mp
    rw [hc]
    exact hB.2.symm.trans (congrArg Subtype.val h.2)

include hL in
theorem tateMarking_nonzero (E : TateLevel k L) :
    E.marking.x ≠ E.law.one _ ∧ E.marking.y ≠ E.law.one _ := by
  constructor
  · have h := E.marking.avoids (⟨1, by omega⟩ : Fin L) (⟨0, by omega⟩ : Fin L)
      (Or.inl one_ne_zero)
    simp only [E.law.nsmul_one_apply, E.law.nsmul_zero, E.law.mul_one] at h
    exact (field_avoids_iff E.originLaw _ _).mp h
  · have h := E.marking.avoids (⟨0, by omega⟩ : Fin L) (⟨1, by omega⟩ : Fin L)
      (Or.inr one_ne_zero)
    simp only [E.law.nsmul_one_apply, E.law.nsmul_zero, E.law.one_mul] at h
    exact (field_avoids_iff E.originLaw _ _).mp h

include hL in
theorem tateResidues_nonzero (hn : 0 < L) (C E : TateLevel k L) :
    let v := tateResidues k L hn C E
    (v.1.1.val ≠ 0 ∨ v.1.2.val ≠ 0) ∧ (v.2.1.val ≠ 0 ∨ v.2.2.val ≠ 0) := by
  letI : NeZero L := ⟨hn.ne'⟩
  have h := tateResidues_sections k L hn C E
  constructor
  · by_contra! hz
    apply (tateMarking_nonzero k L hL E).1
    apply Subtype.ext
    rw [h.1]
    simp only [coordinatePoint, hz.1, hz.2, C.law.nsmul_zero, C.law.one_mul]
    rw [C.originLaw.1, E.originLaw.1]
  · by_contra! hz
    apply (tateMarking_nonzero k L hL E).2
    apply Subtype.ext
    rw [h.2]
    simp only [coordinatePoint, hz.1, hz.2, C.law.nsmul_zero, C.law.one_mul]
    rw [C.originLaw.1, E.originLaw.1]

include hL in
/-- A canonical Tate basis supplies literal coordinates for every actual
full marking, via the proved geometric torsion basis and faithful scalar extension. -/
theorem tateResidues_coordinates (hn : 0 < L) (C E : TateLevel k L)
    (ζ : k) (hC : CanonicalMarking k L ζ C) :
    letI : NeZero L := ⟨hn.ne'⟩
    let v := tateResidues k L hn C E
    HasCoordinates (LaurentSeries k) (TateCurve k L) E.marking.x.val
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX L v.1.2.val (ζ ^ v.1.1.val)))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY L v.1.2.val (ζ ^ v.1.1.val))) ∧
    HasCoordinates (LaurentSeries k) (TateCurve k L) E.marking.y.val
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX L v.2.2.val (ζ ^ v.2.1.val)))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY L v.2.2.val (ζ ^ v.2.1.val))) := by
  letI : NeZero L := ⟨hn.ne'⟩
  have hs := tateResidues_sections k L hn C E
  have hnz := tateResidues_nonzero k L hL hn C E
  constructor
  · rw [hs.1]
    exact hC _ _ hnz.1
  · rw [hs.2]
    exact hC _ _ hnz.2

#print axioms fullLevelResidues_sections
#print axioms tateResidues_sections
#print axioms tateResidues_nonzero
#print axioms tateResidues_coordinates
end CanonicalCoordinates


section ResidueTranslation
open NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177

theorem primitive_unit_residue_sub_mul {n : ℕ} (hn : 0 < n)
    (ζ : kˣ) (hζ : IsPrimitiveRoot ζ n) (a s b : ZMod n) :
    ζ ^ (a - s*b).val = ζ ^ a.val * ((ζ ^ s.val) ^ b.val)⁻¹ := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hd : (n : ℤ) ∣ ((a - s*b).val : ℤ) -
      ((a.val : ℤ) - (s.val : ℤ) * (b.val : ℤ)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
  have h := (hζ.zpow_eq_one_iff_dvd _).mpr hd
  rw [zpow_sub, mul_inv_eq_one] at h
  simpa only [zpow_sub, zpow_mul, zpow_natCast] using h

theorem primitive_residue_sub_mul (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (a s b : ZMod L) :
    ζ ^ (a - s*b).val = ζ ^ a.val * ((ζ ^ s.val) ^ b.val)⁻¹ := by
  let z := (hζ.isUnit hn.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hn.ne').unit_spec
  have h := congrArg (fun u : kˣ => (u : k))
    (primitive_unit_residue_sub_mul k hn z (hζ.isUnit_unit hn.ne') a s b)
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hz] using h

include hL heven in
/-- The finite unipotent action is realized by one actual parameter rotation
on both marking sections. The two matrices may have any determinant here. -/
theorem tateCenter_of_residue_translation (C E F : TateLevel k L)
    (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hC : CanonicalMarking k L ζ C) (s : ZMod L)
    (hEF : tateResidues k L (by omega) C F =
      (((tateResidues k L (by omega) C E).1.1 -
          s * (tateResidues k L (by omega) C E).1.2,
        (tateResidues k L (by omega) C E).1.2),
       ((tateResidues k L (by omega) C E).2.1 -
          s * (tateResidues k L (by omega) C E).2.2,
        (tateResidues k L (by omega) C E).2.2))) :
    tateCenter k L D X hL heven E = tateCenter k L D X hL heven F := by
  let hn : 0 < L := by omega
  letI : NeZero L := ⟨hn.ne'⟩
  let z := (hζ.isUnit hn.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hn.ne').unit_spec
  let α : kˣ := z ^ s.val
  have hα : (α : k)^L = 1 := by
    change (z ^ s.val : kˣ).val ^ L = 1
    rw [Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm, pow_mul, hz, hζ.pow_eq_one, one_pow]
  let v := tateResidues k L hn C E
  have hE := tateResidues_coordinates k L hL hn C E ζ hC
  have hF := tateResidues_coordinates k L hL hn C F ζ hC
  dsimp only at hE hF
  rw [hEF] at hF
  dsimp only at hF
  have hx : ζ ^ (v.1.1 - s*v.1.2).val =
      ζ ^ v.1.1.val * ((α : k)^v.1.2.val)⁻¹ := by
    simpa only [α, Units.val_pow_eq_pow_val, hz] using
      primitive_residue_sub_mul k L hn ζ hζ v.1.1 s v.1.2
  have hy : ζ ^ (v.2.1 - s*v.2.2).val =
      ζ ^ v.2.1.val * ((α : k)^v.2.2.val)⁻¹ := by
    simpa only [α, Units.val_pow_eq_pow_val, hz] using
      primitive_residue_sub_mul k L hn ζ hζ v.2.1 s v.2.2
  have hFx := hF.1
  have hFy := hF.2
  change HasCoordinates _ _ _ _ _ at hFx hFy
  change ζ ^ ((tateResidues k L hn C E).1.1 - s*(tateResidues k L hn C E).1.2).val = _ at hx
  change ζ ^ ((tateResidues k L hn C E).2.1 - s*(tateResidues k L hn C E).2.2).val = _ at hy
  rw [hx] at hFx
  rw [hy] at hFy
  exact tateCenter_eq_of_rotated_coordinates k L D X hL heven α hn hα E F
    ⟨v.1.2.val, ZMod.val_lt _⟩ ⟨v.2.2.val, ZMod.val_lt _⟩
    (ζ ^ v.1.1.val) (ζ ^ v.2.1.val) hE.1 hE.2 hFx hFy

#print axioms primitive_residue_sub_mul
#print axioms tateCenter_of_residue_translation
end ResidueTranslation


section ParameterFreeness
open ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality
open ArithmeticThetaRelativeDiscriminantR0171

include hL heven in
/-- The accepted order-one moduli-function ratio detects every parameter
rotation. This is a statement about the actual classifying morphism. -/
theorem classifying_parameter_injective (E : TateLevel k L)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (α β : kˣ) (hab : rotatePuncture k α ≫ b = rotatePuncture k β ≫ b) : α = β := by
  obtain ⟨r, s, hrs⟩ := CompletedLocalParameter.candidate_open_ratio k L hL heven D E b hb
  let φ := (Spec.preimage b).hom
  have hm : (laurentRescale k α).toRingHom.comp φ =
      (laurentRescale k β).toRingHom.comp φ := by
    have hcat : CommRingCat.ofHom ((laurentRescale k α).toRingHom.comp φ) =
        CommRingCat.ofHom ((laurentRescale k β).toRingHom.comp φ) := by
      apply Spec.map_injective
      simp only [CommRingCat.ofHom_comp, Spec.map_comp]
      change rotatePuncture k α ≫ Spec.map (Spec.preimage b) =
        rotatePuncture k β ≫ Spec.map (Spec.preimage b)
      simpa only [Spec.map_preimage] using hab
    exact congrArg CommRingCat.Hom.hom hcat
  have hf : laurentRescale k α
      (algebraMap (PowerSeries k) (LaurentSeries k) (CompletedLocalParameter.parameterCandidate k L)) =
      laurentRescale k β
      (algebraMap (PowerSeries k) (LaurentSeries k) (CompletedLocalParameter.parameterCandidate k L)) := by
    rw [← hrs, map_div₀, map_div₀]
    exact congrArg₂ (fun a b : LaurentSeries k => a / b)
      (RingHom.congr_fun hm r) (RingHom.congr_fun hm s)
  rw [laurentRescale_powerSeries, laurentRescale_powerSeries] at hf
  have hf' := (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)) hf
  have hc := congrArg (PowerSeries.coeff 1) hf'
  change PowerSeries.coeff 1 (PowerSeries.rescale (α : k) _) =
    PowerSeries.coeff 1 (PowerSeries.rescale (β : k) _) at hc
  simp only [PowerSeries.coeff_rescale, pow_one] at hc
  have hn := (PowerSeries.order_eq_nat.mp
    (CompletedLocalParameter.parameterCandidate_order k L hL heven)).1
  exact Units.ext (mul_right_cancel₀ hn hc)

theorem tateClassifying_rotated (α : kˣ) (hpos : 0 < L) (hα : (α : k)^L = 1)
    (E : TateLevel k L) :
    tateClassifying k L D hL heven (rotatedTate k L heven α hpos hα E) =
      rotatePuncture k α ≫ tateClassifying k L D hL heven E := by
  exact ((TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D
    (rotatedTate k L heven α hpos hα E)).choose_spec.2 _
      (classifies_rotatedTate k L D heven α hpos hα E _
        (tateClassifying_spec k L D hL heven E))).symm

theorem tateClassifying_negative (E : TateLevel k L) :
    tateClassifying k L D hL heven (negativeTate k L (by omega) E) =
      tateClassifying k L D hL heven E := by
  obtain ⟨f, hf⟩ := tateClassifying_spec k L D hL heven E
  exact ((TateLevelClassifyingParameter.classifying_exists_unique k L hL heven D
    (negativeTate k L (by omega) E)).choose_spec.2 _
      ⟨_, classifies_negative k L D (TateCurve k L) E.law (by omega) E.originLaw
        E.marking _ f hf⟩).symm

#print axioms classifying_parameter_injective
#print axioms tateClassifying_rotated
#print axioms tateClassifying_negative
end ParameterFreeness


section SignedRotationOrbits

def rotationRoot (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (s : ZMod L) : kˣ :=
  (hζ.isUnit hn.ne').unit ^ s.val

theorem rotationRoot_pow (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (s : ZMod L) :
    (rotationRoot k L hn ζ hζ s : k)^L = 1 := by
  simp only [rotationRoot, Units.val_pow_eq_pow_val, (hζ.isUnit hn.ne').unit_spec]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem rotationRoot_injective (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L) :
    Function.Injective (rotationRoot k L hn ζ hζ) := by
  letI : NeZero L := ⟨hn.ne'⟩
  intro s t h
  have hp := congrArg (fun z : kˣ => (z : k)) h
  simp only [rotationRoot, Units.val_pow_eq_pow_val, (hζ.isUnit hn.ne').unit_spec] at hp
  exact ZMod.val_injective L (hζ.pow_inj (ZMod.val_lt s) (ZMod.val_lt t) hp)

/-- The signed root-of-unity rotations are actual full Tate markings. -/
def signedRotation (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (E : TateLevel k L) (s : Bool × ZMod L) : TateLevel k L :=
  let R := rotatedTate k L heven (rotationRoot k L hn ζ hζ s.2) hn
    (rotationRoot_pow k L hn ζ hζ s.2) E
  if s.1 then negativeTate k L hn R else R

theorem signedRotation_classifying (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (E : TateLevel k L) (s : Bool × ZMod L) :
    tateClassifying k L D hL heven (signedRotation k L heven hn ζ hζ E s) =
      rotatePuncture k (rotationRoot k L hn ζ hζ s.2) ≫
        tateClassifying k L D hL heven E := by
  rcases s with ⟨b,s⟩
  cases b
  · exact tateClassifying_rotated k L D hL heven _ hn _ E
  · exact (tateClassifying_negative k L D hL heven _).trans
      (tateClassifying_rotated k L D hL heven _ hn _ E)

theorem signedRotation_center (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (E : TateLevel k L) (s : Bool × ZMod L) :
    tateCenter k L D X hL heven (signedRotation k L heven hn ζ hζ E s) =
      tateCenter k L D X hL heven E := by
  rcases s with ⟨b,s⟩
  cases b
  · exact tateCenter_rotatedTate k L D X hL heven _ hn _ E
  · exact (tateCenter_negative k L D X hL heven _).trans
      (tateCenter_rotatedTate k L D X hL heven _ hn _ E)

include D hL heven in
/-- Every actual full Tate marking has 2L distinct signed rotations.
Parameter freeness uses an actual order-one moduli function, and sign freeness
uses the actual full-level avoidance condition. -/
theorem signedRotation_injective (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (E : TateLevel k L) :
    Function.Injective (signedRotation k L heven hn ζ hζ E) := by
  rintro ⟨b,s⟩ ⟨c,t⟩ h
  have hm := congrArg (tateClassifying k L D hL heven) h
  rw [signedRotation_classifying, signedRotation_classifying] at hm
  have hr := classifying_parameter_injective k L D hL heven E
    (tateClassifying k L D hL heven E) (tateClassifying_spec k L D hL heven E) _ _ hm
  have hst := rotationRoot_injective k L hn ζ hζ hr
  change s = t at hst
  subst t
  cases b <;> cases c
  · rfl
  · exact False.elim (negativeTate_ne_self k L hL _ h.symm)
  · exact False.elim (negativeTate_ne_self k L hL _ h)
  · rfl

def cuspOrbitMarking [IsAlgClosed k] (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (p : Cusps k L D X x × (Bool × ZMod L)) : TateLevel k L :=
  signedRotation k L heven (by omega) ζ hζ (cuspTateMarking k L D X x hL heven p.1) p.2

theorem cuspOrbitMarking_center [IsAlgClosed k] (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (p : Cusps k L D X x × (Bool × ZMod L)) :
    (tateCenter k L D X hL heven (cuspOrbitMarking k L D X x hL heven ζ hζ p)).val =
      inclusion k L D X x p.1.val := by
  rw [cuspOrbitMarking, signedRotation_center, cuspTateMarking_center]

theorem cuspOrbitMarking_injective [IsAlgClosed k] (ζ : k) (hζ : IsPrimitiveRoot ζ L) :
    Function.Injective (cuspOrbitMarking k L D X x hL heven ζ hζ) := by
  rintro ⟨c,s⟩ ⟨d,t⟩ h
  have hc : c = d := by
    apply Subtype.ext
    apply (inclusion k L D X x).isOpenEmbedding.injective
    rw [← cuspOrbitMarking_center k L D X x hL heven ζ hζ (c,s),
      ← cuspOrbitMarking_center k L D X x hL heven ζ hζ (d,t), h]
  subst d
  have hs : s = t := signedRotation_injective k L D hL heven (by omega) ζ hζ
    (cuspTateMarking k L D X x hL heven c) h
  subst t
  rfl

include hL heven in
/-- The 2L signed rotations over distinct actual component cusps occupy
disjoint subsets of the same fixed-pairing SL₂ marking set. -/
theorem cusp_orbits_sl2_embedding [IsAlgClosed k] :
    Nonempty ((Cusps k L D X x × (Bool × ZMod L)) ↪
      Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  classical
  obtain ⟨ζ, hζ, hp⟩ := component_pairing_constant k L D X x (by omega)
  let F := cuspOrbitMarking k L D X x hL heven ζ hζ
  have hF (p : Cusps k L D X x × (Bool × ZMod L)) :
      algebraMap k (AlgebraicClosure (LaurentSeries k)) ζ = (tatePairing k L (F p) : _) := by
    apply hp (F p) (tateClassifying k L D hL heven (F p))
      (tateClassifying_spec k L D hL heven (F p))
      (tateDisk k L D X hL heven (F p)) (tateDisk_spec k L D X hL heven (F p))
    change (tateCenter k L D X hL heven (F p)).val ∈ _
    rw [cuspOrbitMarking_center]
    exact p.1.val.property
  let c₀ : Cusps k L D X x := Classical.choice (cusps_nonempty k L D X x)
  letI : NeZero L := ⟨by omega⟩
  let p₀ : Cusps k L D X x × (Bool × ZMod L) := (c₀, (false, 0))
  let E₀ := F p₀
  let f : (Cusps k L D X x × (Bool × ZMod L)) ↪
      {E : TateLevel k L // tatePairing k L E = tatePairing k L E₀} :=
    { toFun p := ⟨F p, Units.ext ((hF p).symm.trans (hF p₀))⟩
      inj' p q h := cuspOrbitMarking_injective k L D X x hL heven ζ hζ
        (congrArg Subtype.val h) }
  exact ⟨f.trans (tateFixedPairingMatrixEmbedding k L (by omega) E₀)⟩

#print axioms signedRotation_injective
#print axioms cuspOrbitMarking_injective
#print axioms cusp_orbits_sl2_embedding
end SignedRotationOrbits


section FinalCount
open ArithmeticThetaMarkingCuspsR0102 ArithmeticThetaIntegralCuspsR0102

include hL in
/-- The accepted arithmetic projection has exactly 2L points in every fiber;
the accepted rational cusp classification identifies its target with signed
primitive pairs. This count is used only after the geometric orbit injection. -/
theorem finite_marking_signed_card :
    2 * L * Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair L) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  classical
  letI : NeZero L := ⟨by omega⟩
  obtain ⟨e, he, hfin, hcount⟩ := rational_cusp_classification L hL
  letI := hfin
  letI := Fintype.ofFinite (RationalCusps L)
  obtain ⟨π, hπ, _⟩ := finite_marking_cusp_projection L hL
  have hf (c : RationalCusps L) : Nat.card {B : FiniteMarking L // π B = c} = 2 * L := by
    induction c using Quot.inductionOn with
    | h q =>
      obtain ⟨f, hf⟩ := hπ.2 (boundaryMarking q)
      have h := Nat.card_congr f
      have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
      rw [Nat.card_prod, hb, Nat.card_zmod] at h
      simpa only [boundary_boundaryMarking, cusp] using h.symm
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv π)
  rw [Nat.card_sigma] at h
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [← Nat.card_congr e]
  simpa only [Nat.card_eq_fintype_card, mul_comm] using h

include hL heven in
theorem geometric_cusp_card_bound [IsAlgClosed k] :
    2 * L * Nat.card (Cusps k L D X x) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  letI : NeZero L := ⟨by omega⟩
  obtain ⟨e⟩ := cusp_orbits_sl2_embedding k L D X x hL heven
  have h := Nat.card_le_card_of_injective e e.injective
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, Nat.card_prod, hb, Nat.card_zmod] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

include hL heven in
/-- A finite embedding follows from the geometric orbit bound and the exact
arithmetic fiber count; no geometric cusp injection is assumed. -/
theorem geometric_cusp_signed_embedding [IsAlgClosed k] :
    Nonempty ((Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) := by
  classical
  letI : NeZero L := ⟨by omega⟩
  letI := cusps_finite k L D X x
  letI := Fintype.ofFinite (Cusps k L D X x)
  letI : Finite (ArithmeticThetaLevelCount.PrimitivePair L) :=
    inferInstanceAs (Finite {v : ZMod L × ZMod L // IsCoprime v.1 v.2})
  letI : Finite (ArithmeticThetaLevelCount.SignedPrimitivePair L) :=
    inferInstanceAs (Finite (Quot (fun a b : ArithmeticThetaLevelCount.PrimitivePair L =>
      b.val = -a.val)))
  letI := Fintype.ofFinite (ArithmeticThetaLevelCount.SignedPrimitivePair L)
  have h := geometric_cusp_card_bound k L D X x hL heven
  rw [← finite_marking_signed_card L hL] at h
  have hc : Nat.card (Cusps k L D X x) ≤ Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair L) :=
    Nat.le_of_mul_le_mul_left h (by omega)
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Nat.card_eq_fintype_card] using hc

#print axioms finite_marking_signed_card
#print axioms geometric_cusp_card_bound
#print axioms geometric_cusp_signed_embedding
end FinalCount

end GeometricComponentCuspBoundR0184

/-- The actual component cusp bound at every even level at least three. -/
theorem geometric_component_cusp_bound :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty ((ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) ∧ 2 * L * Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  intro k _ _ _ L hL heven D X x
  exact ⟨GeometricComponentCuspBoundR0184.cusps_finite k L D X x,
    GeometricComponentCuspBoundR0184.cusps_nonempty k L D X x,
    GeometricComponentCuspBoundR0184.geometric_cusp_signed_embedding k L D X x hL heven,
    GeometricComponentCuspBoundR0184.geometric_cusp_card_bound k L D X x hL heven⟩

#print axioms geometric_component_cusp_bound
end ArithmeticThetaComponentDegreeR0184
