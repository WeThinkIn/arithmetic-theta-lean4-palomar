module

public import GeometricComponentCuspBoundR0184
public import GeometricCanonicalHodgeDescentR0235
public import FinitePullbackSectionDegree

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace ArithmeticThetaCyclotomicModularityR0239
namespace SplitCuspDegree
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaComponentDegreeR0184.GeometricComponentCuspBoundR0184
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaCurveDegree

/-- A rational section induces an isomorphism for its actual structural residue map. -/
lemma residue_bijective_of_section (k : Type) [Field k] {Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of k))
    (s : Spec (CommRingCat.of k) ⟶ Y) (hs : s ≫ f = 𝟙 _) :
    Function.Bijective (baseToResidue k f (s (IsLocalRing.closedPoint k))) := by
  let e := Scheme.SpecToEquivOfField k Y s
  have he : Spec.map e.2 ≫ Y.fromSpecResidueField e.1 = s :=
    (Scheme.SpecToEquivOfField k Y).symm_apply_apply s
  have hcomp : e.2.hom.comp (baseToResidue k f e.1) = RingHom.id k := by
    change (CommRingCat.ofHom (baseToResidue k f e.1) ≫ e.2).hom = CommRingCat.Hom.hom (𝟙 (CommRingCat.of k))
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    rw [Spec.map_comp, specMap_baseToResidue,
      ← Category.assoc, he, hs, Spec.map_id]
  refine ⟨(baseToResidue k f e.1).injective, ?_⟩
  intro z
  refine ⟨e.2 z, e.2.hom.injective ?_⟩
  exact RingHom.congr_fun hcomp (e.2 z)

variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)

/-- Rational tests are supplied by the accepted coefficient-descent theorem. -/
lemma cusp_test (hL : 3 ≤ L) (heven : Even L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (c : Cusps k L D X x) :
    ∃ T : DiskTest k L D X, T.disk (closedPoint k) = inclusion k L D X x c.val := by
  obtain ⟨A, _⟩ := tate_full_level_marking k L hL heven ζ hζ
  exact ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent.tests_cover_of_tateLevel
    k L hL heven A D X _ c.property

/-- A split Tate center is rational on the actual component, over its actual projection. -/
lemma cusp_residue (hL : 3 ≤ L) (heven : Even L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (c : Cusps k L D X x) :
    Function.Bijective (baseToResidue k (projection k L D X x) c.val) := by
  obtain ⟨T, hT⟩ := cusp_test k L D X x hL heven ζ hζ c
  have hc : T.disk (closedPoint k) ∈ componentOpen k L D X x := by
    rw [hT]
    exact c.val.property
  let d := componentDisk k L D X x T.disk hc
  let z : Spec (CommRingCat.of k) ⟶ Disk k :=
    Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have hz : z (IsLocalRing.closedPoint k) = closedPoint k := by
    letI : IsLocalHom (PowerSeries.constantCoeff (R := k)) :=
      ⟨fun a ha => (PowerSeries.isUnit_iff_constantCoeff).mpr ha⟩
    exact IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := k))
  have hd : d (closedPoint k) = c.val := by
    apply (inclusion k L D X x).isOpenEmbedding.injective
    have h := congrArg (fun f : Disk k ⟶ X.space => f (closedPoint k))
      (componentDisk_inclusion k L D X x T.disk hc)
    exact h.trans hT
  have hs : (z ≫ d) ≫ projection k L D X x = 𝟙 _ := by
    change (z ≫ d) ≫ inclusion k L D X x ≫ X.projection = _
    rw [Category.assoc z, ← Category.assoc d, componentDisk_inclusion, T.extends_eq.1]
    change Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))) = _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of k) using 1
    congr 1
  have h := residue_bijective_of_section k (projection k L D X x) (z ≫ d) hs
  have hp : (z ≫ d) (IsLocalRing.closedPoint k) = c.val := by
    change d (z (IsLocalRing.closedPoint k)) = _
    rw [hz, hd]
  rw [hp] at h
  exact h

/-- The finite-dimensional structure and dimension use the structural residue algebra. -/
lemma placeDegree_one (hL : 3 ≤ L) (heven : Even L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (c : Cusps k L D X x) :
    placeDegree k (projection k L D X x) c.val = 1 := by
  letI : Algebra k ((Component k L D X x).residueField c.val) :=
    (baseToResidue k (projection k L D X x) c.val).toAlgebra
  let e := AlgEquiv.ofBijective (Algebra.ofId k ((Component k L D X x).residueField c.val))
    (cusp_residue k L D X x hL heven ζ hζ c)
  letI : FiniteDimensional k ((Component k L D X x).residueField c.val) :=
    Module.Finite.equiv e.toLinearEquiv
  exact e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self k)

/-- The chosen actual marking retains its prescribed cusp center. -/
def cuspMarking (hL : 3 ≤ L) (heven : Even L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (c : Cusps k L D X x) : TateLevel k L :=
  (cusp_test k L D X x hL heven ζ hζ c).choose.level

lemma cuspMarking_center (hL : 3 ≤ L) (heven : Even L) (ζ : k)
    (hζ : IsPrimitiveRoot ζ L) (c : Cusps k L D X x) :
    (tateCenter k L D X hL heven (cuspMarking k L D X x hL heven ζ hζ c)).val =
      inclusion k L D X x c.val := by
  let T := (cusp_test k L D X x hL heven ζ hζ c).choose
  exact (tateCenter_eq_of_extends k L D X hL heven T.level T.base T.disk
    ⟨T.map, T.classifies⟩ T.extends_eq).trans
      (cusp_test k L D X x hL heven ζ hζ c).choose_spec

omit [CharZero k] in
/-- Splitting of roots of unity follows from the specified primitive root. -/
lemma primitive_descends {K : Type} [Field K] [Algebra k K]
    (hn : 0 < L) (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (z : K) (hz : IsPrimitiveRoot z L) :
    ∃ ξ : k, IsPrimitiveRoot ξ L ∧ algebraMap k K ξ = z := by
  letI : NeZero L := ⟨hn.ne'⟩
  obtain ⟨i, _, hi⟩ := (hζ.map_of_injective (algebraMap k K).injective).eq_pow_of_pow_eq_one hz.pow_eq_one
  refine ⟨ζ ^ i, ?_, ?_⟩
  · have hp : IsPrimitiveRoot (algebraMap k K (ζ ^ i)) L := by
      simpa only [map_pow, hi] using hz
    exact hp.of_map_of_injective (algebraMap k K).injective
  · simpa only [map_pow] using hi

open NeronModelInfra ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaFullLevelCoverR0175
theorem split_pairing_constant (hn : 0 < L) (root : k) (hroot : IsPrimitiveRoot root L) :
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
  obtain ⟨ζ, hζ⟩ := primitive_descends k L hn root hroot
    (fullLevelPairing P.equation P.law P.originLaw L M : A)
    ((fullLevelPairing_primitive P.equation P.law P.originLaw L hn M).map_of_injective
      (f := Units.coeHom A) Units.val_injective)
  change IsPrimitiveRoot ζ L ∧ algebraMap k A ζ = (fieldPresentationPairing k L D P : A) at hζ
  refine ⟨ζ, hζ.1, ?_⟩
  intro E b hb d hd hc
  obtain ⟨σ, hσk, hσb⟩ := componentDisk_geometric_embedding k L D X x E b hb d hd hc
  let C := AlgebraicClosure (LaurentSeries k)
  have hscalar : σ.comp (algebraMap k A) = algebraMap k C :=
    hσk.trans (IsScalarTower.algebraMap_eq k (LaurentSeries k) C).symm
  exact tatePairing_of_common_presentation k L D P hn ζ hζ.2 E b hb σ hscalar hσb

variable (hL : 3 ≤ L) (heven : Even L)
def splitOrbitMarking (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (p : Cusps k L D X x × (Bool × ZMod L)) : TateLevel k L :=
  signedRotation k L heven (by omega) ζ hζ (cuspMarking k L D X x hL heven ζ hζ p.1) p.2

theorem splitOrbitMarking_center (ζ : k) (hζ : IsPrimitiveRoot ζ L)
    (p : Cusps k L D X x × (Bool × ZMod L)) :
    (tateCenter k L D X hL heven (splitOrbitMarking k L D X x hL heven ζ hζ p)).val =
      inclusion k L D X x p.1.val := by
  rw [splitOrbitMarking, signedRotation_center, cuspMarking_center]

theorem splitOrbitMarking_injective (ζ : k) (hζ : IsPrimitiveRoot ζ L) :
    Function.Injective (splitOrbitMarking k L D X x hL heven ζ hζ) := by
  rintro ⟨c,s⟩ ⟨d,t⟩ h
  have hc : c = d := by
    apply Subtype.ext
    apply (inclusion k L D X x).isOpenEmbedding.injective
    rw [← splitOrbitMarking_center k L D X x hL heven ζ hζ (c,s),
      ← splitOrbitMarking_center k L D X x hL heven ζ hζ (d,t), h]
  subst d
  have hs : s = t := signedRotation_injective k L D hL heven (by omega) ζ hζ
    (cuspMarking k L D X x hL heven ζ hζ c) h
  subst t
  rfl

include hL heven in
/-- The 2L signed rotations over distinct actual component cusps occupy
disjoint subsets of the same fixed-pairing SL₂ marking set. -/
theorem split_orbits_sl2_embedding (root : k) (hroot : IsPrimitiveRoot root L) :
    Nonempty ((Cusps k L D X x × (Bool × ZMod L)) ↪
      Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  classical
  obtain ⟨ζ, hζ, hp⟩ := split_pairing_constant k L D X x (by omega) root hroot
  let F := splitOrbitMarking k L D X x hL heven ζ hζ
  have hF (p : Cusps k L D X x × (Bool × ZMod L)) :
      algebraMap k (AlgebraicClosure (LaurentSeries k)) ζ = (tatePairing k L (F p) : _) := by
    apply hp (F p) (tateClassifying k L D hL heven (F p))
      (tateClassifying_spec k L D hL heven (F p))
      (tateDisk k L D X hL heven (F p)) (tateDisk_spec k L D X hL heven (F p))
    change (tateCenter k L D X hL heven (F p)).val ∈ _
    rw [splitOrbitMarking_center]
    exact p.1.val.property
  let c₀ : Cusps k L D X x := Classical.choice (cusps_nonempty k L D X x)
  letI : NeZero L := ⟨by omega⟩
  let p₀ : Cusps k L D X x × (Bool × ZMod L) := (c₀, (false, 0))
  let E₀ := F p₀
  let f : (Cusps k L D X x × (Bool × ZMod L)) ↪
      {E : TateLevel k L // tatePairing k L E = tatePairing k L E₀} :=
    { toFun p := ⟨F p, Units.ext ((hF p).symm.trans (hF p₀))⟩
      inj' p q h := splitOrbitMarking_injective k L D X x hL heven ζ hζ
        (congrArg Subtype.val h) }
  exact ⟨f.trans (tateFixedPairingMatrixEmbedding k L (by omega) E₀)⟩

end SplitCuspDegree
open ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaComponentDegreeR0184.GeometricComponentCuspBoundR0184

/-- Every actual cusp has bijective structural residue map and residue degree one. -/
theorem split_cusp_residue :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k), IsPrimitiveRoot ζ L → 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ y : ArithmeticThetaComponentDegreeR0184.Cusps k L D X x, Function.Bijective (ArithmeticThetaCurveDegree.baseToResidue k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) y.val) ∧ ArithmeticThetaCurveDegree.placeDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) y.val = 1 := by
  intro k _ _ L ζ hζ hL heven D X x y
  exact ⟨SplitCuspDegree.cusp_residue k L D X x hL heven ζ hζ y,
    SplitCuspDegree.placeDegree_one k L D X x hL heven ζ hζ y⟩

/-- Count actual cusps through the disjoint 2L signed rotations in one pairing fiber. -/
theorem split_component_cusp_bound :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k), IsPrimitiveRoot ζ L → 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ 2 * L * Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  intro k _ _ L ζ hζ hL heven D X x
  refine ⟨cusps_finite k L D X x, cusps_nonempty k L D X x, ?_⟩
  letI : NeZero L := ⟨by omega⟩
  obtain ⟨e⟩ := SplitCuspDegree.split_orbits_sl2_embedding k L D X x hL heven ζ hζ
  have h := Nat.card_le_card_of_injective e e.injective
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, Nat.card_prod, hb, Nat.card_zmod] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

#print axioms split_cusp_residue
#print axioms split_component_cusp_bound
end ArithmeticThetaCyclotomicModularityR0239
