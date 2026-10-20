module

import all GenericThetaBasisR0140

public import GeometricThetaLiftsDefinitionsR0141

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Scalar-lift geometry and uniqueness for the actual generic ideal power.
All implementation declarations belong to this module's namespace. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open GenericThetaBasisR0140
open Scheme.Modules

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

local instance genericDualAdd (s : baseScheme k ⟶ M.X) (d : ℕ) :
    AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

@[reassoc (attr := simp)]
lemma genericMap_inclusion (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) :
    genericMap k M f hf ≫ genericInclusion k M = genericInclusion k M ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma genericMap_structure (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) :
    genericMap k M f hf ≫ genericStructure k M = genericStructure k M :=
  pullback.lift_snd _ _ _

lemma genericMap_id : genericMap k M (𝟙 M.X) (Category.id_comp _) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp [genericMap, genericInclusion, genericStructure, Category.id_comp] <;>
    exact Category.id_comp _

lemma genericMap_comp (f g : M.X ⟶ M.X)
    (hf : f ≫ M.p = M.p) (hg : g ≫ M.p = M.p) :
    genericMap k M (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      genericMap k M f hf ≫ genericMap k M g hg := by
  apply pullback.hom_ext <;>
    simp [genericMap, genericInclusion, genericStructure, Category.assoc]

lemma inverse_over (e : M.X ≅ M.X) (he : e.hom ≫ M.p = M.p) :
    e.inv ≫ M.p = M.p := by
  calc
    e.inv ≫ M.p = e.inv ≫ (e.hom ≫ M.p) := congrArg (e.inv ≫ ·) he.symm
    _ = M.p := e.inv_hom_id_assoc _

/-- Base change of the specified model automorphism, with its original map. -/
def genericIso (e : M.X ≅ M.X) (he : e.hom ≫ M.p = M.p) :
    genericScheme k M ≅ genericScheme k M where
  hom := genericMap k M e.hom he
  inv := genericMap k M e.inv (inverse_over k M e he)
  hom_inv_id := by
    rw [← genericMap_comp]
    simpa only [e.hom_inv_id] using genericMap_id k M
  inv_hom_id := by
    rw [← genericMap_comp]
    simpa only [e.inv_hom_id] using genericMap_id k M

variable (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
variable (ha : Actions k M rot scal inv)

def scalarIso (ζ : kˣ) : genericScheme k M ≅ genericScheme k M :=
  genericIso k M (scal ζ) (modelOver k M id ζ false (scal ζ) (ha.2.1 ζ))

lemma scalarIso_hom (ζ : kˣ) :
    (scalarIso k M rot scal inv ha ζ).hom = scalarMap k M rot scal inv ha ζ := rfl

lemma scalarMap_isIso (ζ : kˣ) : IsIso (scalarMap k M rot scal inv ha ζ) :=
  inferInstanceAs (IsIso (scalarIso k M rot scal inv ha ζ).hom)

lemma scalarMap_over (ζ : kˣ) :
    scalarMap k M rot scal inv ha ζ ≫ genericStructure k M = genericStructure k M :=
  genericMap_structure k M _ _

omit rot scal inv ha in
lemma base_scalar_fixed (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M) (c : LaurentSeries k) :
    f.appTop (scalarAt k M ⊤ c) = scalarAt k M ⊤ c := by
  have h := congrArg Scheme.Hom.appTop hf
  simp only [Scheme.Hom.comp_appTop] at h
  have hh := congrArg (fun q => q
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c)) h
  dsimp only [scalarAt]
  erw [CategoryTheory.Functor.map_id]
  exact hh

omit rot scal inv ha in
lemma combines_eq (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (c : Fin m → LaurentSeries k)
    (φ : GenericDual k M s d) (hc : Combines k M s d m b c φ) :
    φ = ∑ ν : Fin m, scale (scalarAt k M ⊤ (c ν)) (b ν) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  erw [sum_app]
  change φ.app U x = ∑ ν, (scale (scalarAt k M ⊤ (c ν)) (b ν)).app U x
  rw [hc U x]
  apply Finset.sum_congr rfl
  intro ν _
  rw [GenericThetaBasisR0140.scale_app]
  congr 1
  dsimp only [scalarAt]
  erw [CategoryTheory.Functor.map_id]
  rfl

omit rot scal inv ha in
lemma act_scale (s : baseScheme k ⟶ M.X) (d : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M)
    (e : Lift k M s d f) (c : LaurentSeries k) (φ : GenericDual k M s d) :
    act k M s d f e (scale (scalarAt k M ⊤ c) φ) =
      scale (scalarAt k M ⊤ c) (act k M s d f e φ) := by
  change e.hom ≫ pulledInclusion f (scale (scalarAt k M ⊤ c) φ) = _
  rw [pull_scale, base_scalar_fixed k M f hf c, scale_precomp]
  rfl

omit rot scal inv ha in
lemma act_sum (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M) (e : Lift k M s d f)
    (φ : Fin m → GenericDual k M s d) :
    act k M s d f e (∑ ν, φ ν) = ∑ ν, act k M s d f e (φ ν) := by
  unfold act
  erw [CategoryTheory.Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]

omit rot scal inv ha in
lemma act_eq_of_basis (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M)
    (e e' : Lift k M s d f)
    (h : ∀ ν, act k M s d f e (b ν) = act k M s d f e' (b ν)) :
    ∀ φ, act k M s d f e φ = act k M s d f e' φ := by
  intro φ
  obtain ⟨c, hc, _⟩ := hb φ
  rw [combines_eq k M s d m b c φ hc, act_sum, act_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [act_scale k M s d f hf, act_scale k M s d f hf, h ν]

omit rot scal inv ha in
/-- The actual inclusion of the generic ideal power is still a monomorphism. -/
lemma generic_ideal_realization (s : baseScheme k ⟶ M.X) (d : ℕ) :
    IdealRealization ((s.ker^d).comap (genericInclusion k M))
      (genericPower k M s d)
      (restrictDual k M s d (idealInclusion (s.ker^d))) := by
  letI : IsOpenImmersion (genericInclusion k M) :=
    AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  exact pullback_open_realization (genericInclusion k M) (s.ker^d)
    (powerModule k M s d) (idealInclusion (s.ker^d)) (ideal_realization _)

omit rot scal inv ha in
/-- A lift is determined by its action on every actual dual section. The test
section is the ideal inclusion itself, so no pointwise trivialization or
assumed faithfulness of a representation is used. -/
lemma lift_ext (s : baseScheme k ⟶ M.X) (d : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M) [IsOpenImmersion f]
    (e e' : Lift k M s d f)
    (h : ∀ φ, act k M s d f e φ = act k M s d f e' φ) : e = e' := by
  let I := (s.ker^d).comap (genericInclusion k M)
  let j : GenericDual k M s d := restrictDual k M s d (idealInclusion (s.ker^d))
  have hj : IdealRealization I (genericPower k M s d) j :=
    generic_ideal_realization k M s d
  letI : Mono (pulledInclusion f j) :=
    (pullback_open_realization f I (genericPower k M s d) j hj).1
  apply Iso.ext
  apply (cancel_mono (pulledInclusion f j)).mp
  exact h j

omit rot scal inv ha in
lemma eigen_unique (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (ζ : kˣ) (f : genericScheme k M ⟶ genericScheme k M)
    [IsOpenImmersion f] (hf : f ≫ genericStructure k M = genericStructure k M)
    (e e' : Lift k M s d f) (he : Eigen k M s d m ζ f e b)
    (he' : Eigen k M s d m ζ f e' b) : e = e' := by
  apply lift_ext k M s d f e e'
  apply act_eq_of_basis k M s d m b hb f hf e e'
  intro ν
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact (he ν U x).symm.trans (he' ν U x)

/-- Uniqueness in the frozen scalar-lift obligation, independent of the
remaining construction of its inhabitant. -/
lemma scalar_lift_unique (m : ℕ) (hm : 0 < m) (he : Even m)
    {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (MM : Model k TT) (hMM : IsModel k TT MM)
    (ss : baseScheme k ⟶ MM.X)
    (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
    (rr : MM.X ≅ MM.X) (aa : kˣ → (MM.X ≅ MM.X)) (ii : MM.X ≅ MM.X)
    (hh : Actions k MM rr aa ii) (ζ : kˣ)
    (e e' : Lift k MM ss m (scalarMap k MM rr aa ii hh ζ))
    (heA : Eigen k MM ss m m ζ (scalarMap k MM rr aa ii hh ζ) e
      (genericTheta k m hm he MM hMM ss hss))
    (heA' : Eigen k MM ss m m ζ (scalarMap k MM rr aa ii hh ζ) e'
      (genericTheta k m hm he MM hMM ss hss)) : e = e' := by
  letI := scalarMap_isIso k MM rr aa ii hh ζ
  exact eigen_unique k MM ss m m (genericTheta k m hm he MM hMM ss hss)
    (generic_theta_basis k m hm he TT MM hMM ss hss) ζ _
    (scalarMap_over k MM rr aa ii hh ζ) e e' heA heA'


/-! The finite comparison below re-establishes the private reduction lemmas
from ThetaNumeratorCompatibilityR0138 in this module's namespace. The source
comparison maps and gamma units are exactly the accepted ones. -/
namespace GammaComparison
open ArithmeticThetaIndexedOverlapsR0058 ArithmeticThetaCorrectedGammaR0061

omit [CharZero k] in
private theorem node_equiv_coord (i : Fin 2) :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (MvPolynomial.X i)) = ArithmeticThetaNodeCharts.quotientMap k
        (MvPolynomial.X i) := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private theorem tail_data (r : ℕ) (hr : 0 < r) (i : Fin r) :
    IsGammaData k r i.val (gammaTail k r hr i)
      (ArithmeticThetaCorrectedGammaR0061.horizontal k r i.val * gammaTail k r hr i) := by
  have hv := Classical.choose_spec (gamma_tail_exists k r i.val hr i.isLt)
  have hvv : (gammaTail k r hr i : Hat k) =
      Classical.choose (gamma_tail_exists k r i.val hr i.isLt) := IsUnit.unit_spec _
  rw [hvv]
  refine ⟨hv.1, hv.2, ?_, rfl⟩
  intro n
  obtain ⟨N₀, hN₀⟩ := hv.2 n
  refine ⟨N₀+1, ?_⟩
  intro N hN
  rw [gamma_finite_factorization k r i.val N hr i.isLt (by omega), ← mul_sub]
  exact (ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n).mul_mem_left _
    (hN₀ N (by omega))

private def openReduction (n : ℕ) (s : Bool) : HatOpen k s →+* B k n s :=
  (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) s).toRingHom.comp
    (trunc (HatOpen k s) (completeOpen k 0 s (openParameter k s)) n)

private lemma reduction_of (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1 a

private lemma openReduction_of (n : ℕ) (s : Bool) (a : RawOpen k s) :
    openReduction k n s (completeOpen k 0 s a) = trunc _ (openParameter k s) n a :=
  RingHom.congr_fun ((Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).2.1 s) a

private lemma filtration_eq (n : ℕ) :
    ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n =
      (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})^n := by
  simp [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
    ArithmeticThetaScaledTateBridgeR0046.completedPower,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private lemma reduction_approx (n : ℕ) (z : Hat k) :
    ∃ a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k,
      z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a ∈
        ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (completedReduction k n z)
  refine ⟨(nodeEquiv k).symm a, ?_⟩
  have hh : completedReduction k n z = completedReduction k n
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k ((nodeEquiv k).symm a)) := by
    rw [reduction_of, RingEquiv.apply_symm_apply]
    exact ha.symm
  have hh' := (Classical.choose (finite_stage_completion_comparison k n)).injective hh
  rw [filtration_eq]
  exact Ideal.Quotient.eq.mp hh'

private lemma reduction_kills (n : ℕ) (z : Hat k)
    (hz : z ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1)) :
    completedReduction k n z = 0 := by
  change (Classical.choose (finite_stage_completion_comparison k n)) (trunc _ _ n z) = 0
  rw [filtration_eq] at hz
  rw [show trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]

private lemma reduction_natural (n N : ℕ) (h : n ≤ N) (z : Hat k) :
    truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h (completedReduction k N z) =
      completedReduction k n z := by
  obtain ⟨a, ha⟩ := reduction_approx k N z
  have hn : z - ArithmeticThetaAnnularTorsionPrereqR0053.complete k a ∈
      ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right h 1) ha
  have hN := reduction_kills k N _ ha
  have hn' := reduction_kills k n _ hn
  rw [map_sub, sub_eq_zero] at hN hn'
  rw [hN, hn', reduction_of, reduction_of]
  rfl

private lemma restrict_index (j : ℕ) (s : Bool) : restrict k j s = restrict k 0 s := by
  apply (completed_coordinate_restrictions k 0 s).unique
  · exact (Classical.choose_spec (completed_coordinate_restrictions k j s).exists)
  · exact (Classical.choose_spec (completed_coordinate_restrictions k 0 s).exists)

private lemma reduction_restrict (n j : ℕ) (s : Bool) (z : Hat k) :
    openReduction k n s (restrict k j s z) =
      ArithmeticThetaInfinitesimalPolygonR0129.restriction k n s (completedReduction k n z) := by
  rw [restrict_index]
  have hr : restrict k 0 s = Classical.choose (completed_coordinate_restrictions k 0 s) :=
    (completed_coordinate_restrictions k 0 s).unique
      (Classical.choose_spec (completed_coordinate_restrictions k 0 s).exists)
      (Classical.choose_spec (completed_coordinate_restrictions k 0 s)).1
  rw [hr]
  exact (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).2.2 s z

private lemma openReduction_kills (n : ℕ) (s : Bool) (z : HatOpen k s)
    (hz : z ∈ hatPower k 0 s (n+1)) : openReduction k n s z = 0 := by
  have ht : ot k 0 s = openParameter k s := by
    change algebraMap _ _ (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
    congr 1
  change (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) s) (trunc _ _ n z) = 0
  rw [show trunc _ _ n z = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [hatPower, ht] using hz), map_zero]

private lemma openReduction_approx (n : ℕ) (s : Bool) (z : HatOpen k s) :
    ∃ a : RawOpen k s, openReduction k n s z = openReduction k n s (completeOpen k 0 s a) ∧
      z - completeOpen k 0 s a ∈ hatPower k 0 s (n+1) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (openReduction k n s z)
  have hh : openReduction k n s z = openReduction k n s (completeOpen k 0 s a) := by
    rw [openReduction_of]; exact ha.symm
  refine ⟨a, hh, ?_⟩
  have hh' := (Classical.choose (Classical.choose_spec (finite_stage_completion_comparison k n)) s).injective hh
  have hm := Ideal.Quotient.eq.mp hh'
  have ht : ot k 0 s = openParameter k s := by
    change algebraMap _ _ (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k PowerSeries.X)) = _
    congr 1
  simpa only [hatPower, ht] using hm

private lemma reduction_overlap (n r j : ℕ) (hr : 0 < r) (hj : j < r)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E) (z : HatOpen k false) :
    openReduction k n true (overlap k r j hr hj z) = E (openReduction k n false z) := by
  obtain ⟨a, ha, hm⟩ := openReduction_approx k n false z
  have hspec := Classical.choose_spec (completed_indexed_adjacent k r j hr hj).exists
  have hz := openReduction_kills k n true _ (hspec.2.1 (n+1) _ hm)
  rw [map_sub, map_sub, sub_eq_zero] at hz
  let O : HatOpen k false ≃+* HatOpen k true := overlap k r j hr hj
  change openReduction k n true (O z) = openReduction k n true (O (completeOpen k 0 false a)) at hz
  change openReduction k n true (O z) = E (openReduction k n false z)
  rw [hz, ha]
  have hc := RingHom.congr_fun hspec.1 a
  change overlap k r j hr hj (completeOpen k 0 false a) = completeOpen k 0 true (rawAdjacent k a) at hc
  change O (completeOpen k 0 false a) = completeOpen k 0 true (rawAdjacent k a) at hc
  rw [hc, openReduction_of, openReduction_of]
  exact (RingHom.congr_fun hE a).symm

private lemma reduction_horizontal (n r : ℕ) (i : Fin r) :
    completedReduction k n (ArithmeticThetaCorrectedGammaR0061.horizontal k r i.val) =
      equation k r n i := by
  have hx : completedReduction k n (ArithmeticThetaCorrectedGammaR0061.cx k) = coordX k n := by
    change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
    rw [reduction_of]
    change trunc _ _ n (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0))) = _
    rw [node_equiv_coord]
    rfl
  have hy : completedReduction k n (ArithmeticThetaCorrectedGammaR0061.cy k) = coordY k n := by
    change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
    rw [reduction_of]
    change trunc _ _ n (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 1))) = _
    rw [node_equiv_coord]
    rfl
  unfold ArithmeticThetaCorrectedGammaR0061.horizontal equation
  split_ifs <;> simp only [map_mul, map_sub, map_one, hx, hy]


/-- The actual unit tail reduced at a finite infinitesimal thickness. -/
def finiteTail (r : ℕ) (hr : 0 < r) (n : ℕ) (i : Fin r) : (A k n)ˣ :=
  Units.map (completedReduction k n) (gammaTail k r hr i)

def finiteGamma (r : ℕ) (hr : 0 < r) (n : ℕ) (i : Fin r) : A k n :=
  equation k r n i * finiteTail k r hr n i

lemma finiteGamma_eq (r : ℕ) (hr : 0 < r) (n : ℕ) (i : Fin r) :
    finiteGamma k r hr n i = completedReduction k n
      (ArithmeticThetaCorrectedGammaR0061.horizontal k r i.val * gammaTail k r hr i) := by
  rw [map_mul, reduction_horizontal]
  rfl

lemma finiteTail_natural (r : ℕ) (hr : 0 < r) (n N : ℕ) (h : n ≤ N) (i : Fin r) :
    Units.map (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h)
      (finiteTail k r hr N i) = finiteTail k r hr n i := by
  apply Units.ext
  exact reduction_natural k n N h (gammaTail k r hr i)

lemma finiteGamma_interior (r : ℕ) (hr : 0 < r) (n : ℕ)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (i : Fin r) (hi : i.val+1 < r) :
    E (ArithmeticThetaInfinitesimalPolygonR0129.restriction k n false
      (finiteGamma k r hr n i)) =
    ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true
      (finiteGamma k r hr n (ArithmeticThetaInfinitesimalPolygonR0129.next r hr i)) := by
  let j := ArithmeticThetaInfinitesimalPolygonR0129.next r hr i
  have hg := gamma_interior_overlap k r i.val hr i.isLt hi _ _ _ _
    (tail_data k r hr i) (tail_data k r hr j)
  have h := congrArg (openReduction k n true) hg
  rw [reduction_overlap k n r i.val hr i.isLt E hE,
    reduction_restrict, reduction_restrict] at h
  simpa only [finiteGamma_eq] using h


private lemma reduction_cx (n : ℕ) :
    completedReduction k n (ArithmeticThetaCorrectedGammaR0061.cx k) = coordX k n := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [reduction_of]
  change trunc _ _ n (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0))) = _
  rw [node_equiv_coord]
  rfl

private lemma restrict_cx (j : ℕ) (side : Bool) :
    restrict k j side (ArithmeticThetaCorrectedGammaR0061.cx k) =
      completeOpen k j side (ox k j side) := by
  have hs := Classical.choose_spec (completed_coordinate_restrictions k j side).exists
  have h := RingHom.congr_fun hs.1 (ArithmeticThetaScaledTateBridgeR0046.x k 1)
  simpa [ArithmeticThetaCorrectedGammaR0061.restrict, ArithmeticThetaCorrectedGammaR0061.cx, ArithmeticThetaScaledAnnularR0050.cx,
    ArithmeticThetaAnnularTorsionPrereqR0053.complete, openMap,
    ArithmeticThetaScaledTateBridgeR0046.x, ArithmeticThetaNodeCharts.x,
    node_equiv_coord, ox] using h

lemma finiteGamma_boundary (r : ℕ) (hr : 0 < r) (n : ℕ)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (i : Fin r) (hi : i.val+1 = r) :
    ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true (coordX k n) *
      E (ArithmeticThetaInfinitesimalPolygonR0129.restriction k n false
        (finiteGamma k r hr n i)) =
    -ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true
      (finiteGamma k r hr n (ArithmeticThetaInfinitesimalPolygonR0129.next r hr i)) := by
  let j := ArithmeticThetaInfinitesimalPolygonR0129.next r hr i
  have hg := gamma_period_boundary k r i.val hr i.isLt hi _ _ _ _
    (tail_data k r hr i) (tail_data k r hr j)
  let X := restrict k j.val true (ArithmeticThetaCorrectedGammaR0061.cx k)
  let Y := completeOpen k j.val true
    (↑((ArithmeticThetaIndexedOverlapsR0058.xUnit k j.val)⁻¹))
  have hxy : X * Y = 1 := by
    dsimp only [X, Y]
    rw [restrict_cx, ← map_mul]
    have hu : (↑(ArithmeticThetaIndexedOverlapsR0058.xUnit k j.val) :
        Open k j.val true) = ox k j.val true := IsUnit.unit_spec _
    rw [← hu, Units.mul_inv, map_one]
  have hh := congrArg (fun z => X * z) hg
  change X * _ = X * (-Y * _) at hh
  rw [← mul_assoc, mul_neg, hxy, neg_one_mul] at hh
  have h := congrArg (openReduction k n true) hh
  rw [map_mul, map_neg, reduction_overlap k n r i.val hr i.isLt E hE,
    reduction_restrict, reduction_restrict] at h
  rw [reduction_restrict, reduction_cx] at h
  simpa only [finiteGamma_eq] using h

/-- Root-of-unity normalization in the dual-line convention. -/
def finitePhaseUnit (n : ℕ) (ζ : kˣ) : (A k n)ˣ :=
  Units.map ((base k n).comp ((trunc _ PowerSeries.X n).comp PowerSeries.C)) ζ

/-- The proposed lift sends the actual local ideal generator to this unit
 times the pulled-back ideal generator. Only the proved unit tail is inverted. -/
def localMultiplier (r : ℕ) (hr : 0 < r) (m n : ℕ) (ζ : kˣ) (i : Fin r) : (A k n)ˣ :=
  finitePhaseUnit k n ζ⁻¹ ^ (m/2) *
    (Units.map (TowerScalarTranslation.ringMap k n ζ).toMonoidHom (finiteTail k r hr n i))^m *
    (finiteTail k r hr n i)⁻¹^m

lemma localMultiplier_natural (r : ℕ) (hr : 0 < r) (m n N : ℕ) (h : n ≤ N)
    (ζ : kˣ) (i : Fin r) :
    Units.map (truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h)
      (localMultiplier k r hr m N ζ i) = localMultiplier k r hr m n ζ i := by
  let ρ := truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h
  have hp : Units.map ρ.toMonoidHom (finitePhaseUnit k N ζ⁻¹) = finitePhaseUnit k n ζ⁻¹ := by
    apply Units.ext
    rfl
  have ht : Units.map ρ.toMonoidHom (Units.map (TowerScalarTranslation.ringMap k N ζ).toMonoidHom
        (finiteTail k r hr N i)) =
      Units.map (TowerScalarTranslation.ringMap k n ζ).toMonoidHom (finiteTail k r hr n i) := by
    apply Units.ext
    change ρ (TowerScalarTranslation.ringMap k N ζ (finiteTail k r hr N i)) = _
    have hh := RingHom.congr_fun (TowerScalarTranslation.ringMap_reduce k n N h ζ)
      (finiteTail k r hr N i)
    exact hh.trans (congrArg (TowerScalarTranslation.ringMap k n ζ)
      (congrArg Units.val (finiteTail_natural k r hr n N h i)))
  have hfTail : Units.map ρ.toMonoidHom (finiteTail k r hr N i) =
      finiteTail k r hr n i := finiteTail_natural k r hr n N h i
  change Units.map ρ.toMonoidHom _ = _
  simp only [localMultiplier, map_mul, map_pow, map_inv, hp, ht, hfTail]



/-- Raising a semivariant transition to m kills its root-of-unity character. -/
lemma power_cross {R : Type*} [CommRing R] (σ : R →+* R) (a b x q : R)
    (m : ℕ) (hb : x*a = b) (hx : σ x = q*x) (hq : q^m = 1) :
    (σ a)^m*b^m = (σ b)^m*a^m := by
  rw [← hb, map_mul, hx, mul_pow, mul_pow, mul_pow, hq, one_mul]
  ring

lemma finiteGamma_cross (r : ℕ) (hr : 0 < r) (m n : ℕ)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (ζ : kˣ) (hζ : (ζ : k)^m = 1) (i : Fin r) :
    let j := ArithmeticThetaInfinitesimalPolygonR0129.next r hr i
    let L := E.toRingHom.comp (ArithmeticThetaInfinitesimalPolygonR0129.restriction k n false)
    let R := ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true
    let f := TowerScalarTranslation.ringMap k n ζ
    L (f (finiteGamma k r hr n i))^m * R (finiteGamma k r hr n j)^m =
      R (f (finiteGamma k r hr n j))^m * L (finiteGamma k r hr n i)^m := by
  let j := ArithmeticThetaInfinitesimalPolygonR0129.next r hr i
  let L := E.toRingHom.comp (ArithmeticThetaInfinitesimalPolygonR0129.restriction k n false)
  let R := ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true
  let f := TowerScalarTranslation.ringMap k n ζ
  let σ := TowerScalarTranslation.overlapMap k n ζ
  have hl (z : A k n) : σ (L z) = L (f z) :=
    RingHom.congr_fun (TowerScalarTranslation.overlap_left k n ζ E hE) z
  have hr' (z : A k n) : σ (R z) = R (f z) :=
    TowerScalarTranslation.overlap_right_apply k n ζ z
  change L (f (finiteGamma k r hr n i))^m * R (finiteGamma k r hr n j)^m = _
  rw [← hl, ← hr']
  by_cases hi : i.val+1 < r
  · have he := finiteGamma_interior k r hr n E hE i hi
    change L (finiteGamma k r hr n i) = R (finiteGamma k r hr n j) at he
    rw [he]
  · have hi' : i.val+1 = r := by have := i.isLt; omega
    apply power_cross σ _ _ (-R (coordX k n)) (R (scalar k n (ζ : k))) m
    · have hb := finiteGamma_boundary k r hr n E hE i hi'
      change R (coordX k n) * L (finiteGamma k r hr n i) =
        -R (finiteGamma k r hr n j) at hb
      rw [neg_mul, hb, neg_neg]
    · rw [map_neg, hr', TowerScalarTranslation.ringMap_x, map_mul]
      ring
    · rw [← map_pow]
      have hq : scalar k n (ζ : k)^m = 1 := by
        simp only [scalar, ← map_pow, hζ, map_one]
      rw [hq, map_one]

private lemma clear_units {R : Type*} [CommRing R] (a b A B : R) (u v : Rˣ) (m : ℕ)
    (h : A * (b * v)^m = B * (a * u)^m) :
    (A * (↑u⁻¹ : R)^m) * b^m = (B * (↑v⁻¹ : R)^m) * a^m := by
  apply (u^m * v^m).isUnit.mul_left_cancel
  change ((u : R)^m * (v : R)^m) * _ = ((u : R)^m * (v : R)^m) * _
  calc
    _ = (A * (b * v)^m) * ((u : R) * ↑u⁻¹)^m := by simp only [mul_pow]; ring
    _ = (B * (a * u)^m) * ((v : R) * ↑v⁻¹)^m := by
      simp only [Units.mul_inv, one_pow, mul_one]
      exact h
    _ = _ := by simp only [mul_pow]; ring

/-- The proposed local maps satisfy the exact ideal-power gluing equation. -/
lemma localMultiplier_cocycle (r : ℕ) (hr : 0 < r) (m n : ℕ)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)
    (ζ : kˣ) (hζ : (ζ : k)^m = 1) (i : Fin r) :
    let j := ArithmeticThetaInfinitesimalPolygonR0129.next r hr i
    let L := E.toRingHom.comp (ArithmeticThetaInfinitesimalPolygonR0129.restriction k n false)
    let R := ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true
    let f := TowerScalarTranslation.ringMap k n ζ
    L (localMultiplier k r hr m n ζ i) * L (f (equation k r n i))^m *
      R (equation k r n j)^m =
    R (localMultiplier k r hr m n ζ j) * R (f (equation k r n j))^m *
      L (equation k r n i)^m := by
  let j := ArithmeticThetaInfinitesimalPolygonR0129.next r hr i
  let L := E.toRingHom.comp (ArithmeticThetaInfinitesimalPolygonR0129.restriction k n false)
  let R := ArithmeticThetaInfinitesimalPolygonR0129.restriction k n true
  let f := TowerScalarTranslation.ringMap k n ζ
  have hg := finiteGamma_cross k r hr m n E hE ζ hζ i
  change L (f (finiteGamma k r hr n i))^m * R (finiteGamma k r hr n j)^m =
    R (f (finiteGamma k r hr n j))^m * L (finiteGamma k r hr n i)^m at hg
  have h := clear_units (L (equation k r n i)) (R (equation k r n j))
    (L (f (finiteGamma k r hr n i))^m) (R (f (finiteGamma k r hr n j))^m)
    (Units.map L.toMonoidHom (finiteTail k r hr n i))
    (Units.map R.toMonoidHom (finiteTail k r hr n j)) m (by
      change L (f (finiteGamma k r hr n i))^m *
        (R (equation k r n j) * R (finiteTail k r hr n j))^m =
        R (f (finiteGamma k r hr n j))^m *
        (L (equation k r n i) * L (finiteTail k r hr n i))^m
      simpa only [finiteGamma, map_mul] using hg)
  have hp : L (finitePhaseUnit k n ζ⁻¹) = R (finitePhaseUnit k n ζ⁻¹) := by
    exact RingHom.congr_fun (adjacent_base hE)
      (trunc _ PowerSeries.X n (PowerSeries.C ((ζ⁻¹ : kˣ) : k)))
  have h' := congrArg (fun z => R (finitePhaseUnit k n ζ⁻¹)^(m/2) * z) h
  simp only [finiteGamma, map_mul, mul_pow, Units.coe_map_inv] at h'
  change L (localMultiplier k r hr m n ζ i) * L (f (equation k r n i))^m *
    R (equation k r n j)^m = _
  simp only [localMultiplier, Units.val_mul, Units.val_pow_eq_pow_val, map_mul,
    map_pow, Units.coe_map, hp]
  change R (finitePhaseUnit k n ζ⁻¹)^(m/2) *
      (L (f (equation k r n i))^m * L (f (finiteTail k r hr n i))^m *
        L (↑((finiteTail k r hr n i)⁻¹) : A k n)^m * R (equation k r n j)^m) =
    R (finitePhaseUnit k n ζ⁻¹)^(m/2) *
      (R (f (equation k r n j))^m * R (f (finiteTail k r hr n j))^m *
        R (↑((finiteTail k r hr n j)⁻¹) : A k n)^m * L (equation k r n i)^m) at h'
  change R (finitePhaseUnit k n ζ⁻¹)^(m/2) * L (f (finiteTail k r hr n i))^m *
      L (↑((finiteTail k r hr n i)⁻¹) : A k n)^m * L (f (equation k r n i))^m *
        R (equation k r n j)^m =
    R (finitePhaseUnit k n ζ⁻¹)^(m/2) * R (f (finiteTail k r hr n j))^m *
      R (↑((finiteTail k r hr n j)⁻¹) : A k n)^m * R (f (equation k r n j))^m *
        L (equation k r n i)^m
  linear_combination h' 

end GammaComparison


namespace StageConstruction
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
open GammaComparison
local instance unitSectionsCommRing (X : Scheme.{u}) (U : X.Opens) :
    CommRing Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) :=
  inferInstanceAs (CommRing (X.presheaf.obj (Opposite.op U)))

/-- Local isomorphisms into an actual ideal realization glue by the kernel
property of its inclusion. This constructs a sheaf isomorphism. -/
lemma iso_of_local_factorization {X : Scheme.{u}} {ι : Type*}
    (U : ι → Scheme.{u}) (c : ∀ i, U i ⟶ X)
    (ho : ∀ i, IsOpenImmersion (c i)) (hc : ∀ x : X, ∃ i z, c i z = x)
    (I : X.IdealSheafData) (P Q : X.Modules)
    (j : Q ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hj : IdealRealization I Q j)
    (φ : P ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (q : ∀ i, (Scheme.Modules.pullback (c i)).obj P ≅
      (Scheme.Modules.pullback (c i)).obj Q)
    (hq : ∀ i, (q i).hom ≫ pulledInclusion (c i) j = pulledInclusion (c i) φ) :
    ∃ e : P ≅ Q, e.hom ≫ j = φ := by
  letI : Mono j := hj.1
  letI : ∀ i, IsOpenImmersion (c i) := ho
  have hq' (i : ι) : (q i).hom ≫ (Scheme.Modules.pullback (c i)).map j =
      (Scheme.Modules.pullback (c i)).map φ := by
    letI := unitPullback_isIso (c i)
    apply (cancel_mono (unitPullback (c i))).mp
    exact hq i
  have hz : φ ≫ cokernel.π j = 0 := by
    apply hom_ext_pullback_cover U c ho hc
    intro i
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero, ← hq',
      Category.assoc, ← CategoryTheory.Functor.map_comp, cokernel.condition,
      CategoryTheory.Functor.map_zero, comp_zero]
  let a := Abelian.monoLift j φ hz
  have ha : a ≫ j = φ := Abelian.monoLift_comp j φ hz
  have hai (i : ι) : (Scheme.Modules.pullback (c i)).map a = (q i).hom := by
    letI : Mono (pulledInclusion (c i) j) :=
      (pullback_open_realization (c i) I Q j hj).1
    apply (cancel_mono (pulledInclusion (c i) j)).mp
    rw [hq i]
    change (Scheme.Modules.pullback (c i)).map a ≫
        ((Scheme.Modules.pullback (c i)).map j ≫ unitPullback (c i)) = _
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ha]
    rfl
  letI : IsIso a := isIso_of_pullback_cover U c ho hc a (fun i => by
    rw [hai i]
    infer_instance)
  exact ⟨asIso a, ha⟩

variable (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
variable {E : B k n false ≃+* B k n true} (hE : IsAdjacent k n E)
variable (D : Atlas k r n hr E) (m : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1)

/-- Numerators of the inclusion composed with the proposed scalar lift. -/
def liftNumerator (i : Fin r) : A k n :=
  localMultiplier k r hr m n ζ i *
    TowerScalarTranslation.ringMap k n ζ (equation k r n i)^m

include hE hζ in
lemma liftNumerator_compatible : Compatible k r n hr E m
    (liftNumerator k r n hr m ζ) := by
  intro i
  have h := localMultiplier_cocycle k r hr m n E hE ζ hζ i
  simp only [liftNumerator, map_mul, map_pow, RingHom.comp_apply] at h ⊢
  exact h

/-- The inclusion-valued map exists by the accepted actual-sheaf realization. -/
def inclusionMap : StageDual k D m :=
  Classical.choose (IdentityStageSectionRealizationR0138.exists_realizes k r n hr h3 hE D m
    ⟨liftNumerator k r n hr m ζ, liftNumerator_compatible k r n hr hE m ζ hζ⟩)

lemma inclusionMap_realizes : StageRealizes k D m (liftNumerator k r n hr m ζ)
    (inclusionMap k r n hr h3 hE D m ζ hζ) :=
  Classical.choose_spec (IdentityStageSectionRealizationR0138.exists_realizes k r n hr h3 hE D m
    ⟨liftNumerator k r n hr m ζ, liftNumerator_compatible k r n hr hE m ζ hζ⟩)

lemma inclusionMap_numerator :
    IdentityStageSectionRealizationR0138.numerator k r n hr h3 hE D m
      (inclusionMap k r n hr h3 hE D m ζ hζ) = liftNumerator k r n hr m ζ := by
  exact (IdentityStageSectionRealizationR0138.realizes_iff k r n hr h3 hE D m
    ⟨liftNumerator k r n hr m ζ, liftNumerator_compatible k r n hr hE m ζ hζ⟩
    _).mp (inclusionMap_realizes k r n hr h3 hE D m ζ hζ)


/-- Multiplication by an actual global unit, as a sheaf isomorphism. -/
def unitMulIso {X : Scheme.{u}} (a : Γ(X, ⊤)ˣ) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) where
  hom := fromSection _ (a : Γ(X, ⊤))
  inv := fromSection _ (↑a⁻¹ : Γ(X, ⊤))
  hom_inv_id := by
    apply unit_hom_ext
    change (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (↑a⁻¹ : Γ(X, ⊤))).app ⊤
      ((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        (a : Γ(X, ⊤))).app ⊤ 1) = (1 : Γ(X, ⊤))
    erw [fromSection_apply, fromSection_apply]
    simp only [homOfLE_refl, op_id]
    erw [CategoryTheory.Functor.map_id]
    change (1 * ↑a) * ↑a⁻¹ = (1 : Γ(X, ⊤))
    simp only [one_mul, Units.mul_inv]
  inv_hom_id := by
    apply unit_hom_ext
    change (fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (a : Γ(X, ⊤))).app ⊤
      ((fromSection (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        (↑a⁻¹ : Γ(X, ⊤))).app ⊤ 1) = (1 : Γ(X, ⊤))
    erw [fromSection_apply, fromSection_apply]
    simp only [homOfLE_refl, op_id]
    erw [CategoryTheory.Functor.map_id]
    change (1 * ↑a⁻¹) * ↑a = (1 : Γ(X, ⊤))
    simp only [one_mul, Units.inv_mul]

/-- The canonical source frame evaluates the actual ideal inclusion at its equation. -/
def sourceFrame (i : Fin r) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ≅
      (Scheme.Modules.pullback (D.chart i)).obj (stageModule k D m) := by
  letI := IdentityStageSectionRealizationR0138.localGenerator_frame k r n hr h3 hE D m i
  exact asIso (fromSection _
    (IdentityStageSectionRealizationR0138.localGenerator k r n hr h3 hE D m i))

variable (g : D.X ≅ D.X) (hg : StageAction k D id ζ false g)

include hg in
lemma scalar_chart (i : Fin r) : D.chart i ≫ g.hom =
    TowerScalarTranslation.chartMap k n ζ ≫ D.chart i := by
  obtain ⟨_, f, hf, hc⟩ := hg
  rw [TowerScalarTranslation.coordinates_unique k n ζ f hf] at hc
  exact hc i

/-- The target frame is pulled back along the prescribed scalar chart map. -/
def targetFrame (i : Fin r) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ≅
      (Scheme.Modules.pullback (D.chart i)).obj
        ((Scheme.Modules.pullback g.hom).obj (stageModule k D m)) := by
  let α := (sourceFrame k r n hr h3 hE D m i).hom
  letI : IsIso α := inferInstanceAs (IsIso (sourceFrame k r n hr h3 hE D m i).hom)
  letI := pullFrame_isIso (TowerScalarTranslation.chartMap k n ζ) α
  exact asIso (pullFrame (TowerScalarTranslation.chartMap k n ζ) α) ≪≫
    squareIso g.hom (D.chart i) (D.chart i) (TowerScalarTranslation.chartMap k n ζ)
      (scalar_chart k r n hr D ζ g hg i) (stageModule k D m)

lemma targetFrame_inclusion (i : Fin r) :
    (targetFrame k r n hr h3 hE D m ζ g hg i).hom ≫
      pulledInclusion (D.chart i) (pulledInclusion g.hom (idealInclusion ((stageIdeal k D)^m))) =
    fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
      ((TowerScalarTranslation.chartMap k n ζ).appTop
        (IdentityStageSectionRealizationR0138.localEquation k r n m i)) := by
  dsimp only [targetFrame, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, squareIso_inclusion]
  exact pullFrame_evaluation (TowerScalarTranslation.chartMap k n ζ) _ _ _
    (IdentityStageSectionRealizationR0138.frame_inclusion k r n hr h3 hE D m i)

/-- Explicit isomorphism on each actual chart. -/
def localIso (i : Fin r) :
    (Scheme.Modules.pullback (D.chart i)).obj (stageModule k D m) ≅
      (Scheme.Modules.pullback (D.chart i)).obj
        ((Scheme.Modules.pullback g.hom).obj (stageModule k D m)) :=
  (sourceFrame k r n hr h3 hE D m i).symm ≪≫
    unitMulIso (Units.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom.toMonoidHom
      (localMultiplier k r hr m n ζ i)) ≪≫
    targetFrame k r n hr h3 hE D m ζ g hg i

lemma localIso_inclusion (i : Fin r) :
    (localIso k r n hr h3 hE D m ζ g hg i).hom ≫
      pulledInclusion (D.chart i) (pulledInclusion g.hom (idealInclusion ((stageIdeal k D)^m))) =
    pulledInclusion (D.chart i) (inclusionMap k r n hr h3 hE D m ζ hζ) := by
  apply (cancel_epi (sourceFrame k r n hr h3 hE D m i).hom).mp
  change (sourceFrame k r n hr h3 hE D m i).hom ≫
    ((sourceFrame k r n hr h3 hE D m i).inv ≫
      (unitMulIso (Units.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom.toMonoidHom
        (localMultiplier k r hr m n ζ i))).hom ≫
      (targetFrame k r n hr h3 hE D m ζ g hg i).hom) ≫ _ = _
  rw [← Category.assoc, Iso.hom_inv_id_assoc]
  rw [Category.assoc, targetFrame_inclusion]
  have hφ := IdentityStageSectionRealizationR0138.frame_evaluation k r n hr h3 hE D m
    (inclusionMap k r n hr h3 hE D m ζ hζ) i
  rw [inclusionMap_numerator] at hφ
  change (sourceFrame k r n hr h3 hE D m i).hom ≫ _ = _ at hφ
  rw [hφ]
  apply unit_hom_ext
  simp only [unitMulIso, fromSection_apply,
    homOfLE_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  change (1 * (show Γ(specA k n, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (localMultiplier k r hr m n ζ i))) *
    (TowerScalarTranslation.chartMap k n ζ).appTop
      (IdentityStageSectionRealizationR0138.localEquation k r n m i) =
    1 * (show Γ(specA k n, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (liftNumerator k r n hr m ζ i))
  rw [one_mul, one_mul]
  apply (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.injective
  rw [map_mul]
  erw [affine_pullback_inv]
  simp only [liftNumerator, map_pow]
  erw [(Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply,
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply]
  rfl

include hg in
/-- A scalar sheaf lift on every prescribed finite atlas. -/
lemma stage_lift_exists : ∃ e : stageModule k D m ≅
    (Scheme.Modules.pullback g.hom).obj (stageModule k D m),
    e.hom ≫ pulledInclusion g.hom (idealInclusion ((stageIdeal k D)^m)) =
      inclusionMap k r n hr h3 hE D m ζ hζ := by
  exact iso_of_local_factorization (fun _ : Fin r => specA k n) D.chart D.chart_open D.covers
    (((stageIdeal k D)^m).comap g.hom) (stageModule k D m)
    ((Scheme.Modules.pullback g.hom).obj (stageModule k D m)) _
    (pullback_open_realization g.hom ((stageIdeal k D)^m) (stageModule k D m)
      (idealInclusion _) (ideal_realization _)) _
    (localIso k r n hr h3 hE D m ζ g hg)
    (localIso_inclusion k r n hr h3 hE D m ζ hζ g hg)

end StageConstruction


namespace Completion
open AlgebraizedPositiveFormalSectionsR0136

lemma compIso_naturality {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (c' : Z' ⟶ X)
    (c : Z ⟶ X) (h : t ≫ c' = c) {F G : X.Modules} (a : F ⟶ G) :
    (compIso t c' c h F).hom ≫ (Scheme.Modules.pullback c).map a =
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback c').map a) ≫
        (compIso t c' c h G).hom := by
  exact (((Scheme.Modules.pullbackComp t c') ≪≫
    Scheme.Modules.pullbackCongr h).hom.naturality a).symm

/-- Faithfulness on all infinitesimal fibers, for actual invertible modules. -/
lemma hom_ext (hM : IsModel k T M) (F G : M.X.Modules)
    (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (a b : F ⟶ G) (hab : ∀ n, (Scheme.Modules.pullback (M.inclusion n)).map a =
      (Scheme.Modules.pullback (M.inclusion n)).map b) : a = b := by
  letI : IsProper M.p := hM.1
  have hn (n : ℕ) : (Scheme.Modules.pullback (M.inclusion n)).map a =
      (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
        (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) F).inv ≫
      (Scheme.Modules.pullback (T.transition n (n+1) (Nat.le_succ n))).map
        ((Scheme.Modules.pullback (M.inclusion (n+1))).map a) ≫
      (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
        (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) G).hom := by
    rw [← compIso_naturality, Iso.inv_hom_id_assoc]
  obtain ⟨q, hq, hu⟩ := pullback_completion
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) M.p
    (fun n => (T.atlas n).X) M.inclusion (fun n => (T.atlas n).p)
    (fun n => hM.2.2.1 n) (fun n => T.transition n (n+1) (Nat.le_succ n))
    (fun n => hM.2.2.2 n (n+1) (Nat.le_succ n)) F G hF hG
    (fun n => (Scheme.Modules.pullback (M.inclusion n)).map a) hn
  exact (hu a (fun _ => rfl)).trans (hu b (fun n => (hab n).symm)).symm

/-- Compatible actual isomorphisms algebraize to an actual isomorphism. -/
lemma iso_exists (hM : IsModel k T M) (F G : M.X.Modules)
    (hF : Scheme.Modules.IsInvertible F) (hG : Scheme.Modules.IsInvertible G)
    (e : ∀ n, (Scheme.Modules.pullback (M.inclusion n)).obj F ≅
      (Scheme.Modules.pullback (M.inclusion n)).obj G)
    (he : ∀ n,
      (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
        (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) F).hom ≫ (e n).hom =
      (Scheme.Modules.pullback (T.transition n (n+1) (Nat.le_succ n))).map (e (n+1)).hom ≫
      (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
        (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) G).hom) :
    ∃ q : F ≅ G, ∀ n, (Scheme.Modules.pullback (M.inclusion n)).map q.hom = (e n).hom := by
  letI : IsProper M.p := hM.1
  have hf (n : ℕ) := congrArg (fun a =>
    (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
      (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) F).inv ≫ a) (he n)
  simp only [Iso.inv_hom_id_assoc, Category.assoc] at hf
  have hi (n : ℕ) : (e n).inv =
      (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
        (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) G).inv ≫
      (Scheme.Modules.pullback (T.transition n (n+1) (Nat.le_succ n))).map (e (n+1)).inv ≫
      (compIso (T.transition n (n+1) (Nat.le_succ n)) (M.inclusion (n+1))
        (M.inclusion n) (hM.2.2.2 n (n+1) (Nat.le_succ n)) F).hom := by
    apply (cancel_epi (e n).hom).mp
    rw [Iso.hom_inv_id, hf n]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id]
  obtain ⟨a, ha, _⟩ := pullback_completion
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) M.p
    (fun n => (T.atlas n).X) M.inclusion (fun n => (T.atlas n).p)
    (fun n => hM.2.2.1 n) (fun n => T.transition n (n+1) (Nat.le_succ n))
    (fun n => hM.2.2.2 n (n+1) (Nat.le_succ n)) F G hF hG (fun n => (e n).hom) hf
  obtain ⟨b, hb, _⟩ := pullback_completion
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) M.p
    (fun n => (T.atlas n).X) M.inclusion (fun n => (T.atlas n).p)
    (fun n => hM.2.2.1 n) (fun n => T.transition n (n+1) (Nat.le_succ n))
    (fun n => hM.2.2.2 n (n+1) (Nat.le_succ n)) G F hG hF (fun n => (e n).inv) hi
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply hom_ext k M hM F F hF hF
    intro n
    rw [Functor.map_comp, ha, hb, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  · apply hom_ext k M hM G G hG hG
    intro n
    rw [Functor.map_comp, ha, hb, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end Completion

namespace ModelConstruction
open GammaComparison StageConstruction AlgebraizedThetaSectionsR0138

variable (m : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1)

lemma liftNumerator_natural (r : ℕ) (hr : 0 < r) (n N : ℕ) (h : n ≤ N) (i : Fin r) :
    truncReduce _ (ArithmeticThetaNodeCharts.t k) n N h (liftNumerator k r N hr m ζ i) =
      liftNumerator k r n hr m ζ i := by
  unfold liftNumerator
  rw [map_mul, map_pow]
  have hm := congrArg Units.val (localMultiplier_natural k r hr m n N h ζ i)
  change truncReduce _ _ n N h (↑(localMultiplier k r hr m N ζ i) : A k N) =
    ↑(localMultiplier k r hr m n ζ i) at hm
  rw [hm]
  have hf := RingHom.congr_fun (TowerScalarTranslation.ringMap_reduce k n N h ζ)
    (equation k r N i)
  simp only [RingHom.comp_apply] at hf
  rw [hf, AlgebraizedThetaSectionsR0138.reduce_equation]

/-- The lift numerators form an actual compatible formal section of the
identity ideal power, with no denominator-clearing hypothesis. -/
def formalInclusion : FormalNumerators k (T := T) m :=
  ⟨fun n => ⟨liftNumerator k r n hr m ζ,
    liftNumerator_compatible k r n hr (T.overlap_spec n) m ζ hζ⟩,
    fun n N h i => liftNumerator_natural k m ζ r hr n N h i⟩

variable (h3 : 3 ≤ r) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
variable (hs : MarkedLift k M (zeroIndex r hr) 1 s)

/-- Proper formal functions algebraizes the inclusion-valued morphism. -/
def modelInclusion : Dual k M s m :=
  Classical.choose (algebraize_formal k h3 M hM s hs m (formalInclusion k m ζ hζ))

lemma modelInclusion_realizes : FormalRealizes k M s m (formalInclusion k m ζ hζ)
    (modelInclusion k M m ζ hζ h3 hM s hs) :=
  (Classical.choose_spec (algebraize_formal k h3 M hM s hs m (formalInclusion k m ζ hζ))).1

lemma modelInclusion_reduction (n : ℕ) :
    reduceDual k h3 M hM s hs m n (modelInclusion k M m ζ hζ h3 hM s hs) =
      inclusionMap k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ := by
  apply IdentityStageSectionRealizationR0138.realizes_unique k r n hr h3
    (T.overlap_spec n) (T.atlas n) m
    ⟨liftNumerator k r n hr m ζ,
      liftNumerator_compatible k r n hr (T.overlap_spec n) m ζ hζ⟩
  · exact (realizes_iff_reductions k h3 M hM s hs m (formalInclusion k m ζ hζ) _).mp
      (modelInclusion_realizes k M m ζ hζ h3 hM s hs) n
  · exact inclusionMap_realizes k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ

variable (f : M.X ≅ M.X) (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X)
variable (hg : ∀ n, StageAction k (T.atlas n) id ζ false (g n))
variable (hfg : ∀ n, M.inclusion n ≫ f.hom = (g n).hom ≫ M.inclusion n)

/-- The specified commuting square identifies the target line on each fiber. -/
def targetComparison (n : ℕ) :
    (Scheme.Modules.pullback (g n).hom).obj (stageModule k (T.atlas n) m) ≅
      (Scheme.Modules.pullback (M.inclusion n)).obj
        ((Scheme.Modules.pullback f.hom).obj (powerModule k M s m)) :=
  (Scheme.Modules.pullback (g n).hom).mapIso (stageIso k h3 M hM s hs m n).symm ≪≫
    squareIso f.hom (M.inclusion n) (M.inclusion n) (g n).hom (hfg n)
      (powerModule k M s m)

lemma targetComparison_inclusion (n : ℕ) :
    (targetComparison k M m h3 hM s hs f g hfg n).hom ≫
      pulledInclusion (M.inclusion n) (pulledInclusion f.hom (idealInclusion (s.ker^m))) =
      pulledInclusion (g n).hom (idealInclusion ((stageIdeal k (T.atlas n))^m)) := by
  dsimp only [targetComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc, squareIso_inclusion]
  have hj := stageIso_inclusion k h3 M hM s hs m n
  change (stageIso k h3 M hM s hs m n).hom ≫ idealInclusion _ =
    pulledInclusion (M.inclusion n) (idealInclusion (s.ker^m)) at hj
  rw [← hj]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

include h3 hM hs hfg in
lemma target_inclusion_mono (n : ℕ) :
    Mono (pulledInclusion (M.inclusion n)
      (pulledInclusion f.hom (idealInclusion (s.ker^m)))) := by
  let j := pulledInclusion (g n).hom (idealInclusion ((stageIdeal k (T.atlas n))^m))
  letI : Mono j := (pullback_open_realization (g n).hom _ _ _ (ideal_realization _)).1
  have hj : pulledInclusion (M.inclusion n)
      (pulledInclusion f.hom (idealInclusion (s.ker^m))) =
      (targetComparison k M m h3 hM s hs f g hfg n).inv ≫ j := by
    dsimp only [j]
    rw [← targetComparison_inclusion k M m h3 hM s hs f g hfg n,
      Iso.inv_hom_id_assoc]
  rw [hj]
  infer_instance

/-- The finite scalar isomorphism expressed on the actual model pullbacks. -/
def fiberLift (n : ℕ) :
    (Scheme.Modules.pullback (M.inclusion n)).obj (powerModule k M s m) ≅
      (Scheme.Modules.pullback (M.inclusion n)).obj
        ((Scheme.Modules.pullback f.hom).obj (powerModule k M s m)) :=
  stageIso k h3 M hM s hs m n ≪≫
    (stage_lift_exists k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ (g n) (hg n)).choose ≪≫
    targetComparison k M m h3 hM s hs f g hfg n

lemma fiberLift_inclusion (n : ℕ) :
    (fiberLift k M m ζ hζ h3 hM s hs f g hg hfg n).hom ≫
      pulledInclusion (M.inclusion n) (pulledInclusion f.hom (idealInclusion (s.ker^m))) =
      pulledInclusion (M.inclusion n) (modelInclusion k M m ζ hζ h3 hM s hs) := by
  dsimp only [fiberLift, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, targetComparison_inclusion,
    (stage_lift_exists k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ
      (g n) (hg n)).choose_spec]
  rw [← modelInclusion_reduction k M m ζ hζ h3 hM s hs n]
  exact Iso.hom_inv_id_assoc _ _

lemma fiberLift_compatible (n N : ℕ) (h : n ≤ N) :
    (AlgebraizedPositiveFormalSectionsR0136.compIso (T.transition n N h)
      (M.inclusion N) (M.inclusion n) (hM.2.2.2 n N h) (powerModule k M s m)).hom ≫
      (fiberLift k M m ζ hζ h3 hM s hs f g hg hfg n).hom =
    (Scheme.Modules.pullback (T.transition n N h)).map
      (fiberLift k M m ζ hζ h3 hM s hs f g hg hfg N).hom ≫
    (AlgebraizedPositiveFormalSectionsR0136.compIso (T.transition n N h)
      (M.inclusion N) (M.inclusion n) (hM.2.2.2 n N h)
      ((Scheme.Modules.pullback f.hom).obj (powerModule k M s m))).hom := by
  letI := target_inclusion_mono k M m h3 hM s hs f g hfg n
  apply (cancel_mono (pulledInclusion (M.inclusion n)
    (pulledInclusion f.hom (idealInclusion (s.ker^m))))).mp
  rw [Category.assoc, Category.assoc, fiberLift_inclusion,
    AlgebraizedPositiveFormalSectionsR0136.compIso_inclusion,
    AlgebraizedPositiveFormalSectionsR0136.compIso_inclusion]
  change pulledInclusion (T.transition n N h)
    (pulledInclusion (M.inclusion N) (modelInclusion k M m ζ hζ h3 hM s hs)) = _
  rw [← fiberLift_inclusion k M m ζ hζ h3 hM s hs f g hg hfg N]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

/-- Existence on the proper model, retaining its exact scalar automorphism. -/
lemma model_lift_exists : ∃ e : powerModule k M s m ≅
    (Scheme.Modules.pullback f.hom).obj (powerModule k M s m),
    ∀ n, (Scheme.Modules.pullback (M.inclusion n)).map e.hom =
      (fiberLift k M m ζ hζ h3 hM s hs f g hg hfg n).hom := by
  have hP : Scheme.Modules.IsInvertible (powerModule k M s m) :=
    (power_invertible k h3 M hM s hs m).isInvertible_module
  exact Completion.iso_exists k M hM _ _ hP (Scheme.Modules.IsInvertible.pullback f.hom hP)
    (fiberLift k M m ζ hζ h3 hM s hs f g hg hfg)
    (fun n => fiberLift_compatible k M m ζ hζ h3 hM s hs f g hg hfg n (n+1) (Nat.le_succ n))

/-- Chosen model lift with its defining reduction equation. -/
def modelLift : powerModule k M s m ≅
    (Scheme.Modules.pullback f.hom).obj (powerModule k M s m) :=
  (model_lift_exists k M m ζ hζ h3 hM s hs f g hg hfg).choose

lemma modelLift_reduction (n : ℕ) :
    (Scheme.Modules.pullback (M.inclusion n)).map
      (modelLift k M m ζ hζ h3 hM s hs f g hg hfg).hom =
      (fiberLift k M m ζ hζ h3 hM s hs f g hg hfg n).hom :=
  (model_lift_exists k M m ζ hζ h3 hM s hs f g hg hfg).choose_spec n

lemma modelLift_inclusion :
    (modelLift k M m ζ hζ h3 hM s hs f g hg hfg).hom ≫
      pulledInclusion f.hom (idealInclusion (s.ker^m)) =
      modelInclusion k M m ζ hζ h3 hM s hs := by
  apply Completion.hom_ext k M hM _ _
    (power_invertible k h3 M hM s hs m).isInvertible_module
    (Scheme.Modules.isInvertible_unit M.X)
  intro n
  letI := unitPullback_isIso (M.inclusion n)
  apply (cancel_mono (unitPullback (M.inclusion n))).mp
  rw [Functor.map_comp, Category.assoc, modelLift_reduction]
  exact fiberLift_inclusion k M m ζ hζ h3 hM s hs f g hg hfg n

end ModelConstruction

namespace GenericConstruction
/-- Restriction of a geometric model lift along the actual base-change square. -/
def restrictLift (s : baseScheme k ⟶ M.X) (m : ℕ)
    (f : M.X ≅ M.X) (hf : f.hom ≫ M.p = M.p)
    (e : powerModule k M s m ≅ (Scheme.Modules.pullback f.hom).obj (powerModule k M s m)) :
    Lift k M s m (genericMap k M f.hom hf) :=
  (Scheme.Modules.pullback (genericInclusion k M)).mapIso e ≪≫
    (squareIso f.hom (genericInclusion k M) (genericInclusion k M)
      (genericMap k M f.hom hf) (genericMap_inclusion k M f.hom hf).symm
      (powerModule k M s m)).symm

lemma restrictLift_act (s : baseScheme k ⟶ M.X) (m : ℕ)
    (f : M.X ≅ M.X) (hf : f.hom ≫ M.p = M.p)
    (e : powerModule k M s m ≅ (Scheme.Modules.pullback f.hom).obj (powerModule k M s m))
    (φ : Dual k M s m) :
    act k M s m (genericMap k M f.hom hf) (restrictLift k M s m f hf e)
      (restrictDual k M s m φ) =
      restrictDual k M s m (e.hom ≫ pulledInclusion f.hom φ) := by
  change ((Scheme.Modules.pullback (genericInclusion k M)).map e.hom ≫
    (squareIso f.hom (genericInclusion k M) (genericInclusion k M)
      (genericMap k M f.hom hf) (genericMap_inclusion k M f.hom hf).symm
      (powerModule k M s m)).inv) ≫
    pulledInclusion (genericMap k M f.hom hf) (pulledInclusion (genericInclusion k M) φ) = _
  rw [Category.assoc, ← squareIso_inclusion f.hom (genericInclusion k M)
    (genericInclusion k M) (genericMap k M f.hom hf)
    (genericMap_inclusion k M f.hom hf).symm (powerModule k M s m) φ,
    Iso.inv_hom_id_assoc]
  simp only [restrictDual, pulledInclusion, Functor.map_comp, Category.assoc]

end GenericConstruction

end ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141





namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.StageConstruction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaPolygonCartierR0133 GlobalCartierIdealLineR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
open CanonicalCartierLineReductionR0133 Scheme.Modules GammaComparison
variable (k : Type u) [Field k] [CharZero k]
variable (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
variable {E : B k n false ≃+* B k n true} (hE : IsAdjacent k n E)
variable (D : Atlas k r n hr E) (m : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1)
variable (g : D.X ≅ D.X) (hg : StageAction k D id ζ false g)

lemma targetFrame_evaluation (φ : StageDual k D m) (i : Fin r) :
    (targetFrame k r n hr h3 hE D m ζ g hg i).hom ≫
      pulledInclusion (D.chart i) (pulledInclusion g.hom φ) =
    fromSection (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)
      ((TowerScalarTranslation.chartMap k n ζ).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
          (IdentityStageSectionRealizationR0138.numerator k r n hr h3 hE D m φ i))) := by
  dsimp only [targetFrame, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, squareIso_inclusion]
  exact pullFrame_evaluation (TowerScalarTranslation.chartMap k n ζ) _ _ _
    (IdentityStageSectionRealizationR0138.frame_evaluation k r n hr h3 hE D m φ i)

lemma stage_lift_chart (e : stageModule k D m ≅
    (Scheme.Modules.pullback g.hom).obj (stageModule k D m))
    (he : e.hom ≫ pulledInclusion g.hom (idealInclusion ((stageIdeal k D)^m)) =
      inclusionMap k r n hr h3 hE D m ζ hζ) (i : Fin r) :
    (Scheme.Modules.pullback (D.chart i)).map e.hom =
      (localIso k r n hr h3 hE D m ζ g hg i).hom := by
  let I := ((stageIdeal k D)^m).comap g.hom
  let j := pulledInclusion g.hom (idealInclusion ((stageIdeal k D)^m))
  have hj : IdealRealization I ((Scheme.Modules.pullback g.hom).obj (stageModule k D m)) j :=
    pullback_open_realization g.hom _ _ _ (ideal_realization _)
  letI := D.chart_open i
  letI : Mono (pulledInclusion (D.chart i) j) :=
    (pullback_open_realization (D.chart i) I _ j hj).1
  apply (cancel_mono (pulledInclusion (D.chart i) j)).mp
  rw [localIso_inclusion k r n hr h3 hE D m ζ hζ g hg i]
  change (Scheme.Modules.pullback (D.chart i)).map e.hom ≫
    ((Scheme.Modules.pullback (D.chart i)).map j ≫ unitPullback (D.chart i)) = _
  rw [← Category.assoc, ← Functor.map_comp]
  change pulledInclusion (D.chart i) (e.hom ≫ j) = _
  rw [he]

include hg in
lemma stage_lift_numerator (e : stageModule k D m ≅
    (Scheme.Modules.pullback g.hom).obj (stageModule k D m))
    (he : e.hom ≫ pulledInclusion g.hom (idealInclusion ((stageIdeal k D)^m)) =
      inclusionMap k r n hr h3 hE D m ζ hζ)
    (φ : StageDual k D m) (i : Fin r) :
    IdentityStageSectionRealizationR0138.numerator k r n hr h3 hE D m
      (e.hom ≫ pulledInclusion g.hom φ) i =
      (localMultiplier k r hr m n ζ i : A k n) *
      TowerScalarTranslation.ringMap k n ζ
        (IdentityStageSectionRealizationR0138.numerator k r n hr h3 hE D m φ i) := by
  have h := IdentityStageSectionRealizationR0138.frame_evaluation k r n hr h3 hE D m
    (e.hom ≫ pulledInclusion g.hom φ) i
  change (sourceFrame k r n hr h3 hE D m i).hom ≫ _ = _ at h
  have hj : pulledInclusion (D.chart i) (e.hom ≫ pulledInclusion g.hom φ) =
      (Scheme.Modules.pullback (D.chart i)).map e.hom ≫
        pulledInclusion (D.chart i) (pulledInclusion g.hom φ) := by
    simp only [pulledInclusion, Functor.map_comp, Category.assoc]
  rw [hj, stage_lift_chart k r n hr h3 hE D m ζ hζ g hg e he i] at h
  dsimp only [localIso, Iso.trans_hom, Iso.symm_hom] at h
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h
  rw [Category.assoc, targetFrame_evaluation] at h
  have hh := congrArg (fun (q : (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ⟶
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules)) =>
      (@Scheme.Modules.Hom.app (specA k n)
        (SheafOfModules.unit (specA k n).ringCatSheaf)
        (SheafOfModules.unit (specA k n).ringCatSheaf) q ⊤) (1 : Γ(specA k n, ⊤))) h
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, unitMulIso,
    fromSection_apply, homOfLE_refl, op_id] at hh
  erw [CategoryTheory.Functor.map_id] at hh
  change (1 * (show Γ(specA k n, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (localMultiplier k r hr m n ζ i))) *
    (TowerScalarTranslation.chartMap k n ζ).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (IdentityStageSectionRealizationR0138.numerator k r n hr h3 hE D m φ i)) =
    1 * (show Γ(specA k n, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (IdentityStageSectionRealizationR0138.numerator k r n hr h3 hE D m
        (e.hom ≫ pulledInclusion g.hom φ) i)) at hh
  have hhh := congrArg (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom hh
  rw [one_mul, one_mul, map_mul] at hhh
  erw [affine_pullback_inv,
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply,
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply] at hhh
  exact hhh.symm
end ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.StageConstruction

namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.ScalarSeries
open CategoryTheory AlgebraicGeometry ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaIndexedOverlapsR0058 ArithmeticThetaCorrectedGammaR0061
open GammaComparison
variable (k : Type u) [Field k] [CharZero k]
omit [CharZero k] in
theorem node_equiv_coord (i : Fin 2) :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1
      (MvPolynomial.X i)) = ArithmeticThetaNodeCharts.quotientMap k
        (MvPolynomial.X i) := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.quotientMap
    ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]


lemma reduction_of (n : ℕ) (a : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k a) =
      trunc _ (ArithmeticThetaNodeCharts.t k) n (nodeEquiv k a) :=
  RingHom.congr_fun (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1 a


lemma filtration_eq (n : ℕ) :
    ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n =
      (Ideal.span {ArithmeticThetaAnnularTorsionPrereqR0053.tau k})^n := by
  simp [ArithmeticThetaAnnularTorsionPrereqR0053.filtration,
    ArithmeticThetaScaledTateBridgeR0046.completedPower,
    ArithmeticThetaScaledTateBridgeR0046.completedParameter,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]


lemma reduction_kills (n : ℕ) (z : Hat k)
    (hz : z ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k (n+1)) :
    completedReduction k n z = 0 := by
  change (Classical.choose (finite_stage_completion_comparison k n)) (trunc _ _ n z) = 0
  rw [filtration_eq] at hz
  rw [show trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n z = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]


lemma reduction_cx (n : ℕ) :
    completedReduction k n (ArithmeticThetaCorrectedGammaR0061.cx k) = coordX k n := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.x k 1)) = _
  rw [reduction_of]
  change trunc _ _ n (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 0))) = _
  rw [node_equiv_coord]
  rfl

lemma reduction_cy (n : ℕ) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = coordY k n := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaScaledTateBridgeR0046.y k 1)) = _
  rw [reduction_of]
  change trunc _ _ n (nodeEquiv k
    (ArithmeticThetaScaledTateBridgeR0046.quotientMap k 1 (MvPolynomial.X 1))) = _
  rw [node_equiv_coord]
  rfl

lemma reduction_base (n : ℕ) (a : PowerSeries k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k a) =
      base k n (trunc _ PowerSeries.X n a) := by
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k a)) = _
  rw [reduction_of]
  rfl

lemma ringMap_reduction_tau (n : ℕ) (ζ : kˣ) :
    TowerScalarTranslation.ringMap k n ζ
      (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)) =
      completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1) := by
  change TowerScalarTranslation.ringMap k n ζ
    (completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X)) =
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X)
  rw [reduction_base, TowerScalarTranslation.ringMap_base]

lemma residue_phase (m : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1)
    (ν : Fin m) (b : ℤ) (hb : b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ)) :
    ζ ^ b = ζ ^ ν.val := by
  have hz : ζ^m = 1 := Units.ext hζ
  rw [zpow_eq_zpow_emod' b hz, hb, ← zpow_eq_zpow_emod' (ν.val : ℤ) hz, zpow_natCast]

lemma term_eigen (m n j : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1)
    (ν : Fin m) (b : ℤ) (hb : b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ)) :
    TowerScalarTranslation.ringMap k n ζ
      (completedReduction k n (ArithmeticThetaScaledAnnularR0050.thetaTerm k 1 1 j b)) =
    scalar k n ((ζ : k)^ν.val) *
      completedReduction k n (ArithmeticThetaScaledAnnularR0050.thetaTerm k 1 1 j b) := by
  have hp := residue_phase k m ζ hζ ν b hb
  unfold ArithmeticThetaScaledAnnularR0050.thetaTerm
  split_ifs with hb0
  · have he : (ζ : k)^b.toNat = (ζ : k)^ν.val := by
      have hh : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      rw [← hh, zpow_natCast] at hp
      exact congrArg Units.val hp
    rw [map_mul, map_pow, map_pow, map_mul, map_pow, ringMap_reduction_tau, map_pow]
    have hx : completedReduction k n (ArithmeticThetaScaledAnnularR0050.cx k 1) = coordX k n :=
      reduction_cx k n
    rw [hx, TowerScalarTranslation.ringMap_x, mul_pow]
    have hs : (scalar k n (ζ : k)) ^ b.toNat = scalar k n ((ζ : k)^ν.val) := by
      simp only [scalar, ← map_pow, he]
    rw [hs]
    ring
  · have he : ((ζ⁻¹ : kˣ) : k)^(-b).toNat = (ζ : k)^ν.val := by
      have hh : (((ζ⁻¹)^(-b).toNat : kˣ)) = ζ^b := by
        rw [← zpow_natCast, inv_zpow, ← zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]
      exact congrArg Units.val (hh.trans hp)
    rw [map_mul, map_pow, map_pow, map_mul, map_pow, ringMap_reduction_tau, map_pow]
    have hy : completedReduction k n (ArithmeticThetaScaledAnnularR0050.cy k 1) = coordY k n :=
      reduction_cy k n
    rw [hy, TowerScalarTranslation.ringMap_y, mul_pow]
    have hs : (scalar k n ((ζ⁻¹ : kˣ) : k)) ^ (-b).toNat = scalar k n ((ζ : k)^ν.val) := by
      simp only [scalar, ← map_pow, he]
    rw [hs]
    ring

lemma partial_eigen (m n j N : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1) (ν : Fin m) :
    TowerScalarTranslation.ringMap k n ζ
      (completedReduction k n (ArithmeticThetaScaledAnnularR0050.thetaPartial k 1 m 1 j ν.val N)) =
    scalar k n ((ζ : k)^ν.val) *
      completedReduction k n (ArithmeticThetaScaledAnnularR0050.thetaPartial k 1 m 1 j ν.val N) := by
  classical
  simp only [ArithmeticThetaScaledAnnularR0050.thetaPartial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs with h
  · exact term_eigen k m n j ζ hζ ν b h
  · simp only [map_zero, mul_zero]

lemma section_reduction (m : ℕ) (hm : 0 < m) (he : Even m) (n j : ℕ) (ν : Fin m) :
    completedReduction k n (ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he j ν) =
    completedReduction k n (ArithmeticThetaScaledAnnularR0050.thetaPartial k 1 m 1 j ν.val
      (n+1+2*(j+1)+1)) := by
  have ht := (Classical.choose_spec (ArithmeticThetaScaledAnnularR0050.theta_completed_limit
    k 1 m 1 j (ν.val : ℤ) (by decide) hm he (by decide))).1 (n+1)
    (n+1+2*(j+1)+1) (by omega)
  have hz := reduction_kills k n _ ht
  rw [map_sub, sub_eq_zero] at hz
  exact hz

lemma section_eigen (m : ℕ) (hm : 0 < m) (he : Even m) (n j : ℕ)
    (ζ : kˣ) (hζ : (ζ : k)^m = 1) (ν : Fin m) :
    TowerScalarTranslation.ringMap k n ζ
      (completedReduction k n (ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he j ν)) =
    scalar k n ((ζ : k)^ν.val) *
      completedReduction k n (ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he j ν) := by
  rw [section_reduction]
  exact partial_eigen k m n j _ ζ hζ ν

lemma uniform_eigen (m : ℕ) (hm : 0 < m) (he : Even m) (n : ℕ)
    (ζ : kˣ) (hζ : (ζ : k)^m = 1) (ν : Fin m) (i : Fin (2*m)) :
    TowerScalarTranslation.ringMap k n ζ
      (completedReduction k n (ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
        (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) i)) =
    scalar k n ((ζ : k)^ν.val) *
      completedReduction k n (ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
        (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) i) := by
  classical
  have hc : ArithmeticThetaAnnularThetaR0128.combine k m hm he i.val
      (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) =
      ArithmeticThetaAnnularThetaR0128.thetaSection k m hm he i.val ν := by
    simp [ArithmeticThetaAnnularThetaR0128.combine,
      ArithmeticThetaGenericEvaluationR0140.thetaVector]
  simp only [ArithmeticThetaAnnularThetaR0128.uniformSection, hc, map_mul, map_pow, ArithmeticThetaAnnularTorsionPrereqR0053.tau]
  rw [ringMap_reduction_tau, section_eigen k m hm he n i.val ζ hζ ν]
  ring

lemma normalized_eigen {R : Type*} [CommRing R] (σ : R →+* R) (p u : Rˣ)
    (d m : ℕ) (a c : R) (ha : σ a = (p : R)^d * c * a) :
    ((↑p⁻¹ : R)^d * σ (u : R)^m * (↑u⁻¹ : R)^m) *
      σ (a * (↑u⁻¹ : R)^m) = c * (a * (↑u⁻¹ : R)^m) := by
  rw [map_mul, map_pow, ha]
  calc
    _ = (c * (a * (↑u⁻¹ : R)^m)) *
        ((↑p⁻¹ : R) * (p : R))^d * (σ (u : R) * σ (↑u⁻¹ : R))^m := by
      simp only [mul_pow]
      ring
    _ = _ := by rw [Units.inv_mul, ← map_mul, Units.mul_inv, map_one, one_pow,
      one_pow, mul_one, mul_one]

lemma numerator_eigen (m : ℕ) (hm : 0 < m) (he : Even m) (n : ℕ)
    (ζ : kˣ) (hζ : (ζ : k)^m = 1) (ν : Fin m) (i : Fin (2*m)) :
    (localMultiplier k (2*m) (Nat.mul_pos (by decide) hm) m n ζ i : A k n) *
      TowerScalarTranslation.ringMap k n ζ
        (finiteNumerator k m hm he (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) n i) =
    scalar k n ((ζ : k)^ν.val) *
      finiteNumerator k m hm he (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) n i := by
  let H := ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (i.val * (m/2)) *
    ArithmeticThetaAnnularTorsionPrereqR0053.cx k ^ (m/2) *
    ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
      (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) i
  have hH : TowerScalarTranslation.ringMap k n ζ (completedReduction k n H) =
      (finitePhaseUnit k n ζ : A k n)^(m/2) * scalar k n ((ζ : k)^ν.val) *
        completedReduction k n H := by
    simp only [H, map_mul, map_pow, ArithmeticThetaAnnularTorsionPrereqR0053.tau]
    rw [ringMap_reduction_tau]
    have hx : completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = coordX k n :=
      reduction_cx k n
    rw [hx, TowerScalarTranslation.ringMap_x, mul_pow, uniform_eigen k m hm he n ζ hζ ν i]
    change _ = (scalar k n (ζ : k))^(m/2) * _ * _
    ring
  have hnum : finiteNumerator k m hm he
      (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) n i =
      completedReduction k n H *
        (↑((finiteTail k (2*m) (Nat.mul_pos (by decide) hm) n i)⁻¹) : A k n)^m := by
    simp only [finiteNumerator, thetaNumerator, map_mul, map_pow, H]
    rfl
  rw [hnum]
  have hp : finitePhaseUnit k n ζ⁻¹ = (finitePhaseUnit k n ζ)⁻¹ := map_inv _ ζ
  simp only [localMultiplier, hp, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map]
  exact normalized_eigen (TowerScalarTranslation.ringMap k n ζ) (finitePhaseUnit k n ζ)
    (finiteTail k (2*m) (Nat.mul_pos (by decide) hm) n i) (m/2) m _ _ hH

end ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.ScalarSeries

namespace ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaPolygonCartierR0133 GlobalCartierIdealLineR0133
open CanonicalCartierLineReductionR0133 Scheme.Modules GammaComparison
open AlgebraizedThetaSectionsR0138 GenericThetaBasisR0140
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
namespace ModelConstruction
open StageConstruction
variable (m : ℕ) (ζ : kˣ) (hζ : (ζ : k)^m = 1)
variable (h3 : 3 ≤ r) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
variable (hs : MarkedLift k M (zeroIndex r hr) 1 s)
variable (f : M.X ≅ M.X) (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X)
variable (hg : ∀ n, StageAction k (T.atlas n) id ζ false (g n))
variable (hfg : ∀ n, M.inclusion n ≫ f.hom = (g n).hom ≫ M.inclusion n)

lemma modelLift_action_reduction (φ : Dual k M s m) (n : ℕ) :
    reduceDual k h3 M hM s hs m n
      ((modelLift k M m ζ hζ h3 hM s hs f g hg hfg).hom ≫ pulledInclusion f.hom φ) =
    (stage_lift_exists k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ
      (g n) (hg n)).choose.hom ≫
      pulledInclusion (g n).hom (reduceDual k h3 M hM s hs m n φ) := by
  have hpb : pulledInclusion (M.inclusion n)
      ((modelLift k M m ζ hζ h3 hM s hs f g hg hfg).hom ≫ pulledInclusion f.hom φ) =
      (Scheme.Modules.pullback (M.inclusion n)).map
        (modelLift k M m ζ hζ h3 hM s hs f g hg hfg).hom ≫
      pulledInclusion (M.inclusion n) (pulledInclusion f.hom φ) := by
    simp only [pulledInclusion, Functor.map_comp, Category.assoc]
  dsimp only [reduceDual]
  rw [hpb, modelLift_reduction]
  dsimp only [fiberLift, Iso.trans_hom, targetComparison, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  rw [squareIso_inclusion]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

lemma modelLift_nums (φ : Dual k M s m) (n : ℕ) (i : Fin r) :
    nums k M h3 hM s hs m
      ((modelLift k M m ζ hζ h3 hM s hs f g hg hfg).hom ≫ pulledInclusion f.hom φ) n i =
    (localMultiplier k r hr m n ζ i : A k n) *
      TowerScalarTranslation.ringMap k n ζ (nums k M h3 hM s hs m φ n i) := by
  change IdentityStageSectionRealizationR0138.numerator k r n hr h3 (T.overlap_spec n)
    (T.atlas n) m (reduceDual k h3 M hM s hs m n _) i = _
  rw [modelLift_action_reduction]
  exact stage_lift_numerator k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ
    (g n) (hg n) _ (stage_lift_exists k r n hr h3 (T.overlap_spec n) (T.atlas n) m ζ hζ
      (g n) (hg n)).choose_spec _ i
end ModelConstruction

namespace ThetaAction
open ModelConstruction GenericConstruction
variable (m : ℕ) (hm : 0 < m) (he : Even m)
variable {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
variable (MM : Model k TT) (hMM : IsModel k TT MM) (ss : baseScheme k ⟶ MM.X)
variable (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
variable (ζ : kˣ) (hζ : (ζ : k)^m = 1)
variable (f : MM.X ≅ MM.X) (g : ∀ n, (TT.atlas n).X ≅ (TT.atlas n).X)
variable (hg : ∀ n, StageAction k (TT.atlas n) id ζ false (g n))
variable (hfg : ∀ n, MM.inclusion n ≫ f.hom = (g n).hom ≫ MM.inclusion n)

lemma model_theta_eigen (ν : Fin m) :
    (modelLift k MM m ζ hζ (thetaChartBound m hm he) hMM ss hss f g hg hfg).hom ≫
      pulledInclusion f.hom (thetaSection k m hm he MM hMM ss hss ν) =
    scale (baseScalar k MM (PowerSeries.C ((ζ : k)^ν.val)))
      (thetaSection k m hm he MM hMM ss hss ν) := by
  apply nums_injective k MM (thetaChartBound m hm he) hMM ss hss m
  funext n i
  rw [modelLift_nums, nums_scale, theta_nums]
  exact ScalarSeries.numerator_eigen k m hm he n ζ hζ ν i

lemma generic_theta_eigen (hf : f.hom ≫ MM.p = MM.p) :
    Eigen k MM ss m m ζ (genericMap k MM f.hom hf)
      (restrictLift k MM ss m f hf
        (modelLift k MM m ζ hζ (thetaChartBound m hm he) hMM ss hss f g hg hfg))
      (genericTheta k m hm he MM hMM ss hss) := by
  intro ν U x
  change _ = (act k MM ss m (genericMap k MM f.hom hf) _
    (restrictDual k MM ss m (thetaSection k m hm he MM hMM ss hss ν))).app U x
  rw [restrictLift_act, model_theta_eigen]
  exact (restrict_scale k MM ss m (PowerSeries.C ((ζ : k)^ν.val))
    (thetaSection k m hm he MM hMM ss hss ν) U x).symm
end ThetaAction
end ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141

namespace ArithmeticThetaGeometricLiftsR0141
open GeometricScalarLiftR0141 GeometricScalarLiftR0141.ModelConstruction
open GeometricScalarLiftR0141.GenericConstruction GeometricScalarLiftR0141.ThetaAction
open ArithmeticThetaGenericEvaluationR0140

/-- The unique geometric scalar lift, with exactly the frozen scope. -/
theorem geometric_scalar_lift :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∃! eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ
  obtain ⟨g, hg, hf⟩ := ha.2.1 ζ
  have hz : (ζ : k)^m = 1 := hζ.pow_eq_one
  let e : Lift k M s m (scalarMap k M rot scal inv ha ζ) :=
    restrictLift k M s m (scal ζ) hf.1
      (modelLift k M m ζ hz (thetaChartBound m hm he) hM s hs
        (scal ζ) g hg.2 hf.2)
  have heA : Eigen k M s m m ζ (scalarMap k M rot scal inv ha ζ) e
      (genericTheta k m hm he M hM s hs) :=
    generic_theta_eigen k m hm he M hM s hs ζ hz (scal ζ) g hg.2 hf.2 hf.1
  refine ⟨e, heA, ?_⟩
  intro e' he'
  exact scalar_lift_unique k m hm he M hM s hs rot scal inv ha ζ e' e he' heA
end ArithmeticThetaGeometricLiftsR0141
#print axioms ArithmeticThetaGeometricLiftsR0141.geometric_scalar_lift
