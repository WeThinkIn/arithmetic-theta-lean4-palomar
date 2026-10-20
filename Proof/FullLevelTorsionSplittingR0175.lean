module

public import FullLevelCoverDefinitionsR0175
public import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
namespace FullLevelTorsionSplittingR0175
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} (G : Law R W)

lemma nsmul_pow {T : Scheme.{u}} (t : T ⟶ Base R)
    (n : ℕ) (x : SchemeHomOver t (structureMap R W)) :
    letI := G.pointGroup t
    G.nsmul t n x = x ^ n := by
  letI := G.pointGroup t
  change G.nsmul t n x = x ^ n
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, ih]; rfl

lemma nsmul_val {T : Scheme.{u}} (t : T ⟶ Base R)
    (n : ℕ) (x : SchemeHomOver t (structureMap R W)) :
    (G.nsmul t n x).val = x.val ≫ G.schemeNsmul n := by
  have h := G.nsmul_natural (structureMap R W) t x.val x.property n
    WeierstrassProjModel.RelativeGroupLaw.idPoint
  have hx : WeierstrassProjModel.schemeHomOverComp x.val x.property
      WeierstrassProjModel.RelativeGroupLaw.idPoint = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  exact (congrArg Subtype.val h).symm

lemma pow_residue {H : Type*} [Group H] (x : H) (L n : ℕ) (hx : x ^ L = 1) :
    x ^ (n % L) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n L, pow_add, pow_mul, hx, one_pow, mul_one]

lemma difference_pow {H : Type*} [Group H] (x : H) {L : ℕ}
    (hx : x ^ L = 1) (i j : Fin L) :
    x ^ ((i.val + L - j.val) % L) * x ^ j.val = x ^ i.val := by
  rw [pow_residue x L _ hx, ← pow_add, Nat.sub_add_cancel (by omega), pow_add, hx, mul_one]

lemma difference_nonzero {L : ℕ} (hL : 0 < L) (i j : Fin L)
    (h : (i.val + L - j.val) % L = 0) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hh : i.val + L - j.val < L
  · rw [Nat.mod_eq_of_lt hh] at h
    omega
  · rw [Nat.mod_eq_sub_mod (by omega)] at h
    rw [Nat.mod_eq_of_lt (show i.val + L - j.val - L < L by omega)] at h
    omega

lemma coordinate_over {L : ℕ} (A : FullLevel R W G L (𝟙 (Base R)))
    (i j : Fin L) : coordinatePoint R W G A i j ≫ structureMap R W = 𝟙 _ :=
  (G.mul _ (G.nsmul _ _ A.x) (G.nsmul _ _ A.y)).property

lemma coordinate_killed (hG : IsOriginLaw R W G) {L : ℕ}
    (A : FullLevel R W G L (𝟙 (Base R))) (i j : Fin L) :
    coordinatePoint R W G A i j ≫ G.schemeNsmul L = origin R W := by
  let t := 𝟙 (Base R)
  letI : CommGroup (SchemeHomOver t (structureMap R W)) :=
    { G.pointGroup t with mul_comm := hG.2 t }
  have hx : A.x ^ L = 1 := (nsmul_pow G t L A.x).symm.trans A.killed_x
  have hy : A.y ^ L = 1 := (nsmul_pow G t L A.y).symm.trans A.killed_y
  unfold coordinatePoint
  rw [← nsmul_val G]
  have hk : G.nsmul t L (G.mul t (G.nsmul t i.val A.x) (G.nsmul t j.val A.y)) = G.one t := by
    simp only [nsmul_pow G]
    change (A.x ^ i.val * A.y ^ j.val) ^ L = 1
    rw [mul_pow, ← pow_mul, Nat.mul_comm i.val L, pow_mul, hx, one_pow,
      ← pow_mul, Nat.mul_comm j.val L, pow_mul, hy, one_pow, mul_one]
  exact (congrArg Subtype.val hk).trans (by simpa [t] using hG.1 t)

lemma coordinates_disjoint (hG : IsOriginLaw R W G) {L : ℕ} (hL : 0 < L)
    (A : FullLevel R W G L (𝟙 (Base R))) (a b : Fin L × Fin L) (hab : a ≠ b) :
    Disjoint (Set.range (coordinatePoint R W G A a.1 a.2))
      (Set.range (coordinatePoint R W G A b.1 b.2)) := by
  let s := coordinatePoint R W G A a.1 a.2
  let s' := coordinatePoint R W G A b.1 b.2
  let T := pullback s s'
  let p : T ⟶ Base R := pullback.fst s s'
  have hpq : p = pullback.snd s s' := by
    have h := congrArg (fun f => f ≫ structureMap R W) (pullback.condition (f := s) (g := s'))
    simpa only [Category.assoc, coordinate_over, Category.comp_id, s, s'] using h
  have heq : p ≫ s = p ≫ s' := by
    have h := pullback.condition (f := s) (g := s')
    rw [← hpq] at h
    exact h
  let i : Fin L := ⟨(a.1.val + L - b.1.val) % L, Nat.mod_lt _ hL⟩
  let j : Fin L := ⟨(a.2.val + L - b.2.val) % L, Nat.mod_lt _ hL⟩
  have hij : i.val ≠ 0 ∨ j.val ≠ 0 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext (difference_nonzero hL _ _ h.1) (difference_nonzero hL _ _ h.2))
  let c (z : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :=
    WeierstrassProjModel.schemeHomOverComp p (Category.comp_id p) z
  letI : CommGroup (SchemeHomOver p (structureMap R W)) :=
    { G.pointGroup p with mul_comm := hG.2 p }
  have cn (n : ℕ) (z : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
      c (G.nsmul _ n z) = G.nsmul p n (c z) := G.nsmul_natural _ _ _ _ _ _
  have cm (z z' : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
      c (G.mul _ z z') = G.mul p (c z) (c z') := G.mul_natural _ _ _ _ _ _
  have co : c (G.one (𝟙 (Base R))) = G.one p := G.one_natural _ _ _ _
  have hx : c A.x ^ L = 1 := by rw [← nsmul_pow, ← cn, A.killed_x, co]; rfl
  have hy : c A.y ^ L = 1 := by rw [← nsmul_pow, ← cn, A.killed_y, co]; rfl
  have he : c A.x ^ a.1.val * c A.y ^ a.2.val =
      c A.x ^ b.1.val * c A.y ^ b.2.val := by
    have h : c (G.mul _ (G.nsmul _ a.1.val A.x) (G.nsmul _ a.2.val A.y)) =
        c (G.mul _ (G.nsmul _ b.1.val A.x) (G.nsmul _ b.2.val A.y)) := Subtype.ext heq
    rw [cm, cm, cn, cn, cn, cn] at h
    simp only [nsmul_pow G] at h
    exact h
  have hz : c A.x ^ i.val * c A.y ^ j.val = 1 := by
    have hh : (c A.x ^ i.val * c A.y ^ j.val) *
        (c A.x ^ b.1.val * c A.y ^ b.2.val) =
        1 * (c A.x ^ b.1.val * c A.y ^ b.2.val) := by
      rw [one_mul, mul_mul_mul_comm]
      exact (congrArg₂ (· * ·) (difference_pow (c A.x) hx a.1 b.1)
        (difference_pow (c A.y) hy a.2 b.2)).trans he
    exact mul_right_cancel hh
  have hzero : p ≫ coordinatePoint R W G A i j = p ≫ origin R W := by
    have h : c (G.mul _ (G.nsmul _ i.val A.x) (G.nsmul _ j.val A.y)) = G.one p := by
      rw [cm, cn, cn, nsmul_pow, nsmul_pow]
      exact hz
    exact (congrArg Subtype.val h).trans (hG.1 p)
  apply Scheme.isEmpty_pullback_iff.mp
  exact ⟨fun z => Set.disjoint_left.mp (A.avoids i j hij)
    ⟨p z, rfl⟩ ⟨p z, by exact (congrArg (fun f : T ⟶ Curve R W => f z) hzero).symm⟩⟩

lemma split_geometry [IsDomain R] (L : ℕ) :
    IsFinite (torsionStructure R L) ∧ Etale (torsionStructure R L) ∧
    ∀ z, (torsionStructure R L).finrank z = L ^ 2 := by
  have hf : (algebraMap R ((Fin L × Fin L) → R)).Finite :=
    RingHom.finite_algebraMap.mpr inferInstance
  have he : (algebraMap R ((Fin L × Fin L) → R)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  refine ⟨(IsFinite.SpecMap_iff _).mpr hf, HasRingHomProperty.Spec_iff.mpr he, ?_⟩
  intro z
  rw [torsionStructure, Scheme.Hom.finrank_SpecMap_eq_finrank hf
    (RingHom.flat_algebraMap_iff.mpr inferInstance)]
  change (algebraMap R ((Fin L × Fin L) → R)).finrank z = _
  rw [RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  simp [pow_two]

lemma sigma_spec_iso (L : ℕ) : IsIso (sigmaSpec (fun _ : Fin L × Fin L => CommRingCat.of R)) := by
  let q := sigmaSpec (fun _ : Fin L × Fin L => CommRingCat.of R)
  have : IsOpenImmersion q := by
    classical
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    have ht : DFinsupp.single (β := fun _ : Fin L × Fin L => R) j 1 j ∈ y.asIdeal :=
      (PrimeSpectrum.ext_iff.mp heq).le
        (x := DFinsupp.single j 1)
        (show DFinsupp.single (β := fun _ : Fin L × Fin L => R) j 1 i ∈ x.asIdeal by
          simp [hij.symm])
    simp [← Ideal.eq_top_iff_one, y.2.ne_top] at ht
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin L × Fin L => R)).surjective x
    refine ⟨Sigma.ι (fun _ : Fin L × Fin L => Base R) i y, ?_⟩
    change (Sigma.ι (fun _ : Fin L × Fin L => Spec (CommRingCat.of R)) i ≫ q) y = x
    rw [show Sigma.ι (fun _ : Fin L × Fin L => Spec (CommRingCat.of R)) i ≫ q =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin L × Fin L => R) i)) from
        ι_sigmaSpec _ i]
    exact hy
  exact (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩

end FullLevelTorsionSplittingR0175
open FullLevelTorsionSplittingR0175
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170

/-- The marked residue combinations split the entire scheme-theoretic torsion. -/
theorem full_level_torsion_splitting :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 0 < L) (A : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) , ∃ e : CategoryTheory.Iso (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G L).subscheme (AlgebraicGeometry.Spec (CommRingCat.of ((Fin L × Fin L) → R))), CategoryTheory.CategoryStruct.comp e.hom (ArithmeticThetaFullLevelCoverR0175.torsionStructure R L) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G L).subschemeι (ArithmeticThetaRelativeKatoR0169.structureMap R W) ∧ ∀ i j : Fin L, CategoryTheory.CategoryStruct.comp (ArithmeticThetaFullLevelCoverR0175.torsionComponent R L i j) (CategoryTheory.CategoryStruct.comp e.inv (ArithmeticThetaRelativeKatoNaturalityR0170.torsionIdeal R W G L).subschemeι) = ArithmeticThetaFullLevelCoverR0175.coordinatePoint R W G A i j := by
  intro R _ _ _ _ _ W _ G hG L hL A
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : GeometricallyIntegral (structureMap R W) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  letI : IsIntegral (Curve R W) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (structureMap R W)
  letI : IsLocallyNoetherian (Curve R W) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap R W)
  obtain ⟨hfin, het, _, hdegree, _⟩ := relative_multiplication_degree R W G hG L hL
  letI := hfin
  letI := het
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  letI : IsClosedImmersion (origin R W) := by
    have : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
    exact IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  let T := pullback (G.schemeNsmul L) (origin R W)
  let ti : T ⟶ Curve R W := pullback.fst _ _
  let tp : T ⟶ Base R := pullback.snd _ _
  have htp : ti ≫ structureMap R W = tp := by
    calc
      ti ≫ structureMap R W = ti ≫ G.schemeNsmul L ≫ structureMap R W := by rw [G.schemeNsmul_over]
      _ = tp ≫ origin R W ≫ structureMap R W := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = tp := by rw [ho, Category.comp_id]
  let s (i : Fin L × Fin L) := coordinatePoint R W G A i.1 i.2
  have hs (i : Fin L × Fin L) : s i ≫ structureMap R W = 𝟙 _ := coordinate_over G A _ _
  have hsc (i : Fin L × Fin L) : IsClosedImmersion (s i) := by
    have : IsClosedImmersion (s i ≫ structureMap R W) := by rw [hs]; infer_instance
    exact IsClosedImmersion.of_comp (s i) (structureMap R W)
  let m : (∐ fun _ : Fin L × Fin L => Base R) ⟶ Curve R W := Sigma.desc s
  have hm : IsClosedImmersion m :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
      (coordinates_disjoint G hG hL A)
  let k : (∐ fun _ : Fin L × Fin L => Base R) ⟶ T := Sigma.desc
    (fun i => pullback.lift (s i) (𝟙 _) (by simpa using coordinate_killed G hG A i.1 i.2))
  have hk : k ≫ ti = m := by
    apply Sigma.hom_ext
    intro i
    simp [k, ti, m]
  have : IsClosedImmersion (k ≫ ti) := by rw [hk]; exact hm
  letI : IsClosedImmersion k := IsClosedImmersion.of_comp k ti
  let q := sigmaSpec (fun _ : Fin L × Fin L => CommRingCat.of R)
  letI : IsIso q := sigma_spec_iso L
  obtain ⟨hsfin, hset, hsrank⟩ := split_geometry (R := R) L
  letI := hsfin
  letI := hset
  have hq : q ≫ torsionStructure R L = m ≫ structureMap R W := by
    apply Sigma.hom_ext
    intro i
    simp only [q, ι_sigmaSpec_assoc, m, Sigma.ι_desc_assoc]
    rw [hs i]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin L × Fin L => R) i)) ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi (fun _ : Fin L × Fin L => RingHom.id R))) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of R) using 1
    congr 1
  have hkp : k ≫ tp = q ≫ torsionStructure R L := by rw [← htp, ← Category.assoc, hk, hq]
  letI : IsIso k := isIso_of_isClosedImmersion_of_finrank_comp_eq k tp
    (q ≫ torsionStructure R L) hkp (fun z => by
      rw [Scheme.Hom.finrank_comp_left_of_isIso, hsrank]
      exact (Scheme.Hom.finrank_pullback_snd (G.schemeNsmul L) (origin R W) z).trans (hdegree _)|>.symm)
  let I := torsionIdeal R W G L
  have hi : I.subschemeι.ker = ti.ker := by
    rw [I.ker_subschemeι]
    exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (origin R W) (G.schemeNsmul L)).symm
  let f : T ⟶ I.subscheme := IsClosedImmersion.lift I.subschemeι ti hi.le
  have hf : f ≫ I.subschemeι = ti := IsClosedImmersion.lift_fac _ _ _
  letI : IsIso f := IsClosedImmersion.isIso_lift _ _ hi
  let e : I.subscheme ≅ Spec (CommRingCat.of ((Fin L × Fin L) → R)) :=
    (asIso f).symm ≪≫ (asIso k).symm ≪≫ asIso q
  refine ⟨e, ?_, ?_⟩
  · apply (cancel_epi (k ≫ f)).mp
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      IsIso.hom_inv_id_assoc]
    change q ≫ torsionStructure R L = k ≫ f ≫ I.subschemeι ≫ structureMap R W
    rw [← Category.assoc f, hf, ← Category.assoc k, hk]
    exact hq
  · intro i j
    rw [show torsionComponent R L i j = Sigma.ι (fun _ : Fin L × Fin L => Base R) (i,j) ≫ q from
      (ι_sigmaSpec (fun _ : Fin L × Fin L => CommRingCat.of R) (i,j)).symm]
    simp only [e, Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv, Category.assoc,
      IsIso.hom_inv_id_assoc]
    change Sigma.ι (fun _ : Fin L × Fin L => Base R) (i,j) ≫ k ≫ f ≫ I.subschemeι = _
    rw [hf, hk]
    exact Sigma.ι_desc s (i,j)

#print axioms full_level_torsion_splitting
end ArithmeticThetaFullLevelCoverR0175

