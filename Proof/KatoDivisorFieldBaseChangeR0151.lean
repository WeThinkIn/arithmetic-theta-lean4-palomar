module

public import KatoExistenceDefinitionsR0151
public import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
public import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The specified generic-point map commutes with the actual stalk maps. -/
theorem stalk_field_square (f : X ⟶ Y)
    (α : Y.functionField →+* X.functionField) (hα : IsFieldMap f α) (x : X) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom =
      α.comp (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (f x))).mp
  change Spec.map (f.stalkMap x ≫
      X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ _ =
    Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (f x)) ≫
      CommRingCat.ofHom α) ≫ _
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact hα

/-- Nonzero functions remain nonzero under the specified field map. -/
theorem map_ne_zero (α : Y.functionField →+* X.functionField)
    {g : Y.functionField} (hg : g ≠ 0) : α g ≠ 0 :=
  (map_ne_zero_iff α α.injective).mpr hg

theorem ord_stalk_unit [IsLocallyNoetherian X] (x : X)
    (a : X.presheaf.stalk x) (ha : IsUnit a) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
    letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk x) X.functionField a)).unzeroD 1) = 0
    rw [Ring.ordFrac_of_isUnit ha]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- This includes nongeneric target points above the generic source point,
which occur for transcendental extensions of the coefficient field. -/
theorem ord_map_above_generic [IsLocallyNoetherian X]
    (f : X ⟶ Y) (α : Y.functionField →+* X.functionField)
    (hα : IsFieldMap f α) (x : X) (hx : f x = genericPoint Y)
    (g : Y.functionField) (hg : g ≠ 0) : Scheme.ord (α g) x = 0 := by
  have hfield : IsField (Y.presheaf.stalk (f x)) := by
    rw [hx]
    exact Field.toIsField Y.functionField
  letI := hfield.toField
  obtain ⟨a, d, hd, he⟩ := IsFractionRing.div_surjective (Y.presheaf.stalk (f x)) g
  have ha : a ≠ 0 := by
    intro ha
    apply hg
    rw [← he, ha, map_zero, zero_div]
  have hd' : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hs := DFunLike.congr_fun (stalk_field_square f α hα x)
  simp only [RingHom.comp_apply] at hs
  have hmul : α g * algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x d) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
    rw [hs a, hs d, ← map_mul, ← he]
    rw [div_mul_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd')]
  have hdF : algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x d) ≠ 0 := by
    rw [hs d]
    exact map_ne_zero α ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd')
  have ho := congrArg (fun t => Scheme.ord t x) hmul
  rw [Scheme.ord_mul (map_ne_zero α hg) hdF,
    ord_stalk_unit x _ ((isUnit_iff_ne_zero.mpr ha).map (f.stalkMap x).hom),
    ord_stalk_unit x _ ((isUnit_iff_ne_zero.mpr hd').map (f.stalkMap x).hom), add_zero] at ho
  exact ho

/-- The flat pullback formula uses the fiber length of the actual stalk map.
No finite-type or algebraicity hypothesis on the base change is used here. -/
theorem ord_map_flat [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (α : Y.functionField →+* X.functionField)
    (hα : IsFieldMap f α) (x : X)
    (hx : Order.coheight x = 1) (hy : Order.coheight (f x) = 1)
    (g : Y.functionField) (hg : g ≠ 0) :
    Scheme.ord (α g) x = Scheme.ord g (f x) *
      (ArithmeticThetaDegreeAssembly.stalkFiberLength f x : ℤ) := by
  letI := (f.stalkMap x).hom.toAlgebra
  letI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  letI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    (inferInstance : IsLocalHom (f.stalkMap x).hom)
  obtain ⟨a, d, ha, hd, had, ho⟩ :=
    ArithmeticThetaCurveDegree.exists_principalOrder_eq_sub_lengths Y (f x) hy g hg
  have hs := DFunLike.congr_fun (stalk_field_square f α hα x)
  simp only [RingHom.comp_apply] at hs
  have hnonzero (t : Y.presheaf.stalk (f x)) (ht : t ≠ 0) : f.stalkMap x t ≠ 0 := by
    intro ht'
    have h := hs t
    rw [ht', map_zero] at h
    exact map_ne_zero α ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht) h.symm
  have had' : α g * algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x d) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
    rw [hs d, hs a, ← map_mul, had]
  have hb := ArithmeticThetaCurveDegree.principalOrder_eq_sub_lengths X x hx
    (α g) (map_ne_zero α hg) (f.stalkMap x a) (f.stalkMap x d)
    (hnonzero a ha) (hnonzero d hd) had'
  have ht (t : Y.presheaf.stalk (f x)) :
      ((Ring.ord (X.presheaf.stalk x) (f.stalkMap x t)).toNat : ℤ) =
      ((Ring.ord (Y.presheaf.stalk (f x)) t).toNat : ℤ) *
        (ArithmeticThetaDegreeAssembly.stalkFiberLength f x : ℤ) := by
    have h := congrArg ENat.toNat (ArithmeticThetaDegreeAssembly.ring_ord_flat_local
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) t)
    simp only [ENat.toNat_mul] at h
    exact_mod_cast h
  change Scheme.ord (α g) x = _ at hb
  change Scheme.ord g (f x) = _ at ho
  rw [hb, ho]
  change ((Ring.ord (X.presheaf.stalk x) (f.stalkMap x a)).toNat : ℤ) -
    ((Ring.ord (X.presheaf.stalk x) (f.stalkMap x d)).toNat : ℤ) = _
  rw [ht a, ht d, sub_mul]
  rfl


/-- A cartesian square of structural maps carries compatible sections to
cartesian sections. -/
theorem section_pullback {S Sb Z Zb : Scheme.{u}}
    (p : Z ⟶ S) (pb : Zb ⟶ Sb) (b : Zb ⟶ Z) (i : Sb ⟶ S)
    (h : IsPullback b pb p i) (e : S ⟶ Z) (eb : Sb ⟶ Zb)
    (he : e ≫ p = 𝟙 S) (heb : eb ≫ pb = 𝟙 Sb)
    (heq : eb ≫ b = i ≫ e) : IsPullback eb i b e := by
  have hbig : IsPullback i (eb ≫ pb) (e ≫ p) i := by
    rw [he, heb]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact (hbig.of_bot heq.symm h).flip

/-- Over field spectra, a cartesian compatible section has exactly one
point above its original point, for arbitrary field extensions. -/
theorem section_point_iff {F Fb : Type u} [Field F] [Field Fb]
    {Z Zb : Scheme.{u}} (b : Zb ⟶ Z) (i : Spec (CommRingCat.of Fb) ⟶ Spec (CommRingCat.of F))
    (e : Spec (CommRingCat.of F) ⟶ Z) (eb : Spec (CommRingCat.of Fb) ⟶ Zb)
    (h : IsPullback eb i b e) (x : Zb) :
    b x = e (IsLocalRing.closedPoint F) ↔ x = eb (IsLocalRing.closedPoint Fb) := by
  constructor
  · intro hx
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback h x
      (IsLocalRing.closedPoint F) hx
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Fb)] at hz
    exact hz.symm
  · rintro rfl
    have hw := congrArg (fun t : Spec (CommRingCat.of Fb) ⟶ Z => t (IsLocalRing.closedPoint Fb)) h.w
    simpa only [Scheme.Hom.comp_apply, Subsingleton.elim
      (i (IsLocalRing.closedPoint Fb)) (IsLocalRing.closedPoint F)] using hw

open scoped TensorProduct

/-- A local residue ideal stays radical under an arbitrary extension of a
perfect coefficient field. -/
theorem tensor_residue_radical (F K R : Type u) [Field F] [PerfectField F]
    [Field K] [Algebra F K] [CommRing R] [IsLocalRing R] [Algebra F R] :
    ((IsLocalRing.maximalIdeal R).map
      (algebraMap R (R ⊗[F] K))).IsRadical := by
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  letI : IsReduced (K ⊗[F] (R ⧸ IsLocalRing.maximalIdeal R)) :=
    Algebra.isReduced_tensorProduct_of_perfectField F _ K
  letI : IsReduced ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[F] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm F (R ⧸ IsLocalRing.maximalIdeal R) K)
      (Algebra.TensorProduct.comm F (R ⧸ IsLocalRing.maximalIdeal R) K).injective
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e := Algebra.TensorProduct.quotientTensorEquiv (R := F) F K R
    (IsLocalRing.maximalIdeal R)
  exact isReduced_of_injective e.symm e.symm.injective

/-- Localization and a checked presentation preserve the radical residue ideal. -/
theorem localized_tensor_residue_radical (F K R B : Type u) [Field F] [PerfectField F]
    [Field K] [Algebra F K] [CommRing R] [IsLocalRing R] [Algebra F R]
    [CommRing B] (q : Ideal (R ⊗[F] K)) [q.IsPrime]
    (e : B ≃+* Localization.AtPrime q) (φ : R →+* B)
    (he : ∀ a : R, e (φ a) =
      algebraMap (R ⊗[F] K) (Localization.AtPrime q) (a ⊗ₜ[F] 1)) :
    ((IsLocalRing.maximalIdeal R).map φ).IsRadical := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R (R ⊗[F] K))
  have hJ : J.IsRadical := tensor_residue_radical F K R
  have hloc : (J.map (algebraMap (R ⊗[F] K) (Localization.AtPrime q))).IsRadical := by
    rw [← Ideal.radical_eq_iff, ← IsLocalization.map_radical q.primeCompl,
      hJ.radical]
  have hm : (J.map (algebraMap (R ⊗[F] K) (Localization.AtPrime q))).comap e.toRingHom =
      (IsLocalRing.maximalIdeal R).map φ := by
    have hf : (algebraMap (R ⊗[F] K) (Localization.AtPrime q)).comp
        (algebraMap R (R ⊗[F] K)) = e.toRingHom.comp φ := by
      ext a
      exact (he a).symm
    rw [show J = _ from rfl, Ideal.map_map, hf, ← Ideal.map_map,
      Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  rw [← hm]
  exact Ideal.IsRadical.comap (f := e.toRingHom) hloc

/-- A nonzero proper radical ideal in a DVR is the maximal ideal. -/
theorem radical_eq_maximal_of_dvr (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (J : Ideal R) (hJ : J.IsRadical)
    (hzero : J ≠ ⊥) (htop : J ≠ ⊤) : J = IsLocalRing.maximalIdeal R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hzero hπ
  apply le_antisymm (IsLocalRing.le_maximalIdeal htop)
  rw [hπ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
  apply hJ
  refine ⟨n, ?_⟩
  rw [hn]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The residue ideal in a canonical scheme base change is radical. -/
theorem pullback_residue_radical (F K : Type u) [Field F] [PerfectField F]
    [Field K] [Algebra F K] (Z : Scheme.{u}) (p : Z ⟶ Spec (CommRingCat.of F))
    (x : ↥(CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap F K))))) :
    ((IsLocalRing.maximalIdeal (Z.presheaf.stalk
      (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) x))).map
      ((CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K)))).stalkMap x).hom).IsRadical := by
  let z := CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) x
  letI : Algebra F (Z.presheaf.stalk z) :=
    ((Z.presheaf.germ ⊤ z trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)).toAlgebra
  obtain ⟨q, hq, e, _, he, _⟩ :=
    exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd Z p K x
  letI := hq
  exact localized_tensor_residue_radical F K (Z.presheaf.stalk z) _ q e _ he

/-- Radical ideals are preserved by a ring isomorphism. -/
theorem radical_map_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Bijective φ) (J : Ideal R) (hJ : J.IsRadical) :
    (J.map φ).IsRadical := by
  rw [← Ideal.radical_eq_iff, ← Ideal.map_radical_of_surjective hφ.2
    (show RingHom.ker φ ≤ J by rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ.1]; exact bot_le),
    hJ.radical]

/-- The radical-ideal statement is independent of the chosen cartesian model;
the transition uses the actual comparison isomorphism and its stalk map. -/
theorem basechange_residue_radical (F K : Type u) [Field F] [PerfectField F]
    [Field K] {Z Zb : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of F))
    (pb : Zb ⟶ Spec (CommRingCat.of K)) (ι : F →+* K) (b : Zb ⟶ Z)
    (h : IsPullback b pb p (Spec.map (CommRingCat.ofHom ι))) (x : Zb) :
    ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (b x))).map (b.stalkMap x).hom).IsRadical := by
  letI := ι.toAlgebra
  have he : b = h.isoPullback.hom ≫ CategoryTheory.Limits.pullback.fst p
      (Spec.map (CommRingCat.ofHom ι)) := h.isoPullback_hom_fst.symm
  rw [he, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, ← Ideal.map_map]
  exact radical_map_of_bijective (h.isoPullback.hom.stalkMap x).hom
    (ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.stalkMap x)) _
    (pullback_residue_radical F K Z p (h.isoPullback.hom x))

/-- Orders of rational functions on smooth integral curves are invariant under
arbitrary extensions of a perfect coefficient field, including above the generic point. -/
theorem basechange_order (F K : Type u) [Field F] [PerfectField F] [Field K]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ Spec (CommRingCat.of F)) (pb : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension 1 pb]
    (ι : F →+* K) (b : X ⟶ Y)
    (h : IsPullback b pb p (Spec.map (CommRingCat.ofHom ι)))
    (α : Y.functionField →+* X.functionField) (hα : IsFieldMap b α)
    (g : Y.functionField) (hg : g ≠ 0) (x : X) :
    Scheme.ord (α g) x = Scheme.ord g (b x) := by
  letI : Flat b := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  letI : Surjective b := MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  by_cases hy : b x = _root_.genericPoint Y
  · rw [ord_map_above_generic b α hα x hy g hg, hy, NormOrders.ord_generic]
  have hx : x ≠ _root_.genericPoint X := by
    intro hx
    exact hy (hx ▸ NormOrders.map_generic b)
  letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed p (b x)
    (NormOrders.smooth_closed_of_ne_generic F p (b x) hy)
  letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed pb x
    (NormOrders.smooth_closed_of_ne_generic K pb x hx)
  have hinj : Function.Injective (b.stalkMap x).hom := by
    intro a d had
    apply IsFractionRing.injective (Y.presheaf.stalk (b x)) Y.functionField
    apply α.injective
    have hs := DFunLike.congr_fun (stalk_field_square b α hα x)
    simp only [RingHom.comp_apply] at hs
    rw [← hs a, ← hs d, had]
  let J := (IsLocalRing.maximalIdeal (Y.presheaf.stalk (b x))).map (b.stalkMap x).hom
  have hJ : J = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    apply radical_eq_maximal_of_dvr _ J
      (basechange_residue_radical F K p pb ι b h x)
    · exact (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr
        (IsDiscreteValuationRing.not_a_field (Y.presheaf.stalk (b x)))
    · apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
      exact ((IsLocalRing.local_hom_TFAE (b.stalkMap x).hom).out 1 3 rfl rfl).mp inferInstance
  have hlen : ArithmeticThetaDegreeAssembly.stalkFiberLength b x = 1 := by
    change (Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸ J)).toNat = 1
    rw [hJ, ← pow_one (IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  rw [ord_map_flat b α hα x (NormOrders.smooth_coheight_one_of_ne_generic K pb x hx)
    (NormOrders.smooth_coheight_one_of_ne_generic F p (b x) hy) g hg, hlen]
  simp

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

section Tate
variable (k kb : Type u) [Field k] [CharZero k] [Field kb] [CharZero kb]
variable {r rb : ℕ} {hr : 0 < r} {hrb : 0 < rb}
variable {T : Tower k r hr} {Tb : Tower kb rb hrb}
variable (M : Model k T) (Mb : Model kb Tb)
variable (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k))
variable (sb : baseScheme kb ⟶ Mb.X) (hsb : sb ≫ Mb.p = 𝟙 (baseScheme kb))
variable (G : Law k M) (Gb : Law kb Mb)
variable (ι : LaurentSeries k →+* LaurentSeries kb)
variable (b : genericScheme kb Mb ⟶ genericScheme k M)
variable (h : IsTateBaseChange k kb M Mb s hs sb hsb G Gb ι b)
include h

/-- The actual chosen identity section is cartesian. -/
theorem identity_cartesian :
    IsPullback (ArithmeticThetaGenericEvaluationR0140.genericPoint kb Mb sb hsb)
      (Spec.map (CommRingCat.ofHom ι)) b
      (ArithmeticThetaGenericEvaluationR0140.genericPoint k M s hs) := by
  exact section_pullback (genericStructure k M) (genericStructure kb Mb) b
    (Spec.map (CommRingCat.ofHom ι)) h.1 _ _
    (genericPoint_structure k M s hs) (genericPoint_structure kb Mb sb hsb) h.2.1

/-- Equality with the origin is reflected by the actual base-change map. -/
theorem identity_preimage (x : genericScheme kb Mb) :
    b x = identityPoint k M s hs ↔ x = identityPoint kb Mb sb hsb := by
  exact section_point_iff b (Spec.map (CommRingCat.ofHom ι)) _ _
    (identity_cartesian k kb M Mb s hs sb hsb G Gb ι b h) x

/-- The prescribed nonsplit torsion coefficient is unchanged at every point. -/
theorem katoOrder_base_change (c : ℕ) (x : genericScheme kb Mb) :
    katoOrder k M s hs G c (b x) = katoOrder kb Mb sb hsb Gb c x := by
  classical
  have he := identity_preimage k kb M Mb s hs sb hsb G Gb ι b h
  have hm : multiplication k M G c (b x) = b (multiplication kb Mb Gb c x) := by
    exact (congrArg (fun t : genericScheme kb Mb ⟶ genericScheme k M => t x) (h.2.2 c)).symm
  simp only [katoOrder, hm, he]

end Tate

end ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange

#print axioms ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.stalk_field_square

#print axioms ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.ord_map_above_generic
#print axioms ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.ord_map_flat

#print axioms ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.basechange_residue_radical
#print axioms ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.katoOrder_base_change

#print axioms ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.basechange_order

namespace ArithmeticThetaKatoExistenceR0151
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

/-- The frozen divisor base-change obligation, with its complete field and
geometric scope. -/
theorem kato_divisor_field_base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (kb : Type u) [Field kb] [CharZero kb] (rb : ℕ) (hrb : 0 < rb) (h3b : 3 ≤ rb) (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower kb rb hrb) (heb : Even rb) (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model kb Tb) (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel kb Tb Mb) (sb : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme kb) Mb.X) (hsb : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift kb Mb (ArithmeticThetaIdentitySectionsR0138.zeroIndex rb hrb) 1 sb) (Gb : ArithmeticThetaMarkedGroupLawR0146.Law kb Mb) (hGb : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw kb Mb sb hsb.1 Gb) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb)] (ι : LaurentSeries k →+* LaurentSeries kb) (b : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsTateBaseChange k kb M Mb s hs.1 sb hsb.1 G Gb ι b → ∀ (α : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme kb Mb))), ArithmeticThetaGeometricNormR0150.IsFieldMap b α → ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∀ (g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))), ArithmeticThetaKatoExistenceR0151.HasKatoDivisor k M s hs.1 G c g → ArithmeticThetaKatoExistenceR0151.HasKatoDivisor kb Mb sb hsb.1 Gb c (α g) := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _
    kb _ _ rb hrb h3b Tb heb Mb hMb sb hsb Gb hGb _ _ ι b hb α hα c hc hc6 g hg
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := generic_relative_one k h3 M hM s hs
  letI := generic_relative_one kb h3b Mb hMb sb hsb
  refine ⟨DivisorFieldBaseChange.map_ne_zero α hg.1, fun x => ?_⟩
  rw [DivisorFieldBaseChange.basechange_order (X := genericScheme kb Mb)
    (Y := genericScheme k M) (LaurentSeries k) (LaurentSeries kb)
    (genericStructure k M) (genericStructure kb Mb) ι b hb.1 α hα g hg.1 x, hg.2]
  exact DivisorFieldBaseChange.katoOrder_base_change k kb M Mb s hs.1 sb hsb.1 G Gb ι b hb c x

end ArithmeticThetaKatoExistenceR0151

#print axioms ArithmeticThetaKatoExistenceR0151.kato_divisor_field_base_change
