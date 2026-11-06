import LocalMarkedPairR0133

/-! Chart restrictions of the actual intersection of marked-section kernels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
namespace GlobalMarkedIdealChartsR0133
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131

lemma comap_iInf_open {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {ι : Type*} [Finite ι] (I : ι → Y.IdealSheafData) :
    (⨅ j, I j).comap f = ⨅ j, (I j).comap f := by
  ext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_iInf, iInf_apply, Ideal.comap_iInf]

lemma comap_kernel_factor {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : Z ⟶ Y) [QuasiCompact g] (h : Z ⟶ X) (e : h ≫ f = g) :
    g.ker.comap f = h.ker := by
  have hp : IsPullback h (𝟙 Z) f g :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using e⟩
  ext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g h (𝟙 Z) f hp]

lemma comap_kernel_disjoint {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Z ⟶ Y) [IsClosedImmersion g]
    (hd : Disjoint (Set.range f) (Set.range g)) : g.ker.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change f x ∈ (g.ker.support : Set Y) ↔ False
  rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq]
  exact ⟨fun hx => Set.disjoint_left.mp hd ⟨x, rfl⟩ hx, False.elim⟩

lemma spec_kernel {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Spec.map (CommRingCat.ofHom f)).ker.ideal
        ⟨⊤, isAffineOpen_top _⟩) = RingHom.ker f := by
  rw [Scheme.Hom.ker_apply]
  rw [show RingHom.ker ((Spec.map (CommRingCat.ofHom f)).app ⊤).hom =
      (RingHom.ker f).comap (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom by
    ext x
    change ((Spec.map (CommRingCat.ofHom f)).app ⊤) x = 0 ↔
      f ((Scheme.ΓSpecIso (CommRingCat.of S)).hom x) = 0
    have he := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
    have hh := congrArg (fun q => q x) he
    change (Scheme.ΓSpecIso (CommRingCat.of T)).hom
      ((Spec.map (CommRingCat.ofHom f)).appTop x) =
      f ((Scheme.ΓSpecIso (CommRingCat.of S)).hom x) at hh
    rw [← hh]
    exact (map_eq_zero_iff (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of T)).hom).1).symm]
  exact Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).hom).2 _

variable (k : Type u) [Field k] [CharZero k] (r n : ℕ) (hr : 0 < r)
  {E : B k n false ≃+* B k n true}

lemma left_factor (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (i : Fin r) (b : kˣ) :
    Spec.map (CommRingCat.ofHom (leftMarkedPoint k n b)) ≫ D.chart i =
      markedSection k r n hr D (next r hr i) b := by
  let q : B k n true →+* R k n := openPoint (markedPoint k n b) true (by simp [markedPoint])
  have hq : q.comp (restriction k n true) = markedPoint k n b :=
    openPoint_restriction _ _ _
  have hbase : (q.comp (E.toRingHom.comp (restriction k n false))).comp (base k n) =
      RingHom.id _ := by
    change q.comp (E.toRingHom.comp ((restriction k n false).comp (base k n))) = _
    rw [adjacent_base hE]
    change (q.comp (restriction k n true)).comp (base k n) = _
    rw [hq]
    exact mkPoint_base _ _ _ _
  have hy : q (E (restriction k n false (coordY k n))) = ↑((markedUnit k n b)⁻¹) := by
    have hh := congrArg q (adjacent_y_mul_x hE)
    rw [map_mul, map_one] at hh
    have hx : q (restriction k n true (coordX k n)) = ↑(markedUnit k n b) := by
      change (q.comp (restriction k n true)) (coordX k n) = _
      rw [hq]
      simp [markedPoint]
    rw [hx] at hh
    calc
      _ = q (E (restriction k n false (coordY k n))) *
          (↑(markedUnit k n b) * ↑((markedUnit k n b)⁻¹)) := by simp
      _ = _ := by rw [← mul_assoc, hh, one_mul]
  have hx : q (E (restriction k n false (coordX k n))) =
      parameter k n * ↑(markedUnit k n b) := by
    have hh := congrArg (q.comp (E.toRingHom.comp (restriction k n false)))
      (coordX_mul_coordY k n)
    simp only [map_mul, RingHom.comp_apply] at hh
    change q (E (restriction k n false (coordX k n))) *
      q (E (restriction k n false (coordY k n))) =
      q (E (restriction k n false (base k n (parameter k n)))) at hh
    rw [hy] at hh
    have hb := RingHom.congr_fun hbase (parameter k n)
    change q (E (restriction k n false (base k n (parameter k n)))) = parameter k n at hb
    rw [hb] at hh
    calc
      _ = (q (E (restriction k n false (coordX k n))) * ↑((markedUnit k n b)⁻¹)) *
          ↑(markedUnit k n b) := by simp [mul_assoc]
      _ = _ := by rw [hh]
  have he : q.comp (E.toRingHom.comp (restriction k n false)) = leftMarkedPoint k n b := by
    apply point_ext
    · exact hbase.trans (mkPoint_base _ _ _ _).symm
    · exact hx.trans (mkPoint_x _ _ _ _).symm
    · exact hy.trans (mkPoint_y _ _ _ _).symm
  have hl : Spec.map (CommRingCat.ofHom q) ≫ leftLeg k n E =
      Spec.map (CommRingCat.ofHom (leftMarkedPoint k n b)) := by
    rw [leftLeg, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he
  have hh : Spec.map (CommRingCat.ofHom q) ≫ rightLeg k n =
      Spec.map (CommRingCat.ofHom (markedPoint k n b)) := by
    rw [rightLeg, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hq
  rw [← hl, Category.assoc, (D.adjacent i).w, ← Category.assoc, hh]
  rfl

lemma chart_disjoint_other (D : Atlas k r n hr E) (i j : Fin r)
    (hj : j ≠ i) (hn : j ≠ next r hr i) (b : kˣ) :
    Disjoint (Set.range (D.chart i)) (Set.range (markedSection k r n hr D j b)) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, rfl⟩ ⟨q, hq⟩
  by_cases hp : next r hr j = i
  · subst i
    change D.chart j (Spec.map (CommRingCat.ofHom (markedPoint k n b)) q) =
      D.chart (next r hr j) p at hq
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent j) _ _ hq
    exact Set.disjoint_left.mp (legs_disjoint k n E) ⟨z, hz⟩
      (CompatibleMarkingsR0131.point_in_right k n b q)
  · exact Set.disjoint_left.mp (D.disjoint i j hj.symm hn.symm hp)
      ⟨p, rfl⟩ ⟨Spec.map (CommRingCat.ofHom (markedPoint k n b)) q, hq⟩

lemma restricted_intersection (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (a : Fin r → kˣ) (i : Fin r) :
    (markedIdeal k r n hr D a).comap (D.chart i) =
      (Spec.map (CommRingCat.ofHom (markedPoint k n (a i)))).ker ⊓
      (Spec.map (CommRingCat.ofHom (leftMarkedPoint k n (a (next r hr i))))).ker := by
  let : IsOpenImmersion (D.chart i) := D.chart_open i
  have hc (j : Fin r) : IsClosedImmersion (markedSection k r n hr D j (a j)) := by
    have : IsSeparated D.p := D.isSeparated hE
    have hs := SmoothMarkedSections.section_over k r n hr D j (a j)
    have : IsClosedImmersion (markedSection k r n hr D j (a j) ≫ D.p) := by
      rw [hs]
      infer_instance
    exact IsClosedImmersion.of_comp _ D.p
  have hi : (markedSection k r n hr D i (a i)).ker.comap (D.chart i) =
      (Spec.map (CommRingCat.ofHom (markedPoint k n (a i)))).ker := by
    let := hc i
    exact comap_kernel_factor _ _ _ rfl
  have hn : (markedSection k r n hr D (next r hr i) (a (next r hr i))).ker.comap
      (D.chart i) =
      (Spec.map (CommRingCat.ofHom (leftMarkedPoint k n (a (next r hr i))))).ker := by
    let := hc (next r hr i)
    exact comap_kernel_factor _ _ _ (left_factor k r n hr hE D i _)
  unfold markedIdeal
  rw [comap_iInf_open]
  apply le_antisymm
  · exact le_inf (hi ▸ iInf_le _ i) (hn ▸ iInf_le _ (next r hr i))
  · apply le_iInf
    intro j
    by_cases hj : j = i
    · subst j
      rw [hi]
      exact inf_le_left
    by_cases hjn : j = next r hr i
    · subst j
      rw [hn]
      exact inf_le_right
    · let := hc j
      rw [comap_kernel_disjoint _ _ (chart_disjoint_other k r n hr D i j hj hjn _)]
      exact le_top

lemma chart_ideal_pair_kernel (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (a : Fin r → kˣ) (i : Fin r) : chartIdeal k r n hr D a i =
      RingHom.ker (pairEvaluation k n (a i) (a (next r hr i))) := by
  let : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  unfold chartIdeal
  rw [restricted_intersection k r n hr hE D a i]
  simp only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
  have hm (I J : Ideal (Γ(specA k n, ⊤))) :
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom (I ⊓ J) =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom I ⊓
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom.hom J := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv
    change Ideal.map e.toRingHom (I ⊓ J) = Ideal.map e.toRingHom I ⊓ Ideal.map e.toRingHom J
    simp only [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, Ideal.comap_inf]
  rw [hm, spec_kernel, spec_kernel]
  ext z
  change (markedPoint k n (a i) z = 0 ∧
    leftMarkedPoint k n (a (next r hr i)) z = 0) ↔ _
  change (_ = 0 ∧ _ = 0) ↔ (markedPoint k n (a i) z,
    leftMarkedPoint k n (a (next r hr i)) z) = (0, 0)
  exact ⟨fun h => Prod.ext h.1 h.2,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

end GlobalMarkedIdealChartsR0133

/-- Every chart restriction of the global marked ideal is the prescribed
adjacent product ideal, with the successor interpreted cyclically. -/
theorem global_marked_ideal_charts :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ (D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E) (a : Fin r → kˣ),
    ∀ i : Fin r, chartIdeal k r n hr D a i = Ideal.span
      ({pairEquation k n (a i) (a (ArithmeticThetaInfinitesimalPolygonR0129.next r hr i))} :
        Set (ArithmeticThetaInfinitesimalPolygonR0129.A k n)) := by
  intro k _ _ r n hr _ E hE D a i
  rw [GlobalMarkedIdealChartsR0133.chart_ideal_pair_kernel k r n hr hE D a i]
  obtain ⟨_, e, he⟩ := local_marked_pair k n (a i)
    (a (ArithmeticThetaInfinitesimalPolygonR0129.next r hr i))
  rw [← he, RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]

end ArithmeticThetaPolygonCartierR0133
