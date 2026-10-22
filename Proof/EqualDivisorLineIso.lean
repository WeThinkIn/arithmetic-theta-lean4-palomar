module

public import LineIsomorphismDivisors
public import AffineOrderRegularity
public import GenericLineCoefficients
public import NormalLineFrames
public import CurveDegreeDefinitions
public import SectionOrderDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaSectionOrder ArithmeticThetaSectionCompletion

universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaGeometricPrerequisites

private lemma coefficient_ne_zero (X : Scheme.{u}) [IsIntegral X]
    (H : X.Modules) (hH : IsLineBundle X H) (s : Γ(H, ⊤)) (hs : s ≠ 0)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) :
    sectionCoefficient X H U e s ≠ 0 := by
  intro h
  apply hs
  apply sectionCoefficient_injective X H hH U e
  simpa [sectionCoefficient, sectionCoordinate] using h

private lemma coordinate_restrict (X : Scheme.{u}) (H : X.Modules)
    (U V : X.Opens) (hVU : V ≤ U) (e : LocalFrame X H U) (s : Γ(H, ⊤)) :
    X.presheaf.map (homOfLE hVU).op (sectionCoordinate X H U e s) =
      sectionCoordinate X H V (restrictLocalFrame X H U V hVU e) s := by
  apply (e.equiv V hVU).injective
  rw [← e.naturality U V hVU le_rfl]
  simp only [sectionCoordinate, restrictLocalFrame, LinearEquiv.apply_symm_apply]
  change H.presheaf.map (homOfLE hVU).op
    (H.presheaf.map (homOfLE le_top).op s) =
    H.presheaf.map (homOfLE le_top).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma coefficient_restrict (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    (U V : X.Opens) [Nonempty U] [Nonempty V] (hVU : V ≤ U)
    (e : LocalFrame X H U) (s : Γ(H, ⊤)) :
    sectionCoefficient X H V (restrictLocalFrame X H U V hVU e) s =
      sectionCoefficient X H U e s := by
  unfold sectionCoefficient
  rw [← coordinate_restrict X H U V hVU e s, germ_restrict]

/-- A linear map between two framed lines is determined by a nonzero section. -/
private lemma frame_linear_ext (X : Scheme.{u}) [IsIntegral X]
    (H J : X.Modules) (hH : IsLineBundle X H) (s : Γ(H, ⊤)) (hs : s ≠ 0)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) (f : LocalFrame X J U)
    (a b : Γ(H,U) →ₗ[Γ(X,U)] Γ(J,U))
    (hab : a (H.presheaf.map (homOfLE le_top).op s) =
      b (H.presheaf.map (homOfLE le_top).op s)) : a = b := by
  have hn : sectionCoordinate X H U e s ≠ 0 := by
    intro hz
    exact coefficient_ne_zero X H hH s hs U e (by simp [sectionCoefficient, hz])
  have hscalar (q : Γ(H,U) →ₗ[Γ(X,U)] Γ(J,U)) (z : Γ(X,U)) :
      (f.equiv U le_rfl).symm (q (e.equiv U le_rfl z)) =
        z * (f.equiv U le_rfl).symm (q (e.equiv U le_rfl 1)) := by
    have he : e.equiv U le_rfl z = z • e.equiv U le_rfl 1 := by
      simpa using (e.equiv U le_rfl).map_smul z (1 : Γ(X,U))
    rw [he, q.map_smul, LinearEquiv.map_smul]
    rfl
  have hc := congrArg (f.equiv U le_rfl).symm hab
  have hsec : H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      e.equiv U le_rfl (sectionCoordinate X H U e s) := by
    simp [sectionCoordinate]
  rw [hsec, hscalar a, hscalar b] at hc
  have hbase := mul_left_cancel₀ hn hc
  apply LinearMap.ext
  intro z
  obtain ⟨r, rfl⟩ := (e.equiv U le_rfl).surjective z
  apply (f.equiv U le_rfl).symm.injective
  rw [hscalar a, hscalar b, hbase]

/-- Equal orders make the quotient and its inverse regular on a normal affine. -/
private lemma local_ratio_unit (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H J : X.Modules) (hH : IsLineBundle X H) (hJ : IsLineBundle X J)
    (s : Γ(H, ⊤)) (t : Γ(J, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0)
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X,U)] (e : LocalFrame X H U) (f : LocalFrame X J U)
    (hord : ∀ x ∈ U, Scheme.ord (sectionCoefficient X H U e s) x =
      Scheme.ord (sectionCoefficient X J U f t) x) :
    ∃ b : Γ(X,U)ˣ, (b : Γ(X,U)) * sectionCoordinate X H U e s =
      sectionCoordinate X J U f t := by
  let a := sectionCoefficient X H U e s
  let c := sectionCoefficient X J U f t
  have ha : a ≠ 0 := coefficient_ne_zero X H hH s hs U e
  have hc : c ≠ 0 := coefficient_ne_zero X J hJ t ht U f
  have hca : ∀ x ∈ U, 0 ≤ Scheme.ord (c / a) x := by
    intro x hx
    have hmul : c / a * a = c := div_mul_cancel₀ c ha
    have heq := congrArg (fun z : X.functionField => Scheme.ord z x) hmul
    rw [Scheme.ord_mul (div_ne_zero hc ha) ha] at heq
    have h := hord x hx
    change Scheme.ord a x = Scheme.ord c x at h
    omega
  have hac : ∀ x ∈ U, 0 ≤ Scheme.ord (a / c) x := by
    intro x hx
    have hmul : a / c * c = a := div_mul_cancel₀ a hc
    have heq := congrArg (fun z : X.functionField => Scheme.ord z x) hmul
    rw [Scheme.ord_mul (div_ne_zero ha hc) hc] at heq
    have h := hord x hx
    change Scheme.ord a x = Scheme.ord c x at h
    omega
  obtain ⟨b, hb⟩ := (normal_affine_order_criterion X U hU (c / a)).mp hca
  obtain ⟨d, hd⟩ := (normal_affine_order_criterion X U hU (a / c)).mp hac
  have hbd : b * d = 1 := by
    apply X.germToFunctionField_injective U
    rw [map_mul, hb, hd, map_one]
    field_simp
  refine ⟨⟨b, d, hbd, by rw [mul_comm]; exact hbd⟩, ?_⟩
  apply X.germToFunctionField_injective U
  change X.germToFunctionField U (b * sectionCoordinate X H U e s) = c
  rw [map_mul, hb]
  change c / a * a = c
  exact div_mul_cancel₀ c ha

/-- A natural linear map defined on all subopens of a given open. -/
private structure LocalMap (X : Scheme.{u}) (H J : X.Modules) (U : X.Opens) where
  app (V : X.Opens) (hVU : V ≤ U) : Γ(H,V) →ₗ[Γ(X,V)] Γ(J,V)
  naturality (V W : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (z : Γ(H,V)) :
    J.presheaf.map (homOfLE hWV).op (app V hVU z) =
      app W (hWV.trans hVU) (H.presheaf.map (homOfLE hWV).op z)

private def ratioLocalMap (X : Scheme.{u}) (H J : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) (f : LocalFrame X J U) (b : Γ(X,U)) :
    LocalMap X H J U where
  app V hVU := (f.equiv V hVU).toLinearMap.comp
    ((LinearMap.mulLeft Γ(X,V) (X.presheaf.map (homOfLE hVU).op b)).comp
      (e.equiv V hVU).symm.toLinearMap)
  naturality V W hWV hVU z := by
    change J.presheaf.map (homOfLE hWV).op
      (f.equiv V hVU (X.presheaf.map (homOfLE hVU).op b * (e.equiv V hVU).symm z)) = _
    rw [f.naturality, map_mul]
    have he : X.presheaf.map (homOfLE hWV).op ((e.equiv V hVU).symm z) =
        (e.equiv W (hWV.trans hVU)).symm (H.presheaf.map (homOfLE hWV).op z) := by
      apply (e.equiv W (hWV.trans hVU)).injective
      rw [← e.naturality V W hWV hVU, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [he]
    change f.equiv W (hWV.trans hVU)
      (X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU).op b) * _) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

private lemma ratioLocalMap_section (X : Scheme.{u}) (H J : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) (f : LocalFrame X J U) (b : Γ(X,U))
    (s : Γ(H,⊤)) (t : Γ(J,⊤))
    (hb : b * sectionCoordinate X H U e s = sectionCoordinate X J U f t)
    (V : X.Opens) (hVU : V ≤ U) :
    (ratioLocalMap X H J U e f b).app V hVU
      (H.presheaf.map (homOfLE le_top).op s) =
      J.presheaf.map (homOfLE le_top).op t := by
  have hb' := congrArg (X.presheaf.map (homOfLE hVU).op) hb
  rw [map_mul, coordinate_restrict, coordinate_restrict] at hb'
  change f.equiv V hVU (_ * (e.equiv V hVU).symm _) = _
  change X.presheaf.map (homOfLE hVU).op b *
      (e.equiv V hVU).symm (H.presheaf.map (homOfLE le_top).op s) =
      (f.equiv V hVU).symm (J.presheaf.map (homOfLE le_top).op t) at hb'
  rw [hb', LinearEquiv.apply_symm_apply]

/-- Morphisms between lines on an integral scheme are rigidified by a nonzero section. -/
private lemma hom_rigid (X : Scheme.{u}) [IsIntegral X] (H J : X.Modules)
    (hH : IsLineBundle X H) (hJ : IsLineBundle X J)
    (s : Γ(H,⊤)) (hs : s ≠ 0) (a b : H ⟶ J)
    (hab : a.app ⊤ s = b.app ⊤ s) : a = b := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  apply J.isSheaf.section_ext
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := hH x
  obtain ⟨W, hxW, ⟨f⟩⟩ := hJ x
  let Z := U ⊓ V ⊓ W
  have hZU : Z ≤ U := inf_le_left.trans inf_le_left
  have hZV : Z ≤ V := inf_le_left.trans inf_le_right
  have hZW : Z ≤ W := inf_le_right
  let : Nonempty Z := ⟨⟨x, ⟨hx, hxV⟩, hxW⟩⟩
  let eZ := restrictLocalFrame X H V Z hZV (localFrameOfIso X H V e)
  let fZ := restrictLocalFrame X J W Z hZW (localFrameOfIso X J W f)
  let aZ : Γ(H,Z) →ₗ[Γ(X,Z)] Γ(J,Z) := (a.val.app (op Z)).hom
  let bZ : Γ(H,Z) →ₗ[Γ(X,Z)] Γ(J,Z) := (b.val.app (op Z)).hom
  have habZ : aZ = bZ := by
    apply frame_linear_ext X H J hH s hs Z eZ fZ
    have h := congrArg (J.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op) hab
    exact (PresheafOfModules.naturality_apply a.val (homOfLE (le_top : Z ≤ ⊤)).op s).trans
      (h.trans (PresheafOfModules.naturality_apply b.val (homOfLE (le_top : Z ≤ ⊤)).op s).symm)
  refine ⟨Z, hZU, ⟨⟨hx, hxV⟩, hxW⟩, ?_⟩
  have ha := PresheafOfModules.naturality_apply a.val (homOfLE hZU).op z
  have hb := PresheafOfModules.naturality_apply b.val (homOfLE hZU).op z
  exact ha.symm.trans ((congrArg (fun q : Γ(H,Z) →ₗ[Γ(X,Z)] Γ(J,Z) =>
    q (H.presheaf.map (homOfLE hZU).op z)) habZ).trans hb)

private lemma local_maps_agree (X : Scheme.{u}) [IsIntegral X]
    (H J : X.Modules) (hH : IsLineBundle X H) (s : Γ(H,⊤)) (t : Γ(J,⊤))
    (hs : s ≠ 0) {U V W : X.Opens}
    (e : LocalFrame X H U) (f : LocalFrame X J U)
    (a : LocalMap X H J U) (b : LocalMap X H J V)
    (hWU : W ≤ U) (hWV : W ≤ V)
    (ha : a.app W hWU (H.presheaf.map (homOfLE le_top).op s) =
      J.presheaf.map (homOfLE le_top).op t)
    (hb : b.app W hWV (H.presheaf.map (homOfLE le_top).op s) =
      J.presheaf.map (homOfLE le_top).op t) :
    a.app W hWU = b.app W hWV := by
  by_cases hW : Nonempty W
  · let := hW
    exact frame_linear_ext X H J hH s hs W
      (restrictLocalFrame X H U W hWU e) (restrictLocalFrame X J U W hWU f)
      _ _ (ha.trans hb.symm)
  · apply LinearMap.ext
    intro z
    apply J.isSheaf.section_ext
    intro x hx
    exact (hW ⟨⟨x, hx⟩⟩).elim

private abbrev res (X : Scheme.{u}) (H : X.Modules) {U V : X.Opens}
    (hVU : V ≤ U) (z : Γ(H,U)) : Γ(H,V) :=
  H.presheaf.map (homOfLE hVU).op z

@[simp] private lemma res_res (X : Scheme.{u}) (H : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (z : Γ(H,U)) :
    res X H hWV (res X H hVU z) = res X H (hWV.trans hVU) z := by
  dsimp [res]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma map_res (X : Scheme.{u}) (H J : X.Modules) {U : X.Opens}
    (a : LocalMap X H J U) (V W : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (z : Γ(H,V)) :
    res X J hWV (a.app V hVU z) = a.app W (hWV.trans hVU) (res X H hWV z) :=
  a.naturality V W hWV hVU z

private lemma glue_maps (X : Scheme.{u}) [IsIntegral X]
    (H J : X.Modules) (hH : IsLineBundle X H) (s : Γ(H,⊤)) (t : Γ(J,⊤)) (hs : s ≠ 0)
    {ι : Type v} (U : ι → X.Opens) (hcover : (⊤ : X.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame X H (U i)) (f : ∀ i, LocalFrame X J (U i))
    (a : ∀ i, LocalMap X H J (U i))
    (ha : ∀ i V (hVU : V ≤ U i), (a i).app V hVU (res X H le_top s) = res X J le_top t) :
    ∃ q : H ⟶ J, q.app ⊤ s = t := by
  classical
  have hc (V : X.Opens) : V ≤ iSup (fun i ↦ V ⊓ U i) := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) by trivial))
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  have heq (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
      (a i).app W hi = (a j).app W hj :=
    local_maps_agree X H J hH s t hs (e i) (f i) (a i) (a j) hi hj
      (ha i W hi) (ha j W hj)
  have hex (V : X.Opens) (z : Γ(H,V)) : ∃! y : Γ(J,V), ∀ i,
      res X J inf_le_left y = (a i).app (V ⊓ U i) inf_le_right (res X H inf_le_left z) := by
    apply TopCat.Sheaf.existsUnique_gluing' ⟨J.presheaf, J.isSheaf⟩
      (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left) (hc V)
    intro i j
    change res X J inf_le_left ((a i).app (V ⊓ U i) inf_le_right (res X H inf_le_left z)) =
      res X J inf_le_right ((a j).app (V ⊓ U j) inf_le_right (res X H inf_le_left z))
    rw [map_res X H J (a i), map_res X H J (a j)]
    simp only [res_res]
    rw [heq i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)]
  choose q hq hqu using hex
  have hq' (V W : X.Opens) (i : ι) (hWV : W ≤ V) (hWU : W ≤ U i) (z : Γ(H,V)) :
      res X J hWV (q V z) = (a i).app W hWU (res X H hWV z) := by
    have h := congrArg (res X J (le_inf hWV hWU)) (hq V z i)
    rw [res_res, map_res X H J (a i)] at h
    simpa only [res_res] using h
  have extJ (V : X.Opens) (y z : Γ(J,V))
      (hyz : ∀ i, res X J (inf_le_left : V ⊓ U i ≤ V) y = res X J inf_le_left z) : y = z :=
    TopCat.Sheaf.eq_of_locally_eq' ⟨J.presheaf, J.isSheaf⟩ (fun i ↦ V ⊓ U i)
      V (fun _ ↦ homOfLE inf_le_left) (hc V) y z hyz
  let ql (V : X.Opens) : Γ(H,V) →ₗ[Γ(X,V)] Γ(J,V) :=
    { toFun := q V
      map_add' := by
        intro z z'
        apply extJ V
        intro i
        simp only [hq, res, map_add]
      map_smul' := by
        intro r z
        apply extJ V
        intro i
        simp only [hq, res, Scheme.Modules.map_smul, LinearMap.map_smulₛₗ, RingHom.id_apply] }
  have hnat (V W : X.Opens) (hWV : W ≤ V) (z : Γ(H,V)) :
      res X J hWV (ql V z) = ql W (res X H hWV z) := by
    apply extJ W
    intro i
    change res X J inf_le_left (res X J hWV (q V z)) =
      res X J inf_le_left (q W (res X H hWV z))
    rw [res_res, hq' V (W ⊓ U i) i (inf_le_left.trans hWV) inf_le_right, hq]
    simp only [res_res]
  let Q : H ⟶ J :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (ql V.unop)
        naturality := by
          intro V W g
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          exact (hnat V.unop W.unop g.unop.le z).symm } }
  refine ⟨Q, ?_⟩
  apply extJ ⊤
  intro i
  change res X J inf_le_left (q ⊤ s) = _
  rw [hq]
  exact ha i (⊤ ⊓ U i) inf_le_right

private lemma equal_divisor_hom (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (H J : X.Modules) (hH : IsLineBundle X H) (hJ : IsLineBundle X J)
    {ι : Type v} {κ : Type w} (C : NormalFrameCover X H ι) (E : NormalFrameCover X J κ)
    (s : Γ(H,⊤)) (t : Γ(J,⊤)) (D : X →₀ ℤ) (hs : s ≠ 0) (ht : t ≠ 0)
    (hD : MatchesSectionOrder X H C s D) (hD' : MatchesSectionOrder X J E t D) :
    ∃ q : H ⟶ J, q.app ⊤ s = t := by
  classical
  have hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ (e : LocalFrame X H U) (f : LocalFrame X J U) (b : Γ(X,U)ˣ),
        (b : Γ(X,U)) * sectionCoordinate X H U e s = sectionCoordinate X J U f t := by
    intro x
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (C.covers (show x ∈ (⊤ : X.Opens) by trivial))
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (E.covers (show x ∈ (⊤ : X.Opens) by trivial))
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ C.opens i ⊓ E.opens j from ⟨hxi, hxj⟩)
    let : Nonempty U := ⟨⟨x, hxU⟩⟩
    let : IsIntegrallyClosed Γ(X,U) := hN U hU
    have hUC : U ≤ C.opens i := hUV.trans inf_le_left
    have hUE : U ≤ E.opens j := hUV.trans inf_le_right
    let e := restrictLocalFrame X H (C.opens i) U hUC (C.frame i)
    let f := restrictLocalFrame X J (E.opens j) U hUE (E.frame j)
    have hord : ∀ y ∈ U, Scheme.ord (sectionCoefficient X H U e s) y =
        Scheme.ord (sectionCoefficient X J U f t) y := by
      intro y hy
      rw [coefficient_restrict, coefficient_restrict]
      exact (hD i y (hUC hy)).symm.trans (hD' j y (hUE hy))
    obtain ⟨b, hb⟩ := local_ratio_unit X H J hH hJ s t hs ht U hU e f hord
    exact ⟨U, hxU, hU, e, f, b, hb⟩
  choose U hxU hU e f b hb using hlocal
  have hc : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  exact glue_maps X H J hH s t hs U hc e f
    (fun x ↦ ratioLocalMap X H J (U x) (e x) (f x) (b x))
    (fun x V hVU ↦ ratioLocalMap_section X H J (U x) (e x) (f x) (b x) s t (hb x) V hVU)

/-- Equality of the actual section divisors determines the unique everywhere
invertible sheaf map carrying one nonzero section to the other. -/
theorem equal_divisor_rigidified_isomorphism :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X],
    ArithmeticThetaCurveDegree.OneDimensionalCharts X →
    ArithmeticThetaNormalizedSections.NormalAffine X →
    ∀ (H J : X.Modules), ArithmeticThetaNormalizedSections.IsLineBundle X H →
    ArithmeticThetaNormalizedSections.IsLineBundle X J →
    ∀ (ι : Type v) (κ : Type w)
      (C : ArithmeticThetaLineRoot.NormalFrameCover X H ι)
      (E : ArithmeticThetaLineRoot.NormalFrameCover X J κ)
      (s : H.presheaf.obj (Opposite.op ⊤)) (t : J.presheaf.obj (Opposite.op ⊤)) (D : X →₀ ℤ),
    s ≠ 0 → t ≠ 0 → ArithmeticThetaSectionOrder.MatchesSectionOrder X H C s D →
    ArithmeticThetaSectionOrder.MatchesSectionOrder X J E t D →
    ∃! e : CategoryTheory.Iso H J, e.hom.app ⊤ s = t := by
  intro X _ _ _hcurve hN H J hH hJ ι κ C E s t D hs ht hD hD'
  obtain ⟨q, hq⟩ := equal_divisor_hom X hN H J hH hJ C E s t D hs ht hD hD'
  obtain ⟨r, hr⟩ := equal_divisor_hom X hN J H hJ hH E C t s D ht hs hD' hD
  have hqr : q ≫ r = 𝟙 H := by
    apply hom_rigid X H H hH hH s hs
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply, hq] using hr
  have hrq : r ≫ q = 𝟙 J := by
    apply hom_rigid X J J hJ hJ t ht
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply, hr] using hq
  refine ⟨⟨q, r, hqr, hrq⟩, hq, ?_⟩
  intro e he
  apply CategoryTheory.Iso.ext
  exact hom_rigid X H J hH hJ s hs e.hom q (he.trans hq.symm)

end ArithmeticThetaGeometricPrerequisites

#print axioms ArithmeticThetaGeometricPrerequisites.equal_divisor_rigidified_isomorphism




