import GlobalFamilyDiscriminantR0180
import GlobalFamilyTorsionValueR0180
import GlobalLevelCyclicQuotientR0180

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaOpenHodgeR0180
namespace OpenLevelNormalizedHodgePowerR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaTensorPower ArithmeticThetaRelativeIsogenyHodgeR0172
open GlobalLevelCyclicQuotientR0180

lemma family_hodge_isIso {S : Type u} [CommRing S] {E F : EllipticFamily S}
    (f : Pointed S E F) [Etale f.map] : IsIso (familyHodgeMap f) := by
  letI := F.smooth
  letI := EtaleHodgePullbackIsomorphismR0172.differentialMap_isIso_etale
    F.projection E.projection f.map f.over_eq
  unfold familyHodgeMap
  infer_instance

lemma exponents (N : ℕ) (hN : Even N) :
    48 ∣ (1 + 12*N)^2 - 1 ∧ 24 * (((1+12*N)^2-1)/48) = ((1+12*N)^2-1)/2 := by
  obtain ⟨t, rfl⟩ := hN
  have he : (1 + 12*(t+t))^2-1 = 48*(t*(1+12*t)) := by
    have h : (1 + 12*(t+t))^2 = 48*(t*(1+12*t)) + 1 := by ring
    omega
  rw [he]
  constructor
  · exact dvd_mul_right _ _
  · omega

variable {S : Type u} [CommRing S] (E : EllipticFamily S)

lemma level_lift_conditions {L : ℕ} (hL : 0 < L) (A : FamilyLevel S E L)
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hdiv : m*N ∣ L)
    (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) :
    let p := (E.law.nsmul (𝟙 _) (L/m) A.x).val
    let q := (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (L/(m*N)*b.val) A.x)
      (E.law.nsmul (𝟙 _) (L/N*a.val) A.y)).val
    (∃ i : Fin m, q ≫ E.law.schemeNsmul N = p ≫ E.law.schemeNsmul i.val) ∧
    ∀ i : Fin m, Disjoint (Set.range q) (Set.range (p ≫ E.law.schemeNsmul i.val)) := by
  dsimp only
  letI := sectionGroup E
  have hx : A.x ^ L = 1 := by
    have h := A.killed_x
    rw [comp_nsmul, nsmul_pow] at h
    exact Subtype.ext h
  have hy : A.y ^ L = 1 := by
    have h := A.killed_y
    rw [comp_nsmul, nsmul_pow] at h
    exact Subtype.ext h
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m N) hdiv
  have hNL : N ∣ L := dvd_trans (dvd_mul_left N m) hdiv
  have hc : L / m * m = L := Nat.div_mul_cancel hmL
  have hd : L / N * N = L := Nat.div_mul_cancel hNL
  have hq : L / (m*N) * (m*N) = L := Nat.div_mul_cancel hdiv
  have hcpos : 0 < L / m := Nat.div_pos (Nat.le_of_dvd hL hmL) hm
  have hdpos : 0 < L / N := Nat.div_pos (Nat.le_of_dvd hL hNL) hN
  have hqpos : 0 < L / (m*N) := Nat.div_pos (Nat.le_of_dvd hL hdiv) (Nat.mul_pos hm hN)
  have hqc : L / (m*N) * N = L / m := by nlinarith [hc, hq]
  have hc_lt (i : Fin m) : L / m * i.val < L := by
    have := Nat.mul_lt_mul_of_pos_left i.isLt hcpos
    omega
  have hax : L/N * a.val < L := by
    have := Nat.mul_lt_mul_of_pos_left a.isLt hdpos
    omega
  have hbx : L/(m*N) * b.val < L := by
    have hh := Nat.mul_lt_mul_of_pos_left b.isLt hqpos
    have hh' : L/m ≤ L := Nat.div_le_self L m
    omega
  constructor
  · refine ⟨⟨b.val % m, Nat.mod_lt _ hm⟩, ?_⟩
    change (E.law.mul (𝟙 (Base S))
      (E.law.nsmul (𝟙 (Base S)) (L/(m*N)*b.val) A.x)
      (E.law.nsmul (𝟙 (Base S)) (L/N*a.val) A.y)).val ≫ E.law.schemeNsmul N =
        (E.law.nsmul (𝟙 (Base S)) (L/m) A.x).val ≫ E.law.schemeNsmul (b.val % m)
    rw [comp_nsmul, nsmul_comp]
    apply congrArg Subtype.val
    simp only [nsmul_pow]
    change (A.x ^ (L/(m*N)*b.val) * A.y ^ (L/N*a.val)) ^ N = A.x ^ (L/m*(b.val%m))
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have e₁ : L/(m*N)*b.val*N = L/m*b.val := by nlinarith [hqc]
    have e₂ : L/N*a.val*N = L*a.val := by nlinarith [hd]
    rw [e₁, e₂, pow_mul A.y, hy, one_pow, mul_one]
    have hp : (A.x ^ (L/m)) ^ m = 1 := by rw [← pow_mul, hc, hx]
    simpa only [← pow_mul] using (pow_mod hp b.val).symm
  · intro i
    change Disjoint (Set.range (E.law.mul (𝟙 (Base S))
      (E.law.nsmul (𝟙 (Base S)) (L/(m*N)*b.val) A.x)
      (E.law.nsmul (𝟙 (Base S)) (L/N*a.val) A.y)).val)
      (Set.range ((E.law.nsmul (𝟙 (Base S)) (L/m) A.x).val ≫ E.law.schemeNsmul i.val))
    rw [nsmul_comp]
    have hne : L/(m*N)*b.val ≠ L/m*i.val ∨ L/N*a.val ≠ 0 := by
      by_contra h
      push Not at h
      have ha : a.val = 0 := (Nat.mul_eq_zero.mp h.2).resolve_left (Nat.ne_of_gt hdpos)
      have hb : b.val ≠ 0 := hab.resolve_left (not_not_intro ha)
      have hb' : b.val = N*i.val := by
        apply Nat.eq_of_mul_eq_mul_left hqpos
        nlinarith [h.1, hqc]
      have hi : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi
        apply hb
        simpa [hi] using hb'
      have := b.isLt
      nlinarith
    simpa only [E.law.nsmul_zero, E.law.mul_one] using
      coordinate_disjoint E hL A (L/(m*N)*b.val) (L/N*a.val) (L/m*i.val) 0
        hbx hax (hc_lt i) hL hne

lemma quotient_lift {m : ℕ} (_hm : 0 < m) (P : Cyclic E m)
    (p : Base S ⟶ E.curve) (hP : P.point = p)
    (Q : Quotient S E m p) (N : ℕ) (q : Base S ⟶ E.curve)
    (hq : q ≫ E.projection = 𝟙 _)
    (ht : ∃ i : Fin m, q ≫ E.law.schemeNsmul N = P.point ≫ E.law.schemeNsmul i.val)
    (ha : ∀ i : Fin m, Disjoint (Set.range q)
      (Set.range (P.point ≫ E.law.schemeNsmul i.val))) :
    (q ≫ Q.arrow.map) ≫ Q.target.law.schemeNsmul N = zero Q.target ∧
    Disjoint (Set.range (q ≫ Q.arrow.map)) (Set.range (zero Q.target)) := by
  have hkernel : (zero Q.target).ker.comap Q.arrow.map =
      ⨅ i : Fin m, (P.point ≫ E.law.schemeNsmul i.val).ker := by rw [hP]; exact Q.kernel
  letI := E.proper
  letI := Q.target.proper
  have ho : zero Q.target ≫ Q.target.projection = 𝟙 _ :=
    (Q.target.law.one (𝟙 _)).property
  haveI : IsClosedImmersion (zero Q.target ≫ Q.target.projection) := by rw [ho]; infer_instance
  haveI : IsClosedImmersion (zero Q.target) := IsClosedImmersion.of_comp _ Q.target.projection
  have hkill (i : Fin m) : multiple E P i ≫ Q.arrow.map = zero Q.target := by
    have hle : (zero Q.target).ker ≤ (multiple E P i ≫ Q.arrow.map).ker := by
      rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le, hkernel]
      exact iInf_le _ i
    let a := IsClosedImmersion.lift (zero Q.target) (multiple E P i ≫ Q.arrow.map) hle
    have hfac : a ≫ zero Q.target = multiple E P i ≫ Q.arrow.map :=
      IsClosedImmersion.lift_fac _ _ _
    have hid : a = 𝟙 _ := by
      have he := congrArg (fun f => f ≫ Q.target.projection) hfac
      simpa only [Category.assoc, ho, Category.comp_id, Q.arrow.over_eq, multiple_over] using he
    rw [← hfac, hid, Category.id_comp]
  constructor
  · letI := E.law.pointGroup (𝟙 (Base S))
    letI := Q.target.law.pointGroup (𝟙 (Base S))
    obtain ⟨i, hi⟩ := ht
    have he := (pointHom E Q.arrow Q.hom (𝟙 (Base S))).map_pow
      (⟨q, hq⟩ : sections E) N
    simp only [← nsmul_pow] at he
    have hv := congrArg Subtype.val he
    change (E.law.nsmul (𝟙 _) N ⟨q, hq⟩).val ≫ Q.arrow.map =
      (Q.target.law.nsmul (𝟙 _) N (imagePoint Q.arrow (𝟙 _) ⟨q, hq⟩)).val at hv
    rw [← comp_nsmul, ← comp_nsmul] at hv
    exact hv.symm.trans (by rw [hi]; exact hkill i)
  · let s (i : Fin m) := multiple E P i
    let f : (∐ fun _ : Fin m => Base S) ⟶ E.curve := Sigma.desc s
    haveI (i : Fin m) : IsClosedImmersion (s i) := by
      haveI : IsClosedImmersion (s i ≫ E.projection) := by
        change IsClosedImmersion (multiple E P i ≫ E.projection)
        rw [multiple_over]; infer_instance
      exact IsClosedImmersion.of_comp _ E.projection
    haveI : IsClosedImmersion f :=
      ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
        (fun i j hij => P.disjoint i j hij)
    have hfker : (⨅ i : Fin m, (P.point ≫ E.law.schemeNsmul i.val).ker) = f.ker := by
      rw [← f.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : Fin m => Base S))]
      change (⨅ i, (s i).ker) = _
      congr 1
      funext i
      congr 1
      exact (Sigma.ι_desc s i).symm
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ he
    have hx : q x ∈ ((zero Q.target).ker.comap Q.arrow.map).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change Q.arrow.map (q x) ∈ ((zero Q.target).ker.support : Set Q.target.curve)
      rw [Scheme.Hom.support_ker, (zero Q.target).isClosedEmbedding.isClosed_range.closure_eq]
      exact ⟨y, he.symm⟩
    rw [hkernel, hfker] at hx
    change q x ∈ (f.ker.support : Set E.curve) at hx
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨i, t, ht⟩ := (sigmaOpenCover (fun _ : Fin m => Base S)).exists_eq z
    have ht' : Sigma.ι (fun _ : Fin m => Base S) i t = z := ht
    have he' : multiple E P i t = q x := by
      calc
        multiple E P i t = (Sigma.ι (fun _ : Fin m => Base S) i ≫ f) t := by rw [Sigma.ι_desc]
        _ = q x := by change f (Sigma.ι (fun _ : Fin m => Base S) i t) = q x; rw [ht', hz]
    exact (Set.disjoint_iff_forall_ne.mp (ha i)) ⟨x, rfl⟩ ⟨t, rfl⟩ he'.symm

open InitialHodgeSection GlobalFamilyDiscriminantR0180
open HodgeBaseChange (hom_res frame_restrict)

lemma local_frames {X : Scheme.{u}} (H : X.Modules) (hH : Scheme.Modules.IsInvertible H)
    (x : X) : ∃ (U : X.Opens) (s : Γ(H, U)), x ∈ U ∧ IsFrame H U s := by
  obtain ⟨U, hx, ⟨e⟩⟩ := hH.1 x
  have hunit : IsFrame (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤ (1 : Γ(U.toScheme, ⊤)) := by
    intro V hV
    change Function.Bijective (fun a : Γ(U.toScheme, V) => a *
      U.toScheme.presheaf.map (homOfLE hV).op 1)
    simp only [map_one, mul_one]
    exact ⟨fun _ _ h => h, fun a => ⟨a, rfl⟩⟩
  obtain ⟨s, hs, _⟩ := frame_lift_open U.ι H _ e (1 : Γ(U.toScheme, ⊤)) hunit
  exact ⟨U.ι.opensRange, s, by simpa only [Scheme.Opens.opensRange_ι] using hx, hs⟩

lemma frame_coefficient_unit {X : Scheme.{u}} (H : X.Modules) {U : X.Opens}
    (s d : Γ(H, U)) (hs : IsFrame H U s) (hd : IsFrame H U d)
    (a : Γ(X, U)) (ha : d = a • s) : IsUnit a := by
  obtain ⟨b, hb⟩ := (hd U le_rfl).2 s
  change b • res H le_rfl d = s at hb
  rw [res_self, ha, smul_smul] at hb
  have hab : b*a = 1 := (hs U le_rfl).1 (by simpa only [res_self, one_smul] using hb)
  exact ⟨⟨a, b, by simpa [mul_comm] using hab, hab⟩, rfl⟩

lemma formula_compare {X : Scheme.{u}} (H J : X.Modules) (f : H ⟶ J)
    (e w : ℕ) (hw : 24*e = w) (U : X.Opens) (η ξ : Γ(H, U))
    (hη : IsFrame H U η) (a b : Γ(X, U))
    (he : a • tensorPowerSection X H 24 U η = b • tensorPowerSection X H 24 U ξ) :
    a^e • tensorPowerSection X J w U (f.app U η) =
      b^e • tensorPowerSection X J w U (f.app U ξ) := by
  obtain ⟨t, ht⟩ := (hη U le_rfl).2 ξ
  rw [res_self] at ht
  rw [← ht, tensor_smul, smul_smul] at he
  have ha : a = b*t^24 := ((tensor_frame H η hη 24) U le_rfl).1
    (by simpa only [res_self] using he)
  rw [← ht, Scheme.Modules.Hom.app_smul, tensor_smul, smul_smul, ha, mul_pow, ← pow_mul, hw]

lemma formula_restrict {X : Scheme.{u}} (H J : X.Modules) (f : H ⟶ J)
    (e w : ℕ) {U V : X.Opens} (h : V ≤ U) (η : Γ(H, U)) (a : Γ(X, U)) :
    res (tensorPower X J w) h (a^e • tensorPowerSection X J w U (f.app U η)) =
      (X.presheaf.map (homOfLE h).op a)^e •
        tensorPowerSection X J w V (f.app V (res H h η)) := by
  rw [res_smul, map_pow]
  change _ • (tensorPower X J w).presheaf.map (homOfLE h).op _ = _
  rw [tensorPowerSection_restrict, ← hom_res]
  rfl

/-- A tensor power of a framed higher tensor section is glued in the original
line. Its formula holds in every local frame, including on empty opens. -/
lemma normalized_section {X : Scheme.{u}} (H J : X.Modules)
    (hH : Scheme.Modules.IsInvertible H) (f : H ⟶ J) [IsIso f]
    (e w : ℕ) (hw : 24*e = w)
    (d : Γ(tensorPower X H 24, ⊤)) (hd : IsFrame (tensorPower X H 24) ⊤ d)
    (r : Γ(X, ⊤)) (hr : IsUnit r) :
    ∃! F : Γ(tensorPower X J w, ⊤), IsFrame (tensorPower X J w) ⊤ F ∧
      ∀ (U : X.Opens) (η : Γ(H, U)) (a : Γ(X, U)), IsFrame H U η →
      res (tensorPower X H 24) le_top d = a • tensorPowerSection X H 24 U η →
      res (tensorPower X J w) le_top F =
        (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) •
          tensorPowerSection X J w U (f.app U η) := by
  classical
  choose U η hx hη using local_frames H hH
  have hc : (⨆ x, U x) = ⊤ := top_unique (fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
  have ha : ∀ x, ∃ a : Γ(X, U x), res (tensorPower X H 24) le_top d =
      a • tensorPowerSection X H 24 (U x) (η x) := by
    intro x
    obtain ⟨a, ha⟩ := (tensor_frame H (η x) (hη x) 24 (U x) le_rfl).2
      (res (tensorPower X H 24) le_top d)
    exact ⟨a, by simpa only [res_self] using ha.symm⟩
  choose a ha using ha
  let t (x : X) := a x ^ e • tensorPowerSection X J w (U x) (f.app (U x) (η x))
  have ht : TopCat.Presheaf.IsCompatible (tensorPower X J w).presheaf U t := by
    intro x y
    change res _ inf_le_left (t x) = res _ inf_le_right (t y)
    rw [show t x = _ from rfl, show t y = _ from rfl, formula_restrict, formula_restrict]
    apply formula_compare H J f e w hw _ _ _ (frame_restrict H inf_le_left _ (hη x))
    have he := (congrArg (res (tensorPower X H 24) (show U x ⊓ U y ≤ U x from inf_le_left)) (ha x)).symm.trans
      ((by rw [res_res, res_res] :
        res (tensorPower X H 24) inf_le_left (res (tensorPower X H 24) le_top d) =
        res (tensorPower X H 24) inf_le_right (res (tensorPower X H 24) le_top d)).trans
      (congrArg (res (tensorPower X H 24) (show U x ⊓ U y ≤ U y from inf_le_right)) (ha y)))
    simpa only [res_smul, res, Scheme.Modules.map_smul, tensorPowerSection_restrict] using he
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(tensorPower X J w).presheaf, (tensorPower X J w).isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) hc.ge t ht
  have formula (V : X.Opens) (ξ : Γ(H, V)) (b : Γ(X, V)) (hξ : IsFrame H V ξ)
      (hb : res (tensorPower X H 24) le_top d = b • tensorPowerSection X H 24 V ξ) :
      res (tensorPower X J w) le_top s =
        b^e • tensorPowerSection X J w V (f.app V ξ) := by
    apply sections_eq_local
    intro x hxV
    refine ⟨V ⊓ U x, ⟨hxV, hx x⟩, inf_le_left, ?_⟩
    have hs' : res (tensorPower X J w) le_top s = t x := hs x
    have hl : res (tensorPower X J w) (show V ⊓ U x ≤ V from inf_le_left) (res (tensorPower X J w) le_top s) =
        res (tensorPower X J w) inf_le_right (t x) := by rw [← hs', res_res, res_res]
    rw [hl, show t x = _ from rfl, formula_restrict, formula_restrict]
    apply formula_compare H J f e w hw _ _ _ (frame_restrict H inf_le_right _ (hη x))
    have he := (congrArg (res (tensorPower X H 24) (show V ⊓ U x ≤ U x from inf_le_right)) (ha x)).symm.trans
      ((by rw [res_res, res_res] :
        res (tensorPower X H 24) inf_le_right (res (tensorPower X H 24) le_top d) =
        res (tensorPower X H 24) inf_le_left (res (tensorPower X H 24) le_top d)).trans
      (congrArg (res (tensorPower X H 24) (show V ⊓ U x ≤ V from inf_le_left)) hb))
    simpa only [res_smul, res, Scheme.Modules.map_smul, tensorPowerSection_restrict] using he
  have hsframe : IsFrame (tensorPower X J w) ⊤ s := by
    apply frame_glue_cover _ U hc
    intro x
    rw [formula (U x) (η x) (a x) (hη x) (ha x)]
    have hau := frame_coefficient_unit _ _ _ (tensor_frame H (η x) (hη x) 24)
      (frame_restrict _ le_top d hd) (a x) (ha x)
    exact unit_frame _ _ (tensor_frame J _ (frame_iso (asIso f) _ (hη x)) w) ((hau.pow e).unit)
  refine ⟨r • s, ⟨unit_frame _ s hsframe hr.unit, ?_⟩, ?_⟩
  · intro V ξ b hξ hb
    rw [res_smul, formula V ξ b hξ hb, smul_smul]
  · intro F hF
    apply sections_eq_local
    intro x _
    refine ⟨U x, hx x, le_top, ?_⟩
    rw [hF.2 (U x) (η x) (a x) (hη x) (ha x), res_smul,
      formula (U x) (η x) (a x) (hη x) (ha x), smul_smul]

end OpenLevelNormalizedHodgePowerR0180
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open OpenLevelNormalizedHodgePowerR0180

/-- The normalized source section on the entire open full-level base. -/
theorem open_level_normalized_hodge_power :
∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (hLeven : Even L) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (hmNL : m*N ∣ L), ∃ (Q : ArithmeticThetaOpenHodgeR0180.Quotient A.quotient.ring (ArithmeticThetaOpenHodgeR0180.levelFamily k L A) m (ArithmeticThetaOpenHodgeR0180.kernelPoint k L A m)) (d : (ArithmeticThetaOpenHodgeR0180.power Q.target 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaOpenHodgeR0180.IsD2 Q.target d ∧ CategoryTheory.IsIso (ArithmeticThetaOpenHodgeR0180.familyHodgeMap Q.arrow) ∧ ∀ (a b : Fin N), a.val ≠ 0 ∨ b.val ≠ 0 → ∃! z : A.quotient.ring × (ArithmeticThetaOpenHodgeR0180.power (ArithmeticThetaOpenHodgeR0180.levelFamily k L A) (((1+12*N)^2-1)/2)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaOpenHodgeR0180.IsKatoValue Q.target (1+12*N) (CategoryTheory.CategoryStruct.comp (ArithmeticThetaOpenHodgeR0180.liftPoint k L A m N a.val b.val) Q.arrow.map) z.1 ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaOpenHodgeR0180.power (ArithmeticThetaOpenHodgeR0180.levelFamily k L A) (((1+12*N)^2-1)/2)) ⊤ z.2 ∧ ArithmeticThetaOpenHodgeR0180.IsNormalizedPower k L A m N Q d z.1 z.2 := by
  intro k _ _ L hL hLeven A m N hm hmeven hN hNeven hmN hmNL
  classical
  let E := levelFamily k L A
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m N) hmNL
  obtain ⟨Q⟩ := global_level_cyclic_quotient k L hL hLeven A m hm hmL
  obtain ⟨d, hd, _⟩ := global_family_discriminant k A.quotient.ring A.quotient.smooth Q.target
  letI := Q.etale
  haveI : IsIso (familyHodgeMap Q.arrow) := family_hodge_isIso Q.arrow
  refine ⟨Q, d, hd, inferInstance, ?_⟩
  intro a b hab
  obtain ⟨P, hP⟩ := GlobalLevelCyclicQuotientR0180.cyclic_of_level E (by omega : 0 < L)
    A.marking m hm hmL
  have hP' : P.point = kernelPoint k L A m := hP
  have hl := level_lift_conditions E (by omega : 0 < L) A.marking m N hm hN hmNL a b hab
  have hp : liftPoint k L A m N a.val b.val ≫ E.projection = 𝟙 _ :=
    (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (L/(m*N)*b.val) A.marking.x)
      (E.law.nsmul (𝟙 _) (L/N*a.val) A.marking.y)).property
  have hpoint := quotient_lift E hm P (kernelPoint k L A m) hP' Q N
    (liftPoint k L A m N a.val b.val) hp
    (by simpa only [hP', kernelPoint, liftPoint] using hl.1)
    (by simpa only [hP', kernelPoint, liftPoint] using hl.2)
  have hc : 1 < 1+12*N := by omega
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    simpa [← Nat.mul_assoc] using
      (Nat.coprime_add_mul_left_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  have hcN : Nat.Coprime (1+12*N) N :=
    (Nat.coprime_add_mul_right_left 1 N 12).mpr (Nat.coprime_one_left N)
  obtain ⟨v, hv, hvuniq⟩ := global_family_torsion_value k A.quotient.ring A.quotient.smooth
    Q.target (1+12*N) N hc hc6 hN hcN
    (liftPoint k L A m N a.val b.val ≫ Q.arrow.map)
    (by rw [Category.assoc, Q.arrow.over_eq]; exact hp) hpoint.1 hpoint.2
  let w := ((1+12*N)^2-1)/2
  let e := ((1+12*N)^2-1)/48
  let r := scalar A.quotient.ring ((algebraMap k A.quotient.ring (m : k)⁻¹)^w * v)
  have hmu : IsUnit (algebraMap k A.quotient.ring (m : k)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))).map _
  have hr : IsUnit r := ((hmu.pow w).mul hv.1).map
    (Scheme.ΓSpecIso (CommRingCat.of A.quotient.ring)).inv.hom
  obtain ⟨F, hF, hFuniq⟩ := normalized_section (hodge Q.target) (hodge E)
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible Q.target)
    (familyHodgeMap Q.arrow) e w (exponents N hNeven).2 d hd.1 r hr
  refine ⟨(v,F), ⟨hv, hF.1, hF.2⟩, ?_⟩
  rintro ⟨v',F'⟩ ⟨hv', hframe', hformula'⟩
  have heq : v' = v := hvuniq v' hv'
  subst v'
  exact congrArg (fun s => (v,s)) (hFuniq F' ⟨hframe', hformula'⟩)

#print axioms open_level_normalized_hodge_power
end ArithmeticThetaOpenHodgeR0180
