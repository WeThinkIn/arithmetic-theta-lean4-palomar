module

public import OpenUnaryConstantNaturalityR0236
public import OpenIsogenyAlphaR0193

@[expose] public section

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticHalfLinesR0237
namespace OpenIsogenyAlphaConstantNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaOpenHodgeR0180.OpenLevelNormalizedHodgePowerR0180
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha
open ArithmeticThetaIsogenyHalfLinesR0193
open ArithmeticThetaArithmeticSectionsR0236.OpenUnaryConstantNaturality
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182

/-- Naturality of the intrinsic signed section, checked on the target atlas
with the same ordered marking on each Cartesian test. -/
lemma family_alpha_transport {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hz : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hn : ∀ n, F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n)
    (M : FamilyLevel R E 4) (N : FamilyLevel S F 4)
    (hx : N.x.val ≫ j = baseMap R S ρ ≫ M.x.val)
    (hy : N.y.val ≫ j = baseMap R S ρ ≫ M.y.val)
    (T : Atlas S F) (a : Γ(hodge E, ⊤)) (b : Γ(hodge F, ⊤))
    (ha : IsFamilyAlpha R E M a) (hb : IsFamilyAlpha S F N b) :
    transportSection (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hz) a = b := by
  apply sections_ext_cover (fun i => Base (T.chart i).ring)
    (fun i => baseMap S (T.chart i).ring (T.chart i).comparison.scalar)
    (fun i => (T.chart i).openImmersion) T.covers (hodge F) _ b
  intro i
  let C := T.chart i
  have hgeom := relative_curve_geometry C.ring C.equation
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  let V := composeTest ρ j hj hz hn C.comparison
  let B := liftMarking C.law C.originLaw C.comparison N
  have hbase : baseMap R C.ring V.scalar =
      baseMap S C.ring C.comparison.scalar ≫ baseMap R S ρ := by
    dsimp [V, composeTest, baseMap]
    rw [← Spec.map_comp]
  have hBx : B.x.val ≫ V.map = baseMap R C.ring V.scalar ≫ M.x.val := by
    change B.x.val ≫ (C.comparison.map ≫ j) = _
    rw [← Category.assoc, (show B.x.val ≫ C.comparison.map = _ from liftMarkPoint_map C.law C.comparison N.x), Category.assoc, hx, ← Category.assoc, ← hbase]
  have hBy : B.y.val ≫ V.map = baseMap R C.ring V.scalar ≫ M.y.val := by
    change B.y.val ≫ (C.comparison.map ≫ j) = _
    rw [← Category.assoc, (show B.y.val ≫ C.comparison.map = _ from liftMarkPoint_map C.law C.comparison N.y), Category.assoc, hy, ← Category.assoc, ← hbase]
  have he := RelativeAlphaNaturality.realizes_unique C.ring C.equation C.law 4 B
    (ha.2 C.ring C.equation C.law C.originLaw V B hBx hBy)
    (hb.2 C.ring C.equation C.law C.originLaw C.comparison B
      (liftMarkPoint_map C.law C.comparison N.x)
      (liftMarkPoint_map C.law C.comparison N.y))
  have hc := family_differential_composition ρ j hj hz C.comparison V rfl hbase
  change comparison V = composeComparison _ _ _ _ _ _ _ _ _ at hc
  have ht := transportSection_comp_eq (baseMap R S ρ)
    (baseMap S C.ring C.comparison.scalar) (baseMap R C.ring V.scalar) hbase
    (hodge E) (hodge F) (Hodge C.ring C.equation)
    (familyComparison ρ j hj hz) (comparison C.comparison) a
  rw [← hc] at ht
  have he' : transportSection (baseMap S C.ring C.comparison.scalar) _ _
      (comparison C.comparison)
      (transportSection (baseMap R S ρ) _ _ (familyComparison ρ j hj hz) a) =
      transportSection (baseMap S C.ring C.comparison.scalar) _ _
        (comparison C.comparison) b := ht.symm.trans (by
        simpa only [transportSection, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
          Scheme.Hom.preimage_top, InitialHodgeSection.res_self] using he)
  apply (ConcreteCategory.bijective_of_isIso ((comparison C.comparison).hom.app
    (baseMap S C.ring C.comparison.scalar ⁻¹ᵁ ⊤))).1
  simpa only [transportSection, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
    Scheme.Hom.preimage_top, InitialHodgeSection.res_self] using he'

#print axioms family_alpha_transport

/-- The same quotient construction on a general affine fully marked family. -/
structure FamilyAlpha (k : Type) [Field k] {R : Type} [CommRing R] [Algebra k R]
    (E : EllipticFamily R) {L : ℕ} (M : FamilyLevel R E L) (m : ℕ) where
  quotient : Quotient R E m (familyKernel E M m)
  marking : FamilyLevel R quotient.target 4
  marked : marking.x.val = familyLift E M m 4 0 1 ≫ quotient.arrow.map ∧
    marking.y.val = familyLift E M m 4 1 0 ≫ quotient.arrow.map
  alpha : Γ(hodge quotient.target, ⊤)
  intrinsic : IsFamilyAlpha R quotient.target marking alpha

def familySection {k R : Type} [Field k] [CommRing R] [Algebra k R]
    {E : EllipticFamily R} {L m : ℕ} {M : FamilyLevel R E L}
    (A : FamilyAlpha k E M m) : Γ(hodge E, ⊤) :=
  scalar R (algebraMap k R (m : k)⁻¹) • (familyHodgeMap A.quotient.arrow).app ⊤ A.alpha

lemma family_four_marking {R : Type} [CommRing R] (E : EllipticFamily R)
    {L m : ℕ} (A : FamilyLevel R E L) (hL : 0 < L) (hm : 0 < m)
    (hm4 : m * 4 ∣ L) (Q : Quotient R E m (familyKernel E A m)) :
    ∃ M : FamilyLevel R Q.target 4,
      M.x.val = familyLift E A m 4 0 1 ≫ Q.arrow.map ∧
      M.y.val = familyLift E A m 4 1 0 ≫ Q.arrow.map := by
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m 4) hm4
  obtain ⟨P, hP⟩ := cyclic_of_level E hL A m hm hmL
  have hP' : P.point = familyKernel E A m := hP
  letI := sectionGroup E
  letI := sectionGroup Q.target
  let F : sections E →* sections Q.target := pointHom E Q.arrow Q.hom (𝟙 _)
  let sx : sections E := A.x ^ (L / (m * 4))
  let sy : sections E := A.y ^ (L / 4)
  have hlift (a b : ℕ) :
      (F (sx ^ b * sy ^ a)).val = familyLift E A m 4 a b ≫ Q.arrow.map := by
    change (sx ^ b * sy ^ a).val ≫ Q.arrow.map = _
    dsimp [familyLift, sx, sy]
    simp only [nsmul_pow, pow_mul]
    rfl
  have hpoint (a b : Fin 4) (hab : a.val ≠ 0 ∨ b.val ≠ 0) :
      (familyLift E A m 4 a.val b.val ≫ Q.arrow.map) ≫
          Q.target.law.schemeNsmul 4 = zero Q.target ∧
      Disjoint (Set.range (familyLift E A m 4 a.val b.val ≫ Q.arrow.map))
        (Set.range (zero Q.target)) := by
    have hl := level_lift_conditions E hL A m 4 hm (by decide) hm4 a b hab
    have hp : familyLift E A m 4 a.val b.val ≫ E.projection = 𝟙 _ :=
      (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (L/(m*4)*b.val) A.x)
        (E.law.nsmul (𝟙 _) (L/4*a.val) A.y)).property
    exact quotient_lift E hm P (familyKernel E A m) hP' Q 4
      (familyLift E A m 4 a.val b.val) hp
      (by simpa only [hP', familyKernel, familyLift] using hl.1)
      (by simpa only [hP', familyKernel, familyLift] using hl.2)
  have hx : (F sx).val = familyLift E A m 4 0 1 ≫ Q.arrow.map := by
    simpa only [pow_one, pow_zero, mul_one] using hlift 0 1
  have hy : (F sy).val = familyLift E A m 4 1 0 ≫ Q.arrow.map := by
    simpa only [pow_one, pow_zero, one_mul] using hlift 1 0
  let M : FamilyLevel R Q.target 4 := {
    x := F sx
    y := F sy
    killed_x := by rw [hx]; exact (hpoint 0 1 (by decide)).1
    killed_y := by rw [hy]; exact (hpoint 1 0 (by decide)).1
    avoids := by
      intro i j hij
      have he : (Q.target.law.mul (𝟙 _)
          (Q.target.law.nsmul (𝟙 _) i.val (F sx))
          (Q.target.law.nsmul (𝟙 _) j.val (F sy))).val =
            familyLift E A m 4 j.val i.val ≫ Q.arrow.map := by
        simp only [nsmul_pow]
        change ((F sx) ^ i.val * (F sy) ^ j.val).val = _
        simpa only [map_mul, map_pow] using hlift j.val i.val
      rw [he]
      exact (hpoint j i hij.symm).2 }
  exact ⟨M, hx, hy⟩

lemma family_alpha_exists (k R : Type) [Field k] [CharZero k] [CommRing R] [Algebra k R]
    (hR : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k R))))
    (E : EllipticFamily R) {L : ℕ} (M : FamilyLevel R E L) (hL : 0 < L)
    (m : ℕ) (hm : 0 < m) (hm4 : m*4 ∣ L) :
    Nonempty (FamilyAlpha k E M m) := by
  obtain ⟨T⟩ := elliptic_family_weierstrass_atlas k R hR E
  obtain ⟨P, hP⟩ := cyclic_of_level E hL M m hm
    (dvd_trans (dvd_mul_right m 4) hm4)
  have hQ : Nonempty (Quotient R E m (familyKernel E M m)) := by
    simpa only [hP] using quotient_nonempty E T hm P
  obtain ⟨Q⟩ := hQ
  obtain ⟨N, hN⟩ := family_four_marking E M hL hm hm4 Q
  obtain ⟨U⟩ := elliptic_family_weierstrass_atlas k R hR Q.target
  obtain ⟨a, ha⟩ := OpenIsogenyAlpha.family_alpha_exists Q.target N U
  exact ⟨⟨Q, N, hN, a, ha⟩⟩

/-- Naturality retains the actual quotient map and inverse-degree scalar. -/
lemma family_section_naturality {k l R S : Type} [Field k] [Field l]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra l S]
    (ι : k →+* l) (ρ : R →+* S)
    (hρ : ρ.comp (algebraMap k R) = (algebraMap l S).comp ι)
    (E : EllipticFamily R) (F : EllipticFamily S) {L : ℕ}
    (M : FamilyLevel R E L) (N : FamilyLevel S F L)
    (hL : 0 < L) (m : ℕ) (hm : 0 < m) (hmL : m ∣ L)
    (A : FamilyAlpha k E M m) (B : FamilyAlpha l F N m)
    (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hhom : IsFamilyHom E F j hj.w)
    (hz : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hk : familyKernel F N m ≫ j = baseMap R S ρ ≫ familyKernel E M m)
    (hx : familyLift F N m 4 0 1 ≫ j = baseMap R S ρ ≫ familyLift E M m 4 0 1)
    (hy : familyLift F N m 4 1 0 ≫ j = baseMap R S ρ ≫ familyLift E M m 4 1 0)
    (T : Atlas S B.quotient.target) :
    transportSection (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hz) (familySection A) = familySection B := by
  obtain ⟨⟨p, hp, hpk, hpd⟩, he⟩ := cyclic_of_level E hL M m hm hmL
  change p = familyKernel E M m at he
  subst p
  let P : Cyclic E m := ⟨familyKernel E M m, hp, hpk, hpd⟩
  obtain ⟨⟨p', hp', hpk', hpd'⟩, he'⟩ := cyclic_of_level F hL N m hm hmL
  change p' = familyKernel F N m at he'
  subst p'
  let P' : Cyclic F m := ⟨familyKernel F N m, hp', hpk', hpd'⟩
  have hmultiple (i : Fin m) : multiple F P' i ≫ j = baseMap R S ρ ≫ multiple E P i := by
    change (familyKernel F N m ≫ F.law.schemeNsmul i.val) ≫ j =
      baseMap R S ρ ≫ (familyKernel E M m ≫ E.law.schemeNsmul i.val)
    rw [Category.assoc, familyHom_nsmul E F j hj.w hhom hz i.val,
      ← Category.assoc, hk, Category.assoc]
  obtain ⟨q, hq, harrow, hzq, hnq⟩ := quotient_cartesian_comparison E F P P'
    A.quotient B.quotient (baseMap R S ρ) j hj hhom hz hmultiple
  have hmx : B.marking.x.val ≫ q = baseMap R S ρ ≫ A.marking.x.val := by
    rw [B.marked.1, A.marked.1, Category.assoc, harrow, ← Category.assoc, hx, Category.assoc]
  have hmy : B.marking.y.val ≫ q = baseMap R S ρ ≫ A.marking.y.val := by
    rw [B.marked.2, A.marked.2, Category.assoc, harrow, ← Category.assoc, hy, Category.assoc]
  have ha := family_alpha_transport ρ q hq hzq hnq A.marking B.marking hmx hmy T
    A.alpha B.alpha A.intrinsic B.intrinsic
  have hs := family_hodge_square ρ j q hj hq hz hzq A.quotient.arrow B.quotient.arrow harrow.symm
  have hr : (baseMap R S ρ).appLE ⊤ ⊤ (by simp)
      (scalar R (algebraMap k R (m : k)⁻¹)) = scalar S (algebraMap l S (m : l)⁻¹) := by
    change (baseMap R S ρ).appTop _ = _
    rw [GlobalFamilyTorsionValueR0180.scalar_natural]
    apply congrArg (scalar S)
    have hh := DFunLike.congr_fun hρ ((m : k)⁻¹)
    simpa only [RingHom.comp_apply, map_inv₀, map_natCast] using hh
  unfold familySection
  rw [transportSection_smul, hr]
  congr 1
  have ht : transportSection (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hz) ((familyHodgeMap A.quotient.arrow).app ⊤ A.alpha) =
      (familyHodgeMap B.quotient.arrow).app ⊤
        (transportSection (baseMap R S ρ) _ _ (familyComparison ρ q hq hzq) A.alpha) := by
    unfold transportSection
    have hh := congrArg (fun g => g.app _
      (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) A.alpha)) hs
    change (familyComparison ρ j hj hz).hom.app _
      (((Scheme.Modules.pullback (baseMap R S ρ)).map
        (familyHodgeMap A.quotient.arrow)).app _
        (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) A.alpha)) =
      (familyHodgeMap B.quotient.arrow).app _
        ((familyComparison ρ q hq hzq).hom.app _
          (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) A.alpha)) at hh
    rw [← Scheme.Modules.pullbackLocalSection_app] at hh
    rw [hh, hom_res]
  exact ht.trans (congrArg ((familyHodgeMap B.quotient.arrow).app ⊤) ha)

#print axioms family_four_marking
#print axioms family_alpha_exists
#print axioms family_section_naturality

open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaSchemeHodgeR0205

def ofOpenAlpha (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (A : OpenAlpha k L m D) :
    FamilyAlpha k D.atlas.descent.family D.atlas.marking m :=
  ⟨A.quotient, A.marking, A.marked, A.alpha, A.intrinsic⟩

lemma classified_alpha_transport {k l R : Type} [Field k] [CharZero k]
    [Field l] [CharZero l] [CommRing R] [Algebra l R]
    (ι : k →+* l) (L m : ℕ) (hL : 0 < L) (hm : 0 < m) (hmL : m ∣ L)
    (D : LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L)
    (b : Base R ⟶ OpenBase k L D)
    (j : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D
      (Spec.map (CommRingCat.ofHom (algebraMap l R)) ≫ ArithmeticThetaLevelConstantsR0234.constants ι)
      F M b j)
    (e : (Scheme.Modules.pullback b).obj (ArithmeticThetaLevelConstantsR0234.weight D) ≅ Cotangent F)
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient F b j e)
    (A : OpenAlpha k L m D)
    (B : FamilyAlpha l (ellipticFamily F) (familyLevel F M) m)
    (T : Atlas R B.quotient.target) :
    transportSection b (ArithmeticThetaLevelConstantsR0234.weight D) (hodge (ellipticFamily F))
      (classifierLine F e) (openAlpha k L m D A) = familySection B := by
  let ρ : D.atlas.quotient.ring →+* R := (Spec.preimage (b ≫ D.quotient.inclusion)).hom
  have hρ : baseMap _ _ ρ = b ≫ D.quotient.inclusion := Spec.map_preimage _
  have hj : IsPullback j F.p D.atlas.descent.family.projection (baseMap _ _ ρ) := by
    rw [hρ]; exact hc.2.1
  have hz : F.zero ≫ j = baseMap _ _ ρ ≫ zero D.atlas.descent.family := by
    rw [hρ]; exact hc.2.2.1
  have hh : IsFamilyHom D.atlas.descent.family (ellipticFamily F) j hj.w := by
    simpa only [hρ] using classifier_familyHom D F M _ b j hc
  have hk : familyKernel (ellipticFamily F) (familyLevel F M) m ≫ j =
      baseMap _ _ ρ ≫ familyKernel D.atlas.descent.family D.atlas.marking m := by
    rw [hρ]; exact classifier_multiple_x D F M _ b j hc _
  have hl (a c : ℕ) : familyLift (ellipticFamily F) (familyLevel F M) m 4 a c ≫ j =
      baseMap _ _ ρ ≫ familyLift D.atlas.descent.family D.atlas.marking m 4 a c := by
    rw [hρ]; exact classifier_coordinates D F M _ b j hc _ _
  have hn := family_section_naturality ι ρ (classifier_scalar_eq ι D F M b j hc ρ hρ)
    D.atlas.descent.family (ellipticFamily F) D.atlas.marking (familyLevel F M)
    hL m hm hmL (ofOpenAlpha k L m D A) B j hj hh hz hk (hl 0 1) (hl 1 0) T
  have ho : openAlpha k L m D A =
      transportSection D.quotient.inclusion (hodge D.atlas.descent.family)
        (ArithmeticThetaLevelConstantsR0234.weight D) (Iso.refl _) (familySection (ofOpenAlpha k L m D A)) := by
    simp only [openAlpha, transportSection, Iso.refl_hom, Scheme.Modules.Hom.id_app,
      ConcreteCategory.id_apply]
    simp only [pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
      Scheme.Hom.preimage_top, InitialHodgeSection.res_self]
    rfl
  rw [ho, ← transportSection_comp_eq D.quotient.inclusion b (baseMap _ _ ρ) hρ,
    classifier_total_comparison D F M _ b j hc ρ hρ hj hz e he]
  exact hn

#print axioms classified_alpha_transport

/-- The normalized open isogeny alpha commutes with the prescribed coefficient
comparison, for arbitrary choices of the two quotient constructions. -/
theorem _root_.ArithmeticThetaArithmeticHalfLinesR0237.open_isogeny_alpha_constant_naturality :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L m : ℕ), 0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y) (A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D) (B : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha l L m E), ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transportSection C.openMap (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E) C.hodgeMap (ArithmeticThetaIsogenyHalfLinesR0193.openAlpha k L m D A) = ArithmeticThetaIsogenyHalfLinesR0193.openAlpha l L m E B := by
  intro k l _ _ _ _ ι L m hL hm hmeven hdiv D E X Y C A A'
  have hL3 : 3 ≤ L := by
    have := Nat.le_of_dvd hL hdiv
    omega
  have hLeven : Even L := even_iff_two_dvd.mpr
    (dvd_trans (by use 4*m; omega) hdiv)
  have hm4 : m*4 ∣ L := dvd_trans (by use 2; omega) hdiv
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m 4) hm4
  obtain ⟨F, M, g, j, hg, hj⟩ := common_classifiers ι D E C.openMap C.classifies
  let R := E.quotient.quotient.ring
  obtain ⟨B⟩ := family_alpha_exists l R E.quotient.quotient.smooth
    (ellipticFamily F) (familyLevel F M) hL m hm hm4
  obtain ⟨T⟩ := elliptic_family_weierstrass_atlas l R E.quotient.quotient.smooth B.quotient.target
  obtain ⟨el, hel, _⟩ := classifying_cotangent_hodge l L hL3 hLeven
    E.atlas E.two E.cover E.quotient _ (openStructure l L E) F M (𝟙 _) g hg
  obtain ⟨ek, hek, _⟩ := classifying_cotangent_hodge k L hL3 hLeven
    D.atlas D.two D.cover D.quotient _
    (openStructure l L E ≫ ArithmeticThetaLevelConstantsR0234.constants ι)
    F M ((𝟙 _) ≫ C.openMap) j hj
  have hk := classified_alpha_transport ι L m hL hm hmL
    D F M ((𝟙 _) ≫ C.openMap) j hj ek hek A B T
  have hid : ArithmeticThetaLevelConstantsR0234.constants (RingHom.id l) = 𝟙 (Base l) := by
    change Spec.map (𝟙 (CommRingCat.of l)) = _
    exact Spec.map_id _
  have hg' : ArithmeticThetaLevelConstantsR0234.Classifies E
      (Spec.map (CommRingCat.ofHom (algebraMap l R)) ≫
        ArithmeticThetaLevelConstantsR0234.constants (RingHom.id l)) F M (𝟙 _) g := by
    simpa only [hid, Category.comp_id, openStructure] using hg
  have hl := classified_alpha_transport (RingHom.id l) L m hL hm hmL
    E F M (𝟙 _) g hg' el hel A' B T
  have hn := C.normalized _ (openStructure l L E)
    F M (𝟙 _) g j hg hj el ek hel hek
  letI : IsIso (affineDifferential F) := AffineConormalHodgeNaturality.differential_isIso F
  have hcomp := composeComparison_postcompose C.openMap (𝟙 _)
    (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E)
    (Cotangent F) (hodge (ellipticFamily F)) C.hodgeMap el ek (asIso (affineDifferential F)) hn
  change composeComparison C.openMap (𝟙 _) ((𝟙 _) ≫ C.openMap) rfl
    (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E)
    (hodge (ellipticFamily F)) C.hodgeMap (classifierLine F el) = classifierLine F ek at hcomp
  apply transportSection_injective (𝟙 _) _ _ (classifierLine F el)
  rw [← transportSection_comp_eq C.openMap (𝟙 _) ((𝟙 _) ≫ C.openMap) rfl,
    hcomp, hk, hl]

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.open_isogeny_alpha_constant_naturality
end OpenIsogenyAlphaConstantNaturality
end ArithmeticThetaArithmeticHalfLinesR0237
