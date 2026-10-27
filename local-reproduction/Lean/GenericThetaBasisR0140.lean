import GenericDualLocalizationR0140

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules MonoidalCategory
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133 (pulledInclusion)
open GenericDualLocalizationR0140

/-- Multiplication of an actual dual morphism by a global function. -/
def scale {X : Scheme.{u}} {L : X.Modules} (a : Γ(X, ⊤))
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :=
  ihomGlobalSectionsEquiv L (𝟙_ X.Modules)
    (a • (ihomGlobalSectionsEquiv L (𝟙_ X.Modules)).symm φ)

lemma scale_app {X : Scheme.{u}} {L : X.Modules} (a : Γ(X, ⊤))
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (U : X.Opens) (x : Γ(L, U)) :
    (scale a φ).app U x = X.presheaf.map (homOfLE le_top).op a *
      (show Γ(X, U) from φ.app U x) := by
  unfold scale
  rw [ihomGlobal_smul]
  erw [Equiv.apply_symm_apply]
  rfl

lemma scale_precomp {X : Scheme.{u}} {L P : X.Modules} (a : Γ(X, ⊤))
    (f : P ⟶ L) (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    f ≫ scale a φ = scale a (f ≫ φ) := by
  apply hom_ext
  intro U
  ext x
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, scale_app]

lemma pull_scale {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (a : Γ(Y, ⊤)) (φ : L ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    pulledInclusion f (scale a φ) = scale (f.appTop a) (pulledInclusion f φ) := by
  apply pullback_hom_ext
  intro U x
  change (unitPullback f).app _ (((Scheme.Modules.pullback f).map (scale a φ)).app _
    (pullbackLocalSection f x)) = _
  rw [← pullbackLocalSection_app, unitPullback_app, scale_app, map_mul]
  erw [scale_app]
  have hn := congrArg (fun q => q a) (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.app U (Y.presheaf.map (homOfLE le_top).op a) =
    X.presheaf.map (homOfLE le_top).op (f.appTop a) at hn
  rw [hn]
  congr 1
  change _ = (unitPullback f).app _ (((Scheme.Modules.pullback f).map φ).app _
    (pullbackLocalSection f x))
  rw [← pullbackLocalSection_app, unitPullback_app]

lemma sum_app {X : Scheme.{u}} {L P : X.Modules} {ι : Type*}
    (S : Finset ι) (φ : ι → (L ⟶ P)) (U : X.Opens) (x : Γ(L, U)) :
    (∑ i ∈ S, φ i).app U x = ∑ i ∈ S, (φ i).app U x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert, hi, Hom.add_app, ih]

lemma pull_sum {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {ι : Type*}
    (S : Finset ι) (φ : ι → (L ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))) :
    pulledInclusion f (∑ i ∈ S, φ i) = ∑ i ∈ S, pulledInclusion f (φ i) := by
  simp [pulledInclusion, Functor.map_sum, Preadditive.sum_comp]



open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138
open AlgebraizedThetaSectionsR0138 AlgebraizedThetaSaturationR0138


variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (M : Model k T)

def baseScalar (a : PowerSeries k) : Γ(M.X, ⊤) :=
  M.p.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv a)

lemma chart_base (hM : IsModel k T M) (n : ℕ) (i : Fin r) (a : PowerSeries k) :
    ((T.atlas n).chart i).appTop ((M.inclusion n).appTop (baseScalar k M a)) =
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (fullBase k n a) := by
  change (M.p.appTop ≫ (M.inclusion n).appTop ≫ ((T.atlas n).chart i).appTop)
    ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv a) = _
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    Category.assoc, (hM.2.2.1 n).w, ← Category.assoc, (T.atlas n).chart_over]
  rw [Scheme.Hom.comp_appTop]
  have h1 := congrArg (fun f => f a) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (trunc (PowerSeries k) PowerSeries.X n)))
  have h2 := congrArg (fun f => f (trunc (PowerSeries k) PowerSeries.X n a))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (base k n)))
  exact (congrArg (fun b => (structureMap k n).appTop b) h1.symm).trans h2.symm

variable (h3 : 3 ≤ r) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
variable (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)

local instance dualAdd (s : baseScheme k ⟶ M.X) (d : ℕ) : AddCommGroup (Dual k M s d) :=
  inferInstanceAs (AddCommGroup (powerModule k M s d ⟶
    (SheafOfModules.unit M.X.ringCatSheaf : M.X.Modules)))

def nums (φ : Dual k M s d) (n : ℕ) (i : Fin r) : A k n :=
  ((algebraicFormal k h3 M hM s hs d φ).val n).val i

lemma nums_sum {ι : Type*} (S : Finset ι) (φ : ι → Dual k M s d)
    (n : ℕ) (i : Fin r) :
    nums k M h3 hM s hs d (∑ j ∈ S, φ j) n i =
      ∑ j ∈ S, nums k M h3 hM s hs d (φ j) n i := by
  simp only [nums, algebraicFormal, IdentityStageSectionRealizationR0138.toSections,
    IdentityStageSectionRealizationR0138.numerator, reduceDual]
  erw [pull_sum, Preadditive.comp_sum, pull_sum, sum_app, map_sum]

lemma nums_scale (a : PowerSeries k) (φ : Dual k M s d) (n : ℕ) (i : Fin r) :
    nums k M h3 hM s hs d (scale (baseScalar k M a) φ) n i =
      fullBase k n a * nums k M h3 hM s hs d φ n i := by
  simp only [nums, algebraicFormal, IdentityStageSectionRealizationR0138.toSections,
    IdentityStageSectionRealizationR0138.numerator, reduceDual,
    pull_scale, scale_precomp]
  erw [scale_app]
  simp only [homOfLE_refl, op_id]
  erw [chart_base k M hM, map_mul]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (fullBase k n a)) = fullBase k n a from
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _]

lemma nums_injective : Function.Injective (nums k M h3 hM s hs d) := by
  intro φ ψ h
  apply (algebraicFormal_bijective k h3 M hM s hs d).1
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrFun h n



section Theta
variable (m : ℕ) (hm : 0 < m) (he : Even m)
variable {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
variable (MM : Model k TT) (hMM : IsModel k TT MM) (ss : baseScheme k ⟶ MM.X)
variable (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)

lemma theta_nums (ν : Fin m) (n : ℕ) (i : Fin (2*m)) :
    nums k MM (thetaChartBound m hm he) hMM ss hss m
      (thetaSection k m hm he MM hMM ss hss ν) n i =
      finiteNumerator k m hm he (thetaVector k m ν) n i := by
  exact congrFun (stage_numerator_eq k (thetaChartBound m hm he) m n _ _
    (AlgebraizedThetaFaithfulnessR0138.realizes_reductions k he MM hMM ss hss
      (thetaVector k m ν) _
      (Classical.choose_spec (algebraized_theta_sections k m hm he TT MM hMM ss hss
        (thetaVector k m ν))).1 (thetaChartBound m hm he) n)) i

def algCombo (w : Fin m → PowerSeries k) : Dual k MM ss m :=
  ∑ ν : Fin m, scale (baseScalar k MM (w ν)) (thetaSection k m hm he MM hMM ss hss ν)

omit [CharZero k] in
lemma vector_sum (w : Fin m → PowerSeries k) :
    (∑ ν : Fin m, w ν • thetaVector k m ν) = w := by
  classical
  funext μ
  simp [Finset.sum_apply, Pi.smul_apply, thetaVector]

include TT in
lemma finiteNumerator_sum (w : Fin m → PowerSeries k) (n : ℕ) (i : Fin (2*m)) :
    finiteNumerator k m hm he w n i =
      ∑ ν : Fin m, fullBase k n (w ν) * finiteNumerator k m hm he (thetaVector k m ν) n i := by
  have h := congrArg (fun z : formalModule k TT (thetaChartBound m hm he) m => z.val n i)
    (map_sum (thetaLinear k m hm he TT (thetaChartBound m hm he))
      (fun ν => w ν • thetaVector k m ν) Finset.univ)
  rw [vector_sum] at h
  simpa only [map_smul, thetaLinear, LinearMap.coe_mk, AddHom.coe_mk, ofFormal,
    Submodule.coe_sum, Finset.sum_apply, finiteNumerator_smul] using h

lemma combo_nums (w : Fin m → PowerSeries k) (n : ℕ) (i : Fin (2*m)) :
    nums k MM (thetaChartBound m hm he) hMM ss hss m
      (algCombo k m hm he MM hMM ss hss w) n i = finiteNumerator k m hm he w n i := by
  unfold algCombo
  rw [nums_sum]
  simp_rw [nums_scale, theta_nums]
  exact (finiteNumerator_sum k m hm he (TT := TT) w n i).symm

lemma combo_injective : Function.Injective (algCombo k m hm he MM hMM ss hss) := by
  intro w v h
  apply thetaLinear_injective k m hm he TT (thetaChartBound m hm he)
  apply Subtype.ext
  funext n i
  have hh := congrArg (fun φ => nums k MM (thetaChartBound m hm he) hMM ss hss m φ n i) h
  change finiteNumerator k m hm he w n i = finiteNumerator k m hm he v n i
  simpa only [combo_nums] using hh

lemma algebraic_saturation (φ : Dual k MM ss m) :
    ∃ (b : ℕ) (w : Fin m → PowerSeries k),
      scale (baseScalar k MM (PowerSeries.X^b)) φ = algCombo k m hm he MM hMM ss hss w := by
  obtain ⟨b, hb⟩ := formal_theta_saturation k m hm he TT (thetaChartBound m hm he)
  obtain ⟨w, hw⟩ := hb (algebraicFormal k (thetaChartBound m hm he) MM hMM ss hss m φ)
  refine ⟨b, w, nums_injective k MM (thetaChartBound m hm he) hMM ss hss m ?_⟩
  funext n i
  rw [nums_scale, combo_nums]
  simpa only [fullBase, RingHom.comp_apply, map_pow, nums, parameter] using hw n i

end Theta


/-- The scalar homomorphism is precisely the generic structure map. -/
def scalarHom (U : (genericScheme k M).Opens) : LaurentSeries k →+* Γ(genericScheme k M, U) :=
  ((genericScheme k M).presheaf.map (homOfLE le_top).op).hom.comp
    ((genericStructure k M).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom)

lemma generic_base (a : PowerSeries k) :
    (genericInclusion k M).appTop (baseScalar k M a) =
      (genericStructure k M).appTop ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
        (algebraMap (PowerSeries k) (LaurentSeries k) a)) := by
  have h := congrArg Scheme.Hom.appTop (pullback.condition (f := M.p) (g := genericBase k))
  simp only [Scheme.Hom.comp_appTop] at h
  have hn := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
  change (M.p.appTop ≫ (genericInclusion k M).appTop)
    ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv a) = _
  erw [h]
  exact congrArg (fun b => (genericStructure k M).appTop b)
    (congrArg (fun f => f a) hn).symm

lemma restrict_scale (s : baseScheme k ⟶ M.X) (d : ℕ)
    (a : PowerSeries k) (φ : Dual k M s d)
    (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)) :
    (restrictDual k M s d (scale (baseScalar k M a) φ)).app U x =
      scalarHom k M U (algebraMap (PowerSeries k) (LaurentSeries k) a) *
        (show Γ(genericScheme k M, U) from (restrictDual k M s d φ).app U x) := by
  change (pulledInclusion (genericInclusion k M) (scale (baseScalar k M a) φ)).app U x = _
  rw [pull_scale]
  erw [scale_app, generic_base]
  rfl

lemma restrict_combo (m : ℕ) (hm : 0 < m) (he : Even m)
    {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (MM : Model k TT) (hMM : IsModel k TT MM) (ss : baseScheme k ⟶ MM.X)
    (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
    (w : Fin m → PowerSeries k) (U : (genericScheme k MM).Opens)
    (x : Γ(genericPower k MM ss m, U)) :
    (restrictDual k MM ss m (algCombo k m hm he MM hMM ss hss w)).app U x =
      ∑ ν : Fin m, scalarHom k MM U (algebraMap (PowerSeries k) (LaurentSeries k) (w ν)) *
        (show Γ(genericScheme k MM, U) from (genericTheta k m hm he MM hMM ss hss ν).app U x) := by
  unfold algCombo
  change (pulledInclusion (genericInclusion k MM) (∑ ν : Fin m, _)).app U x = _
  erw [pull_sum, sum_app]
  apply Finset.sum_congr rfl
  intro ν _
  exact restrict_scale k MM ss m (w ν) (thetaSection k m hm he MM hMM ss hss ν) U x

omit [CharZero k] in
lemma clear_vector (m : ℕ) (c : Fin m → LaurentSeries k) :
    ∃ (b : ℕ) (w : Fin m → PowerSeries k), ∀ ν,
      (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^b * c ν =
        algebraMap (PowerSeries k) (LaurentSeries k) (w ν) := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (PowerSeries.X : PowerSeries k)) c
  obtain ⟨b, hb⟩ := a.property
  choose w hw using ha
  refine ⟨b, w, fun ν => ?_⟩
  have h := hw ν
  rw [← hb] at h
  simpa only [Algebra.smul_def, map_pow] using h.symm



section GenericBasis
variable (m : ℕ) (hm : 0 < m) (he : Even m)
variable {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
variable (MM : Model k TT) (hMM : IsModel k TT MM) (ss : baseScheme k ⟶ MM.X)
variable (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)

omit [CharZero k] in
lemma parameter_ne_zero : algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))).mpr
    PowerSeries.X_ne_zero

lemma generic_exists (φ : GenericDual k MM ss m) :
    ∃ c : Fin m → LaurentSeries k,
      Combines k MM ss m m (genericTheta k m hm he MM hMM ss hss) c φ := by
  obtain ⟨a, ξ, hξ⟩ := (generic_dual_localization k (2*m) _ (thetaChartBound m hm he)
    TT MM hMM ss hss m).2 φ
  obtain ⟨b, w, hw⟩ := algebraic_saturation k m hm he MM hMM ss hss ξ
  let t : LaurentSeries k := algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X
  let A : LaurentSeries k := t^b * t^a
  have hA : A ≠ 0 := mul_ne_zero (pow_ne_zero b (parameter_ne_zero k))
    (pow_ne_zero a (parameter_ne_zero k))
  refine ⟨fun ν => A⁻¹ * algebraMap (PowerSeries k) (LaurentSeries k) (w ν), ?_⟩
  intro U x
  let H := scalarHom k MM U
  let y := fun ν => (show Γ(genericScheme k MM, U) from
    (genericTheta k m hm he MM hMM ss hss ν).app U x)
  have heq : H A * (show Γ(genericScheme k MM, U) from φ.app U x) =
      ∑ ν : Fin m, H (algebraMap (PowerSeries k) (LaurentSeries k) (w ν)) * y ν := by
    calc
      _ = H (t^b) * (H (t^a) * (show Γ(genericScheme k MM, U) from φ.app U x)) := by
        rw [show A = t^b * t^a from rfl, map_mul, mul_assoc]
      _ = H (t^b) * (show Γ(genericScheme k MM, U) from (restrictDual k MM ss m ξ).app U x) :=
        congrArg (fun z => H (t^b) * z) (hξ U x)
      _ = (restrictDual k MM ss m (scale (baseScalar k MM (PowerSeries.X^b)) ξ)).app U x := by
        have hh := restrict_scale k MM ss m (PowerSeries.X^b) ξ U x
        erw [map_pow] at hh
        exact hh.symm
      _ = _ := by
        rw [hw]
        exact restrict_combo k m hm he MM hMM ss hss w U x
  change (show Γ(genericScheme k MM, U) from φ.app U x) =
    ∑ ν : Fin m, H (A⁻¹ * algebraMap (PowerSeries k) (LaurentSeries k) (w ν)) * y ν
  calc
    _ = (H A⁻¹ * H A) * (show Γ(genericScheme k MM, U) from φ.app U x) := by
      rw [← map_mul, inv_mul_cancel₀ hA, map_one, one_mul]
    _ = _ := by
      rw [mul_assoc, heq, Finset.mul_sum]
      simp only [map_mul, mul_assoc]

lemma generic_unique (φ : GenericDual k MM ss m) (c v : Fin m → LaurentSeries k)
    (hc : Combines k MM ss m m (genericTheta k m hm he MM hMM ss hss) c φ)
    (hv : Combines k MM ss m m (genericTheta k m hm he MM hMM ss hss) v φ) : c = v := by
  obtain ⟨b, w, hw⟩ := clear_vector k m (fun ν => c ν - v ν)
  have hr := (generic_dual_localization k (2*m) _ (thetaChartBound m hm he)
    TT MM hMM ss hss m).1
  have heq : restrictDual k MM ss m (algCombo k m hm he MM hMM ss hss w) =
      restrictDual k MM ss m (algCombo k m hm he MM hMM ss hss 0) := by
    apply hom_ext
    intro U
    ext x
    let H := scalarHom k MM U
    let y := fun ν => (show Γ(genericScheme k MM, U) from
      (genericTheta k m hm he MM hMM ss hss ν).app U x)
    have hz : (∑ ν : Fin m, H (c ν - v ν) * y ν) = 0 := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr ((hc U x).symm.trans (hv U x))
    erw [restrict_combo, restrict_combo]
    change (∑ ν : Fin m, H (algebraMap (PowerSeries k) (LaurentSeries k) (w ν)) * y ν) =
      ∑ ν : Fin m, H (algebraMap (PowerSeries k) (LaurentSeries k) 0) * y ν
    simp only [map_zero, zero_mul, Finset.sum_const_zero]
    simp_rw [← hw, map_mul, mul_assoc]
    rw [← Finset.mul_sum, hz, mul_zero]
  have hw0 := combo_injective k m hm he MM hMM ss hss (hr heq)
  funext ν
  have hz : (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)^b * (c ν - v ν) = 0 := by
    rw [hw, hw0]
    exact map_zero _
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero b (parameter_ne_zero k)))

end GenericBasis
end ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140

namespace ArithmeticThetaGenericEvaluationR0140
open GenericThetaBasisR0140
/-- The specified theta restrictions give unique Laurent-series coordinates
for every actual generic dual morphism, on every open and every section. -/
theorem generic_theta_basis :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s), ∀ φ : ArithmeticThetaGenericEvaluationR0140.GenericDual k M s m, ∃! c : Fin m → LaurentSeries k, ArithmeticThetaGenericEvaluationR0140.Combines k M s m m (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) c φ := by
  intro k _ _ m hm he T M hM s hs φ
  obtain ⟨c, hc⟩ := generic_exists k m hm he M hM s hs φ
  exact ⟨c, hc, fun v hv => generic_unique k m hm he M hM s hs φ v c hv hc⟩
end ArithmeticThetaGenericEvaluationR0140
#print axioms ArithmeticThetaGenericEvaluationR0140.generic_theta_basis
