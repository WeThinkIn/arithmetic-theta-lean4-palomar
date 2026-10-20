module

public import SharpKernelDefinitionsR0195
public import OneChartRegularRoot

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaSharpKernelR0195.RatioUnaryRegularSectionsR0195
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaSharpCoverR0194 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaOrthogonalConsumerR0127
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaRelativeDiscriminantR0171
open SimultaneousDiskRootSectionsR0187

lemma twice_dvd_level (N m : ℕ) (hd : m ∣ N) : 2*m ∣ level N := by
  obtain ⟨v, hv⟩ := hd
  refine ⟨12*v*N, ?_⟩
  unfold level
  rw [hv]
  ring

/-- The coefficient-cardinality identity includes both centered endpoints. -/
lemma cleared_eq_scaled (m : ℕ) (hm : 0 < m) (ν : ℤ)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν = scaledUnary m 12 ν := by
  ext b
  rw [ArithmeticThetaUnaryProduct.clearedUnaryTheta_residue_coefficient m b ν hm hν]
  simp only [scaledUnary, PowerSeries.coeff_mk]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun r => by
    rw [Int.modEq_iff_dvd, dvd_sub_comm]
    norm_num)

lemma unary_bridge (k : Type) [Field k] [CharZero k]
    (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (hd : m ∣ N)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ))
    (a : Fin m) (ha : Int.ModEq (m : ℤ) ν (a.val : ℤ)) :
    levelUnary k (level N) m a = unarySeries k N m ν := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  have hd2 : m ∣ N^2 := dvd_trans hd (by exact ⟨N, by ring⟩)
  have hq : N^2/m ≠ 0 := ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd (pow_pos hN 2) hd2) hm)
  have he : level N / (2*m) = (N^2/m)*12 := by
    apply Nat.div_eq_of_eq_mul_right (by omega : 0 < 2*m)
    have hmul := Nat.div_mul_cancel hd2
    unfold level
    nlinarith
  have hw : level N / (2*m) ≠ 0 := by rw [he]; exact mul_ne_zero hq (by decide)
  unfold levelUnary unarySeries
  rw [← PowerSeries.expand_apply _ hw, ← PowerSeries.expand_apply _ hq,
    cleared_eq_scaled m hm ν hν, PowerSeries.map_expand]
  rw [unary_parameter_identification k m 12 (by decide) ν a ha]
  rw [← PowerSeries.expand_mul]
  simp only [he]

/-- All centered residues are sent to the accepted full residue family. -/
def residue (m : ℕ) (hm : 0 < m) (ν : ℤ) : Fin m :=
  ⟨(ν % (m : ℤ)).toNat, by
    have h := Int.emod_lt_of_pos ν (show (0 : ℤ) < m by omega)
    have h' := Int.emod_nonneg ν (show (m : ℤ) ≠ 0 by omega)
    omega⟩

lemma residue_modEq (m : ℕ) (hm : 0 < m) (ν : ℤ) :
    Int.ModEq (m : ℤ) ν ((residue m hm ν).val : ℤ) := by
  change ν % (m : ℤ) = _ % (m : ℤ)
  simp only [residue, Int.toNat_of_nonneg (Int.emod_nonneg ν (by omega : (m : ℤ) ≠ 0)),
    Int.emod_emod]

lemma unary_zero_ne_zero (k : Type) [Field k] [CharZero k]
    (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (hd : m ∣ N) :
    algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N m 0) ≠ 0 := by
  rw [← unary_bridge k N m hN hm hd 0 (by constructor <;> omega)
    ⟨0, hm⟩ (Int.ModEq.refl _)]
  exact HigherLevelProjectiveRatiosR0194.levelUnary_denominator_ne_zero
    k (level N) m hm (by unfold level; positivity) (twice_dvd_level N m hd)

/-- The ratios live on the original component and use the specified disk map. -/
lemma centered_rational_ratio (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (he : Even m) (hd : m ∣ N)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ))
    (D : LevelData k (level N)) (X : Compactification k (level N) D)
    (V : DiskTest k (level N) D X) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (level N)) (hmark : CanonicalMarking k (level N) ζ V.level)
    (f : Disk k ⟶ Component k (level N) D X (V.disk (closedPoint k)))
    (hf : f ≫ inclusion k (level N) D X (V.disk (closedPoint k)) = V.disk) :
    ∃ r : (Component k (level N) D X (V.disk (closedPoint k))).functionField,
      RationalExpansion k _ (genericInclusion k ≫ f) r
        (algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N m ν) /
          algebraMap (PowerSeries k) (LaurentSeries k) (unarySeries k N m 0)) := by
  obtain ⟨g, hg, _, r, _, hr⟩ := higher_level_projective_ratios k (level N) m hm
    (by unfold level; positivity) he (twice_dvd_level N m hd) D X V ζ hζ hmark
  have hgf : g = f := (cancel_mono (inclusion k (level N) D X (V.disk (closedPoint k)))).mp
    (hg.trans hf.symm)
  subst g
  refine ⟨r (residue m hm ν), ?_⟩
  have h := hr (residue m hm ν)
  rw [unary_bridge k N m hN hm hd ν hν _ (residue_modEq m hm ν),
    unary_bridge k N m hN hm hd 0 (by constructor <;> omega) ⟨0, hm⟩ (Int.ModEq.refl _)] at h
  exact h

#print axioms centered_rational_ratio


open ArithmeticThetaCommonHalfHodgeR0185.CuspHalfDivisorLineR0185
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- A disk coordinate is computed by the actual generic field map. -/
lemma section_value (k : Type) [Field k] {Z : Scheme} [IsIntegral Z]
    [Algebra Z.functionField (LaurentSeries k)] (f : Disk k ⟶ Z)
    (hf : genericInclusion k ≫ f = ArithmeticThetaNormalization.genericExtensionMap Z (LaurentSeries k))
    (J : Z.Modules) (U : Z.Opens) [Nonempty U] (e : LocalFrame Z J U)
    (hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U)
    (t : Sections Z J) (a : PowerSeries k)
    (ht : pullbackGlobalSection f J t = scalar (PowerSeries k) a •
      res ((Scheme.Modules.pullback f).obj J) hU
        (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1))) :
    algebraMap Z.functionField (LaurentSeries k) (sectionCoefficient Z J U e t) =
      algebraMap (PowerSeries k) (LaurentSeries k) a := by
  have hw := frame_restrict _ hU _ (pullback_frame f J _ (frame_generator Z J U e))
  have he := (pullback_coordinate f J U e hU t).symm.trans ht
  have hc := (hw ⊤ le_rfl).injective (by
    simpa only [InitialHodgeSection.res_self] using he)
  have hc' : specScalar f U hU (sectionCoordinate Z J U e t) = a := by
    exact (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.symm.injective hc
  unfold sectionCoefficient
  rw [← diskScalar_generic k f hf U hU, hc']

/-- Extension on the same normal curve, with the prescribed full disk value.
The rational root is the ratio times the basic section's generic coefficient. -/
lemma same_curve_root (k : Type) [Field k] {Z : Scheme} [IsIntegral Z]
    (hZ : NormalAffine Z) (J : Z.Modules) (hJ : Scheme.Modules.IsInvertible J)
    (f : Disk k ⟶ Z) [IsDominant (genericInclusion k ≫ f)]
    (K : ℕ) (hK : 0 < K) (P : Sections Z (tensorPower Z J K))
    (h : Sections (Disk k) ((Scheme.Modules.pullback f).obj J))
    (a a₀ : PowerSeries k) (ha₀ : algebraMap (PowerSeries k) (LaurentSeries k) a₀ ≠ 0)
    (t₀ : Sections Z J) (ht₀ : pullbackGlobalSection f J t₀ = scalar (PowerSeries k) a₀ • h)
    (hP : pullbackPowerSection f J K P = scalar (PowerSeries k) (a^K) •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj J) K ⊤ h)
    (r : Z.functionField)
    (hr : RationalExpansion k Z (genericInclusion k ≫ f) r
      (algebraMap (PowerSeries k) (LaurentSeries k) a /
        algebraMap (PowerSeries k) (LaurentSeries k) a₀)) :
    ∃ t : Sections Z J, tensorPowerSection Z J K ⊤ t = P ∧
      pullbackGlobalSection f J t = scalar (PowerSeries k) a • h := by
  obtain ⟨θ, hθ⟩ := disk_field_map k f
  letI : Algebra Z.functionField (LaurentSeries k) := θ.toAlgebra
  have hf : genericInclusion k ≫ f = ArithmeticThetaNormalization.genericExtensionMap Z (LaurentSeries k) := hθ.symm
  obtain ⟨U, u, hxU, hu⟩ := local_frame_exists hJ (f (closedPoint k))
  letI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let e := InitialHodgeSection.frame J u hu
  have hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hxU).ge
  obtain ⟨c, hc, hpow⟩ := prescribed_series_roots k f hf J U e hU K 1
    (fun _ => P) h (fun _ => a) (fun _ => hP)
  have ht₀' : pullbackGlobalSection f J t₀ = scalar (PowerSeries k) (a₀*c) •
      res ((Scheme.Modules.pullback f).obj J) hU
        (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1)) := by
    rw [ht₀, hc]
    simp only [scalar, map_mul, mul_smul]
  have hv₀ := section_value k f hf J U e hU t₀ (a₀*c) ht₀'
  have hr' := (FullLevelProjectiveRatiosR0194.rationalExpansion_iff k Z
    (genericInclusion k ≫ f) θ hθ _ _).mp hr
  let q := r * sectionCoefficient Z J U e t₀
  have hq : algebraMap Z.functionField (LaurentSeries k) q =
      algebraMap (PowerSeries k) (LaurentSeries k) (a*c) := by
    change θ (r * sectionCoefficient Z J U e t₀) = _
    rw [map_mul, hr', show θ (sectionCoefficient Z J U e t₀) =
      algebraMap (PowerSeries k) (LaurentSeries k) (a₀*c) from hv₀, map_mul, map_mul]
    field_simp
  have hqpow : q^K = powerCoefficient Z J U e K P := by
    apply θ.injective
    rw [map_pow, show θ q = _ from hq]
    exact hpow 0
  obtain ⟨t, ⟨ht, htP⟩, _⟩ := existsUnique_root_from_one_chart Z J hZ
    (line_of_invertible J hJ) U e K hK q P hqpow
  refine ⟨t, htP, ?_⟩
  have htval : specScalar f U hU (sectionCoordinate Z J U e t) = a*c := by
    apply (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
    rw [diskScalar_generic k f hf U hU]
    change algebraMap Z.functionField (LaurentSeries k) (sectionCoefficient Z J U e t) = _
    rw [ht, hq]
  rw [pullback_coordinate f J U e hU t, htval, hc]
  simp only [scalar, map_mul, mul_smul]

#print axioms same_curve_root


/-- Pullback along a scheme-theoretically dominant map detects local sections
of an invertible sheaf, on every open. -/
lemma local_pullback_injective {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (J : Z.Modules)
    (hJ : Scheme.Modules.IsInvertible J) (W : Z.Opens) :
    Function.Injective (fun s : Γ(J,W) => Scheme.Modules.pullbackLocalSection f s) := by
  classical
  intro s t hst
  choose U u hx hu using fun x : W => local_frame_exists hJ x.val
  let V (x : W) := W ⊓ U x
  have hV (x : W) : V x ≤ W := inf_le_left
  have hcover : W ≤ iSup V := by
    intro x hxW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hxW, hx ⟨x, hxW⟩⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨J.presheaf, J.isSheaf⟩ V W
    (fun x => homOfLE (hV x)) hcover
  intro x
  let e := restrictLocalFrame Z J (U x) (V x) inf_le_right
    (InitialHodgeSection.frame J (u x) (hu x))
  obtain ⟨eY, heY⟩ := exists_pullbackFrame Y Z f J (V x) e
  apply (e.equiv (V x) le_rfl).symm.injective
  apply f.app_injective (V x)
  apply (eY.equiv (f ⁻¹ᵁ V x) le_rfl).injective
  have he (z : Γ(J,W)) :
      eY.equiv (f ⁻¹ᵁ V x) le_rfl
        (f.app (V x) ((e.equiv (V x) le_rfl).symm
          (J.presheaf.map (homOfLE (hV x)).op z))) =
      Scheme.Modules.pullbackLocalSection f (J.presheaf.map (homOfLE (hV x)).op z) := by
    rw [← heY (V x) le_rfl]
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [he, he]
  have hn (z : Γ(J,W)) := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app J).val
    (homOfLE (hV x)).op z
  exact (hn s).trans ((congrArg
    (((Scheme.Modules.pullback f).obj J).presheaf.map
      (homOfLE (f.preimage_mono (hV x))).op) hst).trans (hn t).symm)

#print axioms local_pullback_injective


open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185

lemma puncture_ratio (k : Type) [Field k] {Y : Scheme.{0}}
    (f : Disk k ⟶ Y) (J : Y.Modules) (t t₀ : Sections Y J)
    (h : Sections (Disk k) ((Scheme.Modules.pullback f).obj J))
    (a a₀ : PowerSeries k) (ha₀ : algebraMap (PowerSeries k) (LaurentSeries k) a₀ ≠ 0)
    (ht : pullbackGlobalSection f J t = scalar (PowerSeries k) a • h)
    (ht₀ : pullbackGlobalSection f J t₀ = scalar (PowerSeries k) a₀ • h) :
    transportSection (genericInclusion k ≫ f) J _ (Iso.refl _) t =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv (algebraMap (PowerSeries k) (LaurentSeries k) a /
        algebraMap (PowerSeries k) (LaurentSeries k) a₀) •
          (transportSection (genericInclusion k ≫ f) J _ (Iso.refl _) t₀ :
            Sections (Puncture k) ((Scheme.Modules.pullback (genericInclusion k ≫ f)).obj J)) := by
  let M := (Scheme.Modules.pullback f).obj J
  let T := (Scheme.Modules.pullback (genericInclusion k)).obj M
  let E := composeComparison f (genericInclusion k) (genericInclusion k ≫ f) rfl
    J M T (Iso.refl _) (Iso.refl _)
  have htrans (s : Sections Y J) :
      E.hom.app ⊤ (pullbackGlobalSection (genericInclusion k ≫ f) J s) =
        transportSection (genericInclusion k) M T (Iso.refl _) (pullbackGlobalSection f J s) := by
    rw [← transport_as_app]
    change transportSection _ _ _ (composeComparison _ _ _ _ _ _ _ _ _) _ = _
    rw [transportSection_comp]
    congr 1
    rw [transport_as_app]
    rfl
  have hscalar (b : PowerSeries k) :
      (genericInclusion k).appLE ⊤ ⊤ (by simp) (scalar (PowerSeries k) b) =
        (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv (algebraMap (PowerSeries k) (LaurentSeries k) b) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) b).symm
  simp only [transport_as_app, id_app_apply]
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)).injective
  rw [Scheme.Modules.Hom.app_smul, htrans, htrans, ht, ht₀,
    transportSection_smul, transportSection_smul, hscalar, hscalar, ← mul_smul]
  congr 1
  simp only [← map_mul, div_mul_cancel₀ _ ha₀]

/-- Equality detected at the puncture gives the literal ratio multiple on a
nonempty base open, including all points over that open. -/
lemma ratioMultiple_of_puncture (k : Type) [Field k]
    {B Y : Scheme.{0}} [IsIntegral B] [IsIntegral Y]
    (p : Y ⟶ B) (q : Puncture k ⟶ Y) [IsDominant q] [QuasiCompact q]
    (J : Y.Modules) (hJ : Scheme.Modules.IsInvertible J)
    (t t₀ : Sections Y J) (r : B.functionField) (a : LaurentSeries k)
    (hr : RationalExpansion k B (q ≫ p) r a)
    (ht : transportSection q J _ (Iso.refl _) t = (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv a •
      (transportSection q J _ (Iso.refl _) t₀ : Sections (Puncture k) ((Scheme.Modules.pullback q).obj J))) :
    RatioMultiple p J t t₀ r := by
  simp only [transport_as_app, id_app_apply] at ht
  letI : IsSchemeTheoreticallyDominant q := .of_isDominant q
  obtain ⟨U, hU, v, hv, hpre, heval⟩ := hr
  letI := hU
  refine ⟨U, hU, v, hv, ?_⟩
  apply local_pullback_injective q J hJ (p ⁻¹ᵁ U)
  have hn (s : Sections Y J) := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app J).val
    (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op s
  change Scheme.Modules.pullbackLocalSection q (J.presheaf.map _ t) =
    Scheme.Modules.pullbackLocalSection q (p.app U v • J.presheaf.map _ t₀)
  rw [Scheme.Modules.pullbackLocalSection_smul]
  have hn' (s : Sections Y J) : Scheme.Modules.pullbackLocalSection q
      (J.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op s) =
      res ((Scheme.Modules.pullback q).obj J) le_top (pullbackGlobalSection q J s) := hn s
  rw [hn' t, hn' t₀]
  change res ((Scheme.Modules.pullback q).obj J) le_top (pullbackGlobalSection q J t) =
    q.app (p ⁻¹ᵁ U) (p.app U v) •
      res ((Scheme.Modules.pullback q).obj J) le_top (pullbackGlobalSection q J t₀)
  rw [ht, InitialHodgeSection.res_smul]
  have hcomp : q.app (p ⁻¹ᵁ U) (p.app U v) = (q ≫ p).app U v := rfl
  rw [hcomp, heval]
  rfl

#print axioms puncture_ratio
#print axioms ratioMultiple_of_puncture


/-- Pullback of a rational ratio uses the homomorphism induced by the finite map. -/
lemma pulled_ratio (k : Type) [Field k] [CharZero k] {B Y : Scheme.{0}}
    [IsIntegral B] [IsIntegral Y] (p : Y ⟶ B) [IsDominant p]
    (f : Disk k ⟶ Y) [IsDominant (genericInclusion k ≫ f)]
    (r : B.functionField) (a : LaurentSeries k)
    (hr : RationalExpansion k B (genericInclusion k ≫ (f ≫ p)) r a) :
    ∃ rY : Y.functionField, RationalExpansion k Y (genericInclusion k ≫ f) rY a := by
  haveI : IsDominant (genericInclusion k ≫ (f ≫ p)) := by
    rw [← Category.assoc]
    infer_instance
  obtain ⟨φ, hφ⟩ := HigherLevelProjectiveRatiosR0194.functionField_pullback p
  obtain ⟨θY, hY⟩ := disk_field_map k f
  obtain ⟨θB, hB⟩ := disk_field_map k (f ≫ p)
  refine ⟨φ r, ?_⟩
  exact HigherLevelProjectiveRatiosR0194.rationalExpansion_pullback k p φ hφ
    (genericInclusion k ≫ f) (genericInclusion k ≫ (f ≫ p)) θY θB hY hB
    (RingHom.id _) (by simp) r a hr

#print axioms pulled_ratio
end ArithmeticThetaSharpKernelR0195.RatioUnaryRegularSectionsR0195

namespace ArithmeticThetaSharpKernelR0195
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open RatioUnaryRegularSectionsR0195

theorem ratio_unary_regular_sections :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin s → ℕ) (ν : Fin s → ℤ), (∀ i, 0 < m i ∧ Even (m i) ∧ m i ∣ N ∧ (-(m i : ℤ) ≤ 2*ν i ∧ 2*ν i < (m i : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ∀ (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k))) (ArithmeticThetaComponentDegreeR0184.hodge k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k)) H)) (b : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k))) (ArithmeticThetaComponentDegreeR0184.projection k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k))) b) (F : ArithmeticThetaSharpKernelR0195.CoverFrame k N H V J b C) (t₀ : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections C.space ((AlgebraicGeometry.Scheme.Modules.pullback C.map).obj J.line)), (∀ i, ArithmeticThetaPullback.pullbackGlobalSection F.disk ((AlgebraicGeometry.Scheme.Modules.pullback C.map).obj J.line) (t₀ i) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaSimultaneousUnaryR0187.unarySeries k N (m i) 0) • F.frame) → ArithmeticThetaSharpKernelR0195.RegularUnary k N s m ν H V J b C F t₀ := by
  intro k _ _ _ N s hN hNeven m ν hm D X H hH V ζ hζ hmark J b C F t₀ ht₀
  classical
  letI := C.integral
  letI := C.surjective
  letI := C.finite
  letI := C.smooth
  letI := F.dominant
  have hJ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback C.map).obj J.line) :=
    J.invertible.pullback C.map
  have hnormal : NormalAffine C.space := fun U hU =>
    ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed C.space k
      (C.map ≫ projection k (level N) D X (V.disk (closedPoint k))) U hU
  obtain ⟨P, hP, hPd⟩ := unary_powers_in_common_square_line k N s hN hNeven m ν hm
    D X H hH V ζ hζ hmark C.space
    (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k)))
    ((Scheme.Modules.pullback C.map).obj J.line) hJ
    (squarePull C.map J ≪≫ (Scheme.Modules.pullbackComp C.map
      (inclusion k (level N) D X (V.disk (closedPoint k)))).app H.line)
    F.disk F.triangle F.generator F.extendsGenerator F.frame F.isFrame F.square_eq
  have hK : 0 < exponent N := by
    rw [ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.exponent_formula]
    positivity
  have hr (i : Fin s) := centered_rational_ratio k N (m i) hN (hm i).1 (hm i).2.1
    (hm i).2.2.1 (ν i) (hm i).2.2.2 D X V ζ hζ hmark (F.disk ≫ C.map)
    (by simpa only [Category.assoc] using F.triangle)
  choose r hr using hr
  have ht (i : Fin s) : ∃ t : Sections C.space ((Scheme.Modules.pullback C.map).obj J.line),
      tensorPowerSection _ _ (exponent N) ⊤ t = P i ∧
      pullbackGlobalSection F.disk ((Scheme.Modules.pullback C.map).obj J.line) t =
        ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (unarySeries k N (m i) (ν i)) • F.frame := by
    obtain ⟨rY, hrY⟩ := pulled_ratio k C.map F.disk (r i) _ (hr i)
    exact same_curve_root k hnormal _ hJ F.disk (exponent N) hK (P i) F.frame
      (unarySeries k N (m i) (ν i)) (unarySeries k N (m i) 0)
      (unary_zero_ne_zero k N (m i) hN (hm i).1 (hm i).2.2.1)
      (t₀ i) (ht₀ i) (hPd i) rY hrY
  choose t htP htd using ht
  refine ⟨t, ?_, ?_⟩
  · have he : (fun i => tensorPowerSection _ _ (exponent N) ⊤ (t i)) = P := funext htP
    rw [he]
    exact hP
  · intro i
    refine ⟨?_, htd i, r i, hr i, ?_⟩
    · intro hz
      have hpne := hP.choose_spec.2 i |>.1
      apply hpne
      rw [← htP i, hz]
      have hzero := ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.tensor_smul
        C.space ((Scheme.Modules.pullback C.map).obj J.line) (exponent N) ⊤
        (0 : Γ(C.space, ⊤)) (0 : Sections C.space ((Scheme.Modules.pullback C.map).obj J.line))
      simpa only [zero_smul, zero_pow hK.ne'] using hzero
    · apply ratioMultiple_of_puncture k C.map (genericInclusion k ≫ F.disk) _ hJ
        (t i) (t₀ i) (r i) _
        (by simpa only [Category.assoc] using hr i)
      exact puncture_ratio k F.disk _ (t i) (t₀ i) F.frame _ _
        (unary_zero_ne_zero k N (m i) hN (hm i).1 (hm i).2.2.1) (htd i) (ht₀ i)

#print axioms ratio_unary_regular_sections
end ArithmeticThetaSharpKernelR0195
