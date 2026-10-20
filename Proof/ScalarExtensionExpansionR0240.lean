module

public import ScalarExtensionDefinitionsR0240

@[expose] public section

/-! Full expansions under the specified coefficient extension and frame transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaScalarExtensionR0240
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaTensorPower
open ArithmeticThetaPullback ArithmeticThetaTateCuspsR0181 ArithmeticThetaNormalizedSections
open ArithmeticThetaFiniteFieldModelsR0221
open ArithmeticThetaFiniteFieldModelsR0221.FinitePowerSections
open ArithmeticThetaFiniteFieldModelsR0221.FiniteLineHoms

namespace ExpansionProof

lemma power_smul {X Y : Scheme} (p : X ⟶ Y) (J : Y.Modules) (n : ℕ)
    (a : Γ(Y, ⊤)) (s : (tensorPower Y J n).presheaf.obj (Opposite.op ⊤)) :
    pullbackPowerSection p J n (a • s) = p.appTop a • pullbackPowerSection p J n s := by
  unfold pullbackPowerSection pullbackGlobalSection
  rw [((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tensorPower Y J n)).app_smul]
  exact Scheme.Modules.Hom.app_smul _ _ _

lemma comp_section {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (J : Z.Modules) (hJ : IsLineBundle Z J) (n : ℕ)
    (s : (tensorPower Z J n).presheaf.obj (Opposite.op ⊤)) :
    (powerIso ((Scheme.Modules.pullbackComp p q).app J) n).hom.app ⊤
      (pullbackPowerSection p ((Scheme.Modules.pullback q).obj J) n
        (pullbackPowerSection q J n s)) = pullbackPowerSection (p ≫ q) J n s := by
  have hc := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (powerComparison_comp p q J hJ n))
    (pullbackGlobalSection p ((Scheme.Modules.pullback q).obj (tensorPower Z J n))
      (pullbackGlobalSection q (tensorPower Z J n) s))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hc
  erw [← pullbackGlobalSection_map] at hc
  change _ = (pullback_tensorPower_iso X Z (p ≫ q) J n).hom.app ⊤
    (((Scheme.Modules.pullbackComp p q).app (tensorPower Z J n)).hom.app ⊤
      (pullbackGlobalSection p _ (pullbackGlobalSection q _ s))) at hc
  rw [show ((Scheme.Modules.pullbackComp p q).app (tensorPower Z J n)).hom.app ⊤
      (pullbackGlobalSection p _ (pullbackGlobalSection q _ s)) =
      pullbackGlobalSection (p ≫ q) _ s from pullbackComp_hom_unit p q _ ⊤ s] at hc
  exact hc

lemma triangle_section {X Y Z : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (t : X ⟶ Z) (ht : p ≫ q = t) (J : Z.Modules) (hJ : IsLineBundle Z J) (n : ℕ)
    (s : (tensorPower Z J n).presheaf.obj (Opposite.op ⊤)) :
    (powerIso ((Scheme.Modules.pullbackComp p q).app J ≪≫
      (Scheme.Modules.pullbackCongr ht).app J) n).hom.app ⊤
      (pullbackPowerSection p ((Scheme.Modules.pullback q).obj J) n
        (pullbackPowerSection q J n s)) = pullbackPowerSection t J n s := by
  subst t
  simpa only [show (Scheme.Modules.pullbackCongr (rfl : p ≫ q = p ≫ q)).app J =
    Iso.refl _ from rfl, Iso.trans_refl] using comp_section p q J hJ n s

lemma iso_injective {X : Scheme} {H J : X.Modules} (e : H ≅ J) :
    Function.Injective (e.hom.app ⊤) := by
  intro x y h
  have hx := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤) e.hom_inv_id) x
  have hy := ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤) e.hom_inv_id) y
  exact hx.symm.trans ((congrArg (fun z => e.inv.app ⊤ z) h).trans hy)

lemma square_section {X Y Z W : Scheme} (p : X ⟶ Y) (q : Y ⟶ Z)
    (r : X ⟶ W) (t : W ⟶ Z) (ht : p ≫ q = r ≫ t)
    (J : Z.Modules) (hJ : IsLineBundle Z J) (n : ℕ)
    (s : (tensorPower Z J n).presheaf.obj (Opposite.op ⊤)) :
    (powerIso ((Scheme.Modules.pullbackComp p q).app J ≪≫
      (Scheme.Modules.pullbackCongr ht).app J ≪≫
      ((Scheme.Modules.pullbackComp r t).app J).symm) n).hom.app ⊤
      (pullbackPowerSection p ((Scheme.Modules.pullback q).obj J) n
        (pullbackPowerSection q J n s)) =
    pullbackPowerSection r ((Scheme.Modules.pullback t).obj J) n
      (pullbackPowerSection t J n s) := by
  apply iso_injective (powerIso ((Scheme.Modules.pullbackComp r t).app J) n)
  have hi : (((Scheme.Modules.pullbackComp p q).app J ≪≫
      (Scheme.Modules.pullbackCongr ht).app J ≪≫
      ((Scheme.Modules.pullbackComp r t).app J).symm) ≪≫
      (Scheme.Modules.pullbackComp r t).app J) =
      (Scheme.Modules.pullbackComp p q).app J ≪≫ (Scheme.Modules.pullbackCongr ht).app J := by
    simp
  have hp := congrArg (fun e => (powerIso e n).hom.app ⊤) hi
  rw [PointedSquareCover.powerIso_trans] at hp
  have he := ConcreteCategory.congr_hom hp
    (pullbackPowerSection p ((Scheme.Modules.pullback q).obj J) n
      (pullbackPowerSection q J n s))
  exact he.trans ((triangle_section p q (r ≫ t) ht J hJ n s).trans
    (comp_section r t J hJ n s).symm)

open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaArithmeticFieldR0231 (theta expanded integralTheta)
open ArithmeticThetaCompactUnaryR0183 (level)

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
variable {n h : ℕ} {A : Matrices n h}

omit [CharZero k] [CharZero l] in
lemma mapped_theta (ι : k →+* l) (B : Matrix (Fin n) (Fin n) ℤ) :
    PowerSeries.map ι (theta k B) = theta l B := by
  ext m
  simp [theta]

omit [CharZero k] [CharZero l] in
lemma mapped_subst (ι : k →+* l) (d : ℕ) (hd : d ≠ 0) (f : PowerSeries k) :
    PowerSeries.map ι (PowerSeries.subst (PowerSeries.X ^ d) f) =
      PowerSeries.subst (PowerSeries.X ^ d) (PowerSeries.map ι f) := by
  ext m
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_subst_X_pow hd]
  split_ifs <;> simp

lemma basis_expansion (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (i : Fin h) :
    pullbackPowerSection G.frame.disk (ArithmeticThetaArithmeticFieldR0231.half G) n
      (G.sections i) =
    scalar (PowerSeries k)
      (PowerSeries.subst (PowerSeries.X ^ level (commonN A)) (theta k (A i))) •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback G.frame.disk).obj
        (ArithmeticThetaArithmeticFieldR0231.half G)) n ⊤ G.frame.frame := by
  classical
  simpa [baseScalar, scalar, ArithmeticThetaArithmeticFieldR0231.expanded, Pi.single_apply, apply_ite] using
    G.expansion (Pi.single i 1)

omit [CharZero l] in
lemma transported_basis (ι : k →+* l)
    (G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A) (D : DiskLift ι G)
    (hL : level (commonN A) ≠ 0) (i : Fin h) :
    pullbackPowerSection D.map (line ι G) n (sections ι G i) =
      scalar (PowerSeries l)
        (PowerSeries.subst (PowerSeries.X ^ level (commonN A)) (theta l (A i))) •
        tensorPowerSection (Disk l) ((Scheme.Modules.pullback D.map).obj (line ι G)) n ⊤
          (frame ι G D) := by
  have hJ : IsLineBundle G.cover.space (ArithmeticThetaArithmeticFieldR0231.half G) :=
    ArithmeticThetaSquareLinesR0192.DiskFrameComparisonAdapterR0192.line_of_invertible _
      (G.half.invertible.pullback G.cover.map)
  apply iso_injective (powerIso (frameComparison ι G D) n)
  rw [show (powerIso (frameComparison ι G D) n).hom.app ⊤
      (pullbackPowerSection D.map (line ι G) n (sections ι G i)) =
      pullbackPowerSection (diskMap ι)
        ((Scheme.Modules.pullback G.frame.disk).obj (ArithmeticThetaArithmeticFieldR0231.half G)) n
        (pullbackPowerSection G.frame.disk (ArithmeticThetaArithmeticFieldR0231.half G) n
          (G.sections i)) from
      square_section D.map (projection ι G) (diskMap ι) G.frame.disk D.triangle
        (ArithmeticThetaArithmeticFieldR0231.half G) hJ n (G.sections i)]
  rw [basis_expansion, power_smul]
  have hs (f : PowerSeries k) : (diskMap ι).appTop (scalar (PowerSeries k) f) =
      scalar (PowerSeries l) (PowerSeries.map ι f) :=
    GlobalFamilyTorsionValueR0180.scalar_natural (PowerSeries.map ι) f
  rw [hs, mapped_subst ι _ hL, mapped_theta]
  rw [Scheme.Modules.Hom.app_smul, powerIso_section]
  congr 1
  unfold pullbackPowerSection
  erw [pullback_tensorPower_section]
  congr 1
  exact (ConcreteCategory.congr_hom (congrArg (fun f => f.app ⊤)
    (frameComparison ι G D).inv_hom_id)
      (pullbackGlobalSection (diskMap ι) _ G.frame.frame)).symm

end ExpansionProof
open ExpansionProof

/-- The same compact sections have their complete theta expansions in the
canonical transported original frame, for every new-field coefficient vector. -/
theorem scalar_extension_expansion :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l)
      (n h : ℕ), 0 < n → 0 < h → ∀ (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ G : ArithmeticThetaArithmeticFieldR0231.MatrixData k A,
      ∀ D : DiskLift ι G, Expansion ι G D := by
  intro k l _ _ _ _ ι n h hn hh A hA G D
  classical
  have hN : 0 < commonN A := (indexed_full_unary_factorization n h hn hh A hA).1
  have hL : ArithmeticThetaCompactUnaryR0183.level (commonN A) ≠ 0 := by
    unfold ArithmeticThetaCompactUnaryR0183.level
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos hN 2))
  intro c
  have hc (z : l) : D.map.appTop (baseScalar l (structureMap ι G) z) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries l) (PowerSeries.C z) := by
    change (D.map ≫ structureMap ι G).appTop (ArithmeticThetaOpenHodgeR0180.scalar l z) = _
    rw [D.over_eq]
    exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyTorsionValueR0180.scalar_natural (algebraMap l (PowerSeries l)) z
  have hs (v : Fin h → (tensorPower (Space ι G) (line ι G) n).presheaf.obj (Opposite.op ⊤)) :
      pullbackPowerSection D.map (line ι G) n (∑ i, v i) =
        ∑ i, pullbackPowerSection D.map (line ι G) n (v i) := by
    simp only [pullbackPowerSection, pullbackGlobalSection, map_sum]
  unfold ArithmeticThetaFieldImageR0233.combination
  rw [hs]
  simp only [power_smul, hc, transported_basis ι G D hL]
  unfold ArithmeticThetaArithmeticFieldR0231.expanded
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X_pow hL), map_sum]
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.smul_eq_C_mul,
    ArithmeticThetaOpenHodgeR0180.scalar, map_sum, map_mul, Finset.sum_smul, mul_smul, PowerSeries.subst_C]
  rfl

#print axioms scalar_extension_expansion

end ArithmeticThetaScalarExtensionR0240
