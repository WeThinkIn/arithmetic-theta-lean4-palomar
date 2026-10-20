module

public import RatioUnaryRegularSectionsR0195
public import FieldHigherLevelProjectiveRatiosR0238
public import FieldUnaryPowersInCommonSquareLineR0238

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaArithmeticCommonCoverR0238
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSharpKernelR0195
open ArithmeticThetaSharpKernelR0195.RatioUnaryRegularSectionsR0195
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaCompactUnaryR0183 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaSharpCoverR0194

namespace FieldRatioUnaryRegularSectionsR0238
/-- The ratios live on the original component and use the specified disk map. -/
lemma centered_rational_ratio (k : Type) [Field k] [CharZero k]
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
  obtain ⟨g, hg, _, r, _, hr⟩ := field_higher_level_projective_ratios k (level N) m hm
    (by unfold level; positivity) he (twice_dvd_level N m hd) D X V ζ hζ hmark
  have hgf : g = f := (cancel_mono (inclusion k (level N) D X (V.disk (closedPoint k)))).mp
    (hg.trans hf.symm)
  subst g
  refine ⟨r (residue m hm ν), ?_⟩
  have h := hr (residue m hm ν)
  rw [unary_bridge k N m hN hm hd ν hν _ (residue_modEq m hm ν),
    unary_bridge k N m hN hm hd 0 (by constructor <;> omega) ⟨0, hm⟩ (Int.ModEq.refl _)] at h
  exact h

end FieldRatioUnaryRegularSectionsR0238

/-- Regular unary sections on the prescribed cover over the original coefficient field. -/
theorem field_ratio_unary_regular_sections :
    ∀ (k : Type) [Field k] [CharZero k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin s → ℕ) (ν : Fin s → ℤ), (∀ i, 0 < m i ∧ Even (m i) ∧ m i ∣ N ∧ (-(m i : ℤ) ≤ 2*ν i ∧ 2*ν i < (m i : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ∀ (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k))) (ArithmeticThetaComponentDegreeR0184.hodge k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k)) H)) (b : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k))) (ArithmeticThetaComponentDegreeR0184.projection k (ArithmeticThetaCompactUnaryR0183.level N) D X (V.disk (ArithmeticThetaTateCuspsR0181.closedPoint k))) b) (F : ArithmeticThetaSharpKernelR0195.CoverFrame k N H V J b C) (t₀ : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections C.space ((AlgebraicGeometry.Scheme.Modules.pullback C.map).obj J.line)), (∀ i, ArithmeticThetaPullback.pullbackGlobalSection F.disk ((AlgebraicGeometry.Scheme.Modules.pullback C.map).obj J.line) (t₀ i) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaSimultaneousUnaryR0187.unarySeries k N (m i) 0) • F.frame) → ArithmeticThetaSharpKernelR0195.RegularUnary k N s m ν H V J b C F t₀ := by
  intro k _ _ N s hN hNeven m ν hm D X H hH hgH V ζ hζ hmark J b C F t₀ ht₀
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
  obtain ⟨P, hP, hPd⟩ := field_unary_powers_in_common_square_line k N s hN hNeven m ν hm
    D X H hH hgH V ζ hζ hmark C.space
    (C.map ≫ inclusion k (level N) D X (V.disk (closedPoint k)))
    ((Scheme.Modules.pullback C.map).obj J.line) hJ
    (squarePull C.map J ≪≫ (Scheme.Modules.pullbackComp C.map
      (inclusion k (level N) D X (V.disk (closedPoint k)))).app H.line)
    F.disk F.triangle F.generator F.extendsGenerator F.frame F.isFrame F.square_eq
  have hK : 0 < exponent N := by
    rw [ArithmeticThetaCompactUnaryR0183.TateTorsionNormalizedIntegrality.exponent_formula]
    positivity
  have hr (i : Fin s) := FieldRatioUnaryRegularSectionsR0238.centered_rational_ratio k N (m i) hN (hm i).1 (hm i).2.1
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

#print axioms field_ratio_unary_regular_sections
end ArithmeticThetaArithmeticCommonCoverR0238
