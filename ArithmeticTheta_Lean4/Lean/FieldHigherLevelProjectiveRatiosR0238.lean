import HigherLevelProjectiveRatiosR0194
import FieldFullLevelProjectiveRatiosR0238

/-! Arithmetic projective ratios transported along actual full-level forgetting. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaArithmeticCommonCoverR0238
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaSharpCoverR0194
open ArithmeticThetaSharpCoverR0194.HigherLevelProjectiveRatiosR0194
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaCompatibleLevelR0178

namespace FieldHigherLevelProjectiveRatiosR0238
variable (k : Type) [Field k] [CharZero k]

lemma higher_level_mul (m r : ℕ) (hm : 0 < m) (he : Even m) (hr : 0 < r)
    (D : LevelData k (r*(2*m))) (X : Compactification k (r*(2*m)) D)
    (V : DiskTest k (r*(2*m)) D X) (ζ : k) (hζ : IsPrimitiveRoot ζ (r*(2*m)))
    (hV : CanonicalMarking k (r*(2*m)) ζ V.level) :
    ProjectiveRatios k (r*(2*m)) m hm D X V := by
  have hm2 : 0 < 2*m := Nat.mul_pos (by decide) hm
  have h3 : 3 ≤ 2*m := by obtain ⟨n, hn⟩ := he; omega
  have he2 : Even (2*m) := even_two.mul_right m
  have hL : 3 ≤ r*(2*m) := h3.trans (Nat.le_mul_of_pos_left _ hr)
  have heL : Even (r*(2*m)) := he2.mul_left r
  have hdiv : 2*m ∣ r*(2*m) := dvd_mul_left _ _
  obtain ⟨atlas⟩ := legendre_level_family_construction k (2*m) h3
  obtain ⟨two, htwo, cover, quotient, _⟩ :=
    normal_affine_classifying_construction k (2*m) h3 he2 atlas
  let E : LevelData k (2*m) := ⟨atlas, two, htwo, cover, quotient⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion k (2*m) h3 he2 E
  have hζd : IsPrimitiveRoot (ζ^r) (2*m) := IsPrimitiveRoot.pow (Nat.mul_pos hr hm2) hζ rfl
  obtain ⟨Tlevel, hTlevel⟩ := tate_full_level_marking k (2*m) h3 he2 (ζ^r) hζd
  obtain ⟨b, hb, _⟩ := TateLevelClassifyingParameter.classifying_exists_unique k (2*m) h3 he2 E Tlevel
  obtain ⟨Ttest, hlevel, hbase⟩ := (tate_hodge_comparison_tests k (2*m) h3 he2 E).1 Tlevel b hb
  obtain ⟨disk, hdisk, _⟩ := tate_cusp_disk_extension k (2*m) h3 he2 E Tlevel Y b hb
  let T : DiskTest k (2*m) E Y :=
    { toTest := Ttest, disk := disk, extends_eq := hbase.symm ▸ hdisk }
  have hT : CanonicalMarking k (2*m) (ζ^r) T.level := by
    change CanonicalMarking k (2*m) (ζ^r) Ttest.level
    rw [hlevel]
    exact hTlevel
  have hR := field_full_level_projective_ratios k m hm he E Y T (ζ^r) hζd hT
  obtain ⟨f, ⟨hf, F, hF, _⟩, _⟩ := compactified_level_forgetting k (r*(2*m)) hL heL
    (2*m) h3 he2 hdiv D E X Y
  obtain ⟨ell, hell, _⟩ := ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k r hr
  apply transport_projectiveRatios k m r hm hr D E X Y V T ell hell.1 F _ hR
  exact reduction_disk k (2*m) r (by omega) he2 hr D E X Y V T ζ hζ hT hV ell hell.1 f hf F hF


end FieldHigherLevelProjectiveRatiosR0238

/-- Complete unary ratios on every positive divisible full level over the original field. -/
theorem field_higher_level_projective_ratios :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ) (hm : 0 < m),
      0 < L → Even m → 2*m ∣ L →
      ∀ (D : LevelData k L) (X : Compactification k L D),
      ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
      CanonicalMarking k L ζ V.level → ProjectiveRatios k L m hm D X V := by
  intro k _ _ L m hm hL he hdiv
  obtain ⟨r, h⟩ := hdiv
  rw [Nat.mul_comm] at h
  subst L
  have hr : 0 < r := Nat.pos_of_mul_pos_right hL
  exact FieldHigherLevelProjectiveRatiosR0238.higher_level_mul k m r hm he hr


#print axioms field_higher_level_projective_ratios
end ArithmeticThetaArithmeticCommonCoverR0238
