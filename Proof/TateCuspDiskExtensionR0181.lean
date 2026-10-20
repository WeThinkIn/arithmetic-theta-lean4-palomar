module

public import TateJPoleR0181
public import TateLevelClassifyingParameterR0181
public import DescendedLegendreParameterR0179
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

@[expose] public section

/-! Extension of the actual classified Tate disk to the same compactification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaTateCuspsR0181
namespace DiskExtension
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLevelCompactificationR0179

/-- The structural square uses the given classifying map and the actual
inclusion of the power-series ring into its Laurent-series fraction field. -/
lemma structural_square
    (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (E : TateLevel k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b) :
    (b ≫ X.inclusion) ≫ X.projection = genericInclusion k ≫ diskStructure k := by
  obtain ⟨f, hf⟩ := hb
  rw [Category.assoc, X.over_eq]
  change b ≫ Spec.map (CommRingCat.ofHom (algebraMap k D.quotient.quotient.ring)) = _
  rw [hf.1]
  simp only [genericInclusion, diskStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- Properness and separatedness give precisely the two required morphism
equations, with uniqueness before imposing the boundary condition. -/
lemma unique_extension
    (k : Type u) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (E : TateLevel k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b) :
    ∃! d : Disk k ⟶ X.space,
      d ≫ X.projection = diskStructure k ∧ genericInclusion k ≫ d = b ≫ X.inclusion := by
  let S : ValuativeCommSq X.projection :=
    { R := PowerSeries k
      K := LaurentSeries k
      i₁ := b ≫ X.inclusion
      i₂ := diskStructure k
      commSq := ⟨structural_square k L D E X b hb⟩ }
  have hv : ValuativeCriterion X.projection := by
    have h := X.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨U⟩ := hv S
  refine ⟨U.default.l, ⟨U.default.fac_right, U.default.fac_left⟩, ?_⟩
  intro d hd
  exact congrArg CommSq.LiftStruct.l (U.uniq ⟨d, hd.2, hd.1⟩)

/-- A normalized positive j-pole cannot be evaluated at a Legendre parameter
defined over the power-series ring: its denominator is a unit there. -/
lemma pole_excludes_integral_parameter
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (α : LegendreRing k →+* PowerSeries k)
    (hj : legendreJ k (algebraMap (PowerSeries k) (LaurentSeries k)
      (α (parameter k))) = tateJ k L) : False := by
  let a := α (parameter k)
  let den := a^2 * (1-a)^2
  let num := 256 * (1-a+a^2)^3
  let ι := algebraMap (PowerSeries k) (LaurentSeries k)
  have hu : IsUnit (parameter k * (parameter k - 1)) := by
    have h := IsLocalization.Away.algebraMap_isUnit
      (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
    simpa only [map_mul, map_sub, map_one, parameter] using h
  have hd : IsUnit den := by
    have h := (hu.map α).pow 2
    convert h using 1 <;> simp only [map_mul, map_sub, map_one] <;> dsimp [den, a] <;> ring
  have hd0 : ι den ≠ 0 := (hd.map ι).ne_zero
  have hjd : tateJ k L * ι den = ι num := by
    rw [← hj]
    change (256 * (1-ι a+(ι a)^2)^3 / ((ι a)^2*(1-ι a)^2)) * ι den = _
    have he : ι den = (ι a)^2*(1-ι a)^2 := by simp [den]
    rw [he, div_mul_cancel₀ _ (he ▸ hd0)]
    simp only [num, map_mul, map_pow, map_add, map_sub, map_one, map_ofNat]
  obtain ⟨v, hv, hv0, hpole⟩ := (tate_j_pole k L hL heven).2
  have he : ι (v * den) = ι (num * PowerSeries.X^L) := by
    calc
      ι (v * den) = ι v * ι den := map_mul ι v den
      _ = tateJ k L * (ι PowerSeries.X)^L * ι den := by rw [← hpole]
      _ =
          (tateJ k L * ι den) * (ι PowerSeries.X)^L := by ring
      _ = ι num * ι (PowerSeries.X^L) := by rw [hjd, map_pow]
      _ = ι (num * PowerSeries.X^L) := (map_mul ι num (PowerSeries.X^L)).symm
  have hi : Function.Injective ι := IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  have hc := congrArg PowerSeries.constantCoeff (hi he)
  have hdconst : PowerSeries.constantCoeff den ≠ 0 := (hd.map PowerSeries.constantCoeff).ne_zero
  apply hdconst
  simpa only [map_mul, map_pow, hv0, PowerSeries.constantCoeff_X,
    zero_pow (by omega : L ≠ 0), one_mul, mul_zero] using hc

/-- An interior value at the closed point would factor the entire local disk
through the open base and hence give a forbidden integral Legendre parameter. -/
lemma closed_point_boundary
    (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (D : LevelData k L) (E : TateLevel k L) (X : Compactification k L D)
    (b : Puncture k ⟶ OpenBase k L D) (hb : ClassifiesTate k L D E b)
    (d : Disk k ⟶ X.space) (hd : genericInclusion k ≫ d = b ≫ X.inclusion) :
    d (closedPoint k) ∈ boundary k L D X := by
  letI := X.openImmersion
  intro hinside
  have hr : Set.range d ⊆ Set.range X.inclusion := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map d.continuous).mem_open
      X.inclusion.isOpenEmbedding.isOpen_range hinside
  let a := IsOpenImmersion.lift X.inclusion d hr
  have ha : a ≫ X.inclusion = d := IsOpenImmersion.lift_fac _ _ _
  have hab : genericInclusion k ≫ a = b := by
    apply (cancel_mono X.inclusion).mp
    rw [Category.assoc, ha, hd]
  obtain ⟨p, hp, _⟩ := descended_legendre_parameter k L hL heven D
  let α := (Spec.preimage (a ≫ p)).hom
  have hpar : pulledParameter k L D p b =
      algebraMap (PowerSeries k) (LaurentSeries k) (α (parameter k)) := by
    have hm : Spec.map (CommRingCat.ofHom
        ((algebraMap (PowerSeries k) (LaurentSeries k)).comp α)) = b ≫ p := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
      change genericInclusion k ≫ (a ≫ p) = _
      rw [← Category.assoc, hab]
    have hh := congrArg (fun f => (Spec.preimage f).hom (parameter k)) hm
    simpa only [Spec.preimage_map, CommRingCat.hom_ofHom, RingHom.comp_apply,
      pulledParameter] using hh.symm
  have hj := TateLevelClassifyingParameter.classifying_j k L D E p hp.1 b hb
  rw [hpar] at hj
  exact pole_excludes_integral_parameter k L hL heven α hj

end DiskExtension

open CategoryTheory AlgebraicGeometry ArithmeticThetaLevelCompactificationR0179

/-- The classified punctured Tate disk extends uniquely, and its closed point
lies in the actual boundary of the specified compactification. -/
theorem tate_cusp_disk_extension :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L),
    ∀ (D : LevelData k L) (E : TateLevel k L) (X : Compactification k L D)
      (b : Puncture k ⟶ OpenBase k L D), ClassifiesTate k L D E b →
      ∃! d : Disk k ⟶ X.space, Extends k L D X b d := by
  intro k _ _ L hL heven D E X b hb
  obtain ⟨d, hd, hu⟩ := DiskExtension.unique_extension k L D E X b hb
  refine ⟨d, ⟨hd.1, hd.2,
    DiskExtension.closed_point_boundary k L hL heven D E X b hb d hd.2⟩, ?_⟩
  intro d' hd'
  exact hu d' ⟨hd'.1, hd'.2.1⟩

#print axioms tate_cusp_disk_extension
end ArithmeticThetaTateCuspsR0181
