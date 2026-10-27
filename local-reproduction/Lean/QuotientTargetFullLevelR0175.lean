import FullLevelCyclicLiftsR0175
import FullLevelTorsionSplittingR0175

/-! The two specified lifts give a full marking on the actual cyclic quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeCyclicQuotientR0173 ArithmeticThetaRelativeIsogenyHodgeR0172
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential
open FullLevelCyclicLiftsR0175

namespace QuotientTargetFullLevelR0175

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

/-- Scheme-theoretic kernel equality kills each of its labeled sections. -/
lemma quotient_kills_multiple {m : ℕ} (P : CyclicSection R W G m)
    (V : WeierstrassCurve R) (f : PointedMap R W V) (hf : IsQuotient R W G P f)
    (i : Fin m) : multiple R W G P i ≫ f.map = origin R V := by
  have ho : origin R V ≫ structureMap R V = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R V).property
  letI : IsProper (structureMap R V) :=
    WeierstrassProjModel.projModelStrCR_isProper V.toProjective
  haveI : IsClosedImmersion (origin R V ≫ structureMap R V) := by
    rw [ho]; infer_instance
  haveI : IsClosedImmersion (origin R V) :=
    IsClosedImmersion.of_comp _ (structureMap R V)
  have hle : (origin R V).ker ≤ (multiple R W G P i ≫ f.map).ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le, hf.2.2.2.2]
    exact iInf_le _ i
  let a := IsClosedImmersion.lift (origin R V) (multiple R W G P i ≫ f.map) hle
  have ha : a ≫ origin R V = multiple R W G P i ≫ f.map :=
    IsClosedImmersion.lift_fac _ _ _
  have haid : a = 𝟙 _ := by
    have he := congrArg (fun k => k ≫ structureMap R V) ha
    simpa only [Category.assoc, ho, Category.comp_id, f.over_eq, multiple,
      G.schemeNsmul_over, P.over_eq] using he
  rw [← ha, haid, Category.id_comp]

end QuotientTargetFullLevelR0175

open QuotientTargetFullLevelR0175

/-- Full target marking, with the exact source-lift labels, on the same quotient. -/
theorem QuotientTargetFullLevelR0175.quotient_with_enumeration :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 0 < L) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hdiv : m*N ∣ L) (A : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) , ∃ (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G m) (V : WeierstrassCurve R) (hV : V.IsElliptic) (H : ArithmeticThetaRelativeKatoR0169.Law R V) (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R V H) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (T : ArithmeticThetaFullLevelCoverR0175.FullLevel R V H N (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), P.point = ArithmeticThetaFullLevelCoverR0175.kernelPoint R W G m A ∧ ArithmeticThetaRelativeCyclicQuotientR0173.IsQuotient R W G P f ∧ T.x.val = CategoryTheory.CategoryStruct.comp (ArithmeticThetaFullLevelCoverR0175.liftPoint R W G m N 0 1 A) f.map ∧ T.y.val = CategoryTheory.CategoryStruct.comp (ArithmeticThetaFullLevelCoverR0175.liftPoint R W G m N 1 0 A) f.map ∧
  ∃ e : (torsionIdeal R V H N).subscheme ≅ Spec (CommRingCat.of ((Fin N × Fin N) → R)),
    e.hom ≫ torsionStructure R N = (torsionIdeal R V H N).subschemeι ≫ structureMap R V ∧
    ∀ i j : Fin N, torsionComponent R N i j ≫ (e.inv ≫ (torsionIdeal R V H N).subschemeι) =
      coordinatePoint R V H T i j := by
  intro R _ _ _ _ _ W _ G hG L hL m N hm hN hdiv A
  obtain ⟨P, hP, hlifts⟩ := full_level_cyclic_lifts R W G hG L hL m N hm hN hdiv A
  obtain ⟨V, hV, f, hf⟩ := relative_cyclic_quotient_existence R W G hG m hm P
  letI : V.IsElliptic := hV
  have hgeom := relative_curve_geometry R V
  letI : SmoothOfRelativeDimension 1 (structureMap R V) := hgeom.2.2.2.2.2.1
  letI : GeometricallyIntegral (structureMap R V) := hgeom.2.2.2.2.2.2
  have htwo : IsUnit (2 : R) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  letI : Invertible (2 : R) := htwo.invertible
  obtain ⟨_, _, _, H, _, hone, hcomm⟩ := WeierstrassProjModel.relativeGroupLaw_exists V
    (inferInstance : Smooth (structureMap R V)) hgeom.2.2.2.2.2.2 V.isUnit_Δ
  change Law R V at H
  have hH : IsOriginLaw R V H := ⟨hone, hcomm⟩
  letI := sectionGroup G hG
  letI := sectionGroup H hH
  let F : sections (R := R) (W := W) →* sections (R := R) (W := V) := {
    toFun := mapPoint R W f (𝟙 (Base R))
    map_one' := PointedRelativeGroupHom.map_one R W V G H hG hH f (𝟙 (Base R))
    map_mul' := (pointed_relative_group_hom R W G hG V H hH f).1 (Base R) (𝟙 (Base R)) }
  let sx := A.x ^ (L/(m*N))
  let sy := A.y ^ (L/N)
  have hx : A.x ^ L = 1 := by
    have h := A.killed_x
    rw [RelativeKatoFiberSpecialization.nsmul_pow] at h
    exact h
  have hy : A.y ^ L = 1 := by
    have h := A.killed_y
    rw [RelativeKatoFiberSpecialization.nsmul_pow] at h
    exact h
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m N) hdiv
  have hNL : N ∣ L := dvd_trans (dvd_mul_left N m) hdiv
  have hc : L / m * m = L := Nat.div_mul_cancel hmL
  have hd : L / N * N = L := Nat.div_mul_cancel hNL
  have hq : L / (m*N) * (m*N) = L := Nat.div_mul_cancel hdiv
  have hqc : L / (m*N) * N = L / m := by nlinarith [hc, hq]
  have hkernel : F (A.x ^ (L/m)) = 1 := by
    apply Subtype.ext
    change (A.x ^ (L/m)).val ≫ f.map = (H.one (𝟙 (Base R))).val
    rw [hH.1, Category.id_comp]
    have hk := quotient_kills_multiple R W G P V f hf ⟨1 % m, Nat.mod_lt _ hm⟩
    have he : multiple R W G P ⟨1 % m, Nat.mod_lt _ hm⟩ = (A.x ^ (L/m)).val := by
      rw [multiple, hP]
      change (G.nsmul (𝟙 (Base R)) (L/m) A.x).val ≫ G.schemeNsmul (1 % m) = _
      rw [nsmul_comp, RelativeKatoFiberSpecialization.nsmul_pow]
      have hp : (A.x ^ (L/m)) ^ m = 1 := by rw [← pow_mul, hc, hx]
      simpa only [pow_mul, pow_one] using congrArg Subtype.val (pow_mod hp 1)
    rwa [he] at hk
  have hkillx : H.nsmul (𝟙 (Base R)) N (F sx) = H.one (𝟙 (Base R)) := by
    rw [RelativeKatoFiberSpecialization.nsmul_pow]
    change (F sx) ^ N = 1
    rw [← map_pow]
    change F ((A.x ^ (L/(m*N))) ^ N) = 1
    rw [← pow_mul, hqc, hkernel]
  have hkilly : H.nsmul (𝟙 (Base R)) N (F sy) = H.one (𝟙 (Base R)) := by
    rw [RelativeKatoFiberSpecialization.nsmul_pow]
    change (F sy) ^ N = 1
    rw [← map_pow]
    change F ((A.y ^ (L/N)) ^ N) = 1
    rw [← pow_mul, hd, hy, map_one]
  have hlift (a b : ℕ) : (F (sx ^ b * sy ^ a)).val = liftPoint R W G m N a b A ≫ f.map := by
    change (sx ^ b * sy ^ a).val ≫ f.map = _
    dsimp [liftPoint, sx, sy]
    simp only [RelativeKatoFiberSpecialization.nsmul_pow, pow_mul]
    rfl
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  let T : FullLevel R V H N (𝟙 (Base R)) := {
    x := F sx
    y := F sy
    killed_x := hkillx
    killed_y := hkilly
    avoids := by
      intro i j hij
      have hQ := hlifts j i (hij.symm)
      have ha := (cyclic_quotient_torsion_kato_value R W G hG m hm P V H hH f hf
        N hN (liftPoint R W G m N j.val i.val A) hQ).2.1
      have he : (H.mul (𝟙 (Base R)) (H.nsmul (𝟙 (Base R)) i.val (F sx))
          (H.nsmul (𝟙 (Base R)) j.val (F sy))).val =
          liftPoint R W G m N j.val i.val A ≫ f.map := by
        simp only [RelativeKatoFiberSpecialization.nsmul_pow]
        change ((F sx) ^ i.val * (F sy) ^ j.val).val = _
        simpa only [map_mul, map_pow] using hlift j.val i.val
      rw [he]
      exact ha }
  -- Certify that this marking enumerates the entire actual target N-torsion.
  obtain ⟨e, he, hcomponents⟩ := full_level_torsion_splitting R V H hH N hN T
  refine ⟨P, V, hV, H, hH, f, T, hP, hf, ?_, ?_, e, he, hcomponents⟩
  · simpa only [pow_one, pow_zero, mul_one] using hlift 0 1
  · simpa only [pow_one, pow_zero, one_mul] using hlift 1 0


/-- The frozen target-marking endpoint, from the quotient with its torsion enumeration. -/
theorem quotient_target_full_level :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 0 < L) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hdiv : m*N ∣ L) (A : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) , ∃ (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G m) (V : WeierstrassCurve R) (hV : V.IsElliptic) (H : ArithmeticThetaRelativeKatoR0169.Law R V) (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R V H) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (T : ArithmeticThetaFullLevelCoverR0175.FullLevel R V H N (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), P.point = ArithmeticThetaFullLevelCoverR0175.kernelPoint R W G m A ∧ ArithmeticThetaRelativeCyclicQuotientR0173.IsQuotient R W G P f ∧ T.x.val = CategoryTheory.CategoryStruct.comp (ArithmeticThetaFullLevelCoverR0175.liftPoint R W G m N 0 1 A) f.map ∧ T.y.val = CategoryTheory.CategoryStruct.comp (ArithmeticThetaFullLevelCoverR0175.liftPoint R W G m N 1 0 A) f.map := by
  intro R _ _ _ _ _ W _ G hG L hL m N hm hN hdiv A
  obtain ⟨P, V, hV, H, hH, f, T, hP, hf, hx, hy, _⟩ :=
    QuotientTargetFullLevelR0175.quotient_with_enumeration R W G hG L hL m N hm hN hdiv A
  exact ⟨P, V, hV, H, hH, f, T, hP, hf, hx, hy⟩

end ArithmeticThetaFullLevelCoverR0175
