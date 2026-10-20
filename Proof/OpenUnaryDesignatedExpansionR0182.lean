module

public import OpenDiscriminantFullTateExpansionR0182
public import TateHodgeComparisonTestsR0182
public import ActualUnaryPowerValuesR0160
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
public import Theorems.Thm_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom

@[expose] public section

/-! Supporting comparisons for the designated unary expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180

/-- The designated characteristic already belongs to the chosen fundamental
interval. In particular the endpoint with exponent zero needs no division by
that exponent. -/
lemma residue_bounds (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hNeven : Even N) (hmN : m ∣ N) (ν : ℤ)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    0 ≤ ((N/2 : ℕ) : ℤ) + ((N/m : ℕ) : ℤ)*ν ∧
      ((N/2 : ℕ) : ℤ) + ((N/m : ℕ) : ℤ)*ν < (N : ℤ) := by
  have hhalf : 2*(N/2) = N := Nat.mul_div_cancel' (even_iff_two_dvd.mp hNeven)
  have hmul : m*(N/m) = N := Nat.mul_div_cancel' hmN
  have hq : 0 < N/m := Nat.div_pos (Nat.le_of_dvd hN hmN) hm
  have hhalf' : (2 : ℤ)*((N/2 : ℕ) : ℤ) = N := by exact_mod_cast hhalf
  have hmul' : (m : ℤ)*((N/m : ℕ) : ℤ) = N := by exact_mod_cast hmul
  have hq' : (0 : ℤ) < ((N/m : ℕ) : ℤ) := by exact_mod_cast hq
  have hlo := mul_nonneg hq'.le (show (0 : ℤ) ≤ (m : ℤ)+2*ν by omega)
  have hhi := mul_pos hq' (show (0 : ℤ) < (m : ℤ)-2*ν by omega)
  constructor <;> nlinarith

lemma residue_cast (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hNeven : Even N) (hmN : m ∣ N) (ν : ℤ)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    (unaryResidue m N ν : ℤ) = ((N/2 : ℕ) : ℤ) + ((N/m : ℕ) : ℤ)*ν := by
  obtain ⟨hlo,hhi⟩ := residue_bounds m N hm hN hNeven hmN ν hν
  unfold unaryResidue
  rw [Int.emod_eq_of_lt hlo hhi, Int.toNat_of_nonneg hlo]

lemma residue_lt (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hNeven : Even N) (hmN : m ∣ N) (ν : ℤ)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) : unaryResidue m N ν < N := by
  have h := (residue_bounds m N hm hN hNeven hmN ν hν).2
  rw [← residue_cast m N hm hN hNeven hmN ν hν] at h
  exact_mod_cast h

lemma half_nonzero (N : ℕ) (hN : 0 < N) (hNeven : Even N) :
    N/2 ≠ 0 ∧ N/2 < N := by
  have hhalf : 2*(N/2) = N := Nat.mul_div_cancel' (even_iff_two_dvd.mp hNeven)
  omega

/-- Both source and target periods agree with the literal unary provider. -/
lemma period_parameters (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hmN : m ∣ N) :
    0 < N^2/m ∧ 24*(N^2/m)*m = 24*N^2 ∧
      24*(N^2/m)*m^2 = (24*N^2)*m ∧ m*N ∣ 24*N^2 := by
  have hd : m ∣ N^2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hmN N
  have hmul : (N^2/m)*m = N^2 := Nat.div_mul_cancel hd
  refine ⟨Nat.div_pos (Nat.le_of_dvd (by positivity) hd) hm, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · obtain ⟨a, ha⟩ := hmN
    refine ⟨24*a, ?_⟩
    rw [ha]
    ring

/-- The source lift remains nonidentity in the prescribed quotient, including
the characteristic with zero toric exponent. -/
lemma designated_point_conditions (k : Type) [Field k] [CharZero k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N)
    (D : LevelData k (24*N^2))
    (Q : Quotient D.atlas.quotient.ring (levelFamily k (24*N^2) D.atlas) m
      (kernelPoint k (24*N^2) D.atlas m))
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    (liftPoint k (24*N^2) D.atlas m N (unaryResidue m N ν) (N/2) ≫ Q.arrow.map) ≫
      Q.target.law.schemeNsmul N = zero Q.target ∧
    Disjoint
      (Set.range (liftPoint k (24*N^2) D.atlas m N (unaryResidue m N ν) (N/2) ≫ Q.arrow.map))
      (Set.range (zero Q.target)) := by
  let E := levelFamily k (24*N^2) D.atlas
  have hL : 0 < 24*N^2 := by positivity
  have hmNL := (period_parameters m N hm hN hmN).2.2.2
  have hmL : m ∣ 24*N^2 := dvd_trans (dvd_mul_right m N) hmNL
  obtain ⟨P,hP⟩ := GlobalLevelCyclicQuotientR0180.cyclic_of_level E hL D.atlas.marking m hm hmL
  let a : Fin N := ⟨unaryResidue m N ν, residue_lt m N hm hN hNeven hmN ν hν⟩
  let b : Fin N := ⟨N/2, (half_nonzero N hN hNeven).2⟩
  have hl := OpenLevelNormalizedHodgePowerR0180.level_lift_conditions E hL D.atlas.marking
    m N hm hN hmNL a b (Or.inr (half_nonzero N hN hNeven).1)
  have hp : liftPoint k (24*N^2) D.atlas m N a.val b.val ≫ E.projection = 𝟙 _ :=
    (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (24*N^2/(m*N)*b.val) D.atlas.marking.x)
      (E.law.nsmul (𝟙 _) (24*N^2/N*a.val) D.atlas.marking.y)).property
  exact OpenLevelNormalizedHodgePowerR0180.quotient_lift E hm P _ hP Q N _ hp
    (by simpa only [hP, kernelPoint, liftPoint] using hl.1)
    (by simpa only [hP, kernelPoint, liftPoint] using hl.2)

/-- The exponent of the image of the specified lift is exactly the index in
the accepted literal unary expansion. -/
lemma designated_exponent (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hNeven : Even N) (hmN : m ∣ N) (ν : ℤ)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    m * (24*N^2/N * unaryResidue m N ν) =
      (N^2/m) * ArithmeticThetaUnaryProduct.unaryA m ν := by
  have hres := residue_cast m N hm hN hNeven hmN ν hν
  have ha := (ArithmeticThetaUnaryProduct.unary_parameters m ν hm hν).1
  have hhalf : (2 : ℤ)*((N/2 : ℕ) : ℤ) = N := by
    exact_mod_cast (Nat.mul_div_cancel' (even_iff_two_dvd.mp hNeven))
  have hmul : (m : ℤ)*((N/m : ℕ) : ℤ) = N := by
    exact_mod_cast (Nat.mul_div_cancel' hmN)
  have hd : m ∣ N^2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hmN N
  have hd' : ((N^2/m : ℕ) : ℤ)*(m : ℤ) = (N : ℤ)^2 := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hdiv : 24*N^2/N = 24*N := by
    rw [show 24*N^2 = (24*N)*N by ring, Nat.mul_div_cancel _ hN]
  rw [hdiv]
  apply Int.ofNat_inj.mp
  push_cast
  rw [hres, ha]
  calc
    (m : ℤ) * (24*N*(((N/2 : ℕ) : ℤ)+((N/m : ℕ) : ℤ)*ν)) =
        12*N*(m*(2*((N/2 : ℕ) : ℤ))) + 24*N*ν*(m*((N/m : ℕ) : ℤ)) := by ring
    _ = 12*N*(m*N) + 24*N*ν*N := by rw [hhalf, hmul]
    _ = ((N^2/m : ℕ) : ℤ) * (12*(m : ℤ)^2+24*(m : ℤ)*ν) := by
      nlinarith [congrArg (fun z : ℤ => z*(12*m+24*ν)) hd']

lemma source_indices (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hNeven : Even N) (hmN : m ∣ N) (ν : ℤ)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    0 < 24*N^2/(m*N)*(N/2) ∧
      24*N^2/(m*N)*(N/2) < 24*N^2 ∧
      24*N^2/N*unaryResidue m N ν < 24*N^2 ∧
      (24*N^2/(m*N)*(N/2))*m = (24*N^2)/2 := by
  have hL : 0 < 24*N^2 := by positivity
  have hmNL := (period_parameters m N hm hN hmN).2.2.2
  have hdiv : 24*N^2/(m*N)*(m*N) = 24*N^2 := Nat.div_mul_cancel hmNL
  have hpos : 0 < 24*N^2/(m*N) := Nat.div_pos (Nat.le_of_dvd hL hmNL) (by positivity)
  have hhalf : 2*(N/2) = N := Nat.mul_div_cancel' (even_iff_two_dvd.mp hNeven)
  have hbp := half_nonzero N hN hNeven
  have hj := residue_lt m N hm hN hNeven hmN ν hν
  have hquot : 24*N^2/N = 24*N := by
    rw [show 24*N^2 = (24*N)*N by ring, Nat.mul_div_cancel _ hN]
  refine ⟨Nat.mul_pos hpos (Nat.pos_of_ne_zero hbp.1), ?_, ?_, ?_⟩
  · have hlt := Nat.mul_lt_mul_of_pos_left hbp.2 hpos
    have hh : (24*N^2/(m*N))*N ≤ (24*N^2/(m*N))*(m*N) := by
      gcongr
      nlinarith
    omega
  · rw [hquot]
    nlinarith [Nat.mul_lt_mul_of_pos_left hj (show 0 < 24*N by positivity)]
  · have he : 2*((24*N^2/(m*N)*(N/2))*m) = 24*N^2 := by
      nlinarith [congrArg (fun z => (24*N^2/(m*N))*m*z) hhalf]
    omega

open NeronModelInfra WeierstrassProjModel

lemma mul_val_congr {R : Type} [CommRing R]
    (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R)
    {S : Scheme} {t t' : S ⟶ Base R} (ht : t = t')
    (x y : SchemeHomOver t E.projection) (x' y' : SchemeHomOver t' E.projection)
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (E.law.mul t x y).val = (E.law.mul t' x' y').val := by
  subst t'
  have hx' : x = x' := Subtype.ext hx
  have hy' : y = y' := Subtype.ext hy
  rw [hx', hy']

lemma test_mul (k : Type) [Field k] [CharZero k] (L : ℕ)
    {D : LevelData k L} (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    {S : Scheme} (t : S ⟶ Puncture k)
    (x y : SchemeHomOver t (structureMap (LaurentSeries k) (TateCurve k L))) :
    (V.level.law.mul t x y).val ≫ V.map =
      (D.atlas.descent.family.law.mul (t ≫ (V.base ≫ D.quotient.inclusion))
        ⟨x.val ≫ V.map, by rw [Category.assoc, V.classifies.2.1.w, ← Category.assoc, x.property]⟩
        ⟨y.val ≫ V.map, by rw [Category.assoc, V.classifies.2.1.w, ← Category.assoc, y.property]⟩).val := by
  letI := V.level.elliptic
  let ι : D.atlas.quotient.ring →+* LaurentSeries k :=
    (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom
  have hi : Spec.map (CommRingCat.ofHom ι) = V.base ≫ D.quotient.inclusion := Spec.map_preimage _
  have hp : IsPullback V.map (structureMap (LaurentSeries k) (TateCurve k L))
      D.atlas.descent.family.projection (Spec.map (CommRingCat.ofHom ι)) := by
    rw [hi]; exact V.classifies.2.1
  obtain ⟨H, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι D.atlas.descent.family.projection (structureMap (LaurentSeries k) (TateCurve k L))
    V.map hp (EllipticFamilyWeierstrassAtlasR0180.toWeierstrassLaw D.atlas.descent.family.law)
  have hone : (V.level.law.one (𝟙 _)).val = (H.one (𝟙 _)).val := by
    apply hp.hom_ext
    · rw [V.level.originLaw.1, Category.id_comp, V.classifies.2.2.1, ho, Category.id_comp, hi]
      exact congrArg Subtype.val
        (D.atlas.descent.family.law.one_natural (𝟙 _) (V.base ≫ D.quotient.inclusion)
          (V.base ≫ D.quotient.inclusion) (Category.comp_id _))
    · exact (V.level.law.one (𝟙 _)).property.trans (H.one (𝟙 _)).property.symm
  have he := congrArg (fun P => P.val ≫ V.map)
    (RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
      (TateCurve k L).toProjective V.level.law H hone t x y)
  rw [he]
  dsimp only [EllipticFamilyWeierstrassAtlasR0180.toWeierstrassLaw] at hm
  exact (hm t x y).trans (mul_val_congr D.atlas.descent.family
    (congrArg (fun b => t ≫ b) hi) _ _ _ _ rfl rfl)

lemma test_nsmul (k : Type) [Field k] [CharZero k] (L : ℕ)
    {D : LevelData k L} (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (x : SchemeHomOver (𝟙 (Puncture k)) (structureMap (LaurentSeries k) (TateCurve k L)))
    (y : SchemeHomOver (𝟙 (Base D.atlas.quotient.ring)) D.atlas.descent.family.projection)
    (hxy : x.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ y.val) (n : ℕ) :
    (V.level.law.nsmul (𝟙 _) n x).val ≫ V.map =
      (V.base ≫ D.quotient.inclusion) ≫ (D.atlas.descent.family.law.nsmul (𝟙 _) n y).val := by
  have hx : x.val ≫ V.level.law.schemeNsmul n = (V.level.law.nsmul (𝟙 _) n x).val :=
    congrArg Subtype.val (V.level.law.nsmul_natural
      (structureMap (LaurentSeries k) (TateCurve k L)) (𝟙 _) x.val x.property n
      RelativeGroupLaw.idPoint)
  rw [← hx, Category.assoc, V.nsmul_eq, ← Category.assoc, hxy, Category.assoc,
    GlobalLevelCyclicQuotientR0180.comp_nsmul]

/-- The chosen Tate lift maps to the specified global lift, not to an
unspecified point with the same order. -/
lemma test_lift (k : Type) [Field k] [CharZero k] (L : ℕ)
    {D : LevelData k L} (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (m N a b : ℕ) :
    ArithmeticThetaFullLevelCoverR0175.liftPoint (LaurentSeries k) (TateCurve k L)
      V.level.law m N a b V.level.marking ≫ V.map =
      (V.base ≫ D.quotient.inclusion) ≫ liftPoint k L D.atlas m N a b := by
  let x := V.level.law.nsmul (𝟙 _) (L/(m*N)*b) V.level.marking.x
  let y := V.level.law.nsmul (𝟙 _) (L/N*a) V.level.marking.y
  let x' := D.atlas.descent.family.law.nsmul (𝟙 _) (L/(m*N)*b) D.atlas.marking.x
  let y' := D.atlas.descent.family.law.nsmul (𝟙 _) (L/N*a) D.atlas.marking.y
  have hx : x.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ x'.val :=
    test_nsmul k L V _ _ V.classifies.2.2.2.1 _
  have hy : y.val ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫ y'.val :=
    test_nsmul k L V _ _ V.classifies.2.2.2.2 _
  change (V.level.law.mul (𝟙 _) x y).val ≫ V.map =
    (V.base ≫ D.quotient.inclusion) ≫ (D.atlas.descent.family.law.mul (𝟙 _) x' y').val
  rw [test_mul]
  have hn := congrArg Subtype.val (D.atlas.descent.family.law.mul_natural (𝟙 _)
    (V.base ≫ D.quotient.inclusion) (V.base ≫ D.quotient.inclusion)
    (Category.comp_id _) x' y')
  exact (mul_val_congr D.atlas.descent.family (Category.id_comp _) _ _ _ _ hx hy).trans hn.symm

lemma primitive_half (k : Type) [Field k] (L : ℕ) (hL : 0 < L) (heven : Even L)
    (ζ : k) (hζ : IsPrimitiveRoot ζ L) : ζ^(L/2) = -1 := by
  have hh : 2*(L/2) = L := Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
  have hsq : (ζ^(L/2))^2 = 1 := by
    rw [← pow_mul, show L/2*2 = L by omega]
    exact hζ.pow_eq_one
  exact (sq_eq_one_iff.mp hsq).resolve_left (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega))

/-- The multiplicative coordinate of the specified target point is exactly
minus one after the toric power, with no choice of a root-of-unity factor. -/
lemma designated_toric_scalar (k : Type) [Field k] (m N : ℕ)
    (hm : 0 < m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ))
    (ζ : k) (hζ : IsPrimitiveRoot ζ (24*N^2)) :
    (ζ ^ (24*N^2/(m*N)*(N/2)))^m = -1 := by
  rw [← pow_mul, (source_indices m N hm hN hNeven hmN ν hν).2.2.2]
  exact primitive_half k (24*N^2) (by positivity) ⟨12*N^2, by omega⟩ ζ hζ

lemma designated_lift_coordinates (k : Type) [Field k] [CharZero k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N)
    (E : TateLevel k (24*N^2)) (ζ : k) (hmark : CanonicalMarking k (24*N^2) ζ E)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k (24*N^2))
      (ArithmeticThetaFullLevelCoverR0175.liftPoint (LaurentSeries k) (TateCurve k (24*N^2))
        E.law m N (unaryResidue m N ν) (N/2) E.marking)
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX (24*N^2) (24*N^2/N*unaryResidue m N ν)
          (ζ^(24*N^2/(m*N)*(N/2)))))
      (algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY (24*N^2) (24*N^2/N*unaryResidue m N ν)
          (ζ^(24*N^2/(m*N)*(N/2))))) := by
  have hi := source_indices m N hm hN hNeven hmN ν hν
  exact hmark ⟨_,hi.2.1⟩ ⟨_,hi.2.2.1⟩ (Or.inl (Nat.ne_of_gt hi.1))

namespace PeriodCollapse
open CategoryTheory.Limits
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135

variable (k : Type) [Field k] [CharZero k]

def index {r s : ℕ} (hr : 0 < r) (i : Fin s) : Fin r := ⟨i.val % r, Nat.mod_lt _ hr⟩

lemma index_next {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hdiv : r ∣ s) (i : Fin s) :
    index hr (next s hs i) = next r hr (index hr i) := by
  apply Fin.ext
  change ((i.val+1)%s)%r = (i.val%r+1)%r
  rw [Nat.mod_mod_of_dvd _ hdiv, Nat.add_mod]
  simp only [Nat.mod_mod, Nat.add_mod]

lemma overlap_eq (n : ℕ) (E F : B k n false ≃+* B k n true)
    (hE : IsAdjacent k n E) (hF : IsAdjacent k n F) : E = F := by
  apply RingEquiv.ext
  intro a
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (RingHom.congr_fun hE a).trans (RingHom.congr_fun hF a).symm

/-- The period-lattice inclusion is identity in each annular chart. Its dual
is the toric power map required for the designated quotient. -/
def stage {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) : (T.atlas n).X ⟶ (U.atlas n).X :=
  (T.atlas n).desc (fun i => (U.atlas n).chart (index hr i)) (by
    intro i
    rw [index_next hr hs hdiv, overlap_eq k n (T.overlap n) (U.overlap n)
      (T.overlap_spec n) (U.overlap_spec n)]
    exact (U.atlas n).adjacent (index hr i) |>.w)

@[reassoc]
lemma chart_stage {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) (i : Fin s) :
    (T.atlas n).chart i ≫ stage k hdiv T U n = (U.atlas n).chart (index hr i) :=
  (T.atlas n).chart_desc _ _ i

lemma stage_over {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) :
    stage k hdiv T U n ≫ (U.atlas n).p = (T.atlas n).p := by
  apply (T.atlas n).hom_ext
  intro i
  rw [chart_stage_assoc, (U.atlas n).chart_over, (T.atlas n).chart_over]

lemma stage_compatible {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n N : ℕ) (h : n ≤ N) :
    T.transition n N h ≫ stage k hdiv T U N = stage k hdiv T U n ≫ U.transition n N h := by
  apply (T.atlas n).hom_ext
  intro i
  rw [← Category.assoc, (T.transition_spec n N h).2, Category.assoc, chart_stage,
    chart_stage_assoc, (U.transition_spec n N h).2]

lemma stage_etale {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) : Etale (stage k hdiv T U n) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (T.atlas n).thickeningOpenCoverR0130
  intro i
  change Etale ((T.atlas n).chart i ≫ stage k hdiv T U n)
  rw [chart_stage]
  letI := (U.atlas n).chart_open (index hr i)
  infer_instance

lemma stage_surjective {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) : Surjective (stage k hdiv T U n) := by
  constructor
  intro x
  obtain ⟨i,z,rfl⟩ := (U.atlas n).covers x
  let j : Fin s := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_dvd hs hdiv)⟩
  refine ⟨(T.atlas n).chart j z, ?_⟩
  change ((T.atlas n).chart j ≫ stage k hdiv T U n) z = _
  rw [chart_stage]
  have hij : index hr j = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hij]

lemma stage_finite {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) :
    IsFinite (stage k hdiv T U n) := by
  letI := infinitesimal_polygon_proper k s hs h3s n _ (T.overlap_spec n) (T.atlas n)
  letI := infinitesimal_polygon_proper k r hr h3r n _ (U.overlap_spec n) (U.atlas n)
  letI : IsProper (stage k hdiv T U n ≫ (U.atlas n).p) := by rw [stage_over]; infer_instance
  letI : IsProper (stage k hdiv T U n) := IsProper.of_comp _ (U.atlas n).p
  letI := stage_etale k hdiv T U n
  letI : LocallyQuasiFinite (stage k hdiv T U n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

def completionIso {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (n : ℕ) :
    (T.atlas n).X ≅ adicThickening M.p (Ideal.span {PowerSeries.X}) n :=
  (hM.2.2.1 n).isoPullback

lemma completionIso_inclusion {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (n : ℕ) :
    (completionIso k M hM n).hom ≫ adicThickeningι M.p (Ideal.span {PowerSeries.X}) n =
      M.inclusion n := (hM.2.2.1 n).isoPullback_hom_fst

lemma completionIso_base {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (n : ℕ) :
    (completionIso k M hM n).hom ≫ adicThickeningToBase M.p (Ideal.span {PowerSeries.X}) n =
      (T.atlas n).p := (hM.2.2.1 n).isoPullback_hom_snd

lemma completionIso_transition {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (n : ℕ) :
    T.transition n (n+1) (Nat.le_succ n) ≫ (completionIso k M hM (n+1)).hom =
      (completionIso k M hM n).hom ≫ adicThickeningTransition M.p (Ideal.span {PowerSeries.X}) n := by
  apply pullback.hom_ext
  · change _ ≫ adicThickeningι M.p (Ideal.span {PowerSeries.X}) (n+1) =
      _ ≫ adicThickeningι M.p (Ideal.span {PowerSeries.X}) (n+1)
    rw [Category.assoc, completionIso_inclusion, hM.2.2.2, Category.assoc,
      adicThickeningTransition_ι, completionIso_inclusion]
  · change _ ≫ adicThickeningToBase M.p (Ideal.span {PowerSeries.X}) (n+1) =
      _ ≫ adicThickeningToBase M.p (Ideal.span {PowerSeries.X}) (n+1)
    rw [Category.assoc, completionIso_base, (T.transition_spec n (n+1) (Nat.le_succ n)).1,
      Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, completionIso_base]
    rfl

/-- Algebraize the actual maps of polygon charts between the two periods.
The source and target models may be any accepted realizations. -/
lemma algebraizes {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr)
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    ∃! f : M.X ⟶ N.X, f ≫ N.p = M.p ∧
      ∀ n, M.inclusion n ≫ f = stage k hdiv T U n ≫ N.inclusion n := by
  letI : IsProper M.p := hM.1
  letI : IsProper N.p := hN.1
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  let e (n : ℕ) := completionIso k M hM n
  let e' (n : ℕ) := completionIso k N hN n
  let φ (n : ℕ) : adicThickening M.p I n ⟶ adicThickening N.p I n :=
    (e n).inv ≫ stage k hdiv T U n ≫ (e' n).hom
  have hφ (n : ℕ) : φ n ≫ adicThickeningToBase N.p I n = adicThickeningToBase M.p I n := by
    dsimp only [φ, e, e']
    rw [Category.assoc, Category.assoc, completionIso_base, stage_over]
    exact (hM.2.2.1 n).isoPullback_inv_snd
  have hφt (n : ℕ) : adicThickeningTransition M.p I n ≫ φ (n+1) =
      φ n ≫ adicThickeningTransition N.p I n := by
    apply (cancel_epi (e n).hom).mp
    dsimp only [φ, e, e']
    rw [← Category.assoc, ← completionIso_transition]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← completionIso_transition]
    rw [← Category.assoc, stage_compatible k hdiv T U n (n+1) (Nat.le_succ n), Category.assoc]
  obtain ⟨f,hf,-⟩ :=
    ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.CoherentEffectivity.AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isProper
      I M.p N.p φ hφ hφt
  have hst (n : ℕ) : M.inclusion n ≫ f = stage k hdiv T U n ≫ N.inclusion n := by
    rw [← completionIso_inclusion k M hM n, Category.assoc, hf.2 n]
    dsimp only [φ, e, e']
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [Category.assoc, completionIso_inclusion]
  refine ⟨f, ⟨hf.1,hst⟩, ?_⟩
  intro f' hf'
  exact ArithmeticThetaModelSymmetriesR0137.ProperTowerAutomorphismEffectivityR0137.hom_ext
    k M hM N.p hf'.1 hf.1 (fun n => (hf'.2 n).trans (hst n).symm)

def map {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) : M.X ⟶ N.X :=
  Classical.choose (algebraizes k hdiv T U M hM N hN)

lemma map_over {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    map k hdiv M hM N hN ≫ N.p = M.p :=
  (Classical.choose_spec (algebraizes k hdiv T U M hM N hN)).1.1

lemma map_stage {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) (n : ℕ) :
    M.inclusion n ≫ map k hdiv M hM N hN = stage k hdiv T U n ≫ N.inclusion n :=
  (Classical.choose_spec (algebraizes k hdiv T U M hM N hN)).1.2 n

lemma map_cartesian {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) (n : ℕ) :
    IsPullback (M.inclusion n) (stage k hdiv T U n) (map k hdiv M hM N hN) (N.inclusion n) := by
  have outer : IsPullback (M.inclusion n) (stage k hdiv T U n ≫ (U.atlas n).p)
      (map k hdiv M hM N hN ≫ N.p) (baseInclusion k n) := by
    rw [stage_over, map_over]
    exact hM.2.2.1 n
  exact outer.of_bot (map_stage k hdiv M hM N hN n) (hN.2.2.1 n)

/-- Finiteness is proved on the algebraic models from the actual Cartesian
truncations. The open quasi-finite locus contains each specialization on the
closed fibre, hence every point of the proper source. -/
lemma map_finite {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    IsFinite (map k hdiv M hM N hN) := by
  letI : IsProper M.p := hM.1
  letI : IsProper N.p := hN.1
  let f := map k hdiv M hM N hN
  letI : IsProper (f ≫ N.p) := by dsimp only [f]; rw [map_over]; infer_instance
  letI : IsProper f := IsProper.of_comp _ N.p
  letI := stage_finite k hdiv h3r h3s T U 1
  have hqf : f.quasiFiniteLocus = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i,z,hxz⟩ := AlgebraizedGenericSmoothnessR0135.specializes_firstOrderChart k M hM x
    apply hxz.mem_open f.quasiFiniteLocus.isOpen
    exact Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
      (map_cartesian k hdiv M hM N hN 1) (stage k hdiv T U 1 ((T.atlas 1).chart i z))
      (M.inclusion 1 ((T.atlas 1).chart i z))
      (congrArg (fun g => g ((T.atlas 1).chart i z)) (map_stage k hdiv M hM N hN 1))
  letI : LocallyQuasiFinite f := f.quasiFiniteLocus_eq_top_iff.mp hqf
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaPolygonCohomologyR0131

lemma stage_marked {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ) (i : Fin s) (a : kˣ) :
    markedSection k s n hs (T.atlas n) i a ≫ stage k hdiv T U n =
      markedSection k r n hr (U.atlas n) (index hr i) a := by
  unfold markedSection
  rw [Category.assoc, chart_stage]

lemma map_marked {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (i : Fin s) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p) :
    MarkedLift k N (index hr i) a (p ≫ map k hdiv M hM N hN) := by
  constructor
  · rw [Category.assoc, map_over]; exact hp.1
  · intro n
    rw [← Category.assoc, hp.2, Category.assoc, map_stage, ← Category.assoc, stage_marked]

lemma map_marked_eq {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (i : Fin s) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (index hr i) a q) :
    p ≫ map k hdiv M hM N hN = q := by
  have h := map_marked k hdiv M hM N hN i a p hp
  exact MarkedSectionAlgebraizationR0136.hom_ext k (fun n => (h.2 n).trans (hq.2 n).symm)

def generic {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    ArithmeticThetaGenericEvaluationR0140.genericScheme k M ⟶
      ArithmeticThetaGenericEvaluationR0140.genericScheme k N :=
  pullback.lift (pullback.fst M.p (genericBase k) ≫ map k hdiv M hM N hN)
    (pullback.snd M.p (genericBase k)) (by rw [Category.assoc, map_over, pullback.condition])

lemma generic_over {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    generic k hdiv M hM N hN ≫ genericStructure k N = genericStructure k M :=
  pullback.lift_snd _ _ _

lemma generic_cartesian {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    IsPullback (ArithmeticThetaGenericEvaluationR0140.genericInclusion k M)
      (generic k hdiv M hM N hN) (map k hdiv M hM N hN)
      (ArithmeticThetaGenericEvaluationR0140.genericInclusion k N) := by
  have outer : IsPullback (ArithmeticThetaGenericEvaluationR0140.genericInclusion k M)
      (generic k hdiv M hM N hN ≫ genericStructure k N)
      (map k hdiv M hM N hN ≫ N.p) (genericBase k) := by
    rw [generic_over, map_over]
    exact IsPullback.of_hasPullback _ _
  exact outer.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

lemma generic_finite {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N) :
    IsFinite (generic k hdiv M hM N hN) :=
  MorphismProperty.of_isPullback (generic_cartesian k hdiv M hM N hN)
    (map_finite k hdiv h3r h3s M hM N hN)

lemma generic_flat_surjective {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex s hs) 1 p)
    (q : baseScheme k ⟶ N.X)
    (hq : MarkedLift k N (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 q) :
    Flat (generic k hdiv M hM N hN) ∧ Surjective (generic k hdiv M hM N hN) := by
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k N hN
  letI : IsIntegral (pullback M.p (genericBase k)) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3s M hM
  letI : IsIntegral (pullback N.p (genericBase k)) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3r N hN
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_relative_one k h3s M hM p hp
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_relative_one k h3r N hN q hq
  letI := generic_finite k hdiv h3r h3s M hM N hN
  exact (isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
    (genericStructure k M) (genericStructure k N) 1
    (generic k hdiv M hM N hN) (generic_over k hdiv M hM N hN)).2

lemma generic_marked {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (i : Fin s) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p)
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (index hr i) a q) :
    ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1 ≫ generic k hdiv M hM N hN =
      ArithmeticThetaGenericEvaluationR0140.genericPoint k N q hq.1 := by
  apply pullback.hom_ext
  · simp only [generic, ArithmeticThetaGenericEvaluationR0140.genericPoint,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [map_marked_eq k hdiv M hM N hN i a p hp q hq]
  · simp only [generic, ArithmeticThetaGenericEvaluationR0140.genericPoint,
      Category.assoc, pullback.lift_snd]

lemma index_zero {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    index hr (ArithmeticThetaIdentitySectionsR0138.zeroIndex s hs) =
      ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr := by
  apply Fin.ext
  exact Nat.zero_mod _

open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree (toGRJ)
open ArithmeticThetaGenericEvaluationR0140 (genericScheme genericPoint)

/-- Proper group rigidity makes the constructed pointed period map a
homomorphism on every test scheme. -/
lemma generic_mul {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex s hs) 1 p)
    (q : baseScheme k ⟶ N.X)
    (hq : MarkedLift k N (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 q)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M p hp.1 G)
    (H : ArithmeticThetaMarkedGroupLawR0146.Law k N)
    (hH : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k N q hq.1 H)
    {Z : Scheme} (t : Z ⟶ Puncture k)
    (x y : SchemeHomOver t (genericStructure k M)) :
    (G.mul t x y).val ≫ generic k hdiv M hM N hN =
      (H.mul t
        ⟨x.val ≫ generic k hdiv M hM N hN,
          by rw [Category.assoc, generic_over]; exact x.property⟩
        ⟨y.val ≫ generic k hdiv M hM N hN,
          by rw [Category.assoc, generic_over]; exact y.property⟩).val := by
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k N hN
  letI := algebraized_generic_smoothness k s hs h3s T M hM
  letI := algebraized_generic_smoothness k r hr h3r U N hN
  letI := algebraized_geometric_connectedness k s hs h3s T M hM
  letI := algebraized_geometric_connectedness k r hr h3r U N hN
  letI : ConnectedSpace ↥(pullback M.p (genericBase k) : Scheme) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (genericStructure k M)
  have hgeom : GoodReductionJacobian.AbelianSchemePropertyBundle (LaurentSeries k)
      (genericStructure k N) :=
    ⟨inferInstance, inferInstance,
      fun z => (genericStructure k N).isConnected_preimage_singleton z, ⟨toGRJ H⟩⟩
  let f : SchemeHomOver (genericStructure k M) (genericStructure k N) :=
    ⟨generic k hdiv M hM N hN, generic_over k hdiv M hM N hN⟩
  have hone : NeronModelInfra.schemeHomOverComp ((toGRJ G).one (𝟙 _)) f =
      (toGRJ H).one (𝟙 _) := by
    apply Subtype.ext
    change (G.one (𝟙 _)).val ≫ generic k hdiv M hM N hN = (H.one (𝟙 _)).val
    rw [hG.1, hH.1]
    change (𝟙 _ ≫ genericPoint k M p hp.1) ≫ generic k hdiv M hM N hN =
      𝟙 _ ≫ genericPoint k N q hq.1
    rw [Category.id_comp, Category.id_comp]
    exact generic_marked k hdiv M hM N hN _ 1 p hp q (by simpa only [index_zero] using hq)
  exact congrArg Subtype.val
    ((toGRJ G).comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
      (LaurentSeries k) (toGRJ H) hgeom f hone t x y)

/-- Every point above a target chart has a representative in a source chart
with precisely that reduced index. Adjacent chart representatives are moved
through the specified pullback overlaps, rather than counted twice. -/
lemma stage_preimage_chart {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (T : Tower k s hs) (U : Tower k r hr) (n : ℕ)
    (j : Fin r) (x : (T.atlas n).X) (y : specA k n)
    (hxy : stage k hdiv T U n x = (U.atlas n).chart j y) :
    ∃ i : Fin s, index hr i = j ∧ (T.atlas n).chart i y = x := by
  obtain ⟨i,z,rfl⟩ := (T.atlas n).covers x
  have heq : (U.atlas n).chart (index hr i) z = (U.atlas n).chart j y := by
    simpa only [← Scheme.Hom.comp_apply, chart_stage] using hxy
  by_cases hij : index hr i = j
  · haveI := (U.atlas n).chart_open j
    have hzy : z = y := (U.atlas n).chart j |>.isOpenEmbedding.injective (hij ▸ heq)
    exact ⟨i,hij,by rw [hzy]⟩
  by_cases hn : next r hr (index hr i) = j
  · obtain ⟨w,hwz,hwy⟩ := Scheme.exists_preimage_of_isPullback
      ((U.atlas n).adjacent (index hr i)) z y (hn ▸ heq)
    refine ⟨next s hs i, (index_next hr hs hdiv i).trans hn, ?_⟩
    rw [← hwy, ← hwz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ← overlap_eq k n (T.overlap n) (U.overlap n) (T.overlap_spec n) (U.overlap_spec n)]
    exact congrArg (fun f => f w) ((T.atlas n).adjacent i).w.symm
  by_cases hp : next r hr j = index hr i
  · obtain ⟨i',hi'⟩ := ArithmeticThetaInfinitesimalPolygonR0129.next_surjective s hs i
    have hidx : index hr i' = j := by
      have hinj := (Fintype.bijective_iff_surjective_and_card (next r hr)).mpr
        ⟨ArithmeticThetaInfinitesimalPolygonR0129.next_surjective r hr, rfl⟩
      apply hinj.1
      rw [← index_next hr hs hdiv, hi', hp]
    obtain ⟨w,hwy,hwz⟩ := Scheme.exists_preimage_of_isPullback
      ((U.atlas n).adjacent j) y z (hp ▸ heq.symm)
    refine ⟨i',hidx,?_⟩
    rw [← hwy, ← hwz, ← hi', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ← overlap_eq k n (T.overlap n) (U.overlap n) (T.overlap_spec n) (U.overlap_spec n)]
    exact congrArg (fun f => f w) ((T.atlas n).adjacent i').w
  · exact False.elim (Set.disjoint_left.mp ((U.atlas n).disjoint _ _ hij hn hp)
      ⟨z,rfl⟩ ⟨y,heq.symm⟩)

/-- The scheme fibre above any marked section is exactly the disjoint union
of its marked lifts. This identifies the full infinitesimal fibre, including
its scheme structure, rather than only its rational points. -/
lemma stage_marked_cartesian {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) (T : Tower k s hs) (U : Tower k r hr)
    (n : ℕ) (j : Fin r) (a : kˣ) :
    IsPullback
      (Sigma.desc (fun i : {i : Fin s // index hr i = j} =>
        markedSection k s n hs (T.atlas n) i.val a))
      (Sigma.desc (fun _ : {i : Fin s // index hr i = j} => 𝟙 (specR k n)))
      (stage k hdiv T U n) (markedSection k r n hr (U.atlas n) j a) := by
  classical
  let I := {i : Fin s // index hr i = j}
  let f := stage k hdiv T U n
  let e := markedSection k r n hr (U.atlas n) j a
  let p (i : I) := markedSection k s n hs (T.atlas n) i.val a
  have hp (i : I) : p i ≫ f = e := by
    dsimp only [p,f,e]
    rw [stage_marked, i.property]
  let l (i : I) : specR k n ⟶ pullback f e :=
    pullback.lift (p i) (𝟙 _) (by rw [hp, Category.id_comp])
  letI := stage_etale k hdiv T U n
  letI := stage_finite k hdiv h3r h3s T U n
  letI : Etale f := inferInstanceAs (Etale (stage k hdiv T U n))
  letI : IsFinite f := inferInstanceAs (IsFinite (stage k hdiv T U n))
  letI : IsClosedImmersion e :=
    (polygon_smooth_marked_sections k r n hr h3r _ (U.overlap_spec n) (U.atlas n) j a).1
  have hl (i : I) : l i ≫ pullback.snd f e = 𝟙 _ := pullback.lift_snd _ _ _
  letI (i : I) : IsOpenImmersion (l i) :=
    (isOpenImmersion_and_isClosedImmersion_of_comp_eq_id (pullback.snd f e) (l i) (hl i)).1
  have hd (i i' : I) (hii' : i ≠ i') : Disjoint (Set.range (l i)) (Set.range (l i')) := by
    rw [Set.disjoint_left]
    rintro z ⟨x,rfl⟩ ⟨y,hy⟩
    have heq := congrArg (pullback.fst f e) hy
    have heq' : p i' y = p i x := by
      simpa only [← Scheme.Hom.comp_apply, l, pullback.lift_fst] using heq
    exact Set.disjoint_left.mp
      (CompatibleMarkingsR0131.disjoint_markings k s n hs (T.atlas n) i.val i'.val
        (fun h => hii' (Subtype.ext h)) a a) ⟨x,rfl⟩ ⟨y,heq'⟩
  letI : IsOpenImmersion (Sigma.desc l) := isOpenImmersion_sigmaDesc _ l hd
  letI : Surjective (Sigma.desc l) := by
    constructor
    intro z
    have hz : f (pullback.fst f e z) = e (pullback.snd f e z) :=
      congrArg (fun g => g z) (pullback.condition (f := f) (g := e))
    obtain ⟨i,hi,hiz⟩ := stage_preimage_chart k hdiv T U n j
      (pullback.fst f e z)
      (Spec.map (CommRingCat.ofHom (markedPoint k n a)) (pullback.snd f e z)) hz
    refine ⟨Sigma.ι (fun _ : I => specR k n) ⟨i,hi⟩ (pullback.snd f e z), ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    apply (pullback.fst f e).isClosedEmbedding.injective
    change ((l ⟨i,hi⟩) ≫ pullback.fst f e) (pullback.snd f e z) = _
    rw [show l ⟨i,hi⟩ ≫ pullback.fst f e = p ⟨i,hi⟩ from pullback.lift_fst _ _ _]
    exact hiz
  letI : IsIso (Sigma.desc l) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance,inferInstance⟩
  have hf : Sigma.desc l ≫ pullback.fst f e = Sigma.desc p := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc_assoc, l, pullback.lift_fst, Sigma.ι_desc]
  have he : Sigma.desc l ≫ pullback.snd f e =
      Sigma.desc (fun _ : I => 𝟙 (specR k n)) := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc_assoc, hl, Sigma.ι_desc]
  change IsPullback (Sigma.desc p) (Sigma.desc (fun _ : I => 𝟙 (specR k n))) f e
  exact (IsPullback.of_hasPullback f e).of_iso (asIso (Sigma.desc l)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← hf]) (by simp [← he])
    (by simp) (by simp)

lemma sigma_base_change (I : Type) [Finite I] {A B : Scheme} (g : A ⟶ B) :
    IsPullback (Sigma.desc (fun i : I => g ≫ Sigma.ι (fun _ : I => B) i))
      (Sigma.desc (fun _ : I => 𝟙 A)) (Sigma.desc (fun _ : I => 𝟙 B)) g := by
  have h := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : I => B))).isPullback_of_isColimit_right
    (fun _ : I => 𝟙 B) (Sigma.desc (fun _ : I => 𝟙 B)) g
    (fun _ : I => g) (fun _ : I => 𝟙 A) (fun _ => IsPullback.id_vert g)
    (coproductIsCoproduct (fun _ : I => A))
  simpa [Cofan.IsColimit.desc, Cofan.inj, Limits.Sigma.desc, Sigma.ι, coproductIsCoproduct] using h

/-- Algebraization retains the full split fibre above a marked section. -/
lemma map_marked_cartesian {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (j : Fin r) (a : kˣ)
    (p : Fin s → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i a (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N j a q) :
    IsPullback (Sigma.desc (fun i : {i : Fin s // index hr i = j} => p i.val))
      (Sigma.desc (fun _ : {i : Fin s // index hr i = j} => 𝟙 (baseScheme k)))
      (map k hdiv M hM N hN) q := by
  classical
  let I := {i : Fin s // index hr i = j}
  let f := map k hdiv M hM N hN
  let m := Sigma.desc (fun i : I => p i.val)
  let b := Sigma.desc (fun _ : I => 𝟙 (baseScheme k))
  have hw : m ≫ f = b ≫ q := by
    apply Sigma.hom_ext
    intro i
    simp only [m,b,Sigma.ι_desc_assoc,Category.id_comp]
    exact map_marked_eq k hdiv M hM N hN i.val a (p i.val) (hp i.val) q
      (by simpa only [i.property] using hq)
  let l : (∐ fun _ : I => baseScheme k) ⟶ pullback f q := pullback.lift m b hw
  let c := pullback.snd f q
  have hl : l ≫ c = b := pullback.lift_snd _ _ _
  letI : IsFinite f := map_finite k hdiv h3r h3s M hM N hN
  letI : IsClosedImmersion q :=
    AlgebraizedSplitMarkedDivisorR0136.section_closed k N hN q hq.1
  letI (i : I) : IsClosedImmersion (p i.val) :=
    AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM _ (hp i.val).1
  letI : IsClosedImmersion m :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma
      (fun i : I => p i.val) (fun i i' hii' =>
        AlgebraizedSplitMarkedDivisorR0136.sections_disjoint k M hM (fun _ => a) p hp
          i.val i'.val (fun h => hii' (Subtype.ext h)))
  letI : IsProper (l ≫ pullback.fst f q) := by
    rw [show l ≫ pullback.fst f q = m from pullback.lift_fst _ _ _]
    infer_instance
  letI : IsProper l := IsProper.of_comp _ (pullback.fst f q)
  have hln : IsIso l := by
    apply isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
      (PowerSeries k) (Ideal.span {PowerSeries.X}) c l (baseInclusion k) (fun _ => rfl)
    intro n
    let mn := Sigma.desc (fun i : I => markedSection k s n hs (T.atlas n) i.val a)
    let bn := Sigma.desc (fun _ : I => 𝟙 (specR k n))
    let sn := Sigma.desc (fun i : I => baseInclusion k n ≫ Sigma.ι (fun _ : I => baseScheme k) i)
    let en := markedSection k r n hr (U.atlas n) j a
    have hsm : sn ≫ m = mn ≫ M.inclusion n := by
      apply Sigma.hom_ext
      intro i
      simp only [sn,m,mn,Sigma.ι_desc_assoc,Category.assoc,Sigma.ι_desc]
      exact (hp i.val).2 n
    have hs : IsPullback sn bn b (baseInclusion k n) := sigma_base_change I (baseInclusion k n)
    have houter : IsPullback (mn ≫ M.inclusion n) bn f (baseInclusion k n ≫ q) := by
      rw [hq.2 n]
      exact (stage_marked_cartesian k hdiv h3r h3s T U n j a).paste_horiz
        (map_cartesian k hdiv M hM N hN n)
    have hKl : sn ≫ l ≫ pullback.fst f q = mn ≫ M.inclusion n := by
      rw [show l ≫ pullback.fst f q = m from pullback.lift_fst _ _ _, hsm]
    have hKc : sn ≫ l ≫ c = bn ≫ baseInclusion k n := by
      rw [hl]
      exact hs.w
    have hK : IsPullback (sn ≫ l) bn c (baseInclusion k n) := by
      have ho : IsPullback ((sn ≫ l) ≫ pullback.fst f q) bn f
          (baseInclusion k n ≫ q) := by
        rw [Category.assoc, hKl]
        exact houter
      exact ho.of_right (by simpa only [Category.assoc] using hKc)
        (IsPullback.of_hasPullback f q)
    have hsmall : IsPullback sn (𝟙 _) l (sn ≫ l) := by
      apply IsPullback.of_bot (t := hK) (p := by simp)
      simpa only [hl, Category.id_comp] using hs
    have hcan : IsPullback sn hK.isoPullback.hom l (pullback.fst c (baseInclusion k n)) := by
      exact hsmall.of_iso (Iso.refl _) (Iso.refl _) hK.isoPullback (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
    rw [← hcan.isoPullback_inv_snd]
    infer_instance
  change IsPullback m b f q
  exact (IsPullback.of_hasPullback f q).of_iso (asIso l).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [l]) (by simp [l]) (by simp) (by simp)

lemma generic_marked_cartesian {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (j : Fin r) (a : kˣ)
    (p : Fin s → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i a (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N j a q) :
    IsPullback
      (Sigma.desc (fun i : {i : Fin s // index hr i = j} => genericPoint k M (p i.val) (hp i.val).1))
      (Sigma.desc (fun _ : {i : Fin s // index hr i = j} => 𝟙 (Puncture k)))
      (generic k hdiv M hM N hN) (genericPoint k N q hq.1) := by
  classical
  let I := {i : Fin s // index hr i = j}
  let mg := Sigma.desc (fun i : I => genericPoint k M (p i.val) (hp i.val).1)
  let bg := Sigma.desc (fun _ : I => 𝟙 (Puncture k))
  let sn := Sigma.desc (fun i : I => genericBase k ≫ Sigma.ι (fun _ : I => baseScheme k) i)
  have hsm : sn ≫ Sigma.desc (fun i : I => p i.val) =
      mg ≫ ArithmeticThetaGenericEvaluationR0140.genericInclusion k M := by
    apply Sigma.hom_ext
    intro i
    simp only [sn,mg,Sigma.ι_desc_assoc,Category.assoc,Sigma.ι_desc,ArithmeticThetaGenericEvaluationR0140.genericPoint,
      ArithmeticThetaGenericEvaluationR0140.genericInclusion, pullback.lift_fst]
  have ho := (sigma_base_change I (genericBase k)).paste_horiz
    (map_marked_cartesian k hdiv h3r h3s M hM N hN j a p hp q hq)
  change IsPullback (sn ≫ _) bg _ _ at ho
  rw [hsm] at ho
  have hqg : genericPoint k N q hq.1 ≫ ArithmeticThetaGenericEvaluationR0140.genericInclusion k N =
      genericBase k ≫ q := pullback.lift_fst _ _ _
  rw [← hqg] at ho
  apply ho.of_right ?_ (generic_cartesian k hdiv M hM N hN)
  apply Sigma.hom_ext
  intro i
  simp only [mg,bg,Sigma.ι_desc_assoc,Category.id_comp]
  exact generic_marked k hdiv M hM N hN i.val a (p i.val) (hp i.val) q
    (by simpa only [i.property] using hq)

def zero_fiber_equiv (r m : ℕ) (hr : 0 < r) :
    {i : Fin (r*m) // index hr i = ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr} ≃ Fin m where
  toFun i := ⟨i.val.val / r, (Nat.div_lt_iff_lt_mul hr).mpr (by simpa only [Nat.mul_comm] using i.val.isLt)⟩
  invFun b := ⟨⟨r*b.val, Nat.mul_lt_mul_of_pos_left b.isLt hr⟩, by
    apply Fin.ext
    exact Nat.mul_mod_right r b.val⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hi : i.val.val % r = 0 := congrArg Fin.val i.property
    simpa only [hi, zero_add] using Nat.mod_add_div i.val.val r
  right_inv b := by
    apply Fin.ext
    exact Nat.mul_div_right _ hr

/-- The degree of the actual period-collapse is exactly the period ratio. -/
lemma generic_finrank {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (h3r : 3 ≤ r) (h3s : 3 ≤ r*m)
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : Fin (r*m) → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i 1 (p i))
    (q : baseScheme k ⟶ N.X)
    (hq : MarkedLift k N (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 q)
    (y : genericScheme k N) :
    (generic k (dvd_mul_right r m) M hM N hN).finrank y = m := by
  classical
  let f := generic k (dvd_mul_right r m) M hM N hN
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k N hN
  letI : LocallyOfFiniteType (pullback.snd N.p (genericBase k)) :=
    inferInstanceAs (LocallyOfFiniteType (genericStructure k N))
  letI : IsLocallyNoetherian (genericScheme k N) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k N)
  letI : IsIntegral (genericScheme k N) :=
    ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_integral k h3r N hN
  letI : IsFinite f := generic_finite k (dvd_mul_right r m) h3r h3s M hM N hN
  letI : Flat f := (generic_flat_surjective k (dvd_mul_right r m) h3r h3s M hM N hN
    (p (ArithmeticThetaIdentitySectionsR0138.zeroIndex (r*m) hs))
    (hp _) q hq).1
  let I := {i : Fin (r*m) // index hr i = ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr}
  let z : Puncture k := IsLocalRing.closedPoint (LaurentSeries k)
  have heq := f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y (genericPoint k N q hq.1 z)
  rw [heq]
  have hpb := generic_marked_cartesian k (dvd_mul_right r m) h3r h3s M hM N hN
    (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 p hp q hq
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb z]
  rw [ArithmeticThetaKatoAnnularR0152.ActualSplitTorsionKernel.sigma_structure_rank]
  exact (Fintype.card_congr (zero_fiber_equiv r m hr)).trans (Fintype.card_fin m)

open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaIdentitySectionsR0138

lemma comp_nsmul {s : ℕ} {hs : 0 < s} {T : Tower k s hs} (M : Model k T)
    (G : Law k M) {Z : Scheme} (t : Z ⟶ Puncture k)
    (x : SchemeHomOver t (genericStructure k M)) (n : ℕ) :
    x.val ≫ G.schemeNsmul n = (G.nsmul t n x).val :=
  congrArg Subtype.val (G.nsmul_natural (genericStructure k M) t x.val x.property n
    WeierstrassProjModel.RelativeGroupLaw.idPoint)

/-- The complete kernel, on every test scheme, is killed by the exact period
ratio. This follows from the split scheme fibre and the proved marked torsion
law, with no hypothesis about an unconstructed dual. -/
lemma generic_kernel_killed {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (h3r : 3 ≤ r) (h3s : 3 ≤ r*m) (he : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : Fin (r*m) → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i 1 (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : Law k M) (hG : IsOriginLaw k M (p (zeroIndex (r*m) hs)) (hp _).1 G)
    {Z : Scheme} (t : Z ⟶ Puncture k) (x : SchemeHomOver t (genericStructure k M))
    (hx : x.val ≫ generic k (dvd_mul_right r m) M hM N hN = t ≫ genericPoint k N q hq.1) :
    x.val ≫ G.schemeNsmul m = t ≫ genericPoint k M (p (zeroIndex (r*m) hs)) (hp _).1 := by
  classical
  let I := {i : Fin (r*m) // index hr i = zeroIndex r hr}
  let a := Sigma.desc (fun i : I => genericPoint k M (p i.val) (hp i.val).1)
  let b := Sigma.desc (fun _ : I => 𝟙 (Puncture k))
  let e := genericPoint k M (p (zeroIndex (r*m) hs)) (hp _).1
  have hk : a ≫ G.schemeNsmul m = b ≫ e := by
    apply Sigma.hom_ext
    intro i
    simp only [a,b,Sigma.ι_desc_assoc,Category.id_comp]
    have hi : r ∣ i.val.val := Nat.dvd_iff_mod_eq_zero.mpr (congrArg Fin.val i.property)
    obtain ⟨j,hj⟩ := hi
    have ht := (marked_exact_torsion k (r*m) hs h3s T he M hM
      (p (zeroIndex (r*m) hs)) (hp _) G hG i.val 1 (p i.val) (hp i.val) m).mpr
        ⟨⟨j,by rw [hj]; ring⟩, one_pow _⟩
    have hc := comp_nsmul k M G (𝟙 _) (pointOver k M (𝟙 _) (p i.val) (hp i.val).1) m
    rw [ht,hG.1] at hc
    simpa only [pointOver,Category.id_comp] using hc
  have hpb := generic_marked_cartesian k (dvd_mul_right r m) h3r h3s M hM N hN
    (zeroIndex r hr) 1 p hp q hq
  let l := hpb.lift x.val t hx
  have hl₁ : l ≫ a = x.val := hpb.lift_fst _ _ _
  have hl₂ : l ≫ b = t := hpb.lift_snd _ _ _
  rw [← hl₁,Category.assoc,hk,← Category.assoc,hl₂]

lemma nsmul_mul {s : ℕ} {hs : 0 < s} {T : Tower k s hs} (M : Model k T)
    (G : Law k M)
    (hc : ∀ {Z : Scheme} (t : Z ⟶ Puncture k) (x y : SchemeHomOver t (genericStructure k M)),
      G.mul t x y = G.mul t y x)
    {Z : Scheme} (t : Z ⟶ Puncture k) (n : ℕ) (x y : SchemeHomOver t (genericStructure k M)) :
    G.nsmul t n (G.mul t x y) = G.mul t (G.nsmul t n x) (G.nsmul t n y) := by
  letI : CommGroup (SchemeHomOver t (genericStructure k M)) :=
    { (toGRJ G).pointGroup t with mul_comm := hc t }
  have hn (z : SchemeHomOver t (genericStructure k M)) (a : ℕ) : G.nsmul t a z = z^a := by
    induction a with
    | zero => rfl
    | succ a ih => rw [G.nsmul_succ,ih]; exact (pow_succ z a).symm
  rw [hn,hn,hn]
  exact mul_pow x y n

/-- The dual toric isogeny is obtained by descending multiplication through
the constructed finite flat quotient. Both composites are checked. -/
lemma dual_exists {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (h3r : 3 ≤ r) (h3s : 3 ≤ r*m) (he : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : Fin (r*m) → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i 1 (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : Law k M) (hG : IsOriginLaw k M (p (zeroIndex (r*m) hs)) (hp _).1 G)
    (H : Law k N) (hH : IsOriginLaw k N q hq.1 H) :
    ∃! d : genericScheme k N ⟶ genericScheme k M,
      d ≫ genericStructure k M = genericStructure k N ∧
      generic k (dvd_mul_right r m) M hM N hN ≫ d = G.schemeNsmul m ∧
      d ≫ generic k (dvd_mul_right r m) M hM N hN = H.schemeNsmul m := by
  let f := generic k (dvd_mul_right r m) M hM N hN
  have hf := generic_over k (dvd_mul_right r m) M hM N hN
  have hfs := generic_flat_surjective k (dvd_mul_right r m) h3r h3s M hM N hN
    (p (zeroIndex (r*m) hs)) (hp _) q hq
  letI : Flat f := hfs.1
  letI : Surjective f := hfs.2
  letI : IsFinite f := generic_finite k (dvd_mul_right r m) h3r h3s M hM N hN
  have hfm {Z : Scheme} (t : Z ⟶ Puncture k) (x y : SchemeHomOver t (genericStructure k M)) :
      (⟨(G.mul t x y).val ≫ f, by rw [Category.assoc,hf]; exact (G.mul t x y).property⟩ :
        SchemeHomOver t (genericStructure k N)) = H.mul t
          ⟨x.val ≫ f, by rw [Category.assoc,hf]; exact x.property⟩
          ⟨y.val ≫ f, by rw [Category.assoc,hf]; exact y.property⟩ :=
    Subtype.ext (generic_mul k (dvd_mul_right r m) h3r h3s M hM N hN
      (p (zeroIndex (r*m) hs)) (hp _) q hq G hG H hH t x y)
  obtain ⟨d,hd,⟨hdOver,hdMul⟩,huniq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
      (toGRJ G) (toGRJ H) (toGRJ G) f hf hfm (G.schemeNsmul m) (G.schemeNsmul_over m)
      (fun t x y => Subtype.ext (by
        simp only [toGRJ]
        simp only [comp_nsmul, Subtype.coe_eta]
        exact congrArg Subtype.val (nsmul_mul k M G hG.2 t m x y)))
      (fun t x hx => Subtype.ext (by
        have hx' : x.val ≫ f = t ≫ genericPoint k N q hq.1 := by
          have hv := congrArg Subtype.val hx
          simpa only [toGRJ,hH.1,pointOver] using hv
        have hk := generic_kernel_killed k h3r h3s he M hM N hN p hp q hq G hG t x hx'
        simpa only [toGRJ,hG.1,pointOver] using hk))
  refine ⟨d,⟨hdOver,hd,?_⟩,fun d' hd' => huniq d' hd'.2.1⟩
  letI : Epi f := Flat.epi_of_flat_of_surjective f
  apply (cancel_epi f).mp
  rw [← Category.assoc,hd]
  have hc := (toGRJ G).schemeNsmul_comp_eq_comp_schemeNsmul_of_hom (toGRJ H)
    ⟨f,hf⟩ hfm
  simpa only [ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ_schemeNsmul]
    using hc.2.2 m

/-- The dual sends the literal toric label `(i,a)` to `(m*i,a^m)`.
The proof also covers `i = 0`; it never divides by the point's exponent. -/
lemma dual_marked {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (hm : 0 < m) (h3s : 3 ≤ r*m) (he : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (e : baseScheme k ⟶ M.X) (he0 : MarkedLift k M (zeroIndex (r*m) hs) 1 e)
    (G : Law k M) (hG : IsOriginLaw k M e he0.1 G)
    (d : genericScheme k N ⟶ genericScheme k M)
    (hd : generic k (dvd_mul_right r m) M hM N hN ≫ d = G.schemeNsmul m)
    (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ N.X) (hp : MarkedLift k N i a p)
    (q : baseScheme k ⟶ M.X)
    (hq : MarkedLift k M
      ⟨m*i.val, by simpa only [Nat.mul_comm r m] using Nat.mul_lt_mul_of_pos_left i.isLt hm⟩ (a^m) q) :
    genericPoint k N p hp.1 ≫ d = genericPoint k M q hq.1 := by
  let j : Fin (r*m) := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_dvd hs (dvd_mul_right r m))⟩
  let p' := MarkedPointAddition.sectionAt k h3s M hM j a
  have hp' := MarkedPointAddition.sectionAt_spec k h3s M hM j a
  have hj : index hr j = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [← generic_marked k (dvd_mul_right r m) M hM N hN j a p' hp' p
    (by simpa only [hj] using hp), Category.assoc, hd]
  have hmi : (⟨(m*j.val)%(r*m), Nat.mod_lt _ hs⟩ : Fin (r*m)) =
      ⟨m*i.val, by simpa only [Nat.mul_comm r m] using Nat.mul_lt_mul_of_pos_left i.isLt hm⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by simpa only [j,Nat.mul_comm r m] using Nat.mul_lt_mul_of_pos_left i.isLt hm)
  have hn := MarkedExactTorsion.point_nsmul k M hM h3s he e he0 G hG j a m
  rw [hmi,MarkedPointAddition.point_eq k h3s M hM _ _ q hq] at hn
  have hc := comp_nsmul k M G (𝟙 _) (MarkedPointAddition.point k h3s M hM j a) m
  rw [hn] at hc
  simpa only [MarkedPointAddition.point,pointOver,Category.id_comp] using hc

/-- The constructed dual is finite étale, surjective, and has degree `m`. -/
lemma dual_geometry {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (hm : 0 < m) (h3r : 3 ≤ r) (h3s : 3 ≤ r*m) (her : Even r) (hes : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : Fin (r*m) → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i 1 (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : Law k M) (hG : IsOriginLaw k M (p (zeroIndex (r*m) hs)) (hp _).1 G)
    (H : Law k N) (hH : IsOriginLaw k N q hq.1 H)
    (d : genericScheme k N ⟶ genericScheme k M)
    (hd : generic k (dvd_mul_right r m) M hM N hN ≫ d = G.schemeNsmul m)
    (hd' : d ≫ generic k (dvd_mul_right r m) M hM N hN = H.schemeNsmul m) :
    IsFinite d ∧ Etale d ∧ Surjective d ∧ ∀ y, d.finrank y = m := by
  let f := generic k (dvd_mul_right r m) M hM N hN
  have hmul := ArithmeticThetaHodgeFourTorsionR0147.multiplication_finite_etale_degree
    k (r*m) hs h3s T hes M hM (p (zeroIndex (r*m) hs)) (hp _) G hG m hm
  have hmul' := ArithmeticThetaHodgeFourTorsionR0147.multiplication_finite_etale_degree
    k r hr h3r U her N hN q hq H hH m hm
  letI : IsFinite f := generic_finite k (dvd_mul_right r m) h3r h3s M hM N hN
  letI : Flat f := (generic_flat_surjective k (dvd_mul_right r m) h3r h3s M hM N hN
    (p (zeroIndex (r*m) hs)) (hp _) q hq).1
  letI : Etale (f ≫ d) := by rw [hd]; exact hmul.2.1
  letI : FormallyUnramified f := FormallyUnramified.of_comp f d
  letI : IsFinite (d ≫ f) := by rw [hd']; exact hmul'.1
  letI : Etale (d ≫ f) := by rw [hd']; exact hmul'.2.1
  letI : IsFinite d := IsFinite.of_comp d f
  letI : Etale d := Etale.of_comp d f
  letI : Surjective (f ≫ d) := by rw [hd]; exact hmul.2.2.1
  refine ⟨inferInstance,inferInstance,Surjective.of_comp f d,?_⟩
  intro y
  have hdeg := Scheme.Hom.finrank_comp_of_finrank_eq_const f d m
    (generic_finrank k h3r h3s M hM N hN p hp q hq) y
  rw [hd] at hdeg
  have hsq : (G.schemeNsmul m).finrank y = m^2 := hmul.2.2.2 y
  nlinarith

lemma split_fibre_cartesian {F : Type} [Field F] {X Y : Scheme}
    (qX : X ⟶ Spec (.of F)) (qY : Y ⟶ Spec (.of F))
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (e : Spec (.of F) ⟶ Y) (he : e ≫ qY = 𝟙 _)
    (I : Type) [Fintype I] (p : I → (Spec (.of F) ⟶ X))
    (hp : ∀ i, p i ≫ qX = 𝟙 _) (hinj : Function.Injective p)
    (hkill : ∀ i, p i ≫ f = e) (hrank : ∀ y, f.finrank y = Fintype.card I) :
    IsPullback (Sigma.desc p) (Sigma.desc (fun _ : I => 𝟙 (Spec (.of F)))) f e := by
  letI : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id qY e he
  letI (i : I) : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id qX (p i) (hp i)
  let a := Sigma.desc p
  let b := Sigma.desc (fun _ : I => 𝟙 (Spec (.of F)))
  letI : Etale b := IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  letI : IsClosedImmersion a :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma p
      (fun i j hij => ArithmeticThetaKatoAnnularR0152.ActualSplitTorsionKernel.sections_disjoint
        qX (p i) (p j) (hp i) (hp j) (fun h => hij (hinj h)))
  have hw : a ≫ f = b ≫ e := by
    apply Sigma.hom_ext
    intro i
    simpa only [a,b,Sigma.ι_desc_assoc,Category.id_comp] using hkill i
  let l := pullback.lift a b hw
  have hl : l ≫ pullback.fst f e = a := pullback.lift_fst _ _ _
  letI : IsClosedImmersion l := by
    letI : IsClosedImmersion (l ≫ pullback.fst f e) := by rw [hl]; infer_instance
    exact IsClosedImmersion.of_comp l (pullback.fst f e)
  letI : IsIso l := by
    apply isIso_of_isClosedImmersion_of_finrank_comp_eq l (pullback.snd f e) b
      (pullback.lift_snd _ _ _)
    intro z
    rw [ArithmeticThetaKatoAnnularR0152.ActualSplitTorsionKernel.sigma_structure_rank,
      Scheme.Hom.finrank_pullback_snd]
    exact (hrank _).symm
  change IsPullback a b f e
  exact (IsPullback.of_hasPullback f e).of_iso (asIso l).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [l]) (by simp [l]) (by simp) (by simp)

/-- The dual's kernel is the specified toric roots of unity, as a scheme. -/
lemma dual_toric_kernel {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (hm : 0 < m) (h3r : 3 ≤ r) (h3s : 3 ≤ r*m) (her : Even r) (hes : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : Fin (r*m) → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i 1 (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : Law k M) (hG : IsOriginLaw k M (p (zeroIndex (r*m) hs)) (hp _).1 G)
    (H : Law k N) (hH : IsOriginLaw k N q hq.1 H)
    (d : genericScheme k N ⟶ genericScheme k M)
    (hd : generic k (dvd_mul_right r m) M hM N hN ≫ d = G.schemeNsmul m)
    (hd' : d ≫ generic k (dvd_mul_right r m) M hM N hN = H.schemeNsmul m)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) m)
    (u : Fin m → (baseScheme k ⟶ N.X))
    (hu : ∀ i, MarkedLift k N (zeroIndex r hr) (ζ^i.val) (u i)) :
    IsPullback (Sigma.desc (fun i : Fin m => genericPoint k N (u i) (hu i).1))
      (Sigma.desc (fun _ : Fin m => 𝟙 (Puncture k))) d
      (genericPoint k M (p (zeroIndex (r*m) hs)) (hp _).1) := by
  have hgeo := dual_geometry k hm h3r h3s her hes M hM N hN p hp q hq G hG H hH d hd hd'
  letI : IsFinite d := hgeo.1
  letI : Etale d := hgeo.2.1
  apply split_fibre_cartesian (genericStructure k N) (genericStructure k M) d _
    (pullback.lift_snd _ _ _) (Fin m) _
    (fun i => pullback.lift_snd _ _ _)
  · intro i j hij
    have hpt : pointOver k N (𝟙 _) (u i) (hu i).1 = pointOver k N (𝟙 _) (u j) (hu j).1 := by
      apply Subtype.ext
      simpa only [pointOver,Category.id_comp,ArithmeticThetaGenericEvaluationR0140.genericPoint] using hij
    have hz := (MarkedExactTorsion.labels_eq k N hN (u i) (u j) (hu i) (hu j) hpt).2
    apply Fin.ext
    apply hζ.pow_inj i.isLt j.isLt
    exact congrArg (fun z : kˣ => (z : k)) hz
  · intro i
    apply dual_marked k hm h3s hes M hM N hN (p (zeroIndex (r*m) hs)) (hp _) G hG d hd
      (zeroIndex r hr) (ζ^i.val) (u i) (hu i) (p (zeroIndex (r*m) hs))
    have hpow : (ζ^i.val)^m = 1 := by
      have hz : ζ^m = 1 := Units.ext hζ.pow_eq_one
      rw [← pow_mul,Nat.mul_comm i.val m,pow_mul,hz,one_pow]
    simpa only [hpow,zeroIndex,Nat.mul_zero] using hp (zeroIndex (r*m) hs)
  · intro y
    simpa only [Fintype.card_fin] using hgeo.2.2.2 y

end PeriodCollapse

namespace CubicComparison
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146

/-- The actual model-to-cubic isomorphism retains every literal toric marked
coordinate, together with its base map and origin. -/
lemma model_iso (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
    (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    ∃ E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r),
      E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M ∧
      genericPoint k M s hs.1 ≫ E.hom = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r) ∧
      ∀ (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p),
        i.val ≠ 0 ∨ (a : k) ≠ 1 →
        ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
          (genericPoint k M p hp.1 ≫ E.hom)
          (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val a))
          (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val a)) := by
  obtain ⟨X,hX,-⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y,hY,-⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a,ha,-⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c,hc,-⟩ := projective_cubic_chart k r
  obtain ⟨E,hE,-⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  refine ⟨E,hE.1,hE.2.2,?_⟩
  intro i b p hp hn
  refine ⟨?_, ArithmeticThetaHodgeFourTorsionR0147.marked_coordinate_chart
    k r hr h3 T he M hM s hs X Y hX hY a ha c hc E hE i b p hp hn⟩
  change genericPoint k M p hp.1 ≫ E.hom ≫
    ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r = _
  rw [hE.1]
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

lemma coordinates_unique {F : Type} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law F W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw F W G)
    {P Q : Base F ⟶ Curve F W} {x y : F}
    (hP : ArithmeticThetaLegendreComparisonR0177.HasCoordinates F W P x y)
    (hQ : ArithmeticThetaLegendreComparisonR0177.HasCoordinates F W Q x y) : P = Q := by
  classical
  obtain ⟨ev,hev,he0,hec⟩ := ProjectivePointsEvaluation.coordinateEvaluationExists W G
    (by
      have h := hG.1 (𝟙 (Base F))
      rw [Category.id_comp] at h
      exact h)
  obtain ⟨hPo,χ,hχ,hχx,hχy⟩ := hP
  obtain ⟨hQo,ψ,hψ,hψx,hψy⟩ := hQ
  let P' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F F))) (structureMap F W) :=
    ⟨P,by simpa using hPo⟩
  let Q' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F F))) (structureMap F W) :=
    ⟨Q,by simpa using hQo⟩
  obtain ⟨hxy,hPE⟩ := hec F P' χ hχ
  obtain ⟨hxy',hQE⟩ := hec F Q' ψ hψ
  have hPQ : P' = Q' := (ev F).injective (by
    rw [hPE,hQE]
    congr 1
    · exact hχx.trans hψx.symm
    · exact hχy.trans hψy.symm)
  exact congrArg Subtype.val hPQ

/-- The isomorphism identifies the given canonical full-level marking,
including its identity label; no new marking is substituted. -/
lemma canonical_model_iso (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
    (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (V : TateLevel k r) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) r)
    (hmark : CanonicalMarking k r (ζ : k) V) :
    ∃ E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r),
      E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M ∧
      genericPoint k M s hs.1 ≫ E.hom = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r) ∧
      ∀ (i j : Fin r) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M j (ζ^i.val) p),
        genericPoint k M p hp.1 ≫ E.hom =
          ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k r)
            V.law V.marking i j := by
  obtain ⟨E,hE,hO,hcoord⟩ := model_iso k r hr h3 he T M hM s hs
  letI := V.elliptic
  refine ⟨E,hE,hO,?_⟩
  intro i j p hp
  by_cases hn : i.val ≠ 0 ∨ j.val ≠ 0
  · apply coordinates_unique (TateCurve k r) V.law V.originLaw
      (x := algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX r j.val ((ζ : k)^i.val)))
      (y := algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY r j.val ((ζ : k)^i.val)))
    · have hne : j.val ≠ 0 ∨ ((ζ^i.val : kˣ) : k) ≠ 1 := by
        rcases hn with hi | hj
        · exact Or.inr (by simpa only [Units.val_pow_eq_pow_val] using hζ.pow_ne_one_of_pos_of_lt hi i.isLt)
        · exact Or.inl hj
      simpa only [Units.val_pow_eq_pow_val] using hcoord j (ζ^i.val) p hp hne
    · exact hmark i j hn
  · have hi : i.val = 0 := by tauto
    have hj : j = zeroIndex r hr := Fin.ext (by tauto)
    have hp0 : MarkedLift k M (zeroIndex r hr) 1 p := by simpa only [hi,hj,pow_zero] using hp
    have hps := ActualRotationTranslation.markedLift_unique k M (zeroIndex r hr) 1 p s hp0 hs
    have hpO : genericPoint k M p hp.1 ≫ E.hom =
        ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r) := by
      subst p
      exact hO
    rw [hpO]
    simp only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint,hi,hj,zeroIndex,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,V.law.one_mul,V.originLaw.1,Category.id_comp]

open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw

lemma transported_origin (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    (V : TateLevel k r) (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)
    (hO : genericPoint k M s hs ≫ E.hom = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)) :
    ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs (transport E hE V.law) := by
  constructor
  · intro Z t
    apply Subtype.ext
    change (V.law.one t).val ≫ E.inv = t ≫ genericPoint k M s hs
    rw [V.originLaw.1,← hO]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  · intro Z t x y
    change (pointsEquiv E hE t).symm (V.law.mul t _ _) =
      (pointsEquiv E hE t).symm (V.law.mul t _ _)
    rw [V.originLaw.2]

/-- An existing origin law, including the one from the unary provider,
agrees with the given cubic law under this actual isomorphism. -/
lemma model_nsmul (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G)
    (V : TateLevel k r) (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)
    (hO : genericPoint k M s hs.1 ≫ E.hom = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r)) :
    ∀ n, G.schemeNsmul n ≫ E.hom = E.hom ≫ V.law.schemeNsmul n := by
  have hGt : G = transport E hE V.law :=
    (actual_generic_group_law k r hr h3 T he M hM s hs).unique hG
      (transported_origin k M s hs.1 V E hE hO)
  rw [hGt]
  exact OpenDiscriminantFullTateExpansionR0182.transported_schemeNsmul E hE V.law


/-- The accepted model with its existing law is an actual elliptic family. -/
def modelFamily (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (h3 : 3 ≤ r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) :
    ArithmeticThetaLegendreAtlasR0176.EllipticFamily (LaurentSeries k) where
  curve := genericScheme k M
  projection := genericStructure k M
  law := ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G
  commutative := hG.2
  proper := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  smooth := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3 M hM s hs
  connected := algebraized_geometric_connectedness k r hr h3 T M hM

lemma modelFamily_zero (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (h3 : 3 ≤ r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) :
    zero (modelFamily k h3 M hM s hs G hG) = genericPoint k M s hs.1 := by
  change (G.one (𝟙 _)).val = _
  rw [hG.1]
  exact Category.id_comp _


/-- Any origin law on the target cubic agrees with the existing model law.
This comparison needs no full-level marking on the target. -/
lemma model_nsmul_of_origin (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G)
    (W : WeierstrassCurve (LaurentSeries k))
    (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) W)
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) W H)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) W)
    (hE : E.hom ≫ structureMap (LaurentSeries k) W = genericStructure k M)
    (hO : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) W) :
    ∀ n, G.schemeNsmul n ≫ E.hom = E.hom ≫ H.schemeNsmul n := by
  have ht : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 (transport E hE H) := by
    constructor
    · intro Z t
      apply Subtype.ext
      change (H.one t).val ≫ E.inv = t ≫ genericPoint k M s hs.1
      rw [hH.1,← hO]
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    · intro Z t x y
      change (pointsEquiv E hE t).symm (H.mul t _ _) =
        (pointsEquiv E hE t).symm (H.mul t _ _)
      rw [hH.2]
  have hGt : G = transport E hE H :=
    (actual_generic_group_law k r hr h3 T he M hM s hs).unique hG ht
  rw [hGt]
  exact OpenDiscriminantFullTateExpansionR0182.transported_schemeNsmul E hE H

end CubicComparison



/-- The full-level toric label maps to the corresponding multiple of the
specified global kernel generator. -/
lemma test_kernel_multiple (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 0 < L)
    {D : LevelData k L} (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (m : ℕ) (hm : 0 < m) (hmL : m ∣ L) (i : Fin m) :
    ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k L)
      V.level.law V.level.marking
      ⟨L/m*i.val, by
        have h := Nat.mul_lt_mul_of_pos_left i.isLt (Nat.div_pos (Nat.le_of_dvd hL hmL) hm)
        simpa only [Nat.div_mul_cancel hmL] using h⟩
      (ArithmeticThetaIdentitySectionsR0138.zeroIndex L hL) ≫ V.map =
      (V.base ≫ D.quotient.inclusion) ≫ kernelPoint k L D.atlas m ≫
        D.atlas.descent.family.law.schemeNsmul i.val := by
  simp only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint,
    ArithmeticThetaIdentitySectionsR0138.zeroIndex,
    WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,V.level.law.mul_one]
  rw [test_nsmul k L V _ _ V.classifies.2.2.2.1]
  change _ = (V.base ≫ D.quotient.inclusion) ≫
    (D.atlas.descent.family.law.nsmul (𝟙 _) (L/m) D.atlas.marking.x).val ≫
      D.atlas.descent.family.law.schemeNsmul i.val
  rw [GlobalLevelCyclicQuotientR0180.nsmul_comp]

namespace QuotientComparison
open CategoryTheory.Limits ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180

/-- The specified global quotient kills each specified kernel section. -/
lemma quotient_kills {R : Type} [CommRing R] (E : EllipticFamily R)
    {m : ℕ} (P : Cyclic E m) (Q : Quotient R E m P.point) (i : Fin m) :
    multiple E P i ≫ Q.arrow.map = zero Q.target := by
  have ho : zero Q.target ≫ Q.target.projection = 𝟙 _ :=
    (Q.target.law.one (𝟙 _)).property
  letI := Q.target.proper
  letI : IsClosedImmersion (zero Q.target ≫ Q.target.projection) := by rw [ho]; infer_instance
  letI : IsClosedImmersion (zero Q.target) :=
    IsClosedImmersion.of_comp _ Q.target.projection
  have hle : (zero Q.target).ker ≤ (multiple E P i ≫ Q.arrow.map).ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le, Q.kernel]
    exact iInf_le _ i
  let a := IsClosedImmersion.lift (zero Q.target) (multiple E P i ≫ Q.arrow.map) hle
  have hfac : a ≫ zero Q.target = multiple E P i ≫ Q.arrow.map :=
    IsClosedImmersion.lift_fac _ _ _
  have hid : a = 𝟙 _ := by
    have h := congrArg (fun f => f ≫ Q.target.projection) hfac
    simpa only [Category.assoc,ho,Category.comp_id,Q.arrow.over_eq,multiple_over] using h
  rw [← hfac,hid,Category.id_comp]

/-- Recover the entire split scheme fibre of the given global quotient from
its ideal-theoretic kernel, including nonreduced base changes. -/
lemma quotient_split_cartesian {R : Type} [CommRing R] (E : EllipticFamily R)
    {m : ℕ} (P : Cyclic E m) (Q : Quotient R E m P.point) :
    IsPullback (Sigma.desc (multiple E P))
      (Sigma.desc (fun _ : Fin m => 𝟙 (Base R))) Q.arrow.map (zero Q.target) := by
  let a := Sigma.desc (multiple E P)
  let b := Sigma.desc (fun _ : Fin m => 𝟙 (Base R))
  have ho : zero Q.target ≫ Q.target.projection = 𝟙 _ :=
    (Q.target.law.one (𝟙 _)).property
  letI := Q.target.proper
  letI : IsClosedImmersion (zero Q.target ≫ Q.target.projection) := by rw [ho]; infer_instance
  letI : IsClosedImmersion (zero Q.target) :=
    IsClosedImmersion.of_comp _ Q.target.projection
  letI := E.proper
  letI (i : Fin m) : IsClosedImmersion (multiple E P i) := by
    letI : IsClosedImmersion (multiple E P i ≫ E.projection) := by
      rw [multiple_over]; infer_instance
    exact IsClosedImmersion.of_comp _ E.projection
  letI : IsClosedImmersion a :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma
      (multiple E P) (fun i j hij => P.disjoint i j hij)
  have hker : a.ker = ⨅ i : Fin m, (multiple E P i).ker := by
    rw [← a.iInf_ker_openCover_map_comp (sigmaOpenCover (fun _ : Fin m => Base R))]
    congr 1
    funext i
    congr 1
    exact Sigma.ι_desc _ i
  apply isPullback_of_isClosedImmersion a (zero Q.target) b Q.arrow.map
  · apply Sigma.hom_ext
    intro i
    simpa only [a,b,Sigma.ι_desc_assoc,Category.id_comp] using quotient_kills E P Q i
  · rw [hker,Q.kernel]
    rfl

/-- Two faithfully flat group quotients with the same actual split kernel
have isomorphic targets over the base, and the isomorphism commutes with the
quotient arrows and origins. -/
lemma iso_of_split_kernel {R : Type} [CommRing R] (E F H : EllipticFamily R)
    (f : Pointed R E F) (g : Pointed R E H) (hf : IsHom f) (hg : IsHom g)
    [Flat f.map] [Surjective f.map] [QuasiCompact f.map]
    [Flat g.map] [Surjective g.map] [QuasiCompact g.map]
    {K : Scheme} (a : K ⟶ E.curve) (b : K ⟶ Base R)
    (hKf : IsPullback a b f.map (zero F))
    (hKg : IsPullback a b g.map (zero H)) :
    ∃ e : F.curve ≅ H.curve, f.map ≫ e.hom = g.map ∧
      e.hom ≫ H.projection = F.projection ∧ zero F ≫ e.hom = zero H := by
  have factor {F H : EllipticFamily R} (f : Pointed R E F) (g : Pointed R E H)
      (hf : IsHom f) (hg : IsHom g)
      [Flat f.map] [Surjective f.map] [QuasiCompact f.map]
      (hKf : IsPullback a b f.map (zero F))
      (hKg : IsPullback a b g.map (zero H)) :
      ∃ d : F.curve ⟶ H.curve, f.map ≫ d = g.map ∧ d ≫ H.projection = F.projection := by
    obtain ⟨d,hd,⟨hdo,-⟩,-⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
        E.law F.law H.law f.map f.over_eq (fun t x y => hf _ t x y)
        g.map g.over_eq (fun t x y => hg _ t x y) (fun t x hx => by
          apply Subtype.ext
          have honeF : (F.law.one t).val = t ≫ zero F :=
            (congrArg Subtype.val (F.law.one_natural (𝟙 _) t t (Category.comp_id _))).symm
          have honeH : (H.law.one t).val = t ≫ zero H :=
            (congrArg Subtype.val (H.law.one_natural (𝟙 _) t t (Category.comp_id _))).symm
          have hx' : x.val ≫ f.map = t ≫ zero F := (congrArg Subtype.val hx).trans honeF
          let l := hKf.lift x.val t hx'
          have hl₁ : l ≫ a = x.val := hKf.lift_fst _ _ _
          have hl₂ : l ≫ b = t := hKf.lift_snd _ _ _
          change x.val ≫ g.map = (H.law.one t).val
          rw [honeH,← hl₁,Category.assoc,hKg.w,← Category.assoc,hl₂])
    exact ⟨d,hd,hdo⟩
  obtain ⟨d,hd,hdo⟩ := factor f g hf hg hKf hKg
  obtain ⟨c,hc,hco⟩ := factor g f hg hf hKg hKf
  letI : Epi f.map := Flat.epi_of_flat_of_surjective _
  letI : Epi g.map := Flat.epi_of_flat_of_surjective _
  have hdc : d ≫ c = 𝟙 _ := by
    apply (cancel_epi f.map).mp
    rw [← Category.assoc,hd,hc,Category.comp_id]
  have hcd : c ≫ d = 𝟙 _ := by
    apply (cancel_epi g.map).mp
    rw [← Category.assoc,hc,hd,Category.comp_id]
  refine ⟨⟨d,c,hdc,hcd⟩,hd,hdo,?_⟩
  rw [← f.zero_eq,Category.assoc,hd,g.zero_eq]


section BaseChange
variable {R S : Type} [CommRing R] [CommRing S]
variable (E F : EllipticFamily R) (f : Pointed R E F) (b : Base S ⟶ Base R)
variable {X : Scheme} (p : X ⟶ Base S) (j : X ⟶ E.curve)
variable (hX : IsPullback j p E.projection b)

/-- The arrow into the actual base change of the specified quotient target. -/
def baseChangeArrow : X ⟶ (baseChangeFamily F b).curve :=
  pullback.lift (j ≫ f.map) p (by rw [Category.assoc,f.over_eq]; exact hX.w)

@[reassoc] lemma baseChangeArrow_fst :
    baseChangeArrow E F f b p j hX ≫ pullback.fst F.projection b = j ≫ f.map :=
  pullback.lift_fst _ _ _

@[reassoc] lemma baseChangeArrow_over :
    baseChangeArrow E F f b p j hX ≫ (baseChangeFamily F b).projection = p :=
  pullback.lift_snd _ _ _

lemma baseChangeArrow_cartesian :
    IsPullback j (baseChangeArrow E F f b p j hX) f.map (pullback.fst F.projection b) := by
  have ho : IsPullback j
      (baseChangeArrow E F f b p j hX ≫ pullback.snd F.projection b)
      (f.map ≫ F.projection) b := by
    rw [show baseChangeArrow E F f b p j hX ≫ pullback.snd F.projection b = p from
      baseChangeArrow_over E F f b p j hX,f.over_eq]
    exact hX
  exact ho.of_bot (baseChangeArrow_fst E F f b p j hX).symm (IsPullback.of_hasPullback _ _)

lemma baseChangeArrow_geometry [IsFinite f.map] [Etale f.map] [Surjective f.map]
    {m : ℕ} (hdeg : ∀ y, f.map.finrank y = m) :
    IsFinite (baseChangeArrow E F f b p j hX) ∧
    Etale (baseChangeArrow E F f b p j hX) ∧
    Surjective (baseChangeArrow E F f b p j hX) ∧
    ∀ y, (baseChangeArrow E F f b p j hX).finrank y = m := by
  have hc := baseChangeArrow_cartesian E F f b p j hX
  refine ⟨MorphismProperty.of_isPullback hc inferInstance,
    MorphismProperty.of_isPullback hc inferInstance,
    MorphismProperty.of_isPullback hc inferInstance,?_⟩
  intro y
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hc]
  exact hdeg _

end BaseChange

/-- The kernel of the actual base-changed quotient consists of precisely the
lifts of its specified cyclic labels. This is a Cartesian scheme statement. -/
lemma quotient_split_baseChange {R S : Type} [CommRing R] [CommRing S]
    (E : EllipticFamily R) {m : ℕ} (P : Cyclic E m) (Q : Quotient R E m P.point)
    (b : Base S ⟶ Base R) {X : Scheme} (p : X ⟶ Base S) (j : X ⟶ E.curve)
    (hX : IsPullback j p E.projection b)
    (u : Fin m → (Base S ⟶ X)) (hu : ∀ i, u i ≫ p = 𝟙 _)
    (huj : ∀ i, u i ≫ j = b ≫ multiple E P i) :
    IsPullback (Sigma.desc u) (Sigma.desc (fun _ : Fin m => 𝟙 (Base S)))
      (baseChangeArrow E Q.target Q.arrow b p j hX) (zero (baseChangeFamily Q.target b)) := by
  let a := Sigma.desc u
  let c := Sigma.desc (fun _ : Fin m => 𝟙 (Base S))
  let sn := Sigma.desc (fun i : Fin m => b ≫ Sigma.ι (fun _ : Fin m => Base R) i)
  have hsm : sn ≫ Sigma.desc (multiple E P) = a ≫ j := by
    apply Sigma.hom_ext
    intro i
    simpa only [sn,a,Sigma.ι_desc_assoc,Category.assoc,Sigma.ι_desc] using (huj i).symm
  have ho := (PeriodCollapse.sigma_base_change (Fin m) b).paste_horiz
    (quotient_split_cartesian E P Q)
  change IsPullback (sn ≫ _) c _ _ at ho
  rw [hsm,← baseChange_zero Q.target b] at ho
  apply ho.of_right ?_ (baseChangeArrow_cartesian E Q.target Q.arrow b p j hX)
  apply Sigma.hom_ext
  intro i
  simp only [a,c,Sigma.ι_desc_assoc,Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc,baseChangeArrow_fst,← Category.assoc,huj,Category.assoc,
      quotient_kills,baseChange_zero]
  · rw [Category.assoc,baseChangeArrow_over,hu]
    exact (Q.target.law.baseChange b |>.one (𝟙 _)).property.symm


/-- The cyclic object has definitionally the prescribed global generator. -/
def levelCyclic (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 0 < L)
    (D : LevelData k L) (m : ℕ) (hm : 0 < m) (hmL : m ∣ L) :
    Cyclic D.atlas.descent.family m := by
  let P := (cyclic_of_level D.atlas.descent.family hL D.atlas.marking m hm hmL).choose
  have hP : P.point = kernelPoint k L D.atlas m :=
    (cyclic_of_level D.atlas.descent.family hL D.atlas.marking m hm hmL).choose_spec
  exact {
    point := kernelPoint k L D.atlas m
    over_eq := by rw [← hP]; exact P.over_eq
    killed := by rw [← hP]; exact P.killed
    disjoint := by rw [← hP]; exact P.disjoint }

end QuotientComparison

namespace ToricQuotient
open CategoryTheory.Limits ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open QuotientComparison CubicComparison

lemma model_cartesian (k : Type) [Field k] [CharZero k] (r : ℕ)
    {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    {D : LevelData k r} (V : ArithmeticThetaBoundaryHodgeR0182.Test k r D)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M) :
    IsPullback (E.hom ≫ V.map) (genericStructure k M) D.atlas.descent.family.projection
      (V.base ≫ D.quotient.inclusion) := by
  exact V.classifies.2.1.of_iso E.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp [← hE]) (by simp) (by simp)

/-- Every toric root is sent to the same labeled global kernel section. -/
lemma toric_labels (k : Type) [Field k] [CharZero k] (r m : ℕ)
    (hr : 0 < r) (hm : 0 < m) (hmr : m ∣ r)
    {T : Tower k r hr} (M : Model k T)
    {D : LevelData k r} (V : ArithmeticThetaBoundaryHodgeR0182.Test k r D)
    (ζ : kˣ) (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hmark : ∀ (i j : Fin r) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M j (ζ^i.val) p),
      genericPoint k M p hp.1 ≫ E.hom =
        ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k r)
          V.level.law V.level.marking i j)
    (i : Fin m) (u : baseScheme k ⟶ M.X)
    (hu : MarkedLift k M (zeroIndex r hr) ((ζ^(r/m))^i.val) u) :
    genericPoint k M u hu.1 ≫ E.hom ≫ V.map =
      (V.base ≫ D.quotient.inclusion) ≫ kernelPoint k r D.atlas m ≫
        D.atlas.descent.family.law.schemeNsmul i.val := by
  have hi : r/m*i.val < r := by
    have h := Nat.mul_lt_mul_of_pos_left i.isLt (Nat.div_pos (Nat.le_of_dvd hr hmr) hm)
    simpa only [Nat.div_mul_cancel hmr] using h
  have hu' : MarkedLift k M (zeroIndex r hr) (ζ^(r/m*i.val)) u := by
    simpa only [pow_mul] using hu
  rw [← Category.assoc,hmark ⟨r/m*i.val,hi⟩ (zeroIndex r hr) u hu']
  exact test_kernel_multiple k r hr V m hm hmr i

/-- With the given canonical model comparison, the specified global quotient
is isomorphic over the puncture to the constructed dual toric quotient. -/
lemma compare (k : Type) [Field k] [CharZero k]
    {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (hm : 0 < m) (hmr : m ∣ r) (h3r : 3 ≤ r) (h3s : 3 ≤ r*m)
    (her : Even r) (hes : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (p : Fin (r*m) → (baseScheme k ⟶ M.X)) (hp : ∀ i, MarkedLift k M i 1 (p i))
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M (p (zeroIndex (r*m) hs)) (hp _).1 G)
    (H : ArithmeticThetaMarkedGroupLawR0146.Law k N)
    (hH : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k N q hq.1 H)
    (d : genericScheme k N ⟶ genericScheme k M)
    (hdo : d ≫ genericStructure k M = genericStructure k N)
    (hd : PeriodCollapse.generic k (dvd_mul_right r m) M hM N hN ≫ d = G.schemeNsmul m)
    (hd' : d ≫ PeriodCollapse.generic k (dvd_mul_right r m) M hM N hN = H.schemeNsmul m)
    {D : LevelData k r} (V : ArithmeticThetaBoundaryHodgeR0182.Test k r D)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) r)
    (E : genericScheme k N ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k N)
    (hO : genericPoint k N q hq.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k r))
    (hmark : ∀ (i j : Fin r) (p' : baseScheme k ⟶ N.X) (hp' : MarkedLift k N j (ζ^i.val) p'),
      genericPoint k N p' hp'.1 ≫ E.hom =
        ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k r)
          V.level.law V.level.marking i j)
    (Q : Quotient D.atlas.quotient.ring D.atlas.descent.family m (kernelPoint k r D.atlas m)) :
    ∃ e : (baseChangeFamily Q.target (V.base ≫ D.quotient.inclusion)).curve ≅ genericScheme k M,
      baseChangeArrow D.atlas.descent.family Q.target Q.arrow (V.base ≫ D.quotient.inclusion)
        (genericStructure k N) (E.hom ≫ V.map) (model_cartesian k r N V E hE) ≫ e.hom = d ∧
      e.hom ≫ genericStructure k M = (baseChangeFamily Q.target (V.base ≫ D.quotient.inclusion)).projection ∧
      zero (baseChangeFamily Q.target (V.base ≫ D.quotient.inclusion)) ≫ e.hom =
        genericPoint k M (p (zeroIndex (r*m) hs)) (hp _).1 := by
  let B := V.base ≫ D.quotient.inclusion
  let F := modelFamily k h3r N hN q hq H hH
  let J := modelFamily k h3s M hM (p (zeroIndex (r*m) hs)) (hp _) G hG
  let Y := baseChangeFamily Q.target B
  let a := baseChangeArrow D.atlas.descent.family Q.target Q.arrow B
    (genericStructure k N) (E.hom ≫ V.map) (model_cartesian k r N V E hE)
  have hao : a ≫ Y.projection = F.projection := baseChangeArrow_over _ _ _ _ _ _ _
  have ha0 : zero F ≫ a = zero Y := by
    rw [modelFamily_zero]
    apply pullback.hom_ext
    · rw [Category.assoc,baseChangeArrow_fst,← Category.assoc,← Category.assoc,hO,
        V.classifies.2.2.1,Category.assoc,Q.arrow.zero_eq]
      exact (baseChange_zero Q.target B).symm
    · rw [Category.assoc,hao]
      exact (pullback.lift_snd _ _ _).trans (Y.law.one (𝟙 _)).property.symm
  let f : Pointed (LaurentSeries k) F Y := ⟨a,hao,ha0⟩
  have hd0 : zero F ≫ d = zero J := by
    rw [modelFamily_zero,modelFamily_zero]
    apply PeriodCollapse.dual_marked k hm h3s hes M hM N hN
      (p (zeroIndex (r*m) hs)) (hp _) G hG d hd (zeroIndex r hr) 1 q hq
      (p (zeroIndex (r*m) hs))
    simpa only [zeroIndex,Nat.mul_zero,one_pow] using hp (zeroIndex (r*m) hs)
  let g : Pointed (LaurentSeries k) F J := ⟨d,hdo,hd0⟩
  have hgeo := PeriodCollapse.dual_geometry k hm h3r h3s her hes M hM N hN p hp q hq G hG H hH d hd hd'
  letI : IsFinite Q.arrow.map := Q.finite
  letI : Etale Q.arrow.map := Q.etale
  letI : Surjective Q.arrow.map := Q.surjective
  have hageo := baseChangeArrow_geometry D.atlas.descent.family Q.target Q.arrow B
    (genericStructure k N) (E.hom ≫ V.map) (model_cartesian k r N V E hE) Q.degree
  letI : IsFinite f.map := hageo.1
  letI : Etale f.map := hageo.2.1
  letI : Surjective f.map := hageo.2.2.1
  letI : IsFinite g.map := hgeo.1
  letI : Etale g.map := hgeo.2.1
  letI : Surjective g.map := hgeo.2.2.1
  let z := ζ^(r/m)
  have hz : IsPrimitiveRoot (z : k) m := by
    simpa only [z,Units.val_pow_eq_pow_val] using IsPrimitiveRoot.pow hr hζ (Nat.div_mul_cancel hmr).symm
  let u (i : Fin m) := MarkedPointAddition.sectionAt k h3r N hN (zeroIndex r hr) (z^i.val)
  have hu (i : Fin m) : MarkedLift k N (zeroIndex r hr) (z^i.val) (u i) :=
    MarkedPointAddition.sectionAt_spec k h3r N hN _ _
  let P := levelCyclic k r hr D m hm hmr
  have hKf := quotient_split_baseChange D.atlas.descent.family P Q B
    (genericStructure k N) (E.hom ≫ V.map) (model_cartesian k r N V E hE)
    (fun i => genericPoint k N (u i) (hu i).1) (fun i => pullback.lift_snd _ _ _)
    (fun i => toric_labels k r m hr hm hmr N V ζ E hmark i (u i) (hu i))
  have hKg := PeriodCollapse.dual_toric_kernel k hm h3r h3s her hes
    M hM N hN p hp q hq G hG H hH d hd hd' z hz u hu
  have hKg' : IsPullback (Sigma.desc (fun i => genericPoint k N (u i) (hu i).1))
      (Sigma.desc (fun _ : Fin m => 𝟙 (Puncture k))) g.map (zero J) := by
    rw [modelFamily_zero]
    exact hKg
  obtain ⟨e,he,heOver,he0⟩ := iso_of_split_kernel F Y J f g
    (pointed_hom F f) (pointed_hom F g) _ _ hKf hKg'
  refine ⟨e,he,heOver,?_⟩
  simpa only [J,modelFamily_zero] using he0


/-- The specified characteristic is sent to the exact unary label, including
zero residue. The scalar is literally `-1`, with no root-of-unity ambiguity. -/
lemma designated_dual_marked (k : Type) [Field k] [CharZero k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ))
    {hr : 0 < 24*N^2} {hs : 0 < (24*N^2)*m}
    (h3s : 3 ≤ (24*N^2)*m) (hes : Even ((24*N^2)*m))
    {T : Tower k ((24*N^2)*m) hs} {U : Tower k (24*N^2) hr}
    (M : Model k T) (hM : IsModel k T M) (A : Model k U) (hA : IsModel k U A)
    (e : baseScheme k ⟶ M.X) (he : MarkedLift k M (zeroIndex ((24*N^2)*m) hs) 1 e)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M e he.1 G)
    (d : genericScheme k A ⟶ genericScheme k M)
    (hd : PeriodCollapse.generic k (dvd_mul_right (24*N^2) m) M hM A hA ≫ d = G.schemeNsmul m)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (24*N^2))
    (i : Fin (24*N^2)) (hi : i.val = 24*N^2/N*unaryResidue m N ν)
    (a : baseScheme k ⟶ A.X)
    (ha : MarkedLift k A i (ζ^(24*N^2/(m*N)*(N/2))) a)
    (j : Fin ((24*N^2)*m)) (hj : j.val = (N^2/m)*ArithmeticThetaUnaryProduct.unaryA m ν)
    (b : baseScheme k ⟶ M.X) (hb : MarkedLift k M j (-1) b) :
    genericPoint k A a ha.1 ≫ d = genericPoint k M b hb.1 := by
  have hz : (ζ^(24*N^2/(m*N)*(N/2)))^m = (-1 : kˣ) := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one] using
      designated_toric_scalar k m N hm hN hNeven hmN ν hν (ζ : k) hζ
  have hij : (⟨m*i.val, by
        simpa only [Nat.mul_comm (24*N^2) m] using Nat.mul_lt_mul_of_pos_left i.isLt hm⟩ :
        Fin ((24*N^2)*m)) = j := by
    apply Fin.ext
    change m*i.val = j.val
    rw [hi,hj]
    exact designated_exponent m N hm hN hNeven hmN ν hν
  apply PeriodCollapse.dual_marked k hm h3s hes M hM A hA e he G hG d hd i
    (ζ^(24*N^2/(m*N)*(N/2))) a ha b
  simpa only [hz,hij] using hb

/-- The exact source lift is preserved by the canonical cubic comparison. -/
lemma designated_source_point (k : Type) [Field k] [CharZero k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ))
    {hr : 0 < 24*N^2} {U : Tower k (24*N^2) hr} (A : Model k U)
    {D : LevelData k (24*N^2)} (V : ArithmeticThetaBoundaryHodgeR0182.Test k (24*N^2) D)
    (ζ : kˣ) (E : genericScheme k A ≅ Curve (LaurentSeries k) (TateCurve k (24*N^2)))
    (hmark : ∀ (i j : Fin (24*N^2)) (p : baseScheme k ⟶ A.X) (hp : MarkedLift k A j (ζ^i.val) p),
      genericPoint k A p hp.1 ≫ E.hom =
        ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k (24*N^2))
          V.level.law V.level.marking i j)
    (i : Fin (24*N^2)) (hi : i.val = 24*N^2/N*unaryResidue m N ν)
    (a : baseScheme k ⟶ A.X)
    (ha : MarkedLift k A i (ζ^(24*N^2/(m*N)*(N/2))) a) :
    genericPoint k A a ha.1 ≫ E.hom ≫ V.map = (V.base ≫ D.quotient.inclusion) ≫
      liftPoint k (24*N^2) D.atlas m N (unaryResidue m N ν) (N/2) := by
  have hi' := source_indices m N hm hN hNeven hmN ν hν
  have hc := hmark ⟨24*N^2/(m*N)*(N/2),hi'.2.1⟩ i a ha
  rw [← Category.assoc,hc]
  have hpt : ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k (24*N^2))
      V.level.law V.level.marking ⟨24*N^2/(m*N)*(N/2),hi'.2.1⟩ i =
      ArithmeticThetaFullLevelCoverR0175.liftPoint (LaurentSeries k) (TateCurve k (24*N^2))
        V.level.law m N (unaryResidue m N ν) (N/2) V.level.marking := by
    simp only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint,
      ArithmeticThetaFullLevelCoverR0175.liftPoint,hi]
  rw [hpt]
  exact test_lift k (24*N^2) V m N (unaryResidue m N ν) (N/2)

/-- Transport through the quotient isomorphism retains the actual marked
point in the global target, not merely its order or its coordinate orbit. -/
lemma target_point_map {S : Scheme} {X Y Z C : Scheme}
    (a : S ⟶ X) (b : S ⟶ Y) (d : X ⟶ Y)
    (hpoint : a ≫ d = b) (e : Z ≅ Y) (q : X ⟶ Z) (hqe : q ≫ e.hom = d)
    (j : X ⟶ C) (f : Z ⟶ C) (hqf : q ≫ f = j) :
    b ≫ e.inv ≫ f = a ≫ j := by
  rw [← hpoint,← hqe]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,hqf]

end ToricQuotient



namespace TargetTest
open CategoryTheory.Limits ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw

/-- An actual pointed isomorphism from the base-changed target to a cubic
supplies all the multiplication comparisons required by the intrinsic D2
and Kato predicates. No full marking of the target is required. -/
lemma of_iso {S R : Type} [CommRing S] [CommRing R]
    (F : EllipticFamily S) (ρ : S →+* R) (W : WeierstrassCurve R)
    (e : (baseChangeFamily F (baseMap S R ρ)).curve ≅ Curve R W)
    (he : e.hom ≫ structureMap R W = (baseChangeFamily F (baseMap S R ρ)).projection)
    (heo : zero (baseChangeFamily F (baseMap S R ρ)) ≫ e.hom = origin R W) :
    ∃ (G : ArithmeticThetaRelativeKatoR0169.Law R W)
      (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
      (C : ArithmeticThetaOpenHodgeR0180.Test S F R W G),
      C.scalar = ρ ∧ C.map = e.inv ≫ pullback.fst F.projection (baseMap S R ρ) := by
  let q := baseMap S R ρ
  let H := F.law.baseChange q
  have hei : e.inv ≫ pullback.snd F.projection q = structureMap R W := by
    change e.inv ≫ (baseChangeFamily F (baseMap S R ρ)).projection = _
    rw [← he,e.inv_hom_id_assoc]
  let G : ArithmeticThetaRelativeKatoR0169.Law R W := transport e.symm hei (toWeierstrassLaw H)
  have hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G := by
    constructor
    · intro T t
      change (H.one t).val ≫ e.hom = t ≫ origin R W
      have ht := congrArg Subtype.val (H.one_natural (𝟙 _) t t (by simp))
      change t ≫ (H.one (𝟙 _)).val = (H.one t).val at ht
      rw [← ht,Category.assoc,heo]
    · intro T t P Q
      change (pointsEquiv e.symm hei t).symm (H.mul t _ _) =
        (pointsEquiv e.symm hei t).symm (H.mul t _ _)
      exact congrArg (pointsEquiv e.symm hei t).symm
        (GoodReductionJacobian.RelativeGroupLaw.IsCommutative.baseChange q F.commutative t _ _)
  let b := e.inv ≫ pullback.fst F.projection q
  have hc : IsPullback b (structureMap R W) F.projection q := by
    have comm : b ≫ F.projection = structureMap R W ≫ q := by
      dsimp [b]
      rw [Category.assoc,pullback.condition,← Category.assoc,hei]
    exact IsPullback.of_iso_pullback ⟨comm⟩ e.symm rfl hei
  have hbzero : origin R W ≫ b = q ≫ zero F := by
    rw [← heo]
    simpa only [b,Category.assoc,Iso.hom_inv_id_assoc] using baseChange_zero F q
  have hbn (n : ℕ) : G.schemeNsmul n ≫ b = b ≫ F.law.schemeNsmul n := by
    have ht := transport_nsmul e.symm hei (toWeierstrassLaw H) (structureMap R W)
      WeierstrassProjModel.RelativeGroupLaw.idPoint n
    have hb := baseChange_nsmul F.law q (structureMap R W)
      (pointsEquiv e.symm hei (structureMap R W) WeierstrassProjModel.RelativeGroupLaw.idPoint) n
    have htt := congrArg
      (fun P => (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase q P).val) ht
    have hnat := congrArg Subtype.val
      (F.law.nsmul_natural F.projection (structureMap R W ≫ q) b hc.w n
        GoodReductionJacobian.RelativeGroupLaw.idPoint)
    exact htt.trans ((congrArg Subtype.val hb).trans hnat.symm)
  exact ⟨G,hG,⟨ρ,b,hc,hbzero,hbn⟩,rfl,rfl⟩


/-- A regular-unit value in the relative definition gives the same value in
the actual local ring at the field-valued point. -/
lemma relative_value_stalk {K : Type} [Field K] (W : WeierstrassCurve K)
    [IsIntegral (Curve K W)] (P : Base K ⟶ Curve K W)
    (g : (Curve K W).functionField) (v : K)
    (hv : ArithmeticThetaRelativeKatoNaturalityR0170.HasValue K W P g v) :
    ArithmeticThetaMarkedKatoValuesR0159.HasValue K (Curve K W) P g v := by
  obtain ⟨U,hU,e,a,-,hg,hv⟩ := hv
  letI := hU
  have hx : P (IsLocalRing.closedPoint K) ∈ U := e trivial
  refine ⟨(Curve K W).presheaf.germ U _ hx a,?_,?_⟩
  · rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    exact hg
  · have h := ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo P U hx) a
    change Scheme.stalkClosedPointTo P ((Curve K W).presheaf.germ U _ hx a) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (P.appLE U ⊤ e a) at h
    exact h.trans hv

/-- The relative value equals the local provider's value through the actual
field map and the same marked point. -/
lemma value_eq_model {K : Type} [Field K] (W : WeierstrassCurve K)
    [IsIntegral (Curve K W)] {X : Scheme} [IsIntegral X]
    (f : X ⟶ Curve K W) (α : (Curve K W).functionField →+* X.functionField)
    (hα : ArithmeticThetaGeometricNormR0150.IsFieldMap f α)
    (P : Base K ⟶ Curve K W) (p : Base K ⟶ X) (hp : p ≫ f = P)
    (g : (Curve K W).functionField) (v w : K)
    (hv : ArithmeticThetaRelativeKatoNaturalityR0170.HasValue K W P g v)
    (hw : ArithmeticThetaMarkedKatoValuesR0159.HasValue K X p (α g) w) : v = w := by
  have ht := ArithmeticThetaMarkedKatoValuesR0159.rational_value_transport.2 K K
    (RingHom.id K) (Curve K W) X f α hα P p
    (by simpa only [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ from rfl,Spec.map_id,
      Category.id_comp] using hp) g v (relative_value_stalk W P g v hv)
  exact ArithmeticThetaMarkedKatoValuesR0159.rational_value_transport.1 K X p (α g) v w ht hw


open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150

/-- The intrinsic global Kato value has the literal unary value once its
specified point is transported by the constructed target test. All normalized
functions are supplied by the existing existence and uniqueness theorems. -/
lemma unary_value (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    [SmoothOfRelativeDimension 1 (genericStructure k M)]
    (d m N : ℕ) (hd : 0 < d) (hm : 0 < m) (hem : Even m)
    (hN : 0 < N) (heN : Even N) (hmN : m ∣ N) (hrEq : r = 24*d*m^2)
    (W : WeierstrassCurve (LaurentSeries k)) [W.IsElliptic]
    [IsIntegral (Curve (LaurentSeries k) W)] [IsLocallyNoetherian (Curve (LaurentSeries k) W)]
    [IsIntegral (GenericCurve (LaurentSeries k) W)] [IsLocallyNoetherian (GenericCurve (LaurentSeries k) W)]
    (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) W)
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) W H)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) W)
    (hE : E.hom ≫ structureMap (LaurentSeries k) W = genericStructure k M)
    (hO : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) W)
    {S : Type} [CommRing S] (F : EllipticFamily S)
    (C : ArithmeticThetaOpenHodgeR0180.Test S F (LaurentSeries k) W H)
    (P : Base S ⟶ F.curve) (v : S) (hv : IsKatoValue F (1+12*N) P v)
    (ν : ℤ) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ))
    (j : Fin r) (hj : j.val = d*ArithmeticThetaUnaryProduct.unaryA m ν)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M j (-1) p)
    (hpoint : genericPoint k M p hp.1 ≫ E.hom ≫ C.map = baseMap S (LaurentSeries k) C.scalar ≫ P) :
    C.scalar v = ArithmeticThetaUnaryKatoPowerR0160.unary k d m ν ^ ((1+12*N)^2-1) /
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ (((1+12*N)^2-1)/48) := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have hc : 1 < 1+12*N := by omega
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    rw [show 12*N = (2*N)*6 by omega]
    exact (Nat.coprime_add_mul_right_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  obtain ⟨g,hg⟩ := GlobalFamilyDiscriminantR0180.normalized_exists (LaurentSeries k) W H hH
    (1+12*N) hc hc6
  obtain ⟨α,hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap E.hom
  have hgm := OpenDiscriminantFullTateExpansionR0182.normalized_kato_to_model k M s hs.1 W H hH G E hE hO
    (CubicComparison.model_nsmul_of_origin k h3 he M hM s hs G hG W H hH E hE hO)
    α hα (1+12*N) (by omega) g hg
  obtain ⟨gu,hgu,-⟩ := ArithmeticThetaUnaryKatoPowerR0160.actual_unary_power_values
    k r hr h3 he T M hM s hs G hG d m N hd hm hem hN heN hmN hrEq
  obtain ⟨g₀,-,huniq⟩ := ArithmeticThetaKatoExistenceR0151.actual_kato_function_existence
    k r hr h3 T he M hM s hs G hG (1+12*N) hc hc6
  have hfunc : α g = gu := (huniq _ hgm).trans (huniq _ hgu.1).symm
  obtain ⟨j',p',hp',hj',hvalue⟩ := hgu.2 ν hν
  have hjj : j' = j := Fin.ext (hj'.trans hj.symm)
  subst j'
  have hpp : p' = p :=
    ArithmeticThetaMarkedGroupLawR0146.ActualRotationTranslation.markedLift_unique
      k M j (-1) p' p hp' hp
  subst p'
  have hvRel := hv.2 (LaurentSeries k) W H hH C (genericPoint k M p hp.1 ≫ E.hom)
    (by rw [Category.assoc,hE]; exact CategoryTheory.Limits.pullback.lift_snd _ _ _)
    (by simpa only [Category.assoc] using hpoint) g hg
  apply value_eq_model W E.hom α hα (genericPoint k M p hp.1 ≫ E.hom)
    (genericPoint k M p hp.1) rfl g (C.scalar v) _ hvRel
  rw [hfunc]
  exact hvalue

end TargetTest


namespace TargetDiscriminant
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 OpenDiscriminantFullTateExpansionR0182

/-- The intrinsic target discriminant has its complete literal Tate expansion
through any actual target test, without a full-level target marking. -/
lemma exact (k : Type) [Field k] [CharZero k] (r : ℕ) (h3 : 3 ≤ r) (he : Even r)
    {S : Type} [CommRing S] (F : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S)
    (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) H)
    (C : ArithmeticThetaOpenHodgeR0180.Test S F (LaurentSeries k) (TateCurve k r) H)
    (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ)
    (d : Γ(power F 24,⊤)) (hd : IsD2 F d) :
    pullSection C 24 d = scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) •
      tensorPowerSection (Puncture k) (Hodge (LaurentSeries k) (TateCurve k r)) 24 ⊤
        (hodgeGenerator k r δ) := by
  letI := TateFullLevelMarking.elliptic k r h3 he
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have geom := relative_curve_geometry (LaurentSeries k) (TateCurve k r)
  letI := geom.1
  letI := geom.2.1
  letI := geom.2.2.2.1
  letI := geom.2.2.2.2.1
  letI := geom.2.2.2.2.2.1
  have hpos : 0 < r := by omega
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k r h3 hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k r hpos h3 T M hM (zeroIndex r hpos) 1
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hpos h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hpos h3 T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hpos h3 T he M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k r hpos h3 T he M hM s hs X Y hX hY a ha c hc
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3 M hM s hs
  letI : IsLocallyNoetherian (genericScheme k M) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  have hEs : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M := hE.1
  have hOs : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k r) := hE.2.2
  let G : ArithmeticThetaMarkedGroupLawR0146.Law k M := ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport E hEs H
  have hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G := by
    constructor
    · intro S t
      apply Subtype.ext
      change (H.one t).val ≫ E.inv = t ≫ genericPoint k M s hs.1
      rw [hH.1]
      change (t ≫ origin (LaurentSeries k) (TateCurve k r)) ≫ E.inv = _
      rw [← hOs]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro S t x y
      change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E hEs t).symm
        (H.mul t _ _) =
        (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E hEs t).symm
        (H.mul t _ _)
      rw [hH.2]
  obtain ⟨α,hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap E.hom
  obtain ⟨g,hg⟩ := GlobalFamilyDiscriminantR0180.normalized_exists
    (LaurentSeries k) (TateCurve k r) H hH 5 (by norm_num) (by norm_num)
  have hgm := normalized_kato_to_model k M s hs.1 (TateCurve k r)
    H hH G E hEs hOs
    (fun n => transported_schemeNsmul E hEs H n) α hα 5 (by norm_num) g hg
  obtain ⟨dm,hm,_,hex⟩ := ArithmeticThetaHodgeInitialR0163.geometric_discriminant_hodge
    k r hpos h3 he T M hM s hs G hG X Y hX hY (α g) hgm
  let e := pointedIso _ _ E hEs (genericPoint k M s hs.1) _ hOs
  let p := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (LaurentSeries k)))
  letI : IsIso p := by
    dsimp only [p]
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  let δm : ArithmeticThetaHodgeFourTorsionR0147.Frame k M := pulledCurveFrame _ _ E hEs δ
  have hnorm := model_pulled_frame_normalized k M s hs.1 h3 hM hs X Y a ha c hc E hE
    δ hδ
  have heq := initial_section_comparison k M s hs.1 (TateCurve k r) H hH
    E hEs hOs α hα g (pullSection C 24 d)
    (hd.2 (LaurentSeries k) (TateCurve k r) H hH C g hg) dm hm
  apply transportSection_injective p _ _ (tensorComparison p _ _ e 24)
  rw [heq]
  rw [transportSection_smul, transportSection_tensor]
  have hgen := (transport_pointGenerator _ _ E hEs (genericPoint k M s hs.1) _
    hOs δ).trans
      (pointGenerator_frame (genericStructure k M) (genericPoint k M s hs.1) δm)
  change transportSection p _ _ e (hodgeGenerator k r δ) =
    ArithmeticThetaHodgeFourTorsionR0147.hodgeSection k M s hs.1 δm 1 at hgen
  rw [hgen]
  have hscalar : p.appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
        (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) := by
    have hp : p = 𝟙 _ := by
      dsimp only [p]
      simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [hp]
    erw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
    rfl
  rw [hscalar]
  exact (hex δm hnorm).2

end TargetDiscriminant


namespace PeriodDifferential
open CategoryTheory.Limits ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaKatoAnnularR0152

/-- The algebraized period map is identity on the actual completed chart,
not just on its marked constant points. -/
lemma completed_chart (k : Type) [Field k] [CharZero k]
    {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s) (h3r : 3 ≤ r)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    (i : Fin s) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M i χ)
    (ψ : chartScheme k ⟶ N.X) (hψ : IsChartMap k N (PeriodCollapse.index hr i) ψ) :
    χ ≫ PeriodCollapse.map k hdiv M hM N hN = ψ := by
  apply (completed_model_chart_maps k r hr h3r U N hN (PeriodCollapse.index hr i)).unique
  · constructor
    · rw [Category.assoc,PeriodCollapse.map_over,hχ.1]
    · intro n
      rw [← Category.assoc,hχ.2 n,Category.assoc,PeriodCollapse.map_stage,
        ← Category.assoc,PeriodCollapse.chart_stage]
  · exact hψ

/-- The field expansions commute with period-collapse through the actual
geometric function-field map. This provides the common Taylor parameter for
the differential comparison. -/
lemma completed_field (k : Type) [Field k] [CharZero k]
    {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s) (h3r : 3 ≤ r)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme k N)]
    (i : Fin s) (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M i χ)
    (ψ : chartScheme k ⟶ N.X) (hψ : IsChartMap k N (PeriodCollapse.index hr i) ψ)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (η : (genericScheme k N).functionField →+* ChartField k) (hη : IsChartFieldMap k N ψ η)
    (α : (genericScheme k N).functionField →+* (genericScheme k M).functionField)
    (hα : IsFieldMap (PeriodCollapse.generic k hdiv M hM N hN) α) :
    φ.comp α = η := by
  apply CompletedChartFieldMaps.fieldMap_unique k N ψ η _ hη
  change Spec.map (CommRingCat.ofHom (φ.comp α)) ≫
      (genericScheme k N).fromSpecStalk (_root_.genericPoint (genericScheme k N)) ≫
      genericInclusion k N = Spec.map (CommRingCat.ofHom (chartToField k)) ≫ ψ
  rw [show CommRingCat.ofHom (φ.comp α) = CommRingCat.ofHom α ≫ CommRingCat.ofHom φ from rfl,
    Spec.map_comp,Category.assoc,← Category.assoc (Spec.map (CommRingCat.ofHom α)),← hα]
  rw [Category.assoc,
    show PeriodCollapse.generic k hdiv M hM N hN ≫ genericInclusion k N =
      genericInclusion k M ≫ PeriodCollapse.map k hdiv M hM N hN from
        CategoryTheory.Limits.pullback.lift_fst _ _ _]
  rw [← Category.assoc,← Category.assoc,Category.assoc (Spec.map (CommRingCat.ofHom φ)),hφ,Category.assoc,
    completed_chart k hdiv h3r M hM N hN i χ hχ ψ hψ]


/-- The stalk map and rational-function map commute through their actual
geometric squares. -/
lemma stalk_field {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (α : Y.functionField →+* X.functionField) (hα : IsFieldMap f α)
    (x : X) (y : Y) (τ : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hτ : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom τ) ≫ Y.fromSpecStalk y) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp τ =
      α.comp (algebraMap (Y.presheaf.stalk y) Y.functionField) := by
  have incl (Z : Scheme) [IsIntegral Z] (z : Z) :
      Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk z) Z.functionField)) ≫
        Z.fromSpecStalk z = Z.fromSpecStalk (_root_.genericPoint Z) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk y)).mp
  change Spec.map (CommRingCat.ofHom τ ≫ CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField) ≫
      CommRingCat.ofHom α) ≫ _
  simp only [Spec.map_comp,Category.assoc]
  rw [← hτ,← Category.assoc,incl,incl]
  exact hα

open ArithmeticThetaOriginInitialR0161 ArithmeticThetaConormalInitialR0162
open ArithmeticThetaIdentitySectionsR0138

/-- The entire actual origin Taylor expansion commutes with period-collapse.
Both input Taylor maps are constrained by their geometric chart definitions. -/
lemma origin_taylor (k : Type) [Field k] [CharZero k]
    {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s) (h3r : 3 ≤ r)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme k N)]
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex s hs) 1 p)
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (εM : OriginStalk k M p hp.1 →+* LaurentSeries k)
    (κM : OriginStalk k M p hp.1 →+* PowerSeries (LaurentSeries k))
    (hκM : ActualTaylor k M p hp.1 εM κM)
    (εN : OriginStalk k N q hq.1 →+* LaurentSeries k)
    (κN : OriginStalk k N q hq.1 →+* PowerSeries (LaurentSeries k))
    (hκN : ActualTaylor k N q hq.1 εN κN)
    (α : (genericScheme k N).functionField →+* (genericScheme k M).functionField)
    (hα : IsFieldMap (PeriodCollapse.generic k hdiv M hM N hN) α)
    (τ : OriginStalk k N q hq.1 →+* OriginStalk k M p hp.1)
    (hτ : (genericScheme k M).fromSpecStalk (Origin k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k))) ≫
      PeriodCollapse.generic k hdiv M hM N hN = Spec.map (CommRingCat.ofHom τ) ≫
      (genericScheme k N).fromSpecStalk (Origin k N q hq.1 (IsLocalRing.closedPoint (LaurentSeries k)))) :
    κM.comp τ = κN := by
  obtain ⟨-,χ,φ,σ,Ψ,hχ,hφ,hσ,hΨ,hκ⟩ := hκM
  obtain ⟨-,ψ,η,σ',Ψ',hψ,hη,hσ',hΨ',hκ'⟩ := hκN
  have hσσ : σ' = σ := (completed_chart_taylor k).unique hσ' hσ
  subst σ'
  have hΨΨ : Ψ' = Ψ := (faithful_taylor_field k σ hσ).2.unique hΨ' hΨ
  subst Ψ'
  have hfield := completed_field k hdiv h3r M hM N hN (zeroIndex s hs)
    (χ _) (hχ _) (ψ (zeroIndex r hr))
    (by simpa only [PeriodCollapse.index_zero] using hψ (zeroIndex r hr))
    (φ _) (hφ _) (η _) (hη _) α hα
  have hst := stalk_field _ α hα _ _ τ hτ
  apply RingHom.ext
  intro z
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := LaurentSeries k))
  change HahnSeries.ofPowerSeries ℤ (LaurentSeries k) (κM (τ z)) =
    HahnSeries.ofPowerSeries ℤ (LaurentSeries k) (κN z)
  rw [hκ.1,hκ'.1]
  change Ψ (φ (zeroIndex s hs) (algebraMap _ _ (τ z))) =
    Ψ (η (zeroIndex r hr) (algebraMap _ _ z))
  have hstz := RingHom.congr_fun hst z
  simp only [RingHom.comp_apply] at hstz
  rw [hstz]
  exact congrArg Ψ (RingHom.congr_fun hfield (algebraMap _ _ z))


lemma stalk_square_germ {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    ∃ τ : Y.presheaf.stalk y →+* X.presheaf.stalk x,
      (X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom τ) ≫ Y.fromSpecStalk y) ∧
      ∀ (U : Y.Opens) (hy : y ∈ U) (a : Γ(Y,U)),
        τ (Y.presheaf.germ U y hy a) =
          X.presheaf.germ (f ⁻¹ᵁ U) x (by change f x ∈ U; rw [h]; exact hy) (f.app U a) := by
  subst y
  exact ⟨(f.stalkMap x).hom,(Scheme.SpecMap_stalkMap_fromSpecStalk f).symm,
    fun U hy a => f.germ_stalkMap_apply U x hy a⟩

open ArithmeticThetaHodgeInitialR0163 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149

/-- The actual Hodge value of a differential is the coefficient of u in
its actual Taylor expansion in the specified normalized frame. -/
lemma taylor_differential (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    [IsIntegral (genericScheme k M)]
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (ε : OriginStalk k M p hp →+* LaurentSeries k)
    (κ : OriginStalk k M p hp →+* PowerSeries (LaurentSeries k))
    (hκ : ActualTaylor k M p hp ε κ)
    (δ : Frame k M) (hδ : LogarithmicTaylor k M p hp δ)
    (U : (genericScheme k M).Opens)
    (hx : Origin k M p hp (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
    (a : Γ(genericScheme k M,U)) :
    topSection (Scheme.preimage_eq_top_of_closedPoint_mem (Origin k M p hp) hx)
      (Scheme.Modules.pullbackLocalSection (Origin k M p hp) (differentialAt k M U a)) =
      hodgeSection k M p hp δ
        (PowerSeries.coeff 1 (κ ((genericScheme k M).presheaf.germ U _ hx a))) := by
  have hc := congrArg PowerSeries.constantCoeff (hδ ε κ hκ U hx a)
  rw [GeometricDiscriminantHodgeR0163.actual_constant k M p hp ε κ hκ] at hc
  simp only [map_mul,map_add,map_one,PowerSeries.constantCoeff_X,add_zero,one_mul] at hc
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_derivative] at hc
  have hc' : ε ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a)) =
      PowerSeries.coeff 1 (κ ((genericScheme k M).presheaf.germ U _ hx a)) := by simpa using hc
  rw [← hc',hκ.1]
  exact (OriginHodgeComparisonR0163.frameSections_differential
    (genericStructure k M) δ (Origin k M p hp) U hx a).symm


open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

def pointMap {K : Type} [CommRing K] {X Y : Scheme}
    (f : X ⟶ Base K) (g : Y ⟶ Base K) (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (p : Base K ⟶ X) (q : Base K ⟶ Y) (hpq : p ≫ φ = q) :
    (Scheme.Modules.pullback q).obj g.kaehler ⟶ (Scheme.Modules.pullback p).obj f.kaehler :=
  (pullbackEqIso hpq.symm g.kaehler).hom ≫
    ((Scheme.Modules.pullbackComp p φ).app g.kaehler).inv ≫
    (Scheme.Modules.pullback p).map (differentialMap g f φ (by simpa using hφ))

/-- A common actual Taylor parameter of first coefficient one forces the
canonical Hodge map to carry one normalized generator to the other. -/
lemma pointMap_of_parameter (k : Type) [Field k] [CharZero k]
    {r s : ℕ} {hr : 0 < r} {hs : 0 < s} {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (N : Model k U)
    [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme k N)]
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (q : baseScheme k ⟶ N.X) (hq : q ≫ N.p = 𝟙 _)
    (εM : OriginStalk k M p hp →+* LaurentSeries k)
    (κM : OriginStalk k M p hp →+* PowerSeries (LaurentSeries k))
    (hκM : ActualTaylor k M p hp εM κM)
    (εN : OriginStalk k N q hq →+* LaurentSeries k)
    (κN : OriginStalk k N q hq →+* PowerSeries (LaurentSeries k))
    (hκN : ActualTaylor k N q hq εN κN)
    (δM : Frame k M) (hδM : LogarithmicTaylor k M p hp δM)
    (δN : Frame k N) (hδN : LogarithmicTaylor k N q hq δN)
    (φ : genericScheme k M ⟶ genericScheme k N)
    (hφ : φ ≫ genericStructure k N = genericStructure k M)
    (hpq : Origin k M p hp ≫ φ = Origin k N q hq)
    (τ : OriginStalk k N q hq →+* OriginStalk k M p hp)
    (hτ : ∀ (V : (genericScheme k N).Opens)
      (hx : Origin k N q hq (IsLocalRing.closedPoint (LaurentSeries k)) ∈ V)
      (a : Γ(genericScheme k N,V)),
      τ ((genericScheme k N).presheaf.germ V _ hx a) =
        (genericScheme k M).presheaf.germ (φ ⁻¹ᵁ V) _
          (by change (Origin k M p hp ≫ φ) _ ∈ V; rw [hpq]; exact hx) (φ.app V a))
    (ht : κM.comp τ = κN)
    (π : OriginStalk k N q hq) (hπ : PowerSeries.coeff 1 (κN π) = 1) :
    (pointMap (genericStructure k M) (genericStructure k N) φ hφ
      (Origin k M p hp) (Origin k N q hq) hpq).app ⊤
      (hodgeSection k N q hq δN 1) = hodgeSection k M p hp δM 1 := by
  obtain ⟨V,hx,a,rfl⟩ := (genericScheme k N).presheaf.exists_germ_eq π
  have hy : Origin k M p hp (IsLocalRing.closedPoint (LaurentSeries k)) ∈ φ ⁻¹ᵁ V := by
    change (Origin k M p hp ≫ φ) _ ∈ V
    rw [hpq]
    exact hx
  have hcoeff : PowerSeries.coeff 1
      (κM ((genericScheme k M).presheaf.germ (φ ⁻¹ᵁ V) _ hy (φ.app V a))) = 1 := by
    rw [← hτ V hx a]
    exact (congrArg (PowerSeries.coeff 1) (RingHom.congr_fun ht _)).trans hπ
  have hN := taylor_differential k N q hq εN κN hκN δN hδN V hx a
  have hM := taylor_differential k M p hp εM κM hκM δM hδM (φ ⁻¹ᵁ V) hy (φ.app V a)
  rw [hπ] at hN
  rw [hcoeff] at hM
  rw [← hN,← hM,topSection_map]
  exact ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
    (genericStructure k N) (genericStructure k M) φ (by simpa using hφ)
    (Origin k N q hq) (Origin k M p hp) hpq.symm V a ⊤
    (le_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem (Origin k N q hq) hx).symm)
    (le_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem (Origin k M p hp) hy).symm)


/-- Period-collapse has exactly normalized Hodge factor one. All Taylor,
parameter, origin and function-field comparisons are constructed from the
actual models; no differential comparison is assumed. -/
lemma collapse_hodge (k : Type) [Field k] [CharZero k]
    {r s : ℕ} {hr : 0 < r} {hs : 0 < s} (hdiv : r ∣ s)
    (h3r : 3 ≤ r) (h3s : 3 ≤ s) (her : Even r) (hes : Even s)
    {T : Tower k s hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme k N)]
    [IsLocallyNoetherian (genericScheme k M)] [IsLocallyNoetherian (genericScheme k N)]
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex s hs) 1 p)
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M p hp.1 G)
    (H : ArithmeticThetaMarkedGroupLawR0146.Law k N)
    (hH : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k N q hq.1 H)
    (XM : Dual k M p 2) (YM : Dual k M p 3)
    (hXM : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M p XM)
    (hYM : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M p YM)
    (XN : Dual k N q 2) (YN : Dual k N q 3)
    (hXN : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false N q XN)
    (hYN : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true N q YN)
    (δM : Frame k M) (hδM : IsGlobalDifferentialFrame k M p XM YM δM)
    (δN : Frame k N) (hδN : IsGlobalDifferentialFrame k N q XN YN δN) :
    ∃ hpq : Origin k M p hp.1 ≫ PeriodCollapse.generic k hdiv M hM N hN = Origin k N q hq.1,
      (pointMap (genericStructure k M) (genericStructure k N)
        (PeriodCollapse.generic k hdiv M hM N hN) (PeriodCollapse.generic_over k hdiv M hM N hN)
        (Origin k M p hp.1) (Origin k N q hq.1) hpq).app ⊤
        (hodgeSection k N q hq.1 δN 1) = hodgeSection k M p hp.1 δM 1 := by
  have hpq : Origin k M p hp.1 ≫ PeriodCollapse.generic k hdiv M hM N hN = Origin k N q hq.1 :=
    PeriodCollapse.generic_marked k hdiv M hM N hN (zeroIndex s hs) 1 p hp q
      (by simpa only [PeriodCollapse.index_zero] using hq)
  refine ⟨hpq,?_⟩
  letI : Algebra (LaurentSeries k) (OriginStalk k M p hp.1) := (originScalar k M p hp.1).toAlgebra
  letI : Algebra (LaurentSeries k) (OriginStalk k N q hq.1) := (originScalar k N q hq.1).toAlgebra
  obtain ⟨εM,κM,hκM,-,-,-,-⟩ :=
    actual_origin_augmented_taylor k s hs h3s hes T M hM p hp G hG
  obtain ⟨εN,κN,hκN,-,hpr,hn,ht⟩ :=
    actual_origin_augmented_taylor k r hr h3r her U N hN q hq H hH
  obtain ⟨π,hπ⟩ := (taylor_graded_coefficient (LaurentSeries k)
    (OriginStalk k N q hq.1) εN hpr hn κN ht).1
  let f := PeriodCollapse.generic k hdiv M hM N hN
  letI : Surjective f := (PeriodCollapse.generic_flat_surjective k hdiv h3r h3s M hM N hN p hp q hq).2
  obtain ⟨α,hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap f
  have hpoint : f (Origin k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k))) =
      Origin k N q hq.1 (IsLocalRing.closedPoint (LaurentSeries k)) :=
    congrArg (fun e => e (IsLocalRing.closedPoint (LaurentSeries k))) hpq
  obtain ⟨τ,hτ,hτg⟩ := stalk_square_germ f _ _ hpoint
  have htay := origin_taylor k hdiv h3r M hM N hN p hp q hq
    εM.toRingHom κM.toRingHom hκM εN.toRingHom κN.toRingHom hκN α hα τ hτ
  exact pointMap_of_parameter k M N p hp.1 q hq.1
    εM.toRingHom κM.toRingHom hκM εN.toRingHom κN.toRingHom hκN
    δM (origin_logarithmic_taylor k s hs h3s hes T M hM p hp G hG XM YM hXM hYM δM hδM)
    δN (origin_logarithmic_taylor k r hr h3r her U N hN q hq H hH XN YN hXN hYN δN hδN)
    f (PeriodCollapse.generic_over k hdiv M hM N hN) hpq τ hτg htay π.val hπ


/-- Contravariant composition for the canonical pointed differential maps
on arbitrary smooth curves, retaining the given sections. -/
lemma pointMap_comp {K : Type} [CommRing K] {X Y Z : Scheme}
    (f : X ⟶ Base K) (g : Y ⟶ Base K) (h : Z ⟶ Base K)
    [SmoothOfRelativeDimension 1 h]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)
    (p : Base K ⟶ X) (q : Base K ⟶ Y) (r : Base K ⟶ Z)
    (hpq : p ≫ φ = q) (hqr : q ≫ ψ = r) :
    pointMap f h (φ ≫ ψ) (by rw [Category.assoc,hψ,hφ]) p r
      (by rw [← Category.assoc,hpq,hqr]) =
    pointMap g h ψ hψ q r hqr ≫ pointMap f g φ hφ p q hpq := by
  apply hom_ext_frames
  intro x
  obtain ⟨V,a,hx,hframe⟩ := exists_exact_differential_frame h (r x)
  refine ⟨r ⁻¹ᵁ V,Scheme.Modules.pullbackLocalSection r (relativeD h V a),hx,
    pullback_frame r h.kaehler (relativeD h V a) hframe,?_⟩
  exact ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.local_composition
    p q r φ ψ hpq hqr
    ((Scheme.Modules.pullback p).obj f.kaehler) ((Scheme.Modules.pullback q).obj g.kaehler)
    ((Scheme.Modules.pullback r).obj h.kaehler)
    (fun V a => Scheme.Modules.pullbackLocalSection p (relativeD f V a))
    (fun V a => Scheme.Modules.pullbackLocalSection q (relativeD g V a))
    (fun V a => Scheme.Modules.pullbackLocalSection r (relativeD h V a))
    (pointMap f g φ hφ p q hpq) (pointMap g h ψ hψ q r hqr) _
    (ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
      g f φ (by simpa using hφ) q p hpq.symm)
    (ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
      h g ψ (by simpa using hψ) r q hqr.symm)
    (ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
      h f (φ ≫ ψ) (by simp only [Category.assoc,hψ,hφ,Algebra.algebraMap_self,
        CommRingCat.ofHom_id,Spec.map_id,Category.comp_id]) r p
      (by rw [← Category.assoc,hpq,hqr])) V a


/-- Evaluation at the specified point commutes with the actual pullback of
local functions. -/
lemma evaluated_pull {K : Type} [Field K] {X Y : Scheme}
    (φ : X ⟶ Y) (p : Base K ⟶ X) (q : Base K ⟶ Y) (hpq : p ≫ φ = q)
    (V : Y.Opens) (hx : q (IsLocalRing.closedPoint K) ∈ V) (a : Γ(Y,V)) :
    Scheme.stalkClosedPointTo p
      (X.presheaf.germ (φ ⁻¹ᵁ V) _
        (by change (p ≫ φ) _ ∈ V; rw [hpq]; exact hx) (φ.app V a)) =
    Scheme.stalkClosedPointTo q (Y.presheaf.germ V _ hx a) := by
  subst q
  rw [Scheme.stalkClosedPointTo_comp]
  change _ = Scheme.stalkClosedPointTo p
    (φ.stalkMap _ (Y.presheaf.germ V _ hx a))
  exact congrArg (Scheme.stalkClosedPointTo p)
    (φ.germ_stalkMap_apply V (p (IsLocalRing.closedPoint K)) hx a).symm

/-- A natural-number differential weight gives the identical weight on the
actual Hodge fiber, tested on an actual local parameter. -/
lemma pointMap_natWeight (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (δ : Frame k M) (n : ℕ)
    (φ : genericScheme k M ⟶ genericScheme k M)
    (hw : DifferentialWeight k M δ φ (n : LaurentSeries k))
    (hpoint : Origin k M p hp ≫ φ = Origin k M p hp)
    (V : (genericScheme k M).Opens)
    (hx : Origin k M p hp (IsLocalRing.closedPoint (LaurentSeries k)) ∈ V)
    (a : Γ(genericScheme k M,V))
    (ha : Scheme.stalkClosedPointTo (Origin k M p hp)
      ((genericScheme k M).presheaf.germ V _ hx (frameDerivative k M δ V a)) = 1) :
    (pointMap (genericStructure k M) (genericStructure k M) φ hw.1
      (Origin k M p hp) (Origin k M p hp) hpoint).app ⊤
      (hodgeSection k M p hp δ 1) = hodgeSection k M p hp δ n := by
  have hy : Origin k M p hp (IsLocalRing.closedPoint (LaurentSeries k)) ∈ φ ⁻¹ᵁ V := by
    change (Origin k M p hp ≫ φ) _ ∈ V
    rw [hpoint]
    exact hx
  have hb : Scheme.stalkClosedPointTo (Origin k M p hp)
      ((genericScheme k M).presheaf.germ (φ ⁻¹ᵁ V) _ hy
        (frameDerivative k M δ (φ ⁻¹ᵁ V) (φ.app V a))) = n := by
    rw [hw.2 V a]
    simp only [scalarAt,map_mul,map_natCast]
    rw [evaluated_pull φ (Origin k M p hp) (Origin k M p hp) hpoint V hx,ha,mul_one]
  have hA := (OriginHodgeComparisonR0163.frameSections_differential
    (genericStructure k M) δ (Origin k M p hp) V hx a).symm
  have hB := (OriginHodgeComparisonR0163.frameSections_differential
    (genericStructure k M) δ (Origin k M p hp) (φ ⁻¹ᵁ V) hy (φ.app V a)).symm
  change _ = hodgeSection k M p hp δ _ at hA hB
  erw [ha] at hA
  erw [hb] at hB
  rw [← hA,← hB,topSection_map]
  exact ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
    (genericStructure k M) (genericStructure k M) φ (by simpa using hw.1)
    (Origin k M p hp) (Origin k M p hp) hpoint.symm V a ⊤
    (le_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem (Origin k M p hp) hx).symm)
    (le_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem (Origin k M p hp) hy).symm)

/-- The actual Taylor uniformizer supplies a local function whose differential
has normalized value one. -/
lemma exists_normalized_parameter (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (h3 : 3 ≤ r) (he : Even r) (hM : IsModel k T M)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex r hr) 1 p)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M p hp.1 G)
    (X : Dual k M p 2) (Y : Dual k M p 3)
    (hX : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M p X)
    (hY : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M p Y)
    (δ : Frame k M) (hδ : IsGlobalDifferentialFrame k M p X Y δ) :
    ∃ (V : (genericScheme k M).Opens)
      (hx : Origin k M p hp.1 (IsLocalRing.closedPoint (LaurentSeries k)) ∈ V)
      (a : Γ(genericScheme k M,V)),
      Scheme.stalkClosedPointTo (Origin k M p hp.1)
        ((genericScheme k M).presheaf.germ V _ hx (frameDerivative k M δ V a)) = 1 := by
  letI : Algebra (LaurentSeries k) (OriginStalk k M p hp.1) := (originScalar k M p hp.1).toAlgebra
  obtain ⟨ε,κ,hκ,-,hpr,hn,ht⟩ := actual_origin_augmented_taylor k r hr h3 he T M hM p hp G hG
  obtain ⟨π,hπ⟩ := (taylor_graded_coefficient (LaurentSeries k)
    (OriginStalk k M p hp.1) ε hpr hn κ ht).1
  obtain ⟨V,hx,a,ha⟩ := (genericScheme k M).presheaf.exists_germ_eq π.val
  refine ⟨V,hx,a,?_⟩
  have hc := congrArg PowerSeries.constantCoeff
    (origin_logarithmic_taylor k r hr h3 he T M hM p hp G hG X Y hX hY δ hδ
      ε.toRingHom κ.toRingHom hκ V hx a)
  rw [GeometricDiscriminantHodgeR0163.actual_constant k M p hp.1 ε.toRingHom κ.toRingHom hκ] at hc
  simp only [map_mul,map_add,map_one,PowerSeries.constantCoeff_X,add_zero,one_mul] at hc
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_derivative] at hc
  have hc' : ε.toRingHom ((genericScheme k M).presheaf.germ V _ hx (frameDerivative k M δ V a)) =
      PowerSeries.coeff 1 (κ.toRingHom ((genericScheme k M).presheaf.germ V _ hx a)) := by
    simpa using hc
  rw [ha] at hc'
  have hcoeff := hc'.trans hπ
  rw [hκ.1] at hcoeff
  exact hcoeff

lemma multiplication_origin (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (p : baseScheme k ⟶ M.X) (hp : p ≫ M.p = 𝟙 _)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M p hp G) (n : ℕ) :
    Origin k M p hp ≫ multiplication k M G n = Origin k M p hp := by
  have h := PeriodCollapse.comp_nsmul k M G (𝟙 _) (G.one (𝟙 _)) n
  rw [G.nsmul_unit,hG.1] at h
  simpa only [ArithmeticThetaMarkedGroupLawR0146.pointOver,Category.id_comp,
    multiplication,universalPoint,WeierstrassProjModel.RelativeGroupLaw.schemeNsmul] using h

/-- Multiplication has its exact integer Hodge weight in the normalized frame. -/
lemma multiplication_hodge (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (h3 : 3 ≤ r) (he : Even r) (hM : IsModel k T M)
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex r hr) 1 p)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M p hp.1 G)
    (X : Dual k M p 2) (Y : Dual k M p 3)
    (hX : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M p X)
    (hY : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M p Y)
    (δ : Frame k M) (hδ : IsGlobalDifferentialFrame k M p X Y δ) (n : ℕ) :
    (pointMap (genericStructure k M) (genericStructure k M) (multiplication k M G n)
      (G.schemeNsmul_over n) (Origin k M p hp.1) (Origin k M p hp.1)
      (multiplication_origin k M p hp.1 G hG n)).app ⊤
      (hodgeSection k M p hp.1 δ 1) = hodgeSection k M p hp.1 δ n := by
  obtain ⟨V,hx,a,ha⟩ := exists_normalized_parameter k M h3 he hM p hp G hG X Y hX hY δ hδ
  exact pointMap_natWeight k M p hp.1 δ n (multiplication k M G n)
    (multiplication_differential k r hr h3 T he M hM p hp X Y hX hY G hG δ hδ n)
    (multiplication_origin k M p hp.1 G hG n) V hx a ha

/-- The dual of period-collapse has exactly Hodge factor m. The proof uses the
actual composite with collapse, whose Hodge factor is one, and multiplication. -/
lemma dual_hodge (k : Type) [Field k] [CharZero k]
    {r m : ℕ} {hr : 0 < r} {hs : 0 < r*m}
    (h3r : 3 ≤ r) (h3s : 3 ≤ r*m) (her : Even r) (hes : Even (r*m))
    {T : Tower k (r*m) hs} {U : Tower k r hr}
    (M : Model k T) (hM : IsModel k T M) (N : Model k U) (hN : IsModel k U N)
    [IsIntegral (genericScheme k M)] [IsIntegral (genericScheme k N)]
    [IsLocallyNoetherian (genericScheme k M)] [IsLocallyNoetherian (genericScheme k N)]
    (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M (zeroIndex (r*m) hs) 1 p)
    (q : baseScheme k ⟶ N.X) (hq : MarkedLift k N (zeroIndex r hr) 1 q)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M p hp.1 G)
    (H : ArithmeticThetaMarkedGroupLawR0146.Law k N)
    (hH : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k N q hq.1 H)
    (XM : Dual k M p 2) (YM : Dual k M p 3)
    (hXM : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M p XM)
    (hYM : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M p YM)
    (XN : Dual k N q 2) (YN : Dual k N q 3)
    (hXN : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false N q XN)
    (hYN : ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true N q YN)
    (δM : Frame k M) (hδM : IsGlobalDifferentialFrame k M p XM YM δM)
    (δN : Frame k N) (hδN : IsGlobalDifferentialFrame k N q XN YN δN)
    (d : genericScheme k N ⟶ genericScheme k M)
    (hd : d ≫ genericStructure k M = genericStructure k N)
    (hdo : Origin k N q hq.1 ≫ d = Origin k M p hp.1)
    (hc : d ≫ PeriodCollapse.generic k (dvd_mul_right r m) M hM N hN = H.schemeNsmul m) :
    (pointMap (genericStructure k N) (genericStructure k M) d hd
      (Origin k N q hq.1) (Origin k M p hp.1) hdo).app ⊤
      (hodgeSection k M p hp.1 δM 1) = hodgeSection k N q hq.1 δN m := by
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_relative_one k h3r N hN q hq
  obtain ⟨hfo,hf⟩ := collapse_hodge k (dvd_mul_right r m) h3r h3s her hes
    M hM N hN p hp q hq G hG H hH XM YM hXM hYM XN YN hXN hYN δM hδM δN hδN
  let f := PeriodCollapse.generic k (dvd_mul_right r m) M hM N hN
  have hfOver := PeriodCollapse.generic_over k (dvd_mul_right r m) M hM N hN
  have hcomp := pointMap_comp (genericStructure k N) (genericStructure k M)
    (genericStructure k N) d hd f hfOver
    (Origin k N q hq.1) (Origin k M p hp.1) (Origin k N q hq.1) hdo hfo
  have hc' : d ≫ f = multiplication k N H m := hc
  have hpoint : Origin k N q hq.1 ≫ (d ≫ f) = Origin k N q hq.1 :=
    (by rw [← Category.assoc,hdo,hfo])
  have heq : pointMap (genericStructure k N) (genericStructure k N) (d ≫ f)
      (by rw [Category.assoc,hfOver,hd]) (Origin k N q hq.1) (Origin k N q hq.1) hpoint =
      pointMap (genericStructure k N) (genericStructure k N) (multiplication k N H m)
        (H.schemeNsmul_over m) (Origin k N q hq.1) (Origin k N q hq.1)
        (multiplication_origin k N q hq.1 H hH m) := by
    congr 1
  have heval := congrArg (fun e => e.app ⊤ (hodgeSection k N q hq.1 δN 1))
    (hcomp.symm.trans heq)
  change (pointMap _ _ d hd _ _ hdo).app ⊤
    ((pointMap _ _ f hfOver _ _ hfo).app ⊤ (hodgeSection k N q hq.1 δN 1)) = _ at heval
  rw [hf] at heval
  exact heval.trans (multiplication_hodge k N h3r her hN q hq H hH XN YN hXN hYN δN hδN m)

open OpenDiscriminantFullTateExpansionR0182

/-- The same canonical point map transports the normalized frame through an
actual pointed curve isomorphism. -/
lemma pointMap_pulled_generator {K : Type} [Field K] {X Y : Scheme}
    (f : Y ⟶ Base K) (g : X ⟶ Base K) (E : X ≅ Y) (hE : E.hom ≫ f = g)
    [SmoothOfRelativeDimension 1 f]
    (p : Base K ⟶ X) (q : Base K ⟶ Y) (hpq : p ≫ E.hom = q)
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    (pointMap g f E.hom hE p q hpq).app ⊤ (pointGenerator f q δ) =
      pointGenerator g p (pulledCurveFrame f g E hE δ) := by
  have h := ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_section
    E.hom q p hpq.symm f.kaehler g.kaehler
    (differentialMap f g E.hom (by simpa using hE)) ⊤
    (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))) ⊤ (by simp) (by simp)
  rw [← pulledCurveFrame_one f g E hE δ ⊤] at h
  simpa [pointMap,pointGenerator,InitialHodgeSection.res_self] using h

/-- Naturality for a commutative square of actual pointed maps over a fixed
base, expressed entirely using their canonical Hodge maps. -/
lemma pointMap_square {K : Type} [CommRing K] {X Y X' Y' : Scheme}
    (f : X ⟶ Base K) (g : Y ⟶ Base K)
    (f' : X' ⟶ Base K) (g' : Y' ⟶ Base K) [SmoothOfRelativeDimension 1 g]
    (a : X' ⟶ X) (ha : a ≫ f = f') (b : Y' ⟶ Y) (hb : b ≫ g = g')
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : X' ⟶ Y') (hψ : ψ ≫ g' = f')
    (p : Base K ⟶ X) (q : Base K ⟶ Y)
    (p' : Base K ⟶ X') (q' : Base K ⟶ Y')
    (hpa : p' ≫ a = p) (hqb : q' ≫ b = q)
    (hpq : p ≫ φ = q) (hpq' : p' ≫ ψ = q') (hsq : a ≫ φ = ψ ≫ b) :
    pointMap f g φ hφ p q hpq ≫ pointMap f' f a ha p' p hpa =
      pointMap g' g b hb q' q hqb ≫ pointMap f' g' ψ hψ p' q' hpq' := by
  rw [← pointMap_comp f' f g a ha φ hφ p' p q hpa hpq,
    ← pointMap_comp f' g' g ψ hψ b hb p' q' q hpq' hqb]
  congr 1

lemma topSection_res {X : Scheme} (M : X.Modules) {U V : X.Opens}
    (h : U ≤ V) (hU : U = ⊤) (hV : V = ⊤) (s : Γ(M,V)) :
    topSection hU (res M h s) = topSection hV s := by
  subst U
  subst V
  rw [InitialHodgeSection.res_self]

lemma top_pullback_res {X Y : Scheme} (b : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : U ≤ V) (hU : b ⁻¹ᵁ U = ⊤) (hV : b ⁻¹ᵁ V = ⊤)
    (s : Γ(M,V)) :
    topSection hU (Scheme.Modules.pullbackLocalSection b (res M h s)) =
      topSection hV (Scheme.Modules.pullbackLocalSection b s) := by
  rw [← InitialSectionNaturality.pullback_res]
  exact topSection_res _ _ hU hV _

/-- A local differential followed through a global pointed map and its actual
Cartesian test is the differential of the actual composite on the test. -/
lemma pointMap_baseChange_D {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    {X Y X' : Scheme} (f : X ⟶ Base A) (g : Y ⟶ Base A)
    (f' : X' ⟶ Base B) [SmoothOfRelativeDimension 1 f]
    (a : X' ⟶ X)
    (ha : IsPullback a f' f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (p : Base A ⟶ X) (q : Base A ⟶ Y) (p' : Base B ⟶ X')
    (hpa : p' ≫ a = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ p)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (hpq : p ≫ φ = q)
    (U : Y.Opens) (z : Γ(Y,U))
    (hU : (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ (q ⁻¹ᵁ U) = ⊤)
    (hU' : p' ⁻¹ᵁ (a ⁻¹ᵁ (φ ⁻¹ᵁ U)) = ⊤) :
    (pointedDifferentialIso f f' a ha p p' hpa).hom.app ⊤
      (topSection hU (Scheme.Modules.pullbackLocalSection
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        ((pointMap f g φ hφ p q hpq).app (q ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection q (relativeD g U z))))) =
      topSection hU' (Scheme.Modules.pullbackLocalSection p'
        (relativeD f' (a ⁻¹ᵁ (φ ⁻¹ᵁ U)) (a.app (φ ⁻¹ᵁ U) (φ.app U z)))) := by
  have hpre : p ⁻¹ᵁ (φ ⁻¹ᵁ U) = q ⁻¹ᵁ U := by
    change (p ≫ φ) ⁻¹ᵁ U = q ⁻¹ᵁ U
    rw [hpq]
  have hU0 : (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
      (p ⁻¹ᵁ (φ ⁻¹ᵁ U)) = ⊤ := by rw [hpre]; exact hU
  have hd := ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
    g f φ (by simpa using hφ) q p hpq.symm U z (q ⁻¹ᵁ U) le_rfl (le_of_eq hpre.symm)
  have hd' : (pointMap f g φ hφ p q hpq).app (q ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection q (relativeD g U z)) =
      res ((Scheme.Modules.pullback p).obj f.kaehler) (le_of_eq hpre.symm)
        (Scheme.Modules.pullbackLocalSection p (relativeD f (φ ⁻¹ᵁ U) (φ.app U z))) := by
    simpa only [pointMap,InitialHodgeSection.res_self] using hd
  rw [hd',top_pullback_res _ _ _ hU hU0,topSection_map]
  exact pointedDifferentialIso_D f f' a ha p p' hpa (φ ⁻¹ᵁ U) (φ.app U z) ⊤
    (le_of_eq hU0.symm) (le_of_eq hU'.symm)

lemma pointMap_isIso {K : Type} [CommRing K] {X Y : Scheme}
    (f : X ⟶ Base K) (g : Y ⟶ Base K) [SmoothOfRelativeDimension 1 g]
    (φ : X ⟶ Y) [IsIso φ] (hφ : φ ≫ g = f)
    (p : Base K ⟶ X) (q : Base K ⟶ Y) (hpq : p ≫ φ = q) :
    IsIso (pointMap f g φ hφ p q hpq) := by
  letI := ArithmeticThetaRelativeIsogenyHodgeR0172.EtaleHodgePullbackIsomorphismR0172.differentialMap_isIso_etale
    g f φ (by simpa using hφ)
  unfold pointMap
  infer_instance

/-- An exact Hodge weight transfers through actual pointed isomorphisms on
both curves. The equality of the scheme maps is retained as a hypothesis. -/
lemma transfer_weight {K : Type} [CommRing K] {X Y X' Y' : Scheme}
    (f : X ⟶ Base K) (g : Y ⟶ Base K)
    (f' : X' ⟶ Base K) (g' : Y' ⟶ Base K)
    [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 g]
    (a : X' ≅ X) (ha : a.hom ≫ f = f') (b : Y' ≅ Y) (hb : b.hom ≫ g = g')
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : X' ⟶ Y') (hψ : ψ ≫ g' = f')
    (p : Base K ⟶ X) (q : Base K ⟶ Y)
    (p' : Base K ⟶ X') (q' : Base K ⟶ Y')
    (hpa : p' ≫ a.hom = p) (hqb : q' ≫ b.hom = q)
    (hpq : p ≫ φ = q) (hpq' : p' ≫ ψ = q') (hsq : a.hom ≫ φ = ψ ≫ b.hom)
    (ω : Γ((Scheme.Modules.pullback p).obj f.kaehler,⊤))
    (η : Γ((Scheme.Modules.pullback q).obj g.kaehler,⊤))
    (ω' : Γ((Scheme.Modules.pullback p').obj f'.kaehler,⊤))
    (η' : Γ((Scheme.Modules.pullback q').obj g'.kaehler,⊤))
    (hω : (pointMap f' f a.hom ha p' p hpa).app ⊤ ω = ω')
    (hη : (pointMap g' g b.hom hb q' q hqb).app ⊤ η = η')
    (c : Γ(Base K,⊤))
    (hc : (pointMap f' g' ψ hψ p' q' hpq').app ⊤ η' = c • ω') :
    (pointMap f g φ hφ p q hpq).app ⊤ η = c • ω := by
  letI := pointMap_isIso f' f a.hom ha p' p hpa
  apply (ConcreteCategory.bijective_of_isIso
    ((pointMap f' f a.hom ha p' p hpa).app ⊤)).1
  rw [Scheme.Modules.Hom.app_smul,hω]
  have hs := pointMap_square f g f' g' a.hom ha b.hom hb φ hφ ψ hψ p q p' q'
    hpa hqb hpq hpq' hsq
  have he := congrArg (fun e => e.app ⊤ η) hs
  change (pointMap f' f a.hom ha p' p hpa).app ⊤
    ((pointMap f g φ hφ p q hpq).app ⊤ η) =
    (pointMap f' g' ψ hψ p' q' hpq').app ⊤
      ((pointMap g' g b.hom hb q' q hqb).app ⊤ η) at he
  rw [hη] at he
  exact he.trans hc

lemma top_differential_congr {K : Type} [CommRing K] {X Y : Scheme}
    (f : X ⟶ Base K) (p : Base K ⟶ X) (a b : X ⟶ Y) (hab : a = b)
    (U : Y.Opens) (z : Γ(Y,U)) (ha : p ⁻¹ᵁ (a ⁻¹ᵁ U) = ⊤)
    (hb : p ⁻¹ᵁ (b ⁻¹ᵁ U) = ⊤) :
    topSection ha (Scheme.Modules.pullbackLocalSection p (relativeD f (a ⁻¹ᵁ U) (a.app U z))) =
      topSection hb (Scheme.Modules.pullbackLocalSection p (relativeD f (b ⁻¹ᵁ U) (b.app U z))) := by
  subst b
  rfl

/-- On an actual local differential, Cartesian Hodge comparisons commute with
the given family morphism and its specified base change. -/
lemma pointMap_baseChange_naturality_D
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    {X Y X' Y' : Scheme} (f : X ⟶ Base A) (g : Y ⟶ Base A)
    (f' : X' ⟶ Base B) (g' : Y' ⟶ Base B)
    [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 g]
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (ha : IsPullback a f' f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hb : IsPullback b g' g (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (p : Base A ⟶ X) (q : Base A ⟶ Y) (p' : Base B ⟶ X') (q' : Base B ⟶ Y')
    (hpa : p' ≫ a = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ p)
    (hqb : q' ≫ b = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ q)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (hpq : p ≫ φ = q)
    (ψ : X' ⟶ Y') (hψ : ψ ≫ g' = f') (hpq' : p' ≫ ψ = q')
    (hsq : a ≫ φ = ψ ≫ b)
    (U : Y.Opens) (z : Γ(Y,U))
    (hU : (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ (q ⁻¹ᵁ U) = ⊤)
    (hU' : p' ⁻¹ᵁ (a ⁻¹ᵁ (φ ⁻¹ᵁ U)) = ⊤)
    (hV' : q' ⁻¹ᵁ (b ⁻¹ᵁ U) = ⊤) :
    (pointedDifferentialIso f f' a ha p p' hpa).hom.app ⊤
      (topSection hU (Scheme.Modules.pullbackLocalSection
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        ((pointMap f g φ hφ p q hpq).app (q ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection q (relativeD g U z))))) =
    (pointMap f' g' ψ hψ p' q' hpq').app ⊤
      ((pointedDifferentialIso g g' b hb q q' hqb).hom.app ⊤
        (topSection hU (Scheme.Modules.pullbackLocalSection
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (Scheme.Modules.pullbackLocalSection q (relativeD g U z))))) := by
  have hW' : p' ⁻¹ᵁ (ψ ⁻¹ᵁ (b ⁻¹ᵁ U)) = ⊤ := by
    change (p' ≫ ψ) ⁻¹ᵁ (b ⁻¹ᵁ U) = ⊤
    rw [hpq',hV']
  have ht : (pointedDifferentialIso g g' b hb q q' hqb).hom.app ⊤
      (topSection hU (Scheme.Modules.pullbackLocalSection
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Scheme.Modules.pullbackLocalSection q (relativeD g U z)))) =
      topSection hV' (Scheme.Modules.pullbackLocalSection q' (relativeD g' (b ⁻¹ᵁ U) (b.app U z))) := by
    rw [topSection_map]
    exact pointedDifferentialIso_D g g' b hb q q' hqb U z ⊤
      (le_of_eq hU.symm) (le_of_eq hV'.symm)
  rw [pointMap_baseChange_D f g f' a ha p q p' hpa φ hφ hpq U z hU hU',ht,topSection_map]
  have hd := ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.pointed_D
    g' f' ψ (by simpa using hψ) q' p' hpq'.symm (b ⁻¹ᵁ U) (b.app U z) ⊤
    (le_of_eq hV'.symm) (le_of_eq hW'.symm)
  have hcomp := top_differential_congr f' p' (a ≫ φ) (ψ ≫ b) hsq U z hU' hW'
  exact hcomp.trans hd.symm

/-- The complete canonical Hodge square over a field follows from the local
formula on a genuine differential frame, with all base maps unchanged. -/
lemma pointMap_baseChange_naturality
    {A B : Type} [CommRing A] [Field B] [Algebra A B]
    {X Y X' Y' : Scheme} (f : X ⟶ Base A) (g : Y ⟶ Base A)
    (f' : X' ⟶ Base B) (g' : Y' ⟶ Base B)
    [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 g]
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (ha : IsPullback a f' f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hb : IsPullback b g' g (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (p : Base A ⟶ X) (q : Base A ⟶ Y) (p' : Base B ⟶ X') (q' : Base B ⟶ Y')
    (hpa : p' ≫ a = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ p)
    (hqb : q' ≫ b = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ q)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (hpq : p ≫ φ = q)
    (ψ : X' ⟶ Y') (hψ : ψ ≫ g' = f') (hpq' : p' ≫ ψ = q')
    (hsq : a ≫ φ = ψ ≫ b) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        (pointMap f g φ hφ p q hpq) ≫ (pointedDifferentialIso f f' a ha p p' hpa).hom =
      (pointedDifferentialIso g g' b hb q q' hqb).hom ≫ pointMap f' g' ψ hψ p' q' hpq' := by
  let β := Spec.map (CommRingCat.ofHom (algebraMap A B))
  obtain ⟨U,z,hx,hframe⟩ := exists_exact_differential_frame g
    (q (β (IsLocalRing.closedPoint B)))
  have hU : β ⁻¹ᵁ (q ⁻¹ᵁ U) = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem (β ≫ q) hx
  have hU' : p' ⁻¹ᵁ (a ⁻¹ᵁ (φ ⁻¹ᵁ U)) = ⊤ := by
    change ((p' ≫ a) ≫ φ) ⁻¹ᵁ U = ⊤
    rw [hpa,Category.assoc,hpq]
    exact hU
  have hV' : q' ⁻¹ᵁ (b ⁻¹ᵁ U) = ⊤ := by
    change (q' ≫ b) ⁻¹ᵁ U = ⊤
    rw [hqb]
    exact hU
  apply hom_ext_frames
  intro x
  refine ⟨⊤,topSection hU (Scheme.Modules.pullbackLocalSection β
    (Scheme.Modules.pullbackLocalSection q (relativeD g U z))),by trivial,?_,?_⟩
  · exact frame_restrict _ (le_of_eq hU.symm) _
      (pullback_frame β _ _ (pullback_frame q _ _ hframe))
  · change (pointedDifferentialIso f f' a ha p p' hpa).hom.app ⊤
      (((Scheme.Modules.pullback β).map (pointMap f g φ hφ p q hpq)).app ⊤
        (topSection hU (Scheme.Modules.pullbackLocalSection β
          (Scheme.Modules.pullbackLocalSection q (relativeD g U z))))) = _
    rw [topSection_map,← Scheme.Modules.pullbackLocalSection_app]
    exact pointMap_baseChange_naturality_D f g f' g' a b ha hb p q p' q' hpa hqb
      φ hφ hpq ψ hψ hpq' hsq U z hU hU' hV'

end PeriodDifferential

namespace NormalizedSection
open ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182

/-- A local-frame identity for a global tensor section pulls to exactly the
same scalar and tensor identity through the specified comparison. -/
lemma transport_local_tensor {X Y : Scheme} (b : X ⟶ Y)
    (H : Y.Modules) (J : X.Modules) (E : (Scheme.Modules.pullback b).obj H ≅ J)
    (n : ℕ) (s : Γ(tensorPower Y H n,⊤)) (U : Y.Opens)
    (η : Γ(H,U)) (a : Γ(Y,U)) (hU : (⊤ : X.Opens) ≤ b ⁻¹ᵁ U)
    (hs : res (tensorPower Y H n) le_top s = a • tensorPowerSection Y H n U η) :
    transportSection b (tensorPower Y H n) (tensorPower X J n)
      (tensorComparison b H J E n) s =
      b.appLE U ⊤ hU a • tensorPowerSection X J n ⊤
        (res J hU (E.hom.app _ (Scheme.Modules.pullbackLocalSection b η))) := by
  have h := transportSection_restrict b (tensorPower Y H n) (tensorPower X J n)
    (tensorComparison b H J E n) s U ⊤ hU
  rw [InitialHodgeSection.res_self,hs,Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul,InitialHodgeSection.res_smul,tensorComparison_section] at h
  rw [show res (tensorPower X J n) hU
      (tensorPowerSection X J n (b ⁻¹ᵁ U) (E.hom.app _ (Scheme.Modules.pullbackLocalSection b η))) =
      tensorPowerSection X J n ⊤ (res J hU (E.hom.app _ (Scheme.Modules.pullbackLocalSection b η))) from
    tensorPowerSection_restrict X J n _ _ _ _] at h
  exact h

/-- The frame coefficient cancels without requiring it to be a chosen
normalization unit. This is the scalar identity used after actual pullback. -/
lemma exact_scalar {K : Type} [Field K] (e w : ℕ) (hw : 24*e = w)
    (μ Δ u a t : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0) (ha : a*t^24 = Δ) :
    (μ⁻¹)^w * (u/Δ^e) * a^e * (t*μ)^w = u := by
  have hat : a^e*t^w = Δ^e := by rw [← hw,pow_mul,← mul_pow,ha]
  calc
    (μ⁻¹)^w * (u/Δ^e) * a^e * (t*μ)^w =
        (u/Δ^e)*(a^e*t^w)*((μ⁻¹)^w*μ^w) := by rw [mul_pow]; ring
    _ = (u/Δ^e)*Δ^e*1 := by rw [hat,← mul_pow,inv_mul_cancel₀ hμ,one_pow]
    _ = u := by rw [mul_one,div_mul_cancel₀ _ (pow_ne_zero _ hΔ)]

/-- Every section in the actual global frame has a scalar in the given field,
using the canonical global-sections isomorphism of its spectrum. -/
lemma frame_scalar {K : Type} [Field K] (H : (Base K).Modules)
    (η s : Γ(H,⊤)) (hη : IsFrame H ⊤ η) :
    ∃ t : K, s = scalar K t • η := by
  obtain ⟨t,ht⟩ := (hη ⊤ le_rfl).2 s
  rw [InitialHodgeSection.res_self] at ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom t,?_⟩
  rw [← ht]
  apply congrArg (fun c => c • η)
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id t).symm

/-- The actual target discriminant and Hodge weight remove the coefficient
of an arbitrary pulled local frame from the same normalized source section. -/
lemma normalization_in_frame {K : Type} [Field K]
    (H J : (Base K).Modules) (g : H ⟶ J)
    (η : Γ(H,⊤)) (ω : Γ(J,⊤)) (hη : IsFrame H ⊤ η)
    (e w : ℕ) (hw : 24*e = w) (μ Δ u v a : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0)
    (hv : v = u/Δ^e) (η' : Γ(H,⊤)) (F : Γ(tensorPower (Base K) J w,⊤))
    (hweight : g.app ⊤ η = scalar K μ • ω)
    (hd : scalar K a • tensorPowerSection (Base K) H 24 ⊤ η' =
      scalar K Δ • tensorPowerSection (Base K) H 24 ⊤ η)
    (hF : F = scalar K ((μ⁻¹)^w*v*a^e) •
      tensorPowerSection (Base K) J w ⊤ (g.app ⊤ η')) :
    F = scalar K u • tensorPowerSection (Base K) J w ⊤ ω := by
  obtain ⟨t,ht⟩ := frame_scalar H η η' hη
  rw [ht,InitialHodgeSection.tensor_smul,smul_smul] at hd
  have ha' : scalar K a * (scalar K t)^24 = scalar K Δ :=
    ((tensorPower_frame H η hη 24) ⊤ le_rfl).1
      (by simpa only [InitialHodgeSection.res_self] using hd)
  have ha : a*t^24 = Δ := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
    simpa only [scalar,map_mul,map_pow] using ha'
  rw [ht,Scheme.Modules.Hom.app_smul,hweight,smul_smul,
    InitialHodgeSection.tensor_smul,smul_smul] at hF
  have hc : scalar K ((μ⁻¹)^w*v*a^e) * (scalar K t * scalar K μ)^w = scalar K u := by
    simp only [scalar,← map_mul,← map_pow]
    apply congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv
    rw [hv]
    exact exact_scalar e w hw μ Δ u a t hμ hΔ ha
  rw [hc] at hF
  exact hF

/-- The defining formula for a global normalized section is preserved by the
actual sheaf pullback. The coefficient is eliminated using the target D2 and
the canonical Hodge square; no expansion of the source section is assumed. -/
lemma normalization_after_pullback {K : Type} [Field K] {S : Scheme}
    (b : Base K ⟶ S) (H J : S.Modules) (hH : Scheme.Modules.IsInvertible H)
    (HK JK : (Base K).Modules)
    (EH : (Scheme.Modules.pullback b).obj H ≅ HK)
    (EJ : (Scheme.Modules.pullback b).obj J ≅ JK)
    (g : H ⟶ J) (gK : HK ⟶ JK)
    (hcomm : (Scheme.Modules.pullback b).map g ≫ EJ.hom = EH.hom ≫ gK)
    (e w : ℕ) (hw : 24*e = w)
    (d : Γ(tensorPower S H 24,⊤)) (F : Γ(tensorPower S J w,⊤)) (r : Γ(S,⊤))
    (hF : ∀ (U : S.Opens) (η : Γ(H,U)) (a : Γ(S,U)), IsFrame H U η →
      res (tensorPower S H 24) le_top d = a • tensorPowerSection S H 24 U η →
      res (tensorPower S J w) le_top F =
        (S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) •
          tensorPowerSection S J w U (g.app U η))
    (η₀ : Γ(HK,⊤)) (ω₀ : Γ(JK,⊤)) (hη₀ : IsFrame HK ⊤ η₀)
    (μ Δ u v : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0) (hv : v = u/Δ^e)
    (hr : b.appLE ⊤ ⊤ (by simp) r = scalar K ((μ⁻¹)^w*v))
    (hd : transportSection b (tensorPower S H 24) (tensorPower (Base K) HK 24)
      (tensorComparison b H HK EH 24) d = scalar K Δ • tensorPowerSection (Base K) HK 24 ⊤ η₀)
    (hweight : gK.app ⊤ η₀ = scalar K μ • ω₀) :
    transportSection b (tensorPower S J w) (tensorPower (Base K) JK w)
      (tensorComparison b J JK EJ w) F = scalar K u • tensorPowerSection (Base K) JK w ⊤ ω₀ := by
  obtain ⟨U,η,hx,hη⟩ := OpenLevelNormalizedHodgePowerR0180.local_frames H hH
    (b (IsLocalRing.closedPoint K))
  have hU : (⊤ : (Base K).Opens) ≤ b ⁻¹ᵁ U :=
    le_of_eq (Scheme.preimage_eq_top_of_closedPoint_mem b hx).symm
  obtain ⟨a,ha⟩ := ((tensorPower_frame H η hη 24) U le_rfl).2
    (res (tensorPower S H 24) le_top d)
  rw [InitialHodgeSection.res_self] at ha
  let α : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom (b.appLE U ⊤ hU a)
  have hα : scalar K α = b.appLE U ⊤ hU a :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id _
  let η' : Γ(HK,⊤) := res HK hU (EH.hom.app _ (Scheme.Modules.pullbackLocalSection b η))
  have hd' := transport_local_tensor b H HK EH 24 d U η a hU ha.symm
  rw [← hα] at hd'
  have hdisc : scalar K α • tensorPowerSection (Base K) HK 24 ⊤ η' =
      scalar K Δ • tensorPowerSection (Base K) HK 24 ⊤ η₀ := hd'.symm.trans hd
  have hmap : res JK hU (EJ.hom.app _ (Scheme.Modules.pullbackLocalSection b (g.app U η))) =
      gK.app ⊤ η' := by
    have hc := congrArg (fun f => f.app (b ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection b η)) hcomm
    change EJ.hom.app _ (((Scheme.Modules.pullback b).map g).app _
      (Scheme.Modules.pullbackLocalSection b η)) = gK.app _
        (EH.hom.app _ (Scheme.Modules.pullbackLocalSection b η)) at hc
    rw [← Scheme.Modules.pullbackLocalSection_app] at hc
    have ht := congrArg (res JK hU) hc
    rw [hom_res gK] at ht
    exact ht
  have hcoef : b.appLE U ⊤ hU
      (S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) =
        scalar K ((μ⁻¹)^w*v*α^e) := by
    have hrU : b.appLE U ⊤ hU (S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) =
        b.appLE ⊤ ⊤ (by simp) r :=
      ConcreteCategory.congr_hom (b.map_appLE hU (homOfLE (show U ≤ ⊤ from le_top)).op) r
    rw [map_mul,map_pow,hrU,hr,← hα]
    simp only [scalar,map_mul,map_pow]
  have hFp := transport_local_tensor b J JK EJ w F U (g.app U η)
    (S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) hU
    (hF U η a hη ha.symm)
  rw [hcoef,hmap] at hFp
  exact normalization_in_frame HK JK gK η₀ ω₀ hη₀ e w hw μ Δ u v α hμ hΔ hv η' _
    hweight hdisc hFp

lemma base_scalar {S K : Type} [CommRing S] [CommRing K] (ρ : S →+* K) (v : S) :
    (baseMap S K ρ).appLE ⊤ ⊤ (by simp) (scalar S v) = scalar K (ρ v) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)) v).symm


/-- The test pullback is the same section transport for every tensor degree. -/
lemma pullSection_transport {S K : Type} [CommRing S] [CommRing K]
    {E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S}
    {W : WeierstrassCurve K} {G : ArithmeticThetaRelativeKatoR0169.Law K W}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E K W G) (n : ℕ) (s : Γ(power E n,⊤)) :
    pullSection C n s = transportSection (baseMap S K C.scalar)
      (power E n) (HodgePower K W n)
      (tensorComparison (baseMap S K C.scalar) (hodge E) (Hodge K W) (comparison C) n) s := rfl

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
/-- The test consumer is proved for arbitrary actual elliptic families before
specialization to the full-level atlas, avoiding unfolding that atlas. -/
lemma test_formula {S : Type} [CommRing S]
    (E T : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (f : Pointed S E T)
    (K : Type) [Field K] (W Wt : WeierstrassCurve K)
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (Gt : ArithmeticThetaRelativeKatoR0169.Law K Wt)
    (ρ : S →+* K) (a : Curve K W ⟶ E.curve) (b : Curve K Wt ⟶ T.curve)
    (ha : IsPullback a (structureMap K W) E.projection (baseMap S K ρ))
    (hb : IsPullback b (structureMap K Wt) T.projection (baseMap S K ρ))
    (hao : origin K W ≫ a = baseMap S K ρ ≫ zero E)
    (hbo : origin K Wt ≫ b = baseMap S K ρ ≫ zero T)
    (han : ∀ n, G.schemeNsmul n ≫ a = a ≫ E.law.schemeNsmul n)
    (hbn : ∀ n, Gt.schemeNsmul n ≫ b = b ≫ T.law.schemeNsmul n)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) (hψmap : a ≫ f.map = ψ ≫ b)
    (e w : ℕ) (hw : 24*e = w) (d : Γ(power T 24,⊤)) (F : Γ(power E w,⊤))
    (r : Γ(Base S,⊤))
    (hF : ∀ (U : (Base S).Opens) (η : Γ(hodge T,U)) (c : Γ(Base S,U)),
      IsFrame (hodge T) U η →
      res (power T 24) le_top d = c • tensorPowerSection (Base S) (hodge T) 24 U η →
      res (power E w) le_top F =
        ((Base S).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * c^e) •
          tensorPowerSection (Base S) (hodge E) w U ((familyHodgeMap f).app U η))
    (η : Γ(Hodge K Wt,⊤)) (ω : Γ(Hodge K W,⊤)) (hη : IsFrame (Hodge K Wt) ⊤ η)
    (μ Δ u v : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0) (hv : v = u/Δ^e)
    (hr : (baseMap S K ρ).appLE ⊤ ⊤ (by simp) r = scalar K ((μ⁻¹)^w*v))
    (hd : pullSection (⟨ρ,b,hb,hbo,hbn⟩ : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt) 24 d =
      scalar K Δ • tensorPowerSection (Base K) (Hodge K Wt) 24 ⊤ η)
    (hweight : (PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
      ψ hψ (origin K W) (origin K Wt) hψo).app ⊤ η = scalar K μ • ω) :
    pullSection (⟨ρ,a,ha,hao,han⟩ : ArithmeticThetaOpenHodgeR0180.Test S E K W G) w F =
      scalar K u • tensorPowerSection (Base K) (Hodge K W) w ⊤ ω := by
  letI : Algebra S K := ρ.toAlgebra
  letI := E.smooth
  letI := T.smooth
  let Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G := ⟨ρ,a,ha,hao,han⟩
  let Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt := ⟨ρ,b,hb,hbo,hbn⟩
  let gK := PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
    ψ hψ (origin K W) (origin K Wt) hψo
  have hcomm : (Scheme.Modules.pullback (baseMap S K ρ)).map
      (familyHodgeMap f) ≫ (comparison Cs).hom = (comparison Ct).hom ≫ gK := by
    have hn := PeriodDifferential.pointMap_baseChange_naturality (A := S) (B := K) E.projection T.projection
      (structureMap K W) (structureMap K Wt) a b ha hb (zero E) (zero T)
      (origin K W) (origin K Wt) hao hbo f.map f.over_eq f.zero_eq ψ hψ hψo hψmap
    dsimp only [comparison, familyHodgeMap, PeriodDifferential.pointMap, Cs, Ct, gK] at hn ⊢
    exact hn
  have hinv := EllipticFamilyWeierstrassAtlasR0180.hodge_invertible T
  have hf0 := normalization_after_pullback (K := K) (S := Base S) (baseMap S K ρ) (hodge T) (hodge E)
    hinv
    (Hodge K Wt) (Hodge K W) (comparison Ct) (comparison Cs) (familyHodgeMap f) gK hcomm
    e w hw d F r
  have hf1 := hf0 hF η ω hη μ Δ u v hμ hΔ hv hr
  have hd' := (pullSection_transport Ct 24 d).symm.trans hd
  have hf := hf1 hd' hweight
  exact (pullSection_transport Cs w F).trans hf


set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
/-- The consumer retains the actual tests as arguments; scalar equality is
handled over arbitrary families before any concrete atlas is substituted. -/
lemma test_formula_tests {S : Type} [CommRing S]
    (E T : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (f : Pointed S E T)
    (K : Type) [Field K] (W Wt : WeierstrassCurve K)
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (Gt : ArithmeticThetaRelativeKatoR0169.Law K Wt)
    (Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G)
    (Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt)
    (hscalar : Ct.scalar = Cs.scalar)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) (hψmap : Cs.map ≫ f.map = ψ ≫ Ct.map)
    (e w : ℕ) (hw : 24*e = w) (d : Γ(power T 24,⊤)) (F : Γ(power E w,⊤))
    (r : Γ(Base S,⊤))
    (hF : ∀ (U : (Base S).Opens) (η : Γ(hodge T,U)) (c : Γ(Base S,U)),
      IsFrame (hodge T) U η →
      res (power T 24) le_top d = c • tensorPowerSection (Base S) (hodge T) 24 U η →
      res (power E w) le_top F =
        ((Base S).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * c^e) •
          tensorPowerSection (Base S) (hodge E) w U ((familyHodgeMap f).app U η))
    (η : Γ(Hodge K Wt,⊤)) (ω : Γ(Hodge K W,⊤)) (hη : IsFrame (Hodge K Wt) ⊤ η)
    (μ Δ u v : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0) (hv : v = u/Δ^e)
    (hr : (baseMap S K Cs.scalar).appLE ⊤ ⊤ (by simp) r = scalar K ((μ⁻¹)^w*v))
    (hd : pullSection Ct 24 d =
      scalar K Δ • tensorPowerSection (Base K) (Hodge K Wt) 24 ⊤ η)
    (hweight : (PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
      ψ hψ (origin K W) (origin K Wt) hψo).app ⊤ η = scalar K μ • ω) :
    pullSection Cs w F =
      scalar K u • tensorPowerSection (Base K) (Hodge K W) w ⊤ ω := by
  rcases Cs with ⟨ρ,a,ha,hao,han⟩
  rcases Ct with ⟨ρt,b,hb,hbo,hbn⟩
  dsimp only [ArithmeticThetaOpenHodgeR0180.Test.scalar] at hscalar
  subst ρt
  exact test_formula (S := S) E T f K W Wt G Gt ρ a b ha hb hao hbo han hbn
    ψ hψ hψo hψmap e w hw d F r hF η ω hη μ Δ u v hμ hΔ hv hr hd hweight

end NormalizedSection

namespace CubicComparison
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146 OpenDiscriminantFullTateExpansionR0182

/-- Coordinate formulas identify the supplied canonical marking through this
same chosen isomorphism, including the identity label. -/
lemma marking_of_coordinates (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
    {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (V : TateLevel k r) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) r)
    (hmark : CanonicalMarking k r (ζ : k) V)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hO : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k r))
    (hcoord : ∀ (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p),
      i.val ≠ 0 ∨ (a : k) ≠ 1 →
      ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
        (genericPoint k M p hp.1 ≫ E.hom)
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val a))
        (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val a))) :
    ∀ (i j : Fin r) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M j (ζ^i.val) p),
      genericPoint k M p hp.1 ≫ E.hom =
        ArithmeticThetaFullLevelCoverR0175.coordinatePoint (LaurentSeries k) (TateCurve k r)
          V.law V.marking i j := by
  letI := V.elliptic
  intro i j p hp
  by_cases hn : i.val ≠ 0 ∨ j.val ≠ 0
  · apply coordinates_unique (TateCurve k r) V.law V.originLaw
      (x := algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateX r j.val ((ζ : k)^i.val)))
      (y := algebraMap (PowerSeries k) (LaurentSeries k)
        (ArithmeticThetaTateSeries.tateY r j.val ((ζ : k)^i.val)))
    · have hne : j.val ≠ 0 ∨ ((ζ^i.val : kˣ) : k) ≠ 1 := by
        rcases hn with hi | hj
        · exact Or.inr (by simpa only [Units.val_pow_eq_pow_val] using hζ.pow_ne_one_of_pos_of_lt hi i.isLt)
        · exact Or.inl hj
      simpa only [Units.val_pow_eq_pow_val] using hcoord j (ζ^i.val) p hp hne
    · exact hmark i j hn
  · have hi : i.val = 0 := by tauto
    have hj : j = zeroIndex r hr := Fin.ext (by tauto)
    have hp0 : MarkedLift k M (zeroIndex r hr) 1 p := by simpa only [hi,hj,pow_zero] using hp
    have hps := ActualRotationTranslation.markedLift_unique k M (zeroIndex r hr) 1 p s hp0 hs
    have hpO : genericPoint k M p hp.1 ≫ E.hom =
        ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r) := by
      subst p
      exact hO
    rw [hpO]
    simp only [ArithmeticThetaFullLevelCoverR0175.coordinatePoint,hi,hj,zeroIndex,
      WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,V.law.one_mul,V.originLaw.1,Category.id_comp]

/-- The model comparison retains both the coordinate witnesses and the exact
normalized Hodge generator, needed simultaneously in the quotient comparison. -/
lemma model_iso_framed (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
    (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    ∃ (X : Dual k M s 2) (Y : Dual k M s 3),
      RealizesCoordinate k false M s X ∧ RealizesCoordinate k true M s Y ∧
    ∃ (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
      (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)
      (hO : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k r)),
      (∀ (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X) (hp : MarkedLift k M i a p),
        i.val ≠ 0 ∨ (a : k) ≠ 1 →
        ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
          (genericPoint k M p hp.1 ≫ E.hom)
          (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val a))
          (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val a))) ∧
      ∀ (δ : CurveFrame k r), ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ →
      ∃ δM : ArithmeticThetaHodgeFourTorsionR0147.Frame k M,
        IsGlobalDifferentialFrame k M s X Y δM ∧
        (PeriodDifferential.pointMap (genericStructure k M)
          (structureMap (LaurentSeries k) (TateCurve k r)) E.hom hE
          (genericPoint k M s hs.1) (origin (LaurentSeries k) (TateCurve k r)) hO).app ⊤
          (hodgeGenerator k r δ) = ArithmeticThetaHodgeFourTorsionR0147.hodgeSection k M s hs.1 δM 1 := by
  letI := TateFullLevelMarking.elliptic k r h3 he
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3 M hM
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  obtain ⟨X,hX,-⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y,hY,-⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a,ha,-⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c,hc,-⟩ := projective_cubic_chart k r
  obtain ⟨E,hE,-⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  refine ⟨X,Y,hX,hY,E,hE.1,hE.2.2,?_,?_⟩
  · intro i b p hp hn
    refine ⟨?_, ArithmeticThetaHodgeFourTorsionR0147.marked_coordinate_chart
      k r hr h3 T he M hM s hs X Y hX hY a ha c hc E hE i b p hp hn⟩
    change genericPoint k M p hp.1 ≫ E.hom ≫ projectiveStructure k r = _
    rw [hE.1]
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  · intro δ hδ
    let δM := pulledCurveFrame (structureMap (LaurentSeries k) (TateCurve k r))
      (genericStructure k M) E hE.1 δ
    refine ⟨δM,model_pulled_frame_normalized k M s hs.1 h3 hM hs X Y a ha c hc E hE δ hδ,?_⟩
    exact (PeriodDifferential.pointMap_pulled_generator
      (structureMap (LaurentSeries k) (TateCurve k r)) (genericStructure k M)
      E hE.1 (genericPoint k M s hs.1) (origin (LaurentSeries k) (TateCurve k r)) hE.2.2 δ).trans
      (pointGenerator_frame (genericStructure k M) (genericPoint k M s hs.1) δM)

end CubicComparison

namespace TargetTest
open CategoryTheory.Limits ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180

lemma of_iso_over {S R : Type} [CommRing S] [CommRing R]
    (F : EllipticFamily S) (B : Base R ⟶ Base S) (ρ : S →+* R)
    (hB : baseMap S R ρ = B) (W : WeierstrassCurve R)
    (e : (baseChangeFamily F B).curve ≅ Curve R W)
    (he : e.hom ≫ structureMap R W = (baseChangeFamily F B).projection)
    (heo : zero (baseChangeFamily F B) ≫ e.hom = origin R W) :
    ∃ (G : ArithmeticThetaRelativeKatoR0169.Law R W)
      (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
      (C : ArithmeticThetaOpenHodgeR0180.Test S F R W G),
      C.scalar = ρ ∧ C.map = e.inv ≫ pullback.fst F.projection B := by
  subst B
  exact of_iso F ρ W e he heo

end TargetTest

namespace CubicComparison
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182

lemma normalized_tate_frame (k : Type) [Field k] [CharZero k] (r : ℕ)
    (h3 : 3 ≤ r) (he : Even r) :
    ∃ δ : CurveFrame k r, ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ := by
  letI := TateFullLevelMarking.elliptic k r h3 he
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  have hΩ : Scheme.Modules.IsInvertible
      (structureMap (LaurentSeries k) (TateCurve k r)).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap (LaurentSeries k) (TateCurve k r)).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  exact GlobalNormalizedDifferential.lifted_global_frame k r (Iso.refl _) h3 he
    (structureMap (LaurentSeries k) (TateCurve k r)) (Category.id_comp _) hΩ

lemma generator_frame {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Base K) (q : Base K ⟶ X)
    (δ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ f.kaehler) :
    IsFrame ((Scheme.Modules.pullback q).obj f.kaehler) ⊤ (pointGenerator f q δ) := by
  have hunit : IsFrame (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⊤ (1 : Γ(X,⊤)) := by
    intro U hU
    change Function.Bijective (fun a : Γ(X,U) => a * X.presheaf.map (homOfLE hU).op 1)
    simp only [map_one,mul_one]
    exact Function.bijective_id
  exact frame_restrict _ (by simp) _
    (pullback_frame q _ _ (GlobalFamilyDiscriminantR0180.frame_iso δ _ hunit))

end CubicComparison

#print axioms designated_point_conditions
#print axioms designated_exponent
#print axioms test_lift
#print axioms designated_toric_scalar
#print axioms designated_lift_coordinates
#print axioms PeriodCollapse.algebraizes
#print axioms PeriodCollapse.map_finite
#print axioms PeriodCollapse.generic_flat_surjective
#print axioms PeriodCollapse.generic_mul
#print axioms PeriodCollapse.stage_marked_cartesian
#print axioms PeriodCollapse.map_marked_cartesian
#print axioms PeriodCollapse.generic_marked_cartesian
#print axioms PeriodCollapse.generic_finrank
#print axioms PeriodCollapse.generic_kernel_killed
#print axioms PeriodCollapse.dual_exists
#print axioms PeriodCollapse.dual_marked
#print axioms PeriodCollapse.dual_geometry
#print axioms PeriodCollapse.dual_toric_kernel
#print axioms CubicComparison.model_iso
#print axioms CubicComparison.coordinates_unique
#print axioms CubicComparison.canonical_model_iso
#print axioms CubicComparison.model_nsmul
#print axioms CubicComparison.modelFamily_zero
#print axioms CubicComparison.model_nsmul_of_origin
#print axioms test_kernel_multiple
#print axioms QuotientComparison.quotient_split_cartesian
#print axioms QuotientComparison.iso_of_split_kernel
#print axioms QuotientComparison.baseChangeArrow_geometry
#print axioms QuotientComparison.quotient_split_baseChange
#print axioms ToricQuotient.compare
#print axioms ToricQuotient.designated_dual_marked
#print axioms ToricQuotient.designated_source_point
#print axioms TargetTest.of_iso
#print axioms TargetTest.value_eq_model
#print axioms TargetTest.unary_value
#print axioms TargetDiscriminant.exact
#print axioms PeriodDifferential.completed_field
#print axioms PeriodDifferential.origin_taylor
#print axioms PeriodDifferential.taylor_differential
#print axioms PeriodDifferential.pointMap_of_parameter
#print axioms PeriodDifferential.collapse_hodge
#print axioms PeriodDifferential.pointMap_comp
#print axioms PeriodDifferential.evaluated_pull
#print axioms PeriodDifferential.pointMap_natWeight
#print axioms PeriodDifferential.exists_normalized_parameter
#print axioms PeriodDifferential.multiplication_hodge
#print axioms PeriodDifferential.dual_hodge
#print axioms PeriodDifferential.pointMap_pulled_generator
#print axioms PeriodDifferential.pointMap_square
#print axioms PeriodDifferential.pointMap_baseChange_D
#print axioms PeriodDifferential.transfer_weight
#print axioms PeriodDifferential.pointMap_baseChange_naturality_D
#print axioms PeriodDifferential.pointMap_baseChange_naturality
#print axioms NormalizedSection.transport_local_tensor
#print axioms NormalizedSection.exact_scalar
#print axioms NormalizedSection.normalization_in_frame
#print axioms NormalizedSection.normalization_after_pullback
#print axioms NormalizedSection.test_formula
#print axioms NormalizedSection.test_formula_tests
#print axioms CubicComparison.marking_of_coordinates
#print axioms CubicComparison.model_iso_framed
#print axioms CubicComparison.normalized_tate_frame
#print axioms CubicComparison.generator_frame
#print axioms TargetTest.of_iso_over
end ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182

namespace ArithmeticThetaBoundaryHodgeR0182
open OpenUnaryDesignatedExpansionR0182
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open OpenDiscriminantFullTateExpansionR0182

/-- Exact designated expansion of the same normalized open section. -/
theorem open_unary_designated_expansion :
∀ (k : Type) [Field k] [CharZero k] (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (24*N^2)) (V : ArithmeticThetaBoundaryHodgeR0182.Test k (24*N^2) D) (ζ : k), IsPrimitiveRoot ζ (24*N^2) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (24*N^2) ζ V.level → ∀ (Q : ArithmeticThetaOpenHodgeR0180.Quotient D.atlas.quotient.ring (ArithmeticThetaOpenHodgeR0180.levelFamily k (24*N^2) D.atlas) m (ArithmeticThetaOpenHodgeR0180.kernelPoint k (24*N^2) D.atlas m)) (d : (ArithmeticThetaOpenHodgeR0180.power Q.target 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaOpenHodgeR0180.IsD2 Q.target d → ∀ (ν : ℤ), (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∀ (v : D.atlas.quotient.ring) (F : (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family (((1+12*N)^2-1)/2)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaOpenHodgeR0180.IsKatoValue Q.target (1+12*N) (CategoryTheory.CategoryStruct.comp (ArithmeticThetaOpenHodgeR0180.liftPoint k (24*N^2) D.atlas m N (ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν) (N/2)) Q.arrow.map) v → ArithmeticThetaOpenHodgeR0180.IsNormalizedPower k (24*N^2) D.atlas m N Q d v F → ArithmeticThetaBoundaryHodgeR0182.pullAmbientPower k (24*N^2) V (((1+12*N)^2-1)/2) F = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ ((1+12*N)^2-1)) • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Puncture k) (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k (24*N^2))) (((1+12*N)^2-1)/2) ⊤ (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k (24*N^2) V.differential) := by

  intro k _ _ m N hm hmeven hN hNeven hmN D V ζ hζ hmark Q d hd ν hν v F hv hF
  classical
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have hr : 0 < 24*N^2 := by positivity
  have h3r : 3 ≤ 24*N^2 := by have := Nat.one_le_pow 2 N hN; omega
  have hs : 0 < (24*N^2)*m := by positivity
  have h3s : 3 ≤ (24*N^2)*m := by nlinarith
  have her : Even (24*N^2) := ⟨12*N^2, by ring⟩
  have hes : Even ((24*N^2)*m) := ⟨12*N^2*m, by ring⟩
  have hmr : m ∣ 24*N^2 := dvd_mul_of_dvd_right
    (by simpa only [pow_two] using dvd_mul_of_dvd_left hmN N) 24
  let z : kˣ := (hζ.isUnit hr.ne').unit
  have hz : (z : k) = ζ := (hζ.isUnit hr.ne').unit_spec
  have hzp : IsPrimitiveRoot (z : k) (24*N^2) := by simpa only [hz] using hζ
  have hzm : CanonicalMarking k (24*N^2) (z : k) V.level := by simpa only [hz] using hmark
  obtain ⟨T,M,hM⟩ := TateFullLevelMarking.model_exists k ((24*N^2)*m) h3s hs
  obtain ⟨U,A,hA⟩ := TateFullLevelMarking.model_exists k (24*N^2) h3r hr
  let p (i : Fin ((24*N^2)*m)) :=
    MarkedPointAddition.sectionAt k h3s M hM i 1
  have hp (i : Fin ((24*N^2)*m)) : MarkedLift k M i 1 (p i) :=
    MarkedPointAddition.sectionAt_spec k h3s M hM i 1
  let p₀ := p (zeroIndex ((24*N^2)*m) hs)
  have hp₀ : MarkedLift k M (zeroIndex ((24*N^2)*m) hs) 1 p₀ := hp _
  obtain ⟨q,hq,-⟩ := marked_section_algebraization k (24*N^2) hr h3r U A hA
    (zeroIndex (24*N^2) hr) 1
  obtain ⟨G,hG,-⟩ := actual_generic_group_law k ((24*N^2)*m) hs h3s T hes M hM p₀ hp₀
  obtain ⟨H,hH,-⟩ := actual_generic_group_law k (24*N^2) hr h3r U her A hA q hq
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3s M hM
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k h3r A hA
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3s M hM p₀ hp₀
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k h3r A hA q hq
  letI : IsLocallyNoetherian (genericScheme k M) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  letI : IsLocallyNoetherian (genericScheme k A) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericStructure k A)
  obtain ⟨XA,YA,hXA,hYA,EA,hEA,hOA,hcoordA,hframeA⟩ :=
    CubicComparison.model_iso_framed k (24*N^2) hr h3r her U A hA q hq
  obtain ⟨XM,YM,hXM,hYM,EM,hEM,hOM,hcoordM,hframeM⟩ :=
    CubicComparison.model_iso_framed k ((24*N^2)*m) hs h3s hes T M hM p₀ hp₀
  have hmarkA := CubicComparison.marking_of_coordinates k (24*N^2) hr A q hq
    V.level z hzp hzm EA hOA hcoordA
  obtain ⟨δ,hδ⟩ := CubicComparison.normalized_tate_frame k ((24*N^2)*m) h3s hes
  obtain ⟨δA,hδA,hgenA⟩ := hframeA V.differential V.normalized
  obtain ⟨δM,hδM,hgenM⟩ := hframeM δ hδ
  obtain ⟨dual,⟨hdualOver,hdual,hdual'⟩,-⟩ :=
    PeriodCollapse.dual_exists k h3r h3s hes M hM A hA p hp q hq G hG H hH
  have hdualZero : genericPoint k A q hq.1 ≫ dual = genericPoint k M p₀ hp₀.1 := by
    apply PeriodCollapse.dual_marked k hm h3s hes M hM A hA p₀ hp₀ G hG dual hdual
      (zeroIndex (24*N^2) hr) 1 q hq p₀
    simpa only [zeroIndex,Nat.mul_zero,one_pow] using hp₀
  have hdualWeight := PeriodDifferential.dual_hodge k h3r h3s her hes M hM A hA
    p₀ hp₀ q hq G hG H hH XM YM hXM hYM XA YA hXA hYA δM hδM δA hδA
    dual hdualOver hdualZero hdual'
  rw [ArithmeticThetaHodgeFourTorsionR0147.ActualFourTorsionHodgeRoot.hodgeSection_smul
    k A q hq.1 δA (m : LaurentSeries k)] at hdualWeight
  obtain ⟨e,he,heOver,heZero⟩ := ToricQuotient.compare k hm hmr h3r h3s her hes
    M hM A hA p hp q hq G hG H hH dual hdualOver hdual hdual'
    V z hzp EA hEA hOA hmarkA Q
  let B := V.base ≫ D.quotient.inclusion
  let ρ : D.atlas.quotient.ring →+* LaurentSeries k := (Spec.preimage B).hom
  have hB : baseMap D.atlas.quotient.ring (LaurentSeries k) ρ = B := Spec.map_preimage B
  let et := e ≪≫ EM
  have het : et.hom ≫ structureMap (LaurentSeries k) (TateCurve k ((24*N^2)*m)) =
      (baseChangeFamily Q.target B).projection := by
    change (e.hom ≫ EM.hom) ≫ _ = _
    rw [Category.assoc,hEM,heOver]
  have hetZero : zero (baseChangeFamily Q.target B) ≫ et.hom =
      origin (LaurentSeries k) (TateCurve k ((24*N^2)*m)) := by
    change _ ≫ (e.hom ≫ EM.hom) = _
    rw [← Category.assoc,heZero,hOM]
  obtain ⟨Gt,hGt,Ct,hCtScalar,hCtMap⟩ := TargetTest.of_iso_over Q.target B ρ hB
    (TateCurve k ((24*N^2)*m)) et het hetZero
  let ψ := EA.inv ≫ dual ≫ EM.hom
  have hψ : ψ ≫ structureMap (LaurentSeries k) (TateCurve k ((24*N^2)*m)) =
      structureMap (LaurentSeries k) (TateCurve k (24*N^2)) := by
    dsimp only [ψ]
    rw [Category.assoc,Category.assoc,hEM,hdualOver,← hEA,EA.inv_hom_id_assoc]
  have hψZero : origin (LaurentSeries k) (TateCurve k (24*N^2)) ≫ ψ =
      origin (LaurentSeries k) (TateCurve k ((24*N^2)*m)) := by
    rw [← hOA]
    simp only [ψ,Category.assoc,Iso.hom_inv_id_assoc]
    rw [← Category.assoc,hdualZero,hOM]
  have hψsquare : EA.hom ≫ ψ = dual ≫ EM.hom := by
    simp only [ψ,Iso.hom_inv_id_assoc]
  letI := V.level.elliptic
  letI := TateFullLevelMarking.elliptic k ((24*N^2)*m) h3s hes
  letI : SmoothOfRelativeDimension 1
      (structureMap (LaurentSeries k) (TateCurve k (24*N^2))) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one
      (TateCurve k (24*N^2)).toProjective
  letI : SmoothOfRelativeDimension 1
      (structureMap (LaurentSeries k) (TateCurve k ((24*N^2)*m))) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one
      (TateCurve k ((24*N^2)*m)).toProjective
  have hweight := PeriodDifferential.transfer_weight
    (K := LaurentSeries k)
    (structureMap (LaurentSeries k) (TateCurve k (24*N^2)))
    (structureMap (LaurentSeries k) (TateCurve k ((24*N^2)*m)))
    (genericStructure k A) (genericStructure k M) EA hEA EM hEM ψ hψ dual hdualOver
    (origin (LaurentSeries k) (TateCurve k (24*N^2)))
    (origin (LaurentSeries k) (TateCurve k ((24*N^2)*m)))
    (genericPoint k A q hq.1) (genericPoint k M p₀ hp₀.1)
    hOA hOM hψZero hdualZero hψsquare
    (hodgeGenerator k (24*N^2) V.differential) (hodgeGenerator k ((24*N^2)*m) δ)
    _ _ hgenA hgenM (scalar (LaurentSeries k) (m : LaurentSeries k)) hdualWeight
  have hmodelSquare : EA.hom ≫ V.map ≫ Q.arrow.map = dual ≫ EM.hom ≫ Ct.map := by
    rw [hCtMap]
    change EA.hom ≫ V.map ≫ Q.arrow.map =
      dual ≫ EM.hom ≫ (EM.inv ≫ e.inv) ≫ pullback.fst Q.target.projection B
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [← he]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    exact (Category.assoc EA.hom V.map Q.arrow.map).symm.trans
      (QuotientComparison.baseChangeArrow_fst D.atlas.descent.family Q.target Q.arrow B
        (genericStructure k A) (EA.hom ≫ V.map) (ToricQuotient.model_cartesian k (24*N^2) A V EA hEA)).symm
  have hmap : V.map ≫ Q.arrow.map = ψ ≫ Ct.map := by
    apply (cancel_epi EA.hom).mp
    calc
      EA.hom ≫ (V.map ≫ Q.arrow.map) = dual ≫ EM.hom ≫ Ct.map := hmodelSquare
      _ = EA.hom ≫ (ψ ≫ Ct.map) := by
        rw [← Category.assoc EA.hom ψ Ct.map,hψsquare,Category.assoc]
  have hindices := source_indices m N hm hN hNeven hmN ν hν
  let i : Fin (24*N^2) := ⟨24*N^2/N*unaryResidue m N ν,hindices.2.2.1⟩
  let j : Fin ((24*N^2)*m) := ⟨m*i.val, by
    simpa only [Nat.mul_comm (24*N^2) m] using Nat.mul_lt_mul_of_pos_left i.isLt hm⟩
  have hj : j.val = (N^2/m)*ArithmeticThetaUnaryProduct.unaryA m ν :=
    designated_exponent m N hm hN hNeven hmN ν hν
  obtain ⟨a,ha,-⟩ := marked_section_algebraization k (24*N^2) hr h3r U A hA
    i (z^(24*N^2/(m*N)*(N/2)))
  obtain ⟨b,hb,-⟩ := marked_section_algebraization k ((24*N^2)*m) hs h3s T M hM j (-1)
  have hab := ToricQuotient.designated_dual_marked k m N hm hN hNeven hmN ν hν
    h3s hes M hM A hA p₀ hp₀ G hG dual hdual z hzp i rfl a ha j hj b hb
  have hap := ToricQuotient.designated_source_point k m N hm hN hNeven hmN ν hν
    A V z EA hmarkA i rfl a ha
  have hpoint : genericPoint k M b hb.1 ≫ EM.hom ≫ Ct.map =
      baseMap D.atlas.quotient.ring (LaurentSeries k) Ct.scalar ≫
        (liftPoint k (24*N^2) D.atlas m N (unaryResidue m N ν) (N/2) ≫ Q.arrow.map) := by
    rw [hCtScalar,hB,← hab]
    rw [Category.assoc,Category.assoc,← hmodelSquare]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ Q.arrow.map) hap
  have geom := relative_curve_geometry (LaurentSeries k) (TateCurve k ((24*N^2)*m))
  letI := geom.1
  letI := geom.2.1
  letI := geom.2.2.2.1
  letI := geom.2.2.2.2.1
  letI := geom.2.2.2.2.2.1
  have hparameters := period_parameters m N hm hN hmN
  have hvalue := TargetTest.unary_value k h3s hes M hM p₀ hp₀ G hG
    (N^2/m) m N hparameters.1 hm hmeven hN hNeven hmN hparameters.2.2.1.symm
    (TateCurve k ((24*N^2)*m)) Gt hGt EM hEM hOM Q.target Ct
    (liftPoint k (24*N^2) D.atlas m N (unaryResidue m N ν) (N/2) ≫ Q.arrow.map)
    v hv ν hν j hj b hb hpoint
  have hD := TargetDiscriminant.exact k ((24*N^2)*m) h3s hes Q.target Gt hGt Ct δ hδ d hd
  have hη := CubicComparison.generator_frame (K := LaurentSeries k)
    (structureMap (LaurentSeries k) (TateCurve k ((24*N^2)*m)))
    (origin (LaurentSeries k) (TateCurve k ((24*N^2)*m))) δ
  have hΔ : ArithmeticThetaUnaryKatoPowerR0160.discriminant k ((24*N^2)*m) ≠ 0 := by
    rw [← hparameters.2.2.1]
    exact (ArithmeticThetaUnaryKatoPowerR0160.discriminant_eta_substitution
      k (N^2/m) m hparameters.1 hm).2
  let Cs := affineTest k (24*N^2) V
  have hCsScalar : Cs.scalar = ρ := rfl
  let coef : D.atlas.quotient.ring :=
    (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)^(((1+12*N)^2-1)/2)*v
  have hcoef : (baseMap D.atlas.quotient.ring (LaurentSeries k) ρ).appLE ⊤ ⊤ (by simp)
      (scalar D.atlas.quotient.ring coef) =
      scalar (LaurentSeries k) (((m : LaurentSeries k)⁻¹)^(((1+12*N)^2-1)/2)*(ρ v)) := by
    rw [NormalizedSection.base_scalar]
    congr 1
    dsimp only [coef]
    rw [map_mul,map_pow]
    congr 2
    exact (map_inv₀ (ρ.comp (algebraMap k D.atlas.quotient.ring)) (m : k)).trans
      (congrArg Inv.inv (by simp))
  have hf0 := NormalizedSection.test_formula_tests (S := D.atlas.quotient.ring) D.atlas.descent.family Q.target Q.arrow
    (LaurentSeries k) (TateCurve k (24*N^2)) (TateCurve k ((24*N^2)*m)) V.level.law Gt
    Cs Ct (hCtScalar.trans hCsScalar.symm)
    ψ hψ hψZero hmap
  have hf1 := hf0 (((1+12*N)^2-1)/48) (((1+12*N)^2-1)/2)
    (OpenLevelNormalizedHodgePowerR0180.exponents N hNeven).2 d F
    (scalar D.atlas.quotient.ring coef)
  have hf2 := hf1 hF
  have hmK : (m : LaurentSeries k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hvρ : ρ v = ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ ((1+12*N)^2-1) /
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k ((24*N^2)*m) ^ (((1+12*N)^2-1)/48) := by
    simpa only [hCtScalar] using hvalue
  have hf3 := hf2
    (hodgeGenerator k ((24*N^2)*m) δ) (hodgeGenerator k (24*N^2) V.differential) hη
    (m : LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k ((24*N^2)*m))
    (ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ ((1+12*N)^2-1)) (ρ v)
    hmK hΔ hvρ hcoef
  have hf4 := hf3 hD
  have hf := hf4 (by
    with_reducible exact hweight)
  exact (pullAmbientPower_eq_pullSection k (24*N^2) V (((1+12*N)^2-1)/2) F).trans hf

#print axioms open_unary_designated_expansion
end ArithmeticThetaBoundaryHodgeR0182
