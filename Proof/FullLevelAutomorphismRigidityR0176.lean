module

public import FullLevelTorsionSplittingR0175
public import PointedRelativeGroupHomR0173
public import FullLevelBaseChangeR0175
public import NormalAffineLevelExtensionR0175
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
public import Theorems.Thm_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176
namespace FullLevelAutomorphismRigidity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaRelativeCyclicQuotientR0173
open ArithmeticThetaRelativeIsogenyHodgeR0172 ArithmeticThetaRelativeKatoNaturalityR0170

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) {L : ℕ}
    (M : FullLevel R W G L (𝟙 (Base R))) (f : PointedMap R W W)
    (hx : M.x.val ≫ f.map = M.x.val) (hy : M.y.val ≫ f.map = M.y.val)

include hG hx hy

/-- Fixing the marked generators fixes each actual residue-combination section. -/
lemma coordinate_fixed (i j : Fin L) :
    coordinatePoint R W G M i j ≫ f.map = coordinatePoint R W G M i j := by
  have hf := (pointed_relative_group_hom R W G hG W G hG f).1
  have hx' : mapPoint R W f (𝟙 (Base R)) M.x = M.x := Subtype.ext hx
  have hy' : mapPoint R W f (𝟙 (Base R)) M.y = M.y := Subtype.ext hy
  have h := hf (Base R) (𝟙 (Base R))
    (G.nsmul (𝟙 (Base R)) i.val M.x) (G.nsmul (𝟙 (Base R)) j.val M.y)
  rw [PointedRelativeGroupHom.map_nsmul R W W G G hG hG f hf,
    PointedRelativeGroupHom.map_nsmul R W W G G hG hG f hf, hx', hy'] at h
  exact congrArg Subtype.val h

/-- The entire scheme-theoretic torsion is fixed, including all test schemes. -/
lemma torsion_fixed (hL : 0 < L) :
    (torsionIdeal R W G L).subschemeι ≫ f.map =
      (torsionIdeal R W G L).subschemeι := by
  obtain ⟨e, _, he⟩ := full_level_torsion_splitting R W G hG L hL M
  apply (cancel_epi e.inv).mp
  let q := sigmaSpec (fun _ : Fin L × Fin L => CommRingCat.of R)
  letI : IsIso q := FullLevelTorsionSplittingR0175.sigma_spec_iso L
  apply (cancel_epi q).mp
  apply Sigma.hom_ext
  intro a
  simp only [← Category.assoc]
  rw [show Sigma.ι (fun _ : Fin L × Fin L => Base R) a ≫ q =
    torsionComponent R L a.1 a.2 from ι_sigmaSpec _ a]
  simp only [Category.assoc]
  calc
    _ = (torsionComponent R L a.1 a.2 ≫ e.inv ≫
        (torsionIdeal R W G L).subschemeι) ≫ f.map := by simp only [Category.assoc]
    _ = coordinatePoint R W G M a.1 a.2 ≫ f.map := by rw [he]
    _ = coordinatePoint R W G M a.1 a.2 := coordinate_fixed R W G hG M f hx hy _ _
    _ = _ := (he a.1 a.2).symm


lemma torsion_point_fixed (hL : 0 < L) {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) (hk : G.nsmul t L x = G.one t) :
    x.val ≫ f.map = x.val := by
  letI : IsProper (structureMap R W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W) := by
    haveI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
      rw [BaseChange.origin_over]; infer_instance
    exact IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  let ti := pullback.fst (G.schemeNsmul L) (origin R W)
  let I := torsionIdeal R W G L
  have hi : I.subschemeι.ker = ti.ker := by
    rw [I.ker_subschemeι]
    exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (origin R W)
      (G.schemeNsmul L)).symm
  let a := IsClosedImmersion.lift I.subschemeι ti hi.le
  have ha : a ≫ I.subschemeι = ti := IsClosedImmersion.lift_fac _ _ _
  have ht : ti ≫ f.map = ti := by
    rw [← ha, Category.assoc, torsion_fixed R W G hG M f hx hy hL]
  have hk' : x.val ≫ G.schemeNsmul L = t ≫ origin R W := by
    rw [← FullLevelTorsionSplittingR0175.nsmul_val G, hk, hG.1]
  let a' := pullback.lift x.val t hk'
  have ha' : a' ≫ ti = x.val := pullback.lift_fst _ _ _
  rw [← ha', Category.assoc, ht]

omit hG hx hy in
/-- Cartesian transport of an actual automorphism, retaining the given map. -/
def liftIso {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W) :
    Curve S Ws ≅ Curve S Ws where
  hom := hb.lift (b ≫ e.hom) (structureMap S Ws) (by rw [Category.assoc, he]; exact hb.w)
  inv := hb.lift (b ≫ e.inv) (structureMap S Ws) (by
    rw [← he, Category.assoc, Iso.inv_hom_id_assoc]; exact hb.w)
  hom_inv_id := by
    apply hb.hom_ext <;> simp [Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]
  inv_hom_id := by
    apply hb.hom_ext <;> simp [Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]

omit hG hx hy in
lemma liftIso_over {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W) :
    (liftIso R W Ws ι b hb e he).hom ≫ structureMap S Ws = structureMap S Ws :=
  hb.lift_snd _ _ _

omit hG hx hy in
lemma liftIso_comp {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W) :
    (liftIso R W Ws ι b hb e he).hom ≫ b = b ≫ e.hom := hb.lift_fst _ _ _

omit hG hx hy in
lemma liftIso_origin {S : Type u} [CommRing S] (Ws : WeierstrassCurve S)
    (ι : Base S ⟶ Base R) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) ι)
    (ho : origin S Ws ≫ b = ι ≫ origin R W)
    (e : Curve R W ≅ Curve R W) (he : e.hom ≫ structureMap R W = structureMap R W)
    (heO : origin R W ≫ e.hom = origin R W) :
    origin S Ws ≫ (liftIso R W Ws ι b hb e he).hom = origin S Ws := by
  apply hb.hom_ext
  · rw [Category.assoc, liftIso_comp, ← Category.assoc, ho, Category.assoc, heO]
  · rw [Category.assoc, liftIso_over]

omit hx hy in
lemma finite_relative_originIso :
    Finite (ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms.OriginIso R W) := by
  classical
  have hg := relative_curve_geometry R W
  letI := hg.1
  letI := hg.2.1
  letI := hg.2.2.2.1
  letI := hg.2.2.2.2.1
  letI : IsProper (structureMap R W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  let K := FractionRing R
  let Wk := W.map (algebraMap R K)
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  letI := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms.finite_originIso K Wk
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  letI : Flat ι := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  letI : Flat C.map := MorphismProperty.of_isPullback (P := @Flat) C.cartesian.flip inferInstance
  letI : IsDominant C.map := by
    constructor
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure (Curve R W)]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr ⟨genericPoint (GenericCurve R W),
      GenericComparisonProof.generic_eq_of_flat C.map⟩
  let lift (e : ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms.OriginIso R W) :
      ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms.OriginIso K Wk :=
    ⟨liftIso R W Wk ι C.map C.cartesian e.val e.property.1,
      liftIso_over R W Wk ι C.map C.cartesian e.val e.property.1,
      liftIso_origin R W Wk ι C.map C.cartesian C.origin_eq e.val e.property.1 e.property.2⟩
  apply Finite.of_injective lift
  intro a b hab
  apply Subtype.ext
  apply Iso.ext
  apply ext_of_isDominant_of_isSeparated (structureMap R W)
    (a.property.1.trans b.property.1.symm) C.map
  have h := congrArg (fun e => e.val.hom ≫ C.map) hab
  simpa only [lift, liftIso_comp] using h

end FullLevelAutomorphismRigidity
end ArithmeticThetaLegendreAtlasR0176

namespace ArithmeticThetaLegendreAtlasR0176.FullLevelAutomorphismRigidity.Tate

variable (p : ℕ) (A : Type*) [AddCommGroup A]

/-- Compatible prime-power torsion sequences, with pointwise addition. -/
def tower : AddSubgroup (ℕ → A) where
  carrier := {x | ∀ j, p ^ j • x j = 0 ∧ p • x (j + 1) = x j}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j; exact ⟨by simp [smul_add, (hx j).1, (hy j).1], by simp [smul_add, (hx j).2, (hy j).2]⟩
  neg_mem' := by intro x hx j; exact ⟨by simp [smul_neg, (hx j).1], by simp [smul_neg, (hx j).2]⟩

variable {p A}

lemma compat (x : tower p A) (j a : ℕ) : p ^ a • x.val (j + a) = x.val j := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, mul_smul]
    change p ^ a • (p • x.val ((j + a) + 1)) = _
    rw [(x.property (j + a)).2, ih]

lemma torsion_free (x : tower p A) (hx : p • x = 0) : x = 0 := by
  apply Subtype.ext
  funext j
  have h := congrArg (fun y : tower p A => y.val (j + 1)) hx
  change p • x.val (j + 1) = 0 at h
  rwa [(x.property j).2] at h

lemma separated (x : tower p A) (hx : ∀ n, ∃ y : tower p A, x = p ^ n • y) : x = 0 := by
  apply Subtype.ext
  funext j
  obtain ⟨y, rfl⟩ := hx j
  exact (y.property j).1

def mapEnd (u : AddMonoid.End A) : tower p A →ₗ[ℤ] tower p A :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun x => ⟨fun j => u (x.val j), fun j =>
      ⟨by rw [← map_nsmul, (x.property j).1, map_zero],
       by rw [← map_nsmul, (x.property j).2]⟩⟩
    map_zero' := Subtype.ext (funext fun _ => u.map_zero)
    map_add' := fun x y => Subtype.ext (funext fun j => u.map_add _ _) }

lemma mapEnd_pow (u : AddMonoid.End A) (m : ℕ) (x : tower p A) (j : ℕ) :
    ((mapEnd (p := p) u ^ m) x).val j = (u ^ m) (x.val j) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    change u (((mapEnd u ^ m) x).val j) = (u ^ (m + 1)) (x.val j)
    rw [ih, pow_succ']
    rfl

lemma mapEnd_eq_one (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    (u : AddMonoid.End A) (m : ℕ) (hm : m ≠ 0) (hum : u ^ m = 1)
    (hfix : ∀ x : A, p ^ a • x = 0 → u x = x) : mapEnd (p := p) u = 1 := by
  apply Module.End.eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul
    hp a ha ha2 torsion_free separated _ m hm
  · ext x j
    change ((mapEnd u ^ m) x).val j = x.val j
    rw [mapEnd_pow, hum]
    rfl
  · intro x
    let y : tower p A := ⟨fun j => u (x.val (j + a)) - x.val (j + a), by
      intro j
      constructor
      · rw [smul_sub, ← map_nsmul]
        apply sub_eq_zero.mpr
        apply hfix
        rw [← mul_smul, ← pow_add, Nat.add_comm a j]
        exact (x.property (j + a)).1
      · rw [smul_sub, ← map_nsmul]
        have hc := (x.property (j + a)).2
        have he : j + 1 + a = (j + a) + 1 := by omega
        rw [he, hc]⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    funext j
    change u (x.val j) - x.val j = p ^ a • (u (x.val (j + a)) - x.val (j + a))
    rw [smul_sub, ← map_nsmul, compat]

lemma exists_tower (hdiv : Function.Surjective (fun x : A => p • x))
    (j : ℕ) (z : A) (hz : p ^ j • z = 0) : ∃ x : tower p A, x.val j = z := by
  classical
  choose root hroot using hdiv
  let s : ℕ → A := fun i => Nat.rec z (fun _ w => root w) i
  have hs0 : s 0 = z := rfl
  have hs (i : ℕ) : p • s (i + 1) = s i := hroot _
  let x : ℕ → A := fun i => if i ≤ j then p ^ (j - i) • z else s (i - j)
  have hxle (i : ℕ) (hi : i ≤ j) : x i = p ^ (j - i) • z := if_pos hi
  have hxgt (i : ℕ) (hi : j < i) : x i = s (i - j) := if_neg (not_le.mpr hi)
  have hc (i : ℕ) : p • x (i + 1) = x i := by
    rcases lt_trichotomy (i + 1) (j + 1) with h | h | h
    · rw [hxle _ (by omega), hxle _ (by omega), ← mul_smul, ← pow_succ']
      congr 2
      omega
    · have hij : i = j := by omega
      subst i
      rw [hxgt _ (by omega), hxle _ le_rfl, Nat.add_sub_cancel_left, Nat.sub_self,
        pow_zero, one_smul]
      exact hs 0
    · rw [hxgt _ (by omega), hxgt _ (by omega)]
      rw [show i + 1 - j = (i - j) + 1 by omega, hs]
  have ht (i : ℕ) : p ^ i • x i = 0 := by
    induction i with
    | zero => rw [hxle _ (by omega), pow_zero, one_smul, Nat.sub_zero, hz]
    | succ i ih => rw [pow_succ, mul_smul, hc, ih]
  refine ⟨⟨x, fun i => ⟨ht i, hc i⟩⟩, ?_⟩
  change x j = z
  rw [hxle _ le_rfl, Nat.sub_self, pow_zero, one_smul]

/-- A finite-order automorphism trivial modulo an admissible prime power acts
trivially on every higher primary torsion group. -/
lemma fixes_primary (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    (hdiv : Function.Surjective (fun x : A => p • x))
    (u : AddMonoid.End A) (m : ℕ) (hm : m ≠ 0) (hum : u ^ m = 1)
    (hfix : ∀ x : A, p ^ a • x = 0 → u x = x) (j : ℕ) (z : A)
    (hz : p ^ j • z = 0) : u z = z := by
  obtain ⟨x, hx⟩ := exists_tower hdiv j z hz
  have h := congrArg (fun v : tower p A →ₗ[ℤ] tower p A => (v x).val j)
    (mapEnd_eq_one hp a ha ha2 u m hm hum hfix)
  change u (x.val j) = x.val j at h
  simpa [hx] using h

end ArithmeticThetaLegendreAtlasR0176.FullLevelAutomorphismRigidity.Tate

namespace ArithmeticThetaLegendreAtlasR0176.FullLevelAutomorphismRigidity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaRelativeCyclicQuotientR0173
open ArithmeticThetaRelativeIsogenyHodgeR0172 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

/-- The actual pointed automorphism subgroup. -/
local instance isoGroup (X : Scheme.{u}) : Group (X ≅ X) := inferInstanceAs (Group (Aut X))

def originAut (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    Subgroup (Aut (Curve R W)) where
  carrier := {e | e.hom ≫ structureMap R W = structureMap R W ∧
    origin R W ≫ e.hom = origin R W}
  one_mem' := ⟨Category.id_comp _, Category.comp_id _⟩
  mul_mem' := by
    intro a b ha hb
    constructor
    · change (b.hom ≫ a.hom) ≫ _ = _
      rw [Category.assoc, ha.1, hb.1]
    · change origin R W ≫ b.hom ≫ a.hom = _
      rw [← Category.assoc, hb.2, ha.2]
  inv_mem' := by
    intro a ha
    constructor
    · change a.inv ≫ structureMap R W = structureMap R W
      rw [← ha.1, Iso.inv_hom_id_assoc]
      exact ha.1.symm
    · change origin R W ≫ a.inv = origin R W
      rw [← ha.2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact ha.2.symm

lemma finite_order (K : Type u) [Field K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (e : Curve K W ≅ Curve K W) (he : e.hom ≫ structureMap K W = structureMap K W)
    (ho : origin K W ≫ e.hom = origin K W) :
    ∃ m : ℕ, 0 < m ∧ (e : Aut (Curve K W)) ^ m = 1 := by
  letI : Finite (originAut K W) :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.FiniteOriginAutomorphisms.finite_originIso K W
  let a : originAut K W := ⟨e, he, ho⟩
  obtain ⟨m, hm, hpow⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
  exact ⟨m, hm, congrArg Subtype.val hpow⟩

lemma admissible_prime_power (L : ℕ) (hL : 3 ≤ L) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ (p = 2 → 2 ≤ a) ∧ p ^ a ∣ L := by
  rcases L.eq_two_pow_or_exists_odd_prime_and_dvd with ⟨k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩
  · refine ⟨2, 2, Nat.prime_two, by omega, fun _ => le_rfl, ?_⟩
    have hk : 2 ≤ k := by
      by_contra hk
      push Not at hk
      interval_cases k <;> simp at hL
    exact Nat.pow_dvd_pow 2 hk
  · exact ⟨p, 1, hp, le_rfl, fun h2 => False.elim (by subst p; exact absurd hodd (by decide)), by simpa using hdvd⟩

/-- Infinitely many primary torsion points, from the actual elliptic torsion counts. -/
lemma primary_infinite {A : Type*} [AddCommGroup A] (p : ℕ) (hp : 2 ≤ p)
    (hc : ∀ j, Nat.card (Submodule.torsionBy ℤ A ((p ^ j : ℕ) : ℤ)) = (p ^ j) ^ 2) :
    Infinite {x : A // ∃ j : ℕ, p ^ j • x = 0} := by
  classical
  by_contra h
  haveI : Finite {x : A // ∃ j : ℕ, p ^ j • x = 0} := not_infinite_iff_finite.mp h
  let d := Nat.card {x : A // ∃ j : ℕ, p ^ j • x = 0}
  let f (j : ℕ) : Submodule.torsionBy ℤ A ((p ^ j : ℕ) : ℤ) →
      {x : A // ∃ j : ℕ, p ^ j • x = 0} :=
    fun x => ⟨x.val, j, by simpa only [Submodule.mem_torsionBy_iff,
      Nat.cast_smul_eq_nsmul] using x.property⟩
  have hj (j : ℕ) : (p ^ j) ^ 2 ≤ d := by
    rw [← hc]
    exact Nat.card_le_card_of_injective (f j) (fun x y h => Subtype.ext (congrArg (fun z : {x : A // ∃ j : ℕ, p ^ j • x = 0} => z.val) h))
  have hg' : d + 1 < p ^ (d + 1) := Nat.lt_pow_self (by omega)
  have hg : d < p ^ (d + 1) := by omega
  have hh := hj (d + 1)
  nlinarith

def changePoint {X B C : Scheme.{u}} {t t' : X ⟶ B} {f : C ⟶ B}
    (h : t = t') : SchemeHomOver t f ≃ SchemeHomOver t' f where
  toFun x := ⟨x.val, x.property.trans h⟩
  invFun x := ⟨x.val, x.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma changePoint_mul {R : Type u} [CommRing R] {X C : Scheme.{u}}
    {t t' : X ⟶ Spec (CommRingCat.of R)} {f : C ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) (h : t = t') (x y : SchemeHomOver t f) :
    changePoint h (G.mul t x y) = G.mul t' (changePoint h x) (changePoint h y) := by
  subst t'
  rfl

/-- Geometric elliptic rigidity, using primary Tate sequences and density. -/
lemma field_rigidity (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (G : Law K W) (hG : IsOriginLaw K W G)
    (L : ℕ) (hL : 3 ≤ L) (e : Curve K W ≅ Curve K W)
    (he : e.hom ≫ structureMap K W = structureMap K W)
    (ho : origin K W ≫ e.hom = origin K W)
    (hfix : ∀ x : SchemeHomOver (𝟙 (Base K)) (structureMap K W),
      G.nsmul (𝟙 _) L x = G.one (𝟙 _) → x.val ≫ e.hom = x.val) :
    e.hom = 𝟙 _ := by
  classical
  letI : CommGroup (SchemeHomOver (𝟙 (Base K)) (structureMap K W)) :=
    { G.pointGroup _ with mul_comm := hG.2 _ }
  let A := Additive (SchemeHomOver (𝟙 (Base K)) (structureMap K W))
  let f : PointedMap K W W := ⟨e.hom, he, ho⟩
  have hf := (pointed_relative_group_hom K W G hG W G hG f).1
  let u : AddMonoid.End A := {
    toFun := fun x => Additive.ofMul (mapPoint K W f (𝟙 _) x.toMul)
    map_zero' := by
      apply congrArg Additive.ofMul
      exact PointedRelativeGroupHom.map_one K W W G G hG hG f (𝟙 _)
    map_add' := fun x y => congrArg Additive.ofMul (hf _ _ x.toMul y.toMul) }
  obtain ⟨m, hm, hem⟩ := finite_order K W e he ho
  have hum : u ^ m = 1 := by
    have hp (n : ℕ) (x : A) : ((u ^ n) x).toMul.val = x.toMul.val ≫ (e ^ n).hom := by
      induction n with
      | zero => exact (Category.comp_id _).symm
      | succ n ih =>
        rw [pow_succ']
        change ((u ^ n) x).toMul.val ≫ e.hom = _
        rw [ih, pow_succ' e n]
        exact Category.assoc _ _ _
    apply AddMonoidHom.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hp, hem]
    exact Category.comp_id _
  have hn (n : ℕ) (x : A) : (n • x).toMul = G.nsmul (𝟙 _) n x.toMul := by
    exact (FullLevelTorsionSplittingR0175.nsmul_pow G _ n x.toMul).symm
  obtain ⟨p, a, hp, ha, ha2, hd⟩ := admissible_prime_power L hL
  have hg := relative_curve_geometry K W
  letI := hg.1
  letI := hg.2.1
  letI := hg.2.2.2.2.2.1
  letI : IsProper (structureMap K W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : CompactSpace (Curve K W) := QuasiCompact.compactSpace_of_compactSpace (structureMap K W)
  have hdiv : Function.Surjective (fun x : A => p • x) := by
    have hs := GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
      (toGRJ G) hG.2 p (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero))
    intro x
    obtain ⟨y, hy⟩ := hs x.toMul
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    rw [hn]
    exact (toGRJ_nsmul G _ p y).symm.trans hy
  have hfixp (x : A) (hx : p ^ a • x = 0) : u x = x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply hfix
    obtain ⟨c, hc⟩ := hd
    have hz : L • x = 0 := by rw [hc, mul_comm, mul_smul, hx, smul_zero]
    have hh := congrArg Additive.toMul hz
    rwa [hn] at hh
  let T := {x : A // ∃ j : ℕ, p ^ j • x = 0}
  have ht (x : T) : u x.val = x.val := by
    obtain ⟨j, hj⟩ := x.property
    exact Tate.fixes_primary hp a ha ha2 hdiv u m (by omega) hum hfixp j x.val hj
  have hone : (G.one (𝟙 _)).val = (WeierstrassProjModel.kwZeroSect K W).val := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  obtain ⟨ev, hev, _, _⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G hone
  have hself : (𝟙 (Base K)) = Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
    simp [Algebra.algebraMap_self, Base]
  let ev' : SchemeHomOver (𝟙 (Base K)) (structureMap K W) ≃
      (W.toProjective.baseChange K).toAffine.Point := (changePoint hself).trans (ev K)
  have hevm (x y : SchemeHomOver (𝟙 (Base K)) (structureMap K W)) :
      ev' (G.mul _ x y) = ev' x + ev' y := by
    change ev K (changePoint hself (G.mul _ x y)) = _
    rw [changePoint_mul]
    exact hev.1 K _ _
  let v : A ≃+ (W.toProjective.baseChange K).toAffine.Point := {
    toEquiv := Additive.toMul.trans ev'
    map_add' := fun x y => hevm x.toMul y.toMul }
  letI : (W.toProjective.baseChange K).toAffine.IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  letI : Infinite T := primary_infinite p hp.two_le (fun j => by
    let vj : Submodule.torsionBy ℤ A ((p ^ j : ℕ) : ℤ) ≃
        Submodule.torsionBy ℤ (W.toProjective.baseChange K).toAffine.Point ((p ^ j : ℕ) : ℤ) :=
      Equiv.subtypeEquiv v.toEquiv (fun x => by
        simp only [Submodule.mem_torsionBy_iff]
        change _ ↔ _ • v x = 0
        rw [← map_zsmul, map_eq_zero_iff v v.injective])
    exact (Nat.card_congr vj).trans (WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange K).toAffine
      (Nat.cast_ne_zero.mpr (pow_ne_zero j hp.ne_zero)) (by norm_num)))
  apply ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.CurveDensity.eq_of_infinite_sections
    K (structureMap K W) (structureMap K W) e.hom (𝟙 _) (by simpa using he)
    (fun x : T => x.val.toMul.val) (fun x => x.val.toMul.property)
  · intro x y hxy
    apply Subtype.ext
    apply Additive.toMul.injective
    exact Subtype.ext hxy
  · intro x
    have hh := congrArg (fun y : A => y.toMul.val) (ht x)
    change x.val.toMul.val ≫ e.hom = x.val.toMul.val at hh
    simpa only [Category.comp_id] using hh

end ArithmeticThetaLegendreAtlasR0176.FullLevelAutomorphismRigidity

namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaRelativeKatoNaturalityR0170
open FullLevelAutomorphismRigidity

/-- Full-level pointed automorphism rigidity over the specified rational base. -/
theorem full_level_automorphism_rigidity :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (e : CategoryTheory.Iso (ArithmeticThetaRelativeKatoR0169.Curve R W) (ArithmeticThetaRelativeKatoR0169.Curve R W)), CategoryTheory.CategoryStruct.comp (e.hom) (ArithmeticThetaRelativeKatoR0169.structureMap R W) = ArithmeticThetaRelativeKatoR0169.structureMap R W → CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin R W) (e.hom) = ArithmeticThetaRelativeKatoR0169.origin R W → CategoryTheory.CategoryStruct.comp (M.x.val) (e.hom) = M.x.val → CategoryTheory.CategoryStruct.comp (M.y.val) (e.hom) = M.y.val → e.hom = CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeKatoR0169.Curve R W) := by
  intro R _ _ _ _ _ W _ G hG L hL M e he ho hx hy
  classical
  let K := AlgebraicClosure (FractionRing R)
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  letI : CharZero K := Algebra.charZero_of_charZero (FractionRing R) K
  let t := baseMap R K (algebraMap R K)
  let Mk := BaseChange.restrict M t (Category.comp_id _)
  obtain ⟨H, b, hH, hb, _⟩ := NormalAffineExtensionR0175.change_ring
    R W G hG K (algebraMap R K) L Mk
  let Wk := W.map (algebraMap R K)
  let ek := liftIso R W Wk t b hb.1 e he
  have hek : ek.hom ≫ structureMap K Wk = structureMap K Wk :=
    liftIso_over R W Wk t b hb.1 e he
  have hok : origin K Wk ≫ ek.hom = origin K Wk :=
    liftIso_origin R W Wk t b hb.1 hb.2.1 e he ho
  have hcomp : ek.hom ≫ b = b ≫ e.hom := liftIso_comp R W Wk t b hb.1 e he
  have hid : ek.hom = 𝟙 _ := by
    apply field_rigidity K Wk H hH L hL ek hek hok
    intro x hk
    let y : SchemeHomOver t (structureMap R W) := ⟨x.val ≫ b, by
      rw [Category.assoc, hb.1.w, ← Category.assoc, x.property, Category.id_comp]
      rfl⟩
    have hyk : G.nsmul t L y = G.one t := by
      apply Subtype.ext
      rw [FullLevelTorsionSplittingR0175.nsmul_val]
      change (x.val ≫ b) ≫ G.schemeNsmul L = _
      rw [Category.assoc, ← hb.2.2 L, ← Category.assoc,
        ← FullLevelTorsionSplittingR0175.nsmul_val H, hk,
        hH.1, Category.id_comp, hb.2.1, hG.1]
      rfl
    have hfixed := torsion_point_fixed R W G hG M
      (⟨e.hom, he, ho⟩ : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W W)
      hx hy (by omega) t y hyk
    apply hb.1.hom_ext
    · rw [Category.assoc, hcomp]
      exact hfixed
    · rw [Category.assoc, hek]
  have hg := relative_curve_geometry R W
  letI := hg.1
  letI := hg.2.1
  letI := hg.2.2.2.1
  letI := hg.2.2.2.2.1
  have hgk := relative_curve_geometry K Wk
  letI := hgk.1
  letI := hgk.2.1
  letI : IsProper (structureMap R W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : Module.Flat R K := Module.Flat.trans R (FractionRing R) K
  letI : Flat t := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) := ‹Flat t›
  letI : Flat b := MorphismProperty.of_isPullback (P := @Flat) hb.1.flip inferInstance
  letI : IsDominant b := by
    constructor
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure (Curve R W)]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr ⟨genericPoint (Curve K Wk),
      GenericComparisonProof.generic_eq_of_flat b⟩
  apply ext_of_isDominant_of_isSeparated (structureMap R W) (by simpa using he) b
  rw [← hcomp, hid, Category.id_comp, Category.comp_id]

#print axioms full_level_automorphism_rigidity
end ArithmeticThetaLegendreAtlasR0176
