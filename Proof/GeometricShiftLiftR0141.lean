module

import all GenericThetaBasisR0140

public import GeometricThetaLiftsDefinitionsR0141
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.proofsInPublic true

@[expose] public section

/-! The unique normalized geometric shift lift over the actual generic Tate model.
Finite-chart factorization, proper completion, and generic normalization construct
the morphism; the geometric period and exact theta action prove invertibility. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
  (pulledInclusion)
open ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

@[simp] lemma genericMap_inclusion (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) :
    genericMap k M f hf ≫ genericInclusion k M = genericInclusion k M ≫ f := by
  exact pullback.lift_fst _ _ _

@[simp] lemma genericMap_structure (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) :
    genericMap k M f hf ≫ genericStructure k M = genericStructure k M := by
  exact pullback.lift_snd _ _ _

lemma genericMap_id : genericMap k M (𝟙 M.X) (Category.id_comp M.p) = 𝟙 _ := by
  apply pullback.hom_ext
  · change genericMap k M _ _ ≫ genericInclusion k M = _
    rw [genericMap_inclusion, Category.comp_id, Category.id_comp]
    rfl
  · change genericMap k M _ _ ≫ genericStructure k M = _
    rw [genericMap_structure, Category.id_comp]
    rfl

lemma genericMap_comp (f g : M.X ⟶ M.X)
    (hf : f ≫ M.p = M.p) (hg : g ≫ M.p = M.p) :
    genericMap k M (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      genericMap k M f hf ≫ genericMap k M g hg := by
  apply pullback.hom_ext <;>
    simp [genericMap, genericInclusion, genericStructure, Category.assoc]

/-- Base change retains the actual automorphism and its actual inverse. -/
def genericIso (f : M.X ≅ M.X) (hf : f.hom ≫ M.p = M.p) :
    genericScheme k M ≅ genericScheme k M where
  hom := genericMap k M f.hom hf
  inv := genericMap k M f.inv (by
    calc f.inv ≫ M.p = f.inv ≫ (f.hom ≫ M.p) := congrArg (f.inv ≫ ·) hf.symm
         _ = M.p := f.inv_hom_id_assoc M.p)
  hom_inv_id := by
    rw [← genericMap_comp]
    simpa using genericMap_id k M
  inv_hom_id := by
    rw [← genericMap_comp]
    simpa using genericMap_id k M

variable (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X))
  (inv : M.X ≅ M.X) (ha : Actions k M rot scal inv)

/-- The specified shift, without replacing its underlying morphism. -/
def shiftIso : genericScheme k M ≅ genericScheme k M :=
  let e := genericIso k M rot (modelOver k M (next r hr) 1 false rot ha.1)
  e ≪≫ e

lemma shiftIso_hom : (shiftIso k M rot scal inv ha).hom =
    shiftMap k M rot scal inv ha := rfl

lemma shiftMap_isIso : IsIso (shiftMap k M rot scal inv ha) := by
  change IsIso (shiftIso k M rot scal inv ha).hom
  infer_instance

lemma shiftMap_inclusion :
    shiftMap k M rot scal inv ha ≫ genericInclusion k M =
      genericInclusion k M ≫ rot.hom ≫ rot.hom := by
  simp [shiftMap, Category.assoc]

lemma shiftMap_structure :
    shiftMap k M rot scal inv ha ≫ genericStructure k M = genericStructure k M := by
  simp [shiftMap, Category.assoc]

include scal inv ha in
/-- The actual identity section moves twice around the prescribed polygon. -/
lemma shift_marked (h3 : 3 ≤ r) (hM : IsModel k T M)
    (i : Fin r) (b : kˣ) (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M i b s) :
    MarkedLift k M (next r hr (next r hr i)) b ((s ≫ rot.hom) ≫ rot.hom) := by
  have ht := algebraized_marked_transport k r hr h3 T M hM rot scal inv ha
  exact (ht (next r hr i) b (s ≫ rot.hom) (ht i b s hs).1).1

omit rot scal inv ha in
lemma genericMap_point (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) :
    genericPoint k M s hs ≫ genericMap k M f hf =
      genericPoint k M (s ≫ f) (by rw [Category.assoc, hf, hs]) := by
  apply pullback.hom_ext <;>
    simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericMap, genericInclusion, genericStructure, Category.assoc]


local instance dualAdd (s : baseScheme k ⟶ M.X) (d : ℕ) :
    AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

lemma scalarAt_top (c : LaurentSeries k) : scalarAt k M ⊤ c =
    (genericStructure k M).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c) := by
  unfold scalarAt
  dsimp only [genericScheme, genericStructure]
  erw [CategoryTheory.Functor.map_id]
  rfl

section SectionAction
variable (s : baseScheme k ⟶ M.X) (d : ℕ)
  (f : genericScheme k M ⟶ genericScheme k M)
  (hf : f ≫ genericStructure k M = genericStructure k M)

include hf in
lemma scalarTop_fixed (c : LaurentSeries k) :
    f.appTop (scalarAt k M ⊤ c) = scalarAt k M ⊤ c := by
  have h := congrArg Scheme.Hom.appTop hf
  rw [Scheme.Hom.comp_appTop] at h
  have hc := ConcreteCategory.congr_hom h
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv c)
  rw [scalarAt_top]
  exact hc

lemma scale_scalarAt_app (c : LaurentSeries k) (φ : GenericDual k M s d)
    (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)) :
    (scale (scalarAt k M ⊤ c) φ).app U x = scalarAt k M U c *
      (show Γ(genericScheme k M, U) from φ.app U x) := by
  rw [scale_app]
  rw [scalarAt_top]
  rfl

include hf in
/-- Linearity follows from genuine pullback and the structural scalar map. -/
lemma act_scale (e : Lift k M s d f) (c : LaurentSeries k)
    (φ : GenericDual k M s d) :
    act k M s d f e (scale (scalarAt k M ⊤ c) φ) =
      scale (scalarAt k M ⊤ c) (act k M s d f e φ) := by
  change e.hom ≫ pulledInclusion f (scale _ φ) = _
  rw [pull_scale, scalarTop_fixed k M f hf, scale_precomp]
  rfl

lemma act_sum (e : Lift k M s d f) {ι : Type*} (S : Finset ι)
    (φ : ι → GenericDual k M s d) :
    act k M s d f e (∑ i ∈ S, φ i) = ∑ i ∈ S, act k M s d f e (φ i) := by
  change e.hom ≫ pulledInclusion f (∑ i ∈ S, φ i) = _
  rw [pull_sum]
  dsimp only [GenericDual] at φ
  simp only [Preadditive.comp_sum]
  rfl

lemma combines_iff (m : ℕ) (b : Fin m → GenericDual k M s d)
    (c : Fin m → LaurentSeries k) (φ : GenericDual k M s d) :
    Combines k M s d m b c φ ↔ φ = ∑ ν, scale (scalarAt k M ⊤ (c ν)) (b ν) := by
  constructor
  · intro h
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    rw [sum_app]
    change φ.app U x = _
    rw [h U x]
    apply Finset.sum_congr rfl
    intro ν _
    exact (scale_scalarAt_app k M s d (c ν) (b ν) U x).symm
  · intro h U x
    rw [h, sum_app]
    apply Finset.sum_congr rfl
    intro ν _
    exact scale_scalarAt_app k M s d (c ν) (b ν) U x

include hf in
lemma act_eq_of_basis (m : ℕ) (b : Fin m → GenericDual k M s d)
    (hb : HasBasis k M s d m b) (e e' : Lift k M s d f)
    (h : ∀ ν, act k M s d f e (b ν) = act k M s d f e' (b ν))
    (φ : GenericDual k M s d) : act k M s d f e φ = act k M s d f e' φ := by
  obtain ⟨c, hc, -⟩ := hb φ
  rw [(combines_iff k M s d m b c φ).mp hc]
  rw [act_sum, act_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [act_scale k M s d f hf, act_scale k M s d f hf, h]

end SectionAction

open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (idealPullbackIso idealPullbackIso_inclusion compIso compIso_inclusion)
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
  (idealInclusion idealModule)

lemma genericBase_open : IsOpenImmersion (genericBase k) :=
  IsOpenImmersion.of_isLocalization (PowerSeries.X : PowerSeries k)

lemma genericInclusion_open : IsOpenImmersion (genericInclusion k M) := by
  letI := genericBase_open k
  exact inferInstanceAs (IsOpenImmersion (pullback.fst M.p (genericBase k)))

lemma pulled_ideal_mono {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (I : Y.IdealSheafData) (hI : I.IsInvertible) :
    Mono (pulledInclusion g (idealInclusion I)) := by
  have hJ := hI.comap_of_isOpenImmersion g
  letI : Mono (I.comap g).moduleι :=
    (ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.ideal_realization _).1
  change Mono ((Scheme.Modules.pullback g).map I.moduleι ≫ unitPullback g)
  rw [← idealPullbackIso_inclusion g I (I.comap g) hI hJ rfl]
  infer_instance

/-- The pullback of the canonical ideal inclusion separates two candidate lifts.
This is an equality of sheaf morphisms, not just of their coefficient matrices. -/
lemma lift_ext (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (f : genericScheme k M ⟶ genericScheme k M) [IsIso f]
    (e e' : Lift k M s d f)
    (h : ∀ φ, act k M s d f e φ = act k M s d f e' φ) : e = e' := by
  let j := idealInclusion (s.ker ^ d)
  let c := genericInclusion k M
  letI : IsOpenImmersion c := genericInclusion_open k M
  have hI := AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d
  letI : Mono (pulledInclusion (f ≫ c) j) := pulled_ideal_mono (f ≫ c) _ hI
  have hh := compIso_inclusion f c (f ≫ c) rfl (powerModule k M s d) j
  haveI : Mono (pulledInclusion f (pulledInclusion c j)) := by
    rw [← hh]
    infer_instance
  apply Iso.ext
  apply (cancel_mono (pulledInclusion f (pulledInclusion c j))).mp
  exact h (restrictDual k M s d j)

lemma lift_unique_of_basis (h3 : 3 ≤ r) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d m : ℕ) (f : genericScheme k M ⟶ genericScheme k M) [IsIso f]
    (hf : f ≫ genericStructure k M = genericStructure k M)
    (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    (e e' : Lift k M s d f)
    (h : ∀ ν, act k M s d f e (b ν) = act k M s d f e' (b ν)) : e = e' :=
  lift_ext k M h3 hM s hs d f e e' (act_eq_of_basis k M s d f hf m b hb e e' h)


section NormalizedShift
variable (m : ℕ) (hm : 0 < m) (he : Even m)
  {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
  (MM : Model k TT) (hMM : IsModel k TT MM)
  (ss : baseScheme k ⟶ MM.X)
  (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
  (rr : MM.X ≅ MM.X) (aa : kˣ → (MM.X ≅ MM.X))
  (ii : MM.X ≅ MM.X) (hh : Actions k MM rr aa ii)

/-- Uniqueness in the frozen obligation, with every geometric provider proved.
No existence of a lift or divisor equivalence is used to produce one. -/
lemma cyclic_lift_unique
    (e e' : Lift k MM ss m (shiftMap k MM rr aa ii hh))
    (heB : Cyclic k MM ss m m hm (shiftMap k MM rr aa ii hh) e
      (genericTheta k m hm he MM hMM ss hss))
    (heB' : Cyclic k MM ss m m hm (shiftMap k MM rr aa ii hh) e'
      (genericTheta k m hm he MM hMM ss hss)) : e = e' := by
  letI := shiftMap_isIso k MM rr aa ii hh
  apply lift_unique_of_basis k MM (thetaChartBound m hm he) hMM ss hss m m
    (shiftMap k MM rr aa ii hh) (shiftMap_structure k MM rr aa ii hh)
    (genericTheta k m hm he MM hMM ss hss)
    (generic_theta_basis k m hm he TT MM hMM ss hss) e e'
  intro ν
  exact (heB ν).trans (heB' ν).symm

end NormalizedShift


namespace CompletedShift
open ArithmeticThetaScaledAnnularR0050
open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaAnnularThetaR0128 (thetaSection shift)

lemma xy : cx k 1 * cy k 1 = tau k 1 := by
  have hn : x k 1 * y k 1 = t k 1 := by
    have hh : quotientMap k 1 (relation k 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    exact sub_eq_zero.mp hh
  have hh := congrArg (toCompleted k 1) hn
  simp only [map_mul, t, ArithmeticThetaScaledTateBridgeR0046.parameter, pow_one] at hh
  exact hh

lemma term_nonpos (j : ℕ) (b : ℤ) (hb : b ≤ 0) :
    thetaTerm k 1 1 j b = tau k 1 ^ (thetaExponent 1 1 j b).toNat * cy k 1 ^ (-b).toNat := by
  unfold thetaTerm
  split_ifs with h
  · have : b = 0 := by omega
    subst b
    simp
  · rfl

/-- Exact one-step residue shift on individual completed-node summands.
The extra powers only clear the two chart-dependent normalizations. -/
lemma term_shift (j : ℕ) (b : ℤ) :
    tau k 1 ^ shift (j+2) * thetaTerm k 1 1 j (b+1) =
      tau k 1 ^ (shift j + j + 1) * cx k 1 * thetaTerm k 1 1 (j+2) b := by
  have he := (theta_exponent_control 1 1 j (by decide) (by decide)).1 (b+1)
  have he' := (theta_exponent_control 1 1 (j+2) (by decide) (by decide)).1 b
  by_cases hb : 0 ≤ b
  · have hb' : 0 ≤ b+1 := by omega
    have hexp : shift (j+2) + (thetaExponent 1 1 j (b+1)).toNat =
        shift j + j + 1 + (thetaExponent 1 1 (j+2) b).toNat := by
      have hh : (shift (j+2) : ℤ) + thetaExponent 1 1 j (b+1) =
          (shift j : ℤ) + j + 1 + thetaExponent 1 1 (j+2) b := by
        simp only [shift, thetaExponent, if_pos hb, if_pos hb',
          Nat.cast_add, Nat.cast_ofNat]
        ring
      omega
    have hbN : (b+1).toNat = b.toNat + 1 := by omega
    simp only [thetaTerm, if_pos hb, if_pos hb', hbN, pow_succ]
    calc
      _ = tau k 1 ^ (shift (j+2) + (thetaExponent 1 1 j (b+1)).toNat) *
          (cx k 1 ^ b.toNat * cx k 1) := by rw [pow_add]; ring
      _ = _ := by rw [hexp, pow_add]; ring
  · have hb' : b+1 ≤ 0 := by omega
    have hexp : shift (j+2) + (thetaExponent 1 1 j (b+1)).toNat =
        shift j + j + 1 + (thetaExponent 1 1 (j+2) b).toNat + 1 := by
      have hh : (shift (j+2) : ℤ) + thetaExponent 1 1 j (b+1) =
          (shift j : ℤ) + j + 1 + thetaExponent 1 1 (j+2) b + 1 := by
        by_cases hz : b+1 = 0
        · have : b = -1 := by omega
          subst b
          norm_num [shift, thetaExponent]
          ring
        · have hn : ¬ 0 ≤ b+1 := by omega
          simp only [shift, thetaExponent, if_neg hb, if_neg hn, one_mul,
            Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
      omega
    have hbN : (-b).toNat = (-(b+1)).toNat + 1 := by omega
    rw [term_nonpos k j (b+1) hb', term_nonpos k (j+2) b (by omega), hbN, pow_succ]
    calc
      _ = tau k 1 ^ (shift (j+2) + (thetaExponent 1 1 j (b+1)).toNat) *
          cy k 1 ^ (-(b+1)).toNat := by rw [pow_add]; ring
      _ = tau k 1 ^ (shift j + j + 1) * tau k 1 ^ (thetaExponent 1 1 (j+2) b).toNat *
          (cx k 1 * cy k 1) * cy k 1 ^ (-(b+1)).toNat := by
        rw [hexp, pow_succ, pow_add, xy]
      _ = _ := by ring


lemma residue_shift (m : ℕ) (hm : 0 < m) (ν : Fin m) (b : ℤ) :
    b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) ↔
      (b+1) % (m : ℤ) = ((next m hm ν).val : ℤ) % (m : ℤ) := by
  have hn : Int.ModEq (m : ℤ) ((ν.val : ℤ)+1) ((next m hm ν).val : ℤ) := by
    simp [Int.ModEq, ArithmeticThetaInfinitesimalPolygonR0129.next, Int.natCast_emod]
  constructor
  · intro h
    exact (Int.ModEq.add_right 1 h).trans hn
  · intro h
    have hh := Int.ModEq.sub (Int.ModEq.trans h hn.symm) (Int.ModEq.refl (n := (m : ℤ)) 1)
    simpa only [Int.ModEq, add_sub_cancel_right] using hh

private lemma sum_translate {R : Type*} [AddCommMonoid R]
    (G : ℤ → R) (a b : ℤ) :
    (∑ z ∈ Finset.Icc a b, G (z+1)) = ∑ z ∈ Finset.Icc (a+1) (b+1), G z := by
  apply Finset.sum_bij (fun z _ => z+1)
  · intro z hz
    simp only [Finset.mem_Icc] at hz ⊢
    omega
  · intro z hz w hw h
    omega
  · intro z hz
    refine ⟨z-1, ?_, by omega⟩
    simp only [Finset.mem_Icc] at hz ⊢
    omega
  · intros; rfl

lemma partial_shift {R : Type*} [CommRing R] (π : CompletedNode k 1 →+* R)
    (m : ℕ) (hm : 0 < m) (j : ℕ) (ν : Fin m) (n N : ℕ)
    (hN : n + 2*(j+1) + 2 ≤ N)
    (htail : ∀ b : ℤ, b < -((n + 2*(j+1) + 1 : ℕ) : ℤ) →
      π (thetaTerm k 1 1 j b) = 0) :
    π (tau k 1) ^ shift (j+2) *
        π (thetaPartial k 1 m 1 j ((next m hm ν).val : ℤ) (N+1)) =
      π (tau k 1) ^ (shift j + j + 1) * π (cx k 1) *
        π (thetaPartial k 1 m 1 (j+2) (ν.val : ℤ) N) := by
  classical
  let G : ℤ → R := fun b => if b % (m : ℤ) = ((next m hm ν).val : ℤ) % (m : ℤ)
    then π (tau k 1) ^ shift (j+2) * π (thetaTerm k 1 1 j b) else 0
  have hterm (b : ℤ) :
      π (tau k 1) ^ (shift j + j + 1) * π (cx k 1) *
        (if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ)
          then π (thetaTerm k 1 1 (j+2) b) else 0) = G (b+1) := by
    dsimp only [G]
    simp only [← residue_shift m hm ν b]
    split_ifs
    · symm
      simpa only [map_mul, map_pow] using congrArg π (term_shift k j b)
    · simp
  symm
  simp only [mul_ite, mul_zero] at hterm
  simp only [thetaPartial, map_sum, apply_ite, map_zero, Finset.mul_sum, mul_zero]
  change (∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) then
      π (tau k 1) ^ (shift j+j+1) * π (cx k 1) * π (thetaTerm k 1 1 (j+2) b) else 0) =
    ∑ b ∈ Finset.Icc (-((N+1 : ℕ) : ℤ)) ((N+1 : ℕ) : ℤ), G b
  simp_rw [hterm]
  rw [sum_translate]
  apply Finset.sum_subset
  · intro b hb
    simp only [Finset.mem_Icc, Nat.cast_add, Nat.cast_one] at hb ⊢
    constructor <;> omega
  · intro b hb hnb
    have hl : b < -((n + 2*(j+1) + 1 : ℕ) : ℤ) := by
      simp only [Finset.mem_Icc, Nat.cast_add, Nat.cast_one] at hb hnb
      omega
    simp [G, htail b hl]

/-- The full completed theta sections obey the exact shift identity.
The proof passes through every adic quotient, so no truncation is left unproved. -/
lemma theta_shift (m : ℕ) (hm : 0 < m) (he : Even m) (j : ℕ) (ν : Fin m) :
    tau k 1 ^ shift (j+2) * thetaSection k m hm he j (next m hm ν) =
      tau k 1 ^ (shift j+j+1) * cx k 1 * thetaSection k m hm he (j+2) ν := by
  let J : Ideal (CompletedNode k 1) := Ideal.span {completedParameter k 1}
  letI : IsAdicComplete J (CompletedNode k 1) := theta_completed_adic k 1
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  let π := Ideal.Quotient.mk (J^n)
  let N := n + 2*(j+3) + 2
  have hlim (i : ℕ) (μ : Fin m) : ThetaLimit k 1 m 1 i (μ.val : ℤ)
      (thetaSection k m hm he i μ) :=
    (Classical.choose_spec (theta_completed_limit k 1 m 1 i (μ.val : ℤ)
      (by decide) hm he (by decide))).1
  have hL : π (thetaSection k m hm he j (next m hm ν)) =
      π (thetaPartial k 1 m 1 j ((next m hm ν).val : ℤ) (N+1)) :=
    Ideal.Quotient.eq.mpr (hlim j (next m hm ν) n (N+1) (by dsimp [N]; omega))
  have hR : π (thetaSection k m hm he (j+2) ν) =
      π (thetaPartial k 1 m 1 (j+2) (ν.val : ℤ) N) :=
    Ideal.Quotient.eq.mpr (hlim (j+2) ν n N (by dsimp [N]; omega))
  change π _ = π _
  simp only [map_mul, map_pow, hL, hR]
  apply partial_shift k π m hm j ν n N (by dsimp [N]; omega)
  intro b hb
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact theta_term_tail k 1 1 j n (by decide) (by decide) b (Or.inl (by simpa using hb))


lemma tau_ne_zero : tau k 1 ≠ 0 := by
  intro hz
  have h := (specialization_coordinates k 1 0 (by decide) (by decide)
    (1 : k) one_ne_zero).1
  rw [hz, map_zero] at h
  exact PowerSeries.X_ne_zero h.symm

lemma uniform_basis (m : ℕ) (hm : 0 < m) (he : Even m) (i : Fin (2*m)) (ν : Fin m) :
    ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) i =
      tau k 1 ^ (ArithmeticThetaAnnularThetaR0128.commonShift m - shift i.val) *
        thetaSection k m hm he i.val ν := by
  classical
  unfold ArithmeticThetaAnnularThetaR0128.uniformSection
  congr 1
  simp only [ArithmeticThetaAnnularThetaR0128.combine, thetaVector,
    apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- On an interior pair of charts the common clearing factor cancels exactly. -/
lemma uniform_shift (m : ℕ) (hm : 0 < m) (he : Even m)
    (i : Fin (2*m)) (hi : i.val+2 < 2*m) (ν : Fin m) :
    ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
        (thetaVector k m (next m hm ν)) i =
      tau k 1 ^ (i.val+1) * cx k 1 *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
          (thetaVector k m ν) ⟨i.val+2, hi⟩ := by
  letI : IsDomain (CompletedNode k 1) := (completed_node_normal_domain k 1 (by decide)).1
  rw [uniform_basis, uniform_basis]
  let C := ArithmeticThetaAnnularThetaR0128.commonShift m
  have ha : shift i.val ≤ C := by
    dsimp [shift, thetaShift, C, ArithmeticThetaAnnularThetaR0128.commonShift]
    have := i.isLt
    nlinarith
  have hb : shift (i.val+2) ≤ C := by
    dsimp [shift, thetaShift, C, ArithmeticThetaAnnularThetaR0128.commonShift]
    nlinarith
  apply mul_left_cancel₀ (pow_ne_zero (shift i.val + shift (i.val+2)) (tau_ne_zero k))
  have h := congrArg (fun z => tau k 1 ^ C * z) (theta_shift k m hm he i.val ν)
  convert h using 1
  · rw [← mul_assoc, ← pow_add]
    rw [show shift i.val + shift (i.val+2) + (C-shift i.val) =
      C + shift (i.val+2) by omega, pow_add, mul_assoc]
  · calc
      _ = tau k 1 ^ (shift i.val + shift (i.val+2) + (i.val+1) + (C-shift (i.val+2))) *
          cx k 1 * thetaSection k m hm he (i.val+2) ν := by simp only [pow_add]; ring
      _ = _ := by
        rw [show shift i.val + shift (i.val+2) + (i.val+1) + (C-shift (i.val+2)) =
          C + (shift i.val + i.val+1) by omega, pow_add]
        ring


/-- The actual local multiplier, with one uniform vertical denominator cleared. -/
def interiorMultiplier (m : ℕ) (hm : 0 < m) (i : Fin (2*m))
    (hi : i.val+2 < 2*m) : CompletedNode k 1 :=
  tau k 1 ^ (i.val+1) * cx k 1 *
    (↑(gammaTail k (2*m) (Nat.mul_pos (by decide) hm) ⟨i.val+2, hi⟩ *
      (gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i)⁻¹) : CompletedNode k 1)^m

lemma numerator_shift (m : ℕ) (hm : 0 < m) (he : Even m)
    (i : Fin (2*m)) (hi : i.val+2 < 2*m) (ν : Fin m) :
    tau k 1 ^ m * thetaNumerator k m hm he (thetaVector k m (next m hm ν)) i =
      interiorMultiplier k m hm i hi *
        thetaNumerator k m hm he (thetaVector k m ν) ⟨i.val+2, hi⟩ := by
  have hm2 : 2*(m/2) = m := Nat.mul_div_cancel' he.two_dvd
  have hexp : m + i.val*(m/2) = (i.val+2)*(m/2) := by rw [Nat.add_mul, hm2, Nat.add_comm]
  let a := gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i
  let b := gammaTail k (2*m) (Nat.mul_pos (by decide) hm) ⟨i.val+2, hi⟩
  have hb : (b : CompletedNode k 1)^m * (↑b⁻¹ : CompletedNode k 1)^m = 1 := by
    rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
  unfold thetaNumerator
  rw [uniform_shift k m hm he i hi ν]
  change tau k 1 ^ m *
    (tau k 1 ^ (i.val*(m/2)) * cx k 1 ^ (m/2) *
      (tau k 1 ^ (i.val+1) * cx k 1 *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) ⟨i.val+2,hi⟩) *
      (↑a⁻¹ : CompletedNode k 1)^m) = _
  unfold interiorMultiplier
  change _ = tau k 1 ^ (i.val+1) * cx k 1 * (↑(b*a⁻¹) : CompletedNode k 1)^m *
    (tau k 1 ^ ((i.val+2)*(m/2)) * cx k 1 ^ (m/2) *
      ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) ⟨i.val+2,hi⟩ *
      (↑b⁻¹ : CompletedNode k 1)^m)
  rw [Units.val_mul, mul_pow]
  calc
    _ = tau k 1 ^ (m+i.val*(m/2)) * cx k 1 ^ (m/2) * tau k 1 ^ (i.val+1) * cx k 1 *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) ⟨i.val+2,hi⟩ *
        (↑a⁻¹ : CompletedNode k 1)^m := by rw [pow_add]; ring
    _ = tau k 1 ^ ((i.val+2)*(m/2)) * cx k 1 ^ (m/2) * tau k 1 ^ (i.val+1) * cx k 1 *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) ⟨i.val+2,hi⟩ *
        (↑a⁻¹ : CompletedNode k 1)^m *
        ((b : CompletedNode k 1)^m * (↑b⁻¹ : CompletedNode k 1)^m) := by rw [hb, mul_one, hexp]
    _ = _ := by ring


lemma uniform_iterate (m : ℕ) (hm : 0 < m) (he : Even m) (n : ℕ)
    (i : Fin (2*m)) (hi : i.val+2*n < 2*m) (ν : Fin m) :
    ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
        (thetaVector k m ((next m hm)^[n] ν)) i =
      tau k 1 ^ (n*(i.val+n)) * cx k 1 ^ n *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
          (thetaVector k m ν) ⟨i.val+2*n, hi⟩ := by
  induction n generalizing i with
  | zero => simp only [Function.iterate_zero_apply, Nat.zero_mul, pow_zero, one_mul,
      Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hi2 : i.val+2 < 2*m := by omega
    have hi' : (i.val+2)+2*n < 2*m := by omega
    rw [Function.iterate_succ_apply', uniform_shift k m hm he i hi2]
    rw [ih ⟨i.val+2, hi2⟩ hi']
    have heq : (⟨i.val+2+2*n,hi'⟩ : Fin (2*m)) = ⟨i.val+2*(n+1),hi⟩ := by
      apply Fin.ext
      change i.val+2+2*n = i.val+2*(n+1)
      omega
    rw [heq]
    dsimp only [Fin.val_mk]
    have hexp : i.val+1 + n*(i.val+2+n) = (n+1)*(i.val+(n+1)) := by ring
    calc
      _ = tau k 1 ^ (i.val+1 + n*(i.val+2+n)) * cx k 1 ^ (n+1) *
          ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
            (thetaVector k m ν) ⟨i.val+2*(n+1),hi⟩ := by rw [pow_add, pow_succ]; ring
      _ = _ := by rw [hexp]

lemma wrap_first_bound (m : ℕ) (hm : 0 < m) (l : Fin 2) : l.val < 2*m := by
  have := l.isLt
  omega

lemma wrap_last_bound (m : ℕ) (hm : 0 < m) (l : Fin 2) : l.val+2*(m-1) < 2*m := by
  have := l.isLt
  omega

/-- The two wraparound charts follow from the checked interior identities;
all residue arithmetic is cyclic in the prescribed `next` permutation. -/
lemma uniform_wrap (m : ℕ) (hm : 0 < m) (he : Even m)
    (l : Fin 2) (ν : Fin m) :
    let hlast := wrap_last_bound m hm l
    let hfirst := wrap_first_bound m hm l
    tau k 1 ^ ((m-1)*(l.val+m)) *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
          (thetaVector k m (next m hm ν)) ⟨l.val+2*(m-1), hlast⟩ =
      cy k 1 ^ (m-1) *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
          (thetaVector k m ν) ⟨l.val,hfirst⟩ := by
  dsimp only
  have hfirst : l.val < 2*m := by have := l.isLt; omega
  have hlast : l.val+2*(m-1) < 2*m := by have := l.isLt; omega
  have hh := uniform_iterate k m hm he (m-1) ⟨l.val,hfirst⟩ hlast (next m hm ν)
  have hn : (next m hm)^[m-1] (next m hm ν) = ν := by
    rw [← Function.iterate_succ_apply, show (m-1).succ = m by omega]
    exact AlgebraizedActionLawsR0137.next_period ν
  rw [hn] at hh
  rw [hh]
  have heq : (m-1)*(l.val+m) = (m-1)*(l.val+(m-1)) + (m-1) := by
    have hmp : l.val+m = (l.val+(m-1))+1 := by omega
    rw [hmp, Nat.mul_add, Nat.mul_one]
  rw [heq, pow_add]
  have hxy : cx k 1 ^ (m-1) * cy k 1 ^ (m-1) = tau k 1 ^ (m-1) := by rw [← mul_pow, xy]
  rw [← hxy]
  ring


lemma numerator_wrap (m : ℕ) (hm : 0 < m) (he : Even m)
    (l : Fin 2) (ν : Fin m) :
    let hlast := wrap_last_bound m hm l
    let hfirst := wrap_first_bound m hm l
    let i : Fin (2*m) := ⟨l.val+2*(m-1), hlast⟩
    let j : Fin (2*m) := ⟨l.val,hfirst⟩
    tau k 1 ^ m * thetaNumerator k m hm he (thetaVector k m (next m hm ν)) i =
      tau k 1 ^ (m-l.val*(m-1)) * cy k 1 ^ (m-1) *
        (↑(gammaTail k (2*m) (Nat.mul_pos (by decide) hm) j *
          (gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i)⁻¹) : CompletedNode k 1)^m *
        thetaNumerator k m hm he (thetaVector k m ν) j := by
  dsimp only
  have hfirst : l.val < 2*m := by have := l.isLt; omega
  have hlast : l.val+2*(m-1) < 2*m := by have := l.isLt; omega
  let i : Fin (2*m) := ⟨l.val+2*(m-1), hlast⟩
  let j : Fin (2*m) := ⟨l.val,hfirst⟩
  let a := gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i
  let b := gammaTail k (2*m) (Nat.mul_pos (by decide) hm) j
  let E := (m-1)*(l.val+m)
  let p := m-l.val*(m-1)
  have hm2 : 2*(m/2) = m := Nat.mul_div_cancel' he.two_dvd
  have hl : l.val*(m-1) ≤ m := by
    have : l.val ≤ 1 := by have := l.isLt; omega
    exact (Nat.mul_le_mul_right (m-1) this).trans (by omega)
  have hexp : m + i.val*(m/2) = p + j.val*(m/2) + E := by
    have hp : p + l.val*(m-1) = m := Nat.sub_add_cancel hl
    dsimp only [i, j, E, Fin.val_mk]
    nlinarith [Nat.mul_sub_left_distrib 2 m 1,
      show 2*(m-1)*(m/2) = (m-1)*m by nlinarith [congrArg ((m-1)*·) hm2]]
  have hb : (b : CompletedNode k 1)^m * (↑b⁻¹ : CompletedNode k 1)^m = 1 := by
    rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
  have hw : tau k 1 ^ E *
      ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m (next m hm ν)) i =
    cy k 1 ^ (m-1) *
      ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) j :=
    uniform_wrap k m hm he l ν
  change tau k 1 ^ m * thetaNumerator k m hm he (thetaVector k m (next m hm ν)) i = _
  unfold thetaNumerator
  change tau k 1 ^ m * (tau k 1 ^ (i.val*(m/2)) * cx k 1 ^ (m/2) *
    ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m (next m hm ν)) i *
    (↑a⁻¹ : CompletedNode k 1)^m) = tau k 1 ^ p * cy k 1 ^ (m-1) * (↑(b*a⁻¹) : CompletedNode k 1)^m *
      (tau k 1 ^ (j.val*(m/2)) * cx k 1 ^ (m/2) *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m ν) j *
        (↑b⁻¹ : CompletedNode k 1)^m)
  rw [Units.val_mul, mul_pow]
  calc
    _ = tau k 1 ^ (m+i.val*(m/2)) * cx k 1 ^ (m/2) *
        ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he (thetaVector k m (next m hm ν)) i *
        (↑a⁻¹ : CompletedNode k 1)^m := by rw [pow_add]; ring
    _ = tau k 1 ^ p * tau k 1 ^ (j.val*(m/2)) * cx k 1 ^ (m/2) *
        (tau k 1 ^ E * ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
          (thetaVector k m (next m hm ν)) i) * (↑a⁻¹ : CompletedNode k 1)^m := by
      rw [hexp, pow_add, pow_add]; ring
    _ = tau k 1 ^ p * tau k 1 ^ (j.val*(m/2)) * cx k 1 ^ (m/2) *
        (cy k 1 ^ (m-1) * ArithmeticThetaAnnularThetaR0128.uniformSection k m hm he
          (thetaVector k m ν) j) * (↑a⁻¹ : CompletedNode k 1)^m *
          ((b : CompletedNode k 1)^m * (↑b⁻¹ : CompletedNode k 1)^m) := by rw [hw, hb, mul_one]
    _ = _ := by ring


lemma next_twice (m : ℕ) (hm : 0 < m) (i : Fin (2*m)) :
    (next (2*m) (Nat.mul_pos (by decide) hm)
      (next (2*m) (Nat.mul_pos (by decide) hm) i)).val = (i.val+2) % (2*m) := by
  simp only [ArithmeticThetaInfinitesimalPolygonR0129.next, Nat.mod_add_mod]

def shiftedIndex (m : ℕ) (hm : 0 < m) (i : Fin (2*m)) : Fin (2*m) :=
  next (2*m) (Nat.mul_pos (by decide) hm) (next (2*m) (Nat.mul_pos (by decide) hm) i)

/-- Coefficient of the uniformly cleared sheaf map in the actual ideal frames. -/
def shiftMultiplier (m : ℕ) (hm : 0 < m) (i : Fin (2*m)) : CompletedNode k 1 :=
  (if i.val+2 < 2*m then tau k 1 ^ (i.val+1) * cx k 1
   else tau k 1 ^ (m-(i.val+2-2*m)*(m-1)) * cy k 1 ^ (m-1)) *
    (↑(gammaTail k (2*m) (Nat.mul_pos (by decide) hm) (shiftedIndex m hm i) *
      (gammaTail k (2*m) (Nat.mul_pos (by decide) hm) i)⁻¹) : CompletedNode k 1)^m

/-- One identity for all charts, including both boundary charts. -/
lemma all_numerators_shift (m : ℕ) (hm : 0 < m) (he : Even m)
    (i : Fin (2*m)) (ν : Fin m) :
    tau k 1 ^ m * thetaNumerator k m hm he (thetaVector k m (next m hm ν)) i =
      shiftMultiplier k m hm i *
        thetaNumerator k m hm he (thetaVector k m ν) (shiftedIndex m hm i) := by
  by_cases hi : i.val+2 < 2*m
  · have hj : shiftedIndex m hm i = ⟨i.val+2,hi⟩ := by
      apply Fin.ext
      exact (next_twice m hm i).trans (Nat.mod_eq_of_lt hi)
    simpa only [shiftMultiplier, if_pos hi, hj, interiorMultiplier] using
      numerator_shift k m hm he i hi ν
  · let l : Fin 2 := ⟨i.val+2-2*m, by have := i.isLt; omega⟩
    have hil : i = ⟨l.val+2*(m-1),wrap_last_bound m hm l⟩ := by
      apply Fin.ext
      change i.val = (i.val+2-2*m)+2*(m-1)
      omega
    have hj : shiftedIndex m hm i = ⟨l.val,wrap_first_bound m hm l⟩ := by
      apply Fin.ext
      rw [show (shiftedIndex m hm i).val = (i.val+2)%(2*m) from next_twice m hm i]
      change (i.val+2)%(2*m) = i.val+2-2*m
      have heq : i.val+2 = (i.val+2-2*m) + 2*m := by omega
      rw [heq, Nat.add_mod_right, Nat.add_sub_cancel_right]
      apply Nat.mod_eq_of_lt
      have := l.isLt
      dsimp [l] at this
      omega
    have h := numerator_wrap k m hm he l ν
    dsimp only at h
    rw [← hil, ← hj] at h
    simpa only [shiftMultiplier, if_neg hi, l, Fin.val_mk] using h

lemma all_finite_numerators_shift (m : ℕ) (hm : 0 < m) (he : Even m)
    (n : ℕ) (i : Fin (2*m)) (ν : Fin m) :
    completedReduction k n (tau k 1) ^ m *
        finiteNumerator k m hm he (thetaVector k m (next m hm ν)) n i =
      completedReduction k n (shiftMultiplier k m hm i) *
        finiteNumerator k m hm he (thetaVector k m ν) n (shiftedIndex m hm i) := by
  exact (by simpa only [map_mul, map_pow, finiteNumerator] using
    congrArg (completedReduction k n) (all_numerators_shift k m hm he i ν))

end CompletedShift



/-- Local factorizations through an actual ideal sheaf glue uniquely. The proof
uses the kernel defining that ideal, so no arbitrary morphism-gluing provider
is assumed. -/
lemma factor_ideal_of_cover {X : Scheme.{u}} {ι : Type*}
    (U : ι → Scheme.{u}) (c : ∀ i, U i ⟶ X)
    (ho : ∀ i, IsOpenImmersion (c i)) (hc : ∀ x : X, ∃ i z, c i z = x)
    (I : X.IdealSheafData) {F G : X.Modules}
    (e : G ≅ idealModule I)
    (j : G ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (he : e.hom ≫ idealInclusion I = j)
    (α : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (β : ∀ i, (Scheme.Modules.pullback (c i)).obj F ⟶
      (Scheme.Modules.pullback (c i)).obj G)
    (hβ : ∀ i, β i ≫ (Scheme.Modules.pullback (c i)).map j =
      (Scheme.Modules.pullback (c i)).map α) :
    ∃! f : F ⟶ G, f ≫ j = α := by
  open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133 in
  have hz : α ≫ quotientMap I = 0 := by
    apply ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.hom_ext_pullback_cover
      U c ho hc
    intro i
    rw [Functor.map_comp, ← hβ i, Category.assoc, ← Functor.map_comp]
    have hj : j ≫ quotientMap I = 0 := by
      rw [← he, Category.assoc]
      change e.hom ≫ (kernel.ι (quotientMap I) ≫ quotientMap I) = 0
      rw [kernel.condition, Limits.comp_zero]
    rw [hj]
    simp
  let f : F ⟶ G := kernel.lift _ α hz ≫ e.inv
  have hf : f ≫ j = α := by
    rw [← he]
    simp only [f, Category.assoc, Iso.inv_hom_id_assoc]
    exact kernel.lift_ι _ _ _
  haveI : Mono j := by
    rw [← he]
    letI : Mono (idealInclusion I) :=
      (ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.ideal_realization I).1
    infer_instance
  exact ⟨f, hf, fun f' hf' => (cancel_mono j).mp (hf'.trans hf.symm)⟩

namespace StageLocalShift
set_option maxHeartbeats 1600000
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaIdentitySectionsR0138.IdentityStageSectionRealizationR0138
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (multiplication_eq_iff)
open CompletedShift

variable (m : ℕ) (hm : 0 < m) (he : Even m) (n : ℕ)
  {E : B k n false ≃+* B k n true} (hE : IsAdjacent k n E)
  (D : Atlas k (2*m) n (Nat.mul_pos (by decide) hm) E)

/-- The actual ideal generator trivializes the source line on a finite chart. -/
def frame (i : Fin (2*m)) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ≅
      (Scheme.Modules.pullback (D.chart i)).obj (stageModule k D m) := by
  let f := fromSection _ (localGenerator k (2*m) n (Nat.mul_pos (by decide) hm)
    (thetaChartBound m hm he) hE D m i)
  letI : IsIso (C := (specA k n).Modules) f := localGenerator_frame k (2*m) n (Nat.mul_pos (by decide) hm)
    (thetaChartBound m hm he) hE D m i
  exact asIso f

/-- Multiplication by a literal element of the actual chart ring. -/
def multiply (a : A k n) :
    (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ⟶
      (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) :=
  fromSection _ ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv a)

lemma multiply_mul (a b : A k n) :
    multiply k n a ≫ multiply k n b = multiply k n (a*b) := by
  apply unit_hom_ext
  change (Scheme.Modules.Hom.app (multiply k n b)) ⊤
    ((Scheme.Modules.Hom.app (multiply k n a)) ⊤ (1 : Γ(specA k n, ⊤))) =
    (Scheme.Modules.Hom.app (multiply k n (a*b))) ⊤ (1 : Γ(specA k n, ⊤))
  simp [multiply, fromSection_apply, map_mul]

lemma frame_eval (φ : StageDual k D m) (i : Fin (2*m)) :
    (frame k m hm he n hE D i).hom ≫ pulledInclusion (D.chart i) φ =
      multiply k n (numerator k (2*m) n (Nat.mul_pos (by decide) hm)
        (thetaChartBound m hm he) hE D m φ i) :=
  frame_evaluation k (2*m) n (Nat.mul_pos (by decide) hm)
    (thetaChartBound m hm he) hE D m φ i

variable (g : D.X ⟶ D.X)
  (hg : ∀ i, D.chart i ≫ g = D.chart (shiftedIndex m hm i))

/-- A map into the genuine pullback under two rotations, expressed in the
canonical ideal frames. This is defined on every chart, including the boundary. -/
def localMap (i : Fin (2*m)) :
    (Scheme.Modules.pullback (D.chart i)).obj (stageModule k D m) ⟶
      (Scheme.Modules.pullback (D.chart i)).obj
        ((Scheme.Modules.pullback g).obj (stageModule k D m)) :=
  (frame k m hm he n hE D i).inv ≫
    multiply k n (completedReduction k n (shiftMultiplier k m hm i)) ≫
    (frame k m hm he n hE D (shiftedIndex m hm i)).hom ≫
    (compIso (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
      (stageModule k D m)).inv

/-- Evaluation of the local geometric map is multiplication by the specified
completed coefficient, followed by evaluation on the shifted chart. -/
lemma localMap_eval (φ : StageDual k D m) (i : Fin (2*m)) :
    (frame k m hm he n hE D i).hom ≫ localMap k m hm he n hE D g hg i ≫
        pulledInclusion (D.chart i) (pulledInclusion g φ) =
      multiply k n (completedReduction k n (shiftMultiplier k m hm i)) ≫
        multiply k n (numerator k (2*m) n (Nat.mul_pos (by decide) hm)
          (thetaChartBound m hm he) hE D m φ (shiftedIndex m hm i)) := by
  rw [← compIso_inclusion (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
    (stageModule k D m) φ]
  simp only [localMap, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [frame_eval]

/-- The local sheaf morphism has the exact required theta action after the
single uniform vertical factor is cleared. -/
lemma localMap_theta (ν : Fin m) (φ ψ : StageDual k D m)
    (hφ : ∀ i, numerator k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m φ i =
        finiteNumerator k m hm he (ArithmeticThetaGenericEvaluationR0140.thetaVector k m ν) n i)
    (hψ : ∀ i, numerator k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m ψ i =
        finiteNumerator k m hm he
          (ArithmeticThetaGenericEvaluationR0140.thetaVector k m (next m hm ν)) n i)
    (i : Fin (2*m)) :
    localMap k m hm he n hE D g hg i ≫
        pulledInclusion (D.chart i) (pulledInclusion g φ) =
      scale ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^m))
        (pulledInclusion (D.chart i) ψ) := by
  apply (cancel_epi (frame k m hm he n hE D i).hom).mp
  rw [localMap_eval, scale_precomp, frame_eval, hφ, hψ]
  apply unit_hom_ext
  change (Scheme.Modules.Hom.app (multiply k n (finiteNumerator k m hm he (thetaVector k m ν) n
      (shiftedIndex m hm i)))) ⊤
    ((Scheme.Modules.Hom.app (multiply k n (completedReduction k n (shiftMultiplier k m hm i)))) ⊤
      (1 : Γ(specA k n, ⊤))) =
    (Scheme.Modules.Hom.app (scale ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^m))
      (multiply k n (finiteNumerator k m hm he (thetaVector k m (next m hm ν)) n i))))
        ⊤ (1 : Γ(specA k n, ⊤))
  rw [scale_app]
  simp only [multiply]
  erw [fromSection_apply, fromSection_apply, fromSection_apply]
  simpa [map_mul, map_pow] using
    congrArg (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (all_finite_numerators_shift k m hm he n i ν).symm


include hg in
/-- A prescribed dual map factors through the rotated ideal as soon as its
literal numerators are divisible in every actual ideal frame. -/
lemma factor_of_numerators [IsIso g] (α : StageDual k D m) (b : Fin (2*m) → A k n)
    (hb : ∀ i, numerator k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m α i =
        b i * (equation k (2*m) n (shiftedIndex m hm i))^m) :
    ∃! f : stageModule k D m ⟶ (Scheme.Modules.pullback g).obj (stageModule k D m),
      f ≫ pulledInclusion g (idealInclusion ((stageIdeal k D)^m)) = α := by
  let I := (stageIdeal k D)^m
  have hI : I.IsInvertible :=
    (ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.effective_invertible
      _ (AlgebraizedThetaSectionsR0138.single_effective_cartier k (2*m) n
        (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) E hE D)).pow m
  let e := idealPullbackIso g I (I.comap g) hI (hI.comap_of_isOpenImmersion g) rfl
  let β (i : Fin (2*m)) :=
    (frame k m hm he n hE D i).inv ≫ multiply k n (b i) ≫
      (frame k m hm he n hE D (shiftedIndex m hm i)).hom ≫
      (compIso (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
        (stageModule k D m)).inv
  apply factor_ideal_of_cover (fun _ : Fin (2*m) => specA k n) D.chart
    D.chart_open D.covers (I.comap g) e
    (pulledInclusion g (idealInclusion I))
    (idealPullbackIso_inclusion g I (I.comap g) hI (hI.comap_of_isOpenImmersion g) rfl)
    α β
  intro i
  letI := unitPullback_isIso (D.chart i)
  apply (cancel_mono (unitPullback (D.chart i))).mp
  change β i ≫ pulledInclusion (D.chart i) (pulledInclusion g (idealInclusion I)) =
    pulledInclusion (D.chart i) α
  apply (cancel_epi (frame k m hm he n hE D i).hom).mp
  rw [← compIso_inclusion (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
    (stageModule k D m) (idealInclusion I)]
  simp only [β, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [frame_eval k m hm he n hE D α i, hb]
  have hf := IdentityStageSectionRealizationR0138.frame_inclusion k (2*m) n
    (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) hE D m (shiftedIndex m hm i)
  change (frame k m hm he n hE D (shiftedIndex m hm i)).hom ≫
    pulledInclusion (D.chart (shiftedIndex m hm i)) (idealInclusion I) =
      multiply k n ((equation k (2*m) n (shiftedIndex m hm i))^m) at hf
  rw [hf, multiply_mul]

include hg in
lemma factor_frame_eval [IsIso g] (α φ : StageDual k D m)
    (b : Fin (2*m) → A k n)
    (hb : ∀ i, numerator k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m α i =
        b i * (equation k (2*m) n (shiftedIndex m hm i))^m)
    (f : stageModule k D m ⟶ (Scheme.Modules.pullback g).obj (stageModule k D m))
    (hf : f ≫ pulledInclusion g (idealInclusion ((stageIdeal k D)^m)) = α)
    (i : Fin (2*m)) :
    (frame k m hm he n hE D i).hom ≫
      (Scheme.Modules.pullback (D.chart i)).map f ≫
        pulledInclusion (D.chart i) (pulledInclusion g φ) =
      multiply k n (b i * numerator k (2*m) n (Nat.mul_pos (by decide) hm)
        (thetaChartBound m hm he) hE D m φ (shiftedIndex m hm i)) := by
  let I := (stageIdeal k D)^m
  have hI : I.IsInvertible :=
    (ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.effective_invertible
      _ (AlgebraizedThetaSectionsR0138.single_effective_cartier k (2*m) n
        (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) E hE D)).pow m
  letI := D.chart_open i
  let β := multiply k n (b i) ≫ (frame k m hm he n hE D (shiftedIndex m hm i)).hom ≫
    (compIso (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
      (stageModule k D m)).inv
  letI : Mono (pulledInclusion (D.chart i ≫ g) (idealInclusion I)) :=
    pulled_ideal_mono (D.chart i ≫ g) I hI
  haveI : Mono (pulledInclusion (D.chart i) (pulledInclusion g (idealInclusion I))) := by
    rw [← compIso_inclusion (D.chart i) g (D.chart i ≫ g) rfl]
    infer_instance
  have hβ : (frame k m hm he n hE D i).hom ≫
      (Scheme.Modules.pullback (D.chart i)).map f = β := by
    apply (cancel_mono (pulledInclusion (D.chart i) (pulledInclusion g (idealInclusion I)))).mp
    change _ = β ≫ _
    have hh : (Scheme.Modules.pullback (D.chart i)).map f ≫
        pulledInclusion (D.chart i) (pulledInclusion g (idealInclusion I)) =
        pulledInclusion (D.chart i) α := by
      change _ ≫ ((Scheme.Modules.pullback (D.chart i)).map _ ≫ _) = _
      rw [← Category.assoc, ← Functor.map_comp, hf]
      rfl
    rw [Category.assoc, hh, frame_eval, hb]
    rw [← compIso_inclusion (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
      (stageModule k D m)]
    simp only [β, Category.assoc, Iso.inv_hom_id_assoc]
    have hj := frame_inclusion k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m (shiftedIndex m hm i)
    change (frame k m hm he n hE D (shiftedIndex m hm i)).hom ≫
      pulledInclusion (D.chart (shiftedIndex m hm i)) (idealInclusion I) =
        multiply k n ((equation k (2*m) n (shiftedIndex m hm i))^m) at hj
    rw [hj, multiply_mul]
  rw [← Category.assoc, hβ]
  rw [← compIso_inclusion (D.chart i) g (D.chart (shiftedIndex m hm i)) (hg i)
      (stageModule k D m)]
  simp only [β, Category.assoc, Iso.inv_hom_id_assoc]
  rw [frame_eval, multiply_mul]

lemma multiply_injective : Function.Injective (multiply k n) := by
  intro a b h
  have hh := congrArg (fun f : (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) ⟶ (SheafOfModules.unit (specA k n).ringCatSheaf : (specA k n).Modules) => (Scheme.Modules.Hom.app f) ⊤ (1 : Γ(specA k n, ⊤))) h
  simp [multiply, fromSection_apply] at hh
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.symm.injective hh

include hg in
lemma factor_numerator [IsIso g] (α φ : StageDual k D m)
    (b : Fin (2*m) → A k n)
    (hb : ∀ i, numerator k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m α i =
        b i * (equation k (2*m) n (shiftedIndex m hm i))^m)
    (f : stageModule k D m ⟶ (Scheme.Modules.pullback g).obj (stageModule k D m))
    (hf : f ≫ pulledInclusion g (idealInclusion ((stageIdeal k D)^m)) = α)
    (i : Fin (2*m)) :
    numerator k (2*m) n (Nat.mul_pos (by decide) hm)
      (thetaChartBound m hm he) hE D m (f ≫ pulledInclusion g φ) i =
      b i * numerator k (2*m) n (Nat.mul_pos (by decide) hm)
        (thetaChartBound m hm he) hE D m φ (shiftedIndex m hm i) := by
  apply multiply_injective k n
  rw [← frame_eval]
  have hp : pulledInclusion (D.chart i) (f ≫ pulledInclusion g φ) =
      (Scheme.Modules.pullback (D.chart i)).map f ≫
        pulledInclusion (D.chart i) (pulledInclusion g φ) := by
    simp only [pulledInclusion, Functor.map_comp, Category.assoc]
  rw [hp]
  exact factor_frame_eval k m hm he n hE D g hg α φ b hb f hf i

end StageLocalShift


namespace ActualStages
set_option maxHeartbeats 1600000
open CompletedShift
open ArithmeticThetaModelSymmetriesR0137.AlgebraizedActionLawsR0137 (modelChart)

/-- The stage automorphism is the one supplied by the actual algebraized action. -/
def rotation (n : ℕ) : (T.atlas n).X ≅ (T.atlas n).X := ha.1.choose n

def shift (n : ℕ) : (T.atlas n).X ≅ (T.atlas n).X :=
  rotation k M rot scal inv ha n ≪≫ rotation k M rot scal inv ha n

lemma rotation_chart (n : ℕ) (i : Fin r) :
    (T.atlas n).chart i ≫ (rotation k M rot scal inv ha n).hom =
      (T.atlas n).chart (next r hr i) := by
  obtain ⟨_, q, hq, hc⟩ := ha.1.choose_spec.1.2 n
  rw [TowerPeriodRotationR0137.coordinate_unique k n q hq] at hc
  simpa only [rotation, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using hc i

lemma shift_chart (n : ℕ) (i : Fin r) :
    (T.atlas n).chart i ≫ (shift k M rot scal inv ha n).hom =
      (T.atlas n).chart (next r hr (next r hr i)) := by
  change (T.atlas n).chart i ≫ (rotation k M rot scal inv ha n).hom ≫
    (rotation k M rot scal inv ha n).hom = _
  rw [← Category.assoc, rotation_chart, rotation_chart]

lemma shift_inclusion (n : ℕ) :
    (shift k M rot scal inv ha n).hom ≫ M.inclusion n =
      M.inclusion n ≫ rot.hom ≫ rot.hom := by
  have h : M.inclusion n ≫ rot.hom =
      (rotation k M rot scal inv ha n).hom ≫ M.inclusion n := ha.1.choose_spec.2.2 n
  change ((rotation k M rot scal inv ha n).hom ≫
    (rotation k M rot scal inv ha n).hom) ≫ M.inclusion n = _
  rw [Category.assoc, ← h, ← Category.assoc, ← h, Category.assoc]

lemma shift_transition (n N : ℕ) (h : n ≤ N) :
    T.transition n N h ≫ (shift k M rot scal inv ha N).hom =
      (shift k M rot scal inv ha n).hom ≫ T.transition n N h := by
  have ht : T.transition n N h ≫ (rotation k M rot scal inv ha N).hom =
      (rotation k M rot scal inv ha n).hom ≫ T.transition n N h :=
    ha.1.choose_spec.1.1.2 n N h
  change T.transition n N h ≫ ((rotation k M rot scal inv ha N).hom ≫
    (rotation k M rot scal inv ha N).hom) =
    ((rotation k M rot scal inv ha n).hom ≫ (rotation k M rot scal inv ha n).hom) ≫ _
  rw [← Category.assoc, ht, Category.assoc, ht, ← Category.assoc]

section Theta
variable (m : ℕ) (hm : 0 < m) (he : Even m)
  {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
  (MM : Model k TT) (hMM : IsModel k TT MM)
  (ss : baseScheme k ⟶ MM.X)
  (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
  (rr : MM.X ≅ MM.X) (aa : kˣ → (MM.X ≅ MM.X)) (ii : MM.X ≅ MM.X)
  (hh : Actions k MM rr aa ii)

def theta (n : ℕ) (ν : Fin m) : StageDual k (TT.atlas n) m :=
  AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he) MM hMM ss hss m n
    (thetaSection k m hm he MM hMM ss hss ν)

lemma theta_numerator (n : ℕ) (ν : Fin m) (i : Fin (2*m)) :
    IdentityStageSectionRealizationR0138.numerator k (2*m) n
      (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) (TT.overlap_spec n)
      (TT.atlas n) m (theta k m hm he MM hMM ss hss n ν) i =
        finiteNumerator k m hm he (thetaVector k m ν) n i :=
  theta_nums k m hm he MM hMM ss hss ν n i

/-- The local morphisms lie above the prescribed rotations on the actual tower. -/
def localMap (n : ℕ) (i : Fin (2*m)) :
    (Scheme.Modules.pullback ((TT.atlas n).chart i)).obj (stageModule k (TT.atlas n) m) ⟶
      (Scheme.Modules.pullback ((TT.atlas n).chart i)).obj
        ((Scheme.Modules.pullback (shift k MM rr aa ii hh n).hom).obj
          (stageModule k (TT.atlas n) m)) :=
  StageLocalShift.localMap k m hm he n (TT.overlap_spec n) (TT.atlas n)
    (shift k MM rr aa ii hh n).hom (shift_chart k MM rr aa ii hh n) i

/-- Exact finite-stage action on the accepted theta sections, with the uniform
clearing power retained explicitly until generic restriction. -/
lemma localMap_theta (n : ℕ) (ν : Fin m) (i : Fin (2*m)) :
    localMap k m hm he MM rr aa ii hh n i ≫
      pulledInclusion ((TT.atlas n).chart i)
        (pulledInclusion (shift k MM rr aa ii hh n).hom
          (theta k m hm he MM hMM ss hss n ν)) =
      scale ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^m))
        (pulledInclusion ((TT.atlas n).chart i)
          (theta k m hm he MM hMM ss hss n (next m hm ν))) :=
  StageLocalShift.localMap_theta k m hm he n (TT.overlap_spec n) (TT.atlas n)
    (shift k MM rr aa ii hh n).hom (shift_chart k MM rr aa ii hh n) ν
    (theta k m hm he MM hMM ss hss n ν)
    (theta k m hm he MM hMM ss hss n (next m hm ν))
    (theta_numerator k m hm he MM hMM ss hss n ν)
    (theta_numerator k m hm he MM hMM ss hss n (next m hm ν)) i


local instance algebraicDualAdd : AddCommGroup (Dual k MM ss m) :=
  inferInstanceAs (AddCommGroup (powerModule k MM ss m ⟶
    (SheafOfModules.unit MM.X.ringCatSheaf : MM.X.Modules)))

/-- The shifted algebraic theta combination is used only as a dual map for
checking divisibility; the geometric lift itself is constructed by factorization. -/
def shiftedCombo (w : Fin m → PowerSeries k) : Dual k MM ss m := by
  letI : AddCommGroup (Dual k MM ss m) :=
    inferInstanceAs (AddCommGroup (powerModule k MM ss m ⟶
      (SheafOfModules.unit MM.X.ringCatSheaf : MM.X.Modules)))
  exact ∑ ν : Fin m, scale (baseScalar k MM (w ν))
    (thetaSection k m hm he MM hMM ss hss (next m hm ν))

lemma shiftedCombo_nums (w : Fin m → PowerSeries k) (n : ℕ) (i : Fin (2*m)) :
    nums k MM (thetaChartBound m hm he) hMM ss hss m
      (shiftedCombo k m hm he MM hMM ss hss w) n i =
      ∑ ν : Fin m, AlgebraizedThetaSaturationR0138.fullBase k n (w ν) *
        finiteNumerator k m hm he (thetaVector k m (next m hm ν)) n i := by
  unfold shiftedCombo
  rw [nums_sum]
  simp_rw [nums_scale, theta_nums]

lemma ideal_nums (n : ℕ) (i : Fin (2*m)) :
    nums k MM (thetaChartBound m hm he) hMM ss hss m
      (idealInclusion (ss.ker^m)) n i = (equation k (2*m) n i)^m := by
  change IdentityStageSectionRealizationR0138.numerator k (2*m) n
    (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) (TT.overlap_spec n)
    (TT.atlas n) m
    (AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
      MM hMM ss hss m n (idealInclusion (ss.ker^m))) i = _
  have hj : AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
      MM hMM ss hss m n (idealInclusion (ss.ker^m)) =
      idealInclusion ((stageIdeal k (TT.atlas n))^m) := by
    unfold AlgebraizedThetaSectionsR0138.reduceDual pulledInclusion
    rw [← AlgebraizedThetaSectionsR0138.stageIso_inclusion k (thetaChartBound m hm he)
      MM hMM ss hss m n, Iso.inv_hom_id_assoc]
  rw [hj]
  unfold IdentityStageSectionRealizationR0138.numerator
  erw [IdentityStageSectionRealizationR0138.localGenerator_spec k (2*m) n
    (Nat.mul_pos (by decide) hm) (thetaChartBound m hm he) (TT.overlap_spec n) (TT.atlas n) m i]
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _

lemma fullBase_parameter (n d : ℕ) :
    AlgebraizedThetaSaturationR0138.fullBase k n (PowerSeries.X^d) =
      completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^d := by
  rw [map_pow]
  congr 1
  exact (AlgebraizedThetaSaturationR0138.completedReduction_base k n PowerSeries.X).symm

/-- Saturation of the canonical ideal inclusion supplies the common clearing
power. The resulting divisibility is proved on all actual finite charts. -/
lemma exists_cleared_numerators :
    ∃ (a : ℕ) (w : Fin m → PowerSeries k), ∀ (n : ℕ) (i : Fin (2*m)),
      nums k MM (thetaChartBound m hm he) hMM ss hss m
        (scale (baseScalar k MM (PowerSeries.X^m))
          (shiftedCombo k m hm he MM hMM ss hss w)) n i =
        (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^a *
          completedReduction k n (shiftMultiplier k m hm i)) *
            (equation k (2*m) n (shiftedIndex m hm i))^m := by
  obtain ⟨a, w, hw⟩ := algebraic_saturation k m hm he MM hMM ss hss
    (idealInclusion (ss.ker^m))
  refine ⟨a, w, ?_⟩
  intro n i
  have hsat := congrArg (fun φ : Dual k MM ss m =>
    nums k MM (thetaChartBound m hm he) hMM ss hss m φ n (shiftedIndex m hm i)) hw
  rw [nums_scale, ideal_nums k m hm he MM hMM ss hss,
    combo_nums k m hm he MM hMM ss hss, fullBase_parameter] at hsat
  rw [nums_scale, shiftedCombo_nums, fullBase_parameter]
  calc
    _ = completedReduction k n (shiftMultiplier k m hm i) *
        ∑ ν : Fin m, AlgebraizedThetaSaturationR0138.fullBase k n (w ν) *
          finiteNumerator k m hm he (thetaVector k m ν) n (shiftedIndex m hm i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      rw [mul_left_comm, all_finite_numerators_shift]
      ring
    _ = completedReduction k n (shiftMultiplier k m hm i) *
        finiteNumerator k m hm he w n (shiftedIndex m hm i) := by
      rw [← finiteNumerator_sum k m hm he (TT := TT)]
    _ = _ := by rw [← hsat]; ring


/-- Whole finite-stage sheaf morphisms exist over the actual two-rotation
maps. Both the global dual map and its uniform chart divisibility are retained. -/
lemma exists_finite_cleared_shift :
    ∃ (a : ℕ) (w : Fin m → PowerSeries k),
      (∀ (n : ℕ) (i : Fin (2*m)),
        nums k MM (thetaChartBound m hm he) hMM ss hss m
          (scale (baseScalar k MM (PowerSeries.X^m))
            (shiftedCombo k m hm he MM hMM ss hss w)) n i =
          (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^a *
            completedReduction k n (shiftMultiplier k m hm i)) *
              (equation k (2*m) n (shiftedIndex m hm i))^m) ∧
      ∀ n, ∃! f : stageModule k (TT.atlas n) m ⟶
          (Scheme.Modules.pullback (shift k MM rr aa ii hh n).hom).obj
            (stageModule k (TT.atlas n) m),
        f ≫ pulledInclusion (shift k MM rr aa ii hh n).hom
            (idealInclusion ((stageIdeal k (TT.atlas n))^m)) =
          AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
            MM hMM ss hss m n
            (scale (baseScalar k MM (PowerSeries.X^m))
              (shiftedCombo k m hm he MM hMM ss hss w)) := by
  obtain ⟨a, w, hw⟩ := exists_cleared_numerators k m hm he MM hMM ss hss
  refine ⟨a, w, hw, ?_⟩
  intro n
  exact StageLocalShift.factor_of_numerators k m hm he n (TT.overlap_spec n) (TT.atlas n)
    (shift k MM rr aa ii hh n).hom (shift_chart k MM rr aa ii hh n)
    (AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
      MM hMM ss hss m n
      (scale (baseScalar k MM (PowerSeries.X^m))
        (shiftedCombo k m hm he MM hMM ss hss w)))
    (fun i => completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^a *
      completedReduction k n (shiftMultiplier k m hm i)) (hw n)

end Theta
end ActualStages


namespace FactorCompletion
set_option maxHeartbeats 1600000

lemma transport {C : Type*} [Category C] {F F' G G' H U : C}
    (e : F ≅ F') (d : G ≅ G') (μ : H ⟶ U) [Mono μ]
    (j : G ⟶ H) (j' : G' ⟶ U) (α : F ⟶ H) (f : F' ⟶ G')
    (hd : d.hom ≫ j' = j ≫ μ) (hf : f ≫ j' = e.inv ≫ α ≫ μ) :
    (e.hom ≫ f ≫ d.inv) ≫ j = α := by
  apply (cancel_mono μ).mp
  simp only [Category.assoc]
  rw [← hd]
  simp only [Iso.inv_hom_id_assoc]
  rw [hf, Iso.hom_inv_id_assoc]

lemma reduceDual_cancel (k : Type u) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (h3 : 3 ≤ r)
    (M : Model k T) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d n : ℕ) (α : Dual k M s d) :
    (AlgebraizedThetaSectionsR0138.stageIso k h3 M hM s hs d n).hom ≫
      AlgebraizedThetaSectionsR0138.reduceDual k h3 M hM s hs d n α =
        pulledInclusion (M.inclusion n) α := by
  unfold AlgebraizedThetaSectionsR0138.reduceDual
  exact Iso.hom_inv_id_assoc _ _

lemma compIso_map {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (c' : Z' ⟶ X)
    (c : Z ⟶ X) (h : t ≫ c' = c) {F G : X.Modules} (φ : F ⟶ G) :
    (compIso t c' c h F).hom ≫ (Scheme.Modules.pullback c).map φ =
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback c').map φ) ≫
        (compIso t c' c h G).hom :=
  ((Scheme.Modules.pullbackComp t c' ≪≫ Scheme.Modules.pullbackCongr h).hom.naturality φ).symm

/-- Factorizations through a monomorphism are automatically compatible under
base change; this is the compatibility needed by proper morphism completion. -/
lemma compatible {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (c' : Z' ⟶ X)
    (c : Z ⟶ X) (h : t ≫ c' = c) {F G H : X.Modules} (j : G ⟶ H)
    [Mono ((Scheme.Modules.pullback c).map j)] (α : F ⟶ H)
    (φ : (Scheme.Modules.pullback c).obj F ⟶ (Scheme.Modules.pullback c).obj G)
    (ψ : (Scheme.Modules.pullback c').obj F ⟶ (Scheme.Modules.pullback c').obj G)
    (hφ : φ ≫ (Scheme.Modules.pullback c).map j = (Scheme.Modules.pullback c).map α)
    (hψ : ψ ≫ (Scheme.Modules.pullback c').map j = (Scheme.Modules.pullback c').map α) :
    φ = (compIso t c' c h F).inv ≫ (Scheme.Modules.pullback t).map ψ ≫
      (compIso t c' c h G).hom := by
  apply (cancel_mono ((Scheme.Modules.pullback c).map j)).mp
  rw [hφ]
  simp only [Category.assoc]
  rw [compIso_map, ← Category.assoc ((Scheme.Modules.pullback t).map ψ),
    ← Functor.map_comp, hψ, ← compIso_map, Iso.inv_hom_id_assoc]

/-- Compatible finite factorizations algebraize to an actual sheaf morphism.
All compatibility is derived from the fixed global maps and finite monicity. -/
lemma exists_map {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsProper p]
    (Y : ℕ → Scheme.{u}) (c : ∀ n, Y n ⟶ X)
    (pn : ∀ n, Y n ⟶ Spec (.of (R ⧸ I^(n+1))))
    (hc : ∀ n, IsPullback (c n) (pn n) p
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I^(n+1))))))
    (t : ∀ n, Y n ⟶ Y (n+1)) (ht : ∀ n, t n ≫ c (n+1) = c n)
    (F G H : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (hG : Scheme.Modules.IsInvertible G) (j : G ⟶ H)
    (hj : ∀ n, Mono ((Scheme.Modules.pullback (c n)).map j)) (α : F ⟶ H)
    (hex : ∀ n, ∃ f : (Scheme.Modules.pullback (c n)).obj F ⟶
      (Scheme.Modules.pullback (c n)).obj G,
      f ≫ (Scheme.Modules.pullback (c n)).map j = (Scheme.Modules.pullback (c n)).map α) :
    ∃ f : F ⟶ G, ∀ n,
      (Scheme.Modules.pullback (c n)).map f ≫ (Scheme.Modules.pullback (c n)).map j =
        (Scheme.Modules.pullback (c n)).map α := by
  let fn n := (hex n).choose
  have hfn n := (hex n).choose_spec
  obtain ⟨f, hf, _⟩ :=
    ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.pullback_completion
      I p Y c pn hc t ht F G hF hG fn (by
        intro n
        letI := hj n
        exact compatible (t n) (c (n+1)) (c n) (ht n) j α (fn n) (fn (n+1))
          (hfn n) (hfn (n+1)))
  exact ⟨f, fun n => by rw [hf]; exact hfn n⟩


lemma target_eval {X Y : Scheme.{u}} (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) (L : X.Modules) (Q : Y.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ Q)
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    ((compIso c f (g ≫ c) h L) ≪≫
      ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.chartIso g c L Q e).hom ≫
      pulledInclusion g (e.inv ≫ pulledInclusion c φ) =
        pulledInclusion c (pulledInclusion f φ) := by
  rw [Iso.trans_hom, Category.assoc]
  rw [ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.chartIso_inclusion
    g c L Q e φ (e.inv ≫ pulledInclusion c φ) (e.hom_inv_id_assoc _)]
  exact compIso_inclusion _ _ _ _ _ _

lemma reduce_action {X Y : Scheme.{u}} (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (L : X.Modules) (Q : Y.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ Q)
    (d : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback f).obj L) ≅
      (Scheme.Modules.pullback g).obj Q)
    (q : L ⟶ (Scheme.Modules.pullback f).obj L)
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (ψ : Q ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
    (hd : d.hom ≫ pulledInclusion g ψ = pulledInclusion c (pulledInclusion f φ)) :
    (e.inv ≫ (Scheme.Modules.pullback c).map q ≫ d.hom) ≫ pulledInclusion g ψ =
      e.inv ≫ pulledInclusion c (q ≫ pulledInclusion f φ) := by
  simp only [Category.assoc]
  rw [hd]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

lemma factor_back {C : Type*} [Category C] {F F' G G' H U : C}
    (e : F ≅ F') (d : G ≅ G') (μ : H ⟶ U)
    (j : G ⟶ H) (j' : G' ⟶ U) (α : F ⟶ H) (q : F ⟶ G)
    (hd : d.hom ≫ j' = j ≫ μ) (hq : q ≫ j = α) :
    (e.inv ≫ q ≫ d.hom) ≫ j' = e.inv ≫ α ≫ μ := by
  simp only [Category.assoc]
  rw [hd, ← Category.assoc q, hq]

end FactorCompletion

namespace ModelShift
set_option maxHeartbeats 1600000
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (chartIso chartIso_inclusion)
variable (m : ℕ) (hm : 0 < m) (he : Even m)
  {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
  (MM : Model k TT) (hMM : IsModel k TT MM)
  (ss : baseScheme k ⟶ MM.X)
  (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
  (rr : MM.X ≅ MM.X) (aa : kˣ → (MM.X ≅ MM.X)) (ii : MM.X ≅ MM.X)
  (hh : Actions k MM rr aa ii)

def targetIso (n : ℕ) :
    (Scheme.Modules.pullback (MM.inclusion n)).obj
      ((Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m)) ≅
      (Scheme.Modules.pullback (ActualStages.shift k MM rr aa ii hh n).hom).obj
        (stageModule k (TT.atlas n) m) :=
  compIso (MM.inclusion n) (rr.hom ≫ rr.hom)
    ((ActualStages.shift k MM rr aa ii hh n).hom ≫ MM.inclusion n)
    (ActualStages.shift_inclusion k MM rr aa ii hh n).symm (powerModule k MM ss m) ≪≫
  chartIso (ActualStages.shift k MM rr aa ii hh n).hom (MM.inclusion n)
    (powerModule k MM ss m) (stageModule k (TT.atlas n) m)
    (AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n)

lemma targetIso_inclusion (n : ℕ) :
    (targetIso k m hm he MM hMM ss hss rr aa ii hh n).hom ≫
      pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
        (idealInclusion ((stageIdeal k (TT.atlas n))^m)) =
      pulledInclusion (MM.inclusion n)
        (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))) := by
  unfold targetIso
  rw [Iso.trans_hom, Category.assoc]
  rw [chartIso_inclusion _ _ _ _ _ _ _
    (AlgebraizedThetaSectionsR0138.stageIso_inclusion k (thetaChartBound m hm he)
      MM hMM ss hss m n)]
  exact compIso_inclusion _ _ _ _ _ _

include he hMM hss aa ii hh in
lemma reduced_inclusion_mono (n : ℕ) :
    Mono ((Scheme.Modules.pullback (MM.inclusion n)).map
      (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m)))) := by
  let g := (ActualStages.shift k MM rr aa ii hh n).hom
  let j := pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))
  letI : Mono (pulledInclusion g (idealInclusion ((stageIdeal k (TT.atlas n))^m))) :=
    pulled_ideal_mono g _
      (AlgebraizedThetaSectionsR0138.stage_invertible k (thetaChartBound m hm he) m n)
  haveI : Mono (pulledInclusion (MM.inclusion n) j) := by
    rw [← targetIso_inclusion k m hm he MM hMM ss hss rr aa ii hh n]
    infer_instance
  constructor
  intro Z f f' h
  apply (cancel_mono (pulledInclusion (MM.inclusion n) j)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ unitPullback (MM.inclusion n)) h).trans (Category.assoc _ _ _))

/-- A genuine finite-stage factorization transports to the raw categorical
base changes used by proper completion, with the same structural morphisms. -/
lemma transport_factor (n : ℕ) (α : Dual k MM ss m)
    (f : stageModule k (TT.atlas n) m ⟶
      (Scheme.Modules.pullback (ActualStages.shift k MM rr aa ii hh n).hom).obj
        (stageModule k (TT.atlas n) m))
    (hf : f ≫ pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
      (idealInclusion ((stageIdeal k (TT.atlas n))^m)) =
      AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
        MM hMM ss hss m n α) :
    ∃ β : (Scheme.Modules.pullback (MM.inclusion n)).obj (powerModule k MM ss m) ⟶
        (Scheme.Modules.pullback (MM.inclusion n)).obj
          ((Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m)),
      β ≫ (Scheme.Modules.pullback (MM.inclusion n)).map
        (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))) =
          (Scheme.Modules.pullback (MM.inclusion n)).map α := by
  refine ⟨(AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n).hom ≫ f ≫
    (targetIso k m hm he MM hMM ss hss rr aa ii hh n).inv, ?_⟩
  letI := ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unitPullback_isIso
    (MM.inclusion n)
  apply FactorCompletion.transport
    (AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n)
    (targetIso k m hm he MM hMM ss hss rr aa ii hh n)
    (unitPullback (MM.inclusion n))
    ((Scheme.Modules.pullback (MM.inclusion n)).map
      (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))))
    (pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
      (idealInclusion ((stageIdeal k (TT.atlas n))^m)))
    ((Scheme.Modules.pullback (MM.inclusion n)).map α) f
  · exact targetIso_inclusion k m hm he MM hMM ss hss rr aa ii hh n
  · simpa only [AlgebraizedThetaSectionsR0138.reduceDual, pulledInclusion,
      Category.assoc] using hf


include aa ii hh in
/-- Existence of an algebraic sheaf morphism over the specified two rotations.
Its finite reductions factor the same fixed algebraic theta combination. -/
lemma exists_algebraic_cleared_shift :
    ∃ (a : ℕ) (w : Fin m → PowerSeries k)
      (f : powerModule k MM ss m ⟶
        (Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m)),
      (∀ (n : ℕ) (i : Fin (2*m)),
        nums k MM (thetaChartBound m hm he) hMM ss hss m
          (scale (baseScalar k MM (PowerSeries.X^m))
            (ActualStages.shiftedCombo k m hm he MM hMM ss hss w)) n i =
          (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^a *
            completedReduction k n (CompletedShift.shiftMultiplier k m hm i)) *
              (equation k (2*m) n (CompletedShift.shiftedIndex m hm i))^m) ∧
      ∀ n, (Scheme.Modules.pullback (MM.inclusion n)).map f ≫
        (Scheme.Modules.pullback (MM.inclusion n)).map
          (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))) =
        (Scheme.Modules.pullback (MM.inclusion n)).map
          (scale (baseScalar k MM (PowerSeries.X^m))
            (ActualStages.shiftedCombo k m hm he MM hMM ss hss w)) := by
  obtain ⟨a, w, hnum, hex⟩ := ActualStages.exists_finite_cleared_shift
    k m hm he MM hMM ss hss rr aa ii hh
  letI : IsProper MM.p := hMM.1
  have hP : Scheme.Modules.IsInvertible (powerModule k MM ss m) :=
    (AlgebraizedThetaSectionsR0138.power_invertible k (thetaChartBound m hm he)
      MM hMM ss hss m).isInvertible_module
  obtain ⟨f, hf⟩ := FactorCompletion.exists_map
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) MM.p
    (fun n => (TT.atlas n).X) MM.inclusion (fun n => (TT.atlas n).p)
    (fun n => hMM.2.2.1 n)
    (fun n => TT.transition n (n+1) (Nat.le_succ n))
    (fun n => hMM.2.2.2 n (n+1) (Nat.le_succ n))
    (powerModule k MM ss m)
    ((Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m))
    (SheafOfModules.unit MM.X.ringCatSheaf : MM.X.Modules) hP (hP.pullback _)
    (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m)))
    (reduced_inclusion_mono k m hm he MM hMM ss hss rr aa ii hh)
    (scale (baseScalar k MM (PowerSeries.X^m))
      (ActualStages.shiftedCombo k m hm he MM hMM ss hss w)) (by
        intro n
        obtain ⟨fn, hfn, _⟩ := hex n
        exact transport_factor k m hm he MM hMM ss hss rr aa ii hh n _ fn hfn)
  exact ⟨a, w, f, hnum, hf⟩

lemma targetIso_eval (n : ℕ) (φ : Dual k MM ss m) :
    (targetIso k m hm he MM hMM ss hss rr aa ii hh n).hom ≫
      pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
        (AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
          MM hMM ss hss m n φ) =
      pulledInclusion (MM.inclusion n) (pulledInclusion (rr.hom ≫ rr.hom) φ) := by
  dsimp only [targetIso, AlgebraizedThetaSectionsR0138.reduceDual]
  exact FactorCompletion.target_eval (MM.inclusion n) (rr.hom ≫ rr.hom)
    (ActualStages.shift k MM rr aa ii hh n).hom
    (ActualStages.shift_inclusion k MM rr aa ii hh n).symm
    (powerModule k MM ss m) (stageModule k (TT.atlas n) m)
    (AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n) φ

#print axioms targetIso_eval

set_option maxHeartbeats 100000 in
lemma stageMap_eval (n : ℕ)
    (f : powerModule k MM ss m ⟶
      (Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m))
    (φ : Dual k MM ss m) :
    ((AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n).inv ≫
      (Scheme.Modules.pullback (MM.inclusion n)).map f ≫
      (targetIso k m hm he MM hMM ss hss rr aa ii hh n).hom) ≫
      pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
        (AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
          MM hMM ss hss m n φ) =
    AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
      MM hMM ss hss m n (f ≫ pulledInclusion (rr.hom ≫ rr.hom) φ) := by
  dsimp only [AlgebraizedThetaSectionsR0138.reduceDual]
  have result := FactorCompletion.reduce_action (MM.inclusion n) (rr.hom ≫ rr.hom)
    (ActualStages.shift k MM rr aa ii hh n).hom
    (powerModule k MM ss m) (stageModule k (TT.atlas n) m)
    (AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n)
    (targetIso k m hm he MM hMM ss hss rr aa ii hh n) f φ
    (AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he) MM hMM ss hss m n φ)
    (targetIso_eval k m hm he MM hMM ss hss rr aa ii hh n φ)
  simp only [AlgebraizedThetaSectionsR0138.reduceDual] at result

  set_option backward.isDefEq.respectTransparency true in
    exact result
#print axioms stageMap_eval

set_option maxHeartbeats 100000 in
lemma stageMap_factor (n : ℕ)
    (f : powerModule k MM ss m ⟶
      (Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m))
    (α : Dual k MM ss m)
    (hf : (Scheme.Modules.pullback (MM.inclusion n)).map f ≫
      (Scheme.Modules.pullback (MM.inclusion n)).map
        (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))) =
      (Scheme.Modules.pullback (MM.inclusion n)).map α) :
    ((AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n).inv ≫
      (Scheme.Modules.pullback (MM.inclusion n)).map f ≫
      (targetIso k m hm he MM hMM ss hss rr aa ii hh n).hom) ≫
      pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
        (idealInclusion ((stageIdeal k (TT.atlas n))^m)) =
      AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he)
        MM hMM ss hss m n α := by
  dsimp only [AlgebraizedThetaSectionsR0138.reduceDual]
  have result := FactorCompletion.factor_back
    (AlgebraizedThetaSectionsR0138.stageIso k (thetaChartBound m hm he) MM hMM ss hss m n)
    (targetIso k m hm he MM hMM ss hss rr aa ii hh n) (unitPullback (MM.inclusion n))
    ((Scheme.Modules.pullback (MM.inclusion n)).map
      (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))))
    (pulledInclusion (ActualStages.shift k MM rr aa ii hh n).hom
      (idealInclusion ((stageIdeal k (TT.atlas n))^m)))
    ((Scheme.Modules.pullback (MM.inclusion n)).map α)
    ((Scheme.Modules.pullback (MM.inclusion n)).map f)
    (targetIso_inclusion k m hm he MM hMM ss hss rr aa ii hh n) hf
  set_option backward.isDefEq.respectTransparency true in
    simpa only [pulledInclusion] using result
#print axioms stageMap_factor


end ModelShift

namespace RawAction

open CategoryTheory AlgebraicGeometry Scheme.Modules
open ArithmeticThetaGenericEvaluationR0140.GenericThetaBasisR0140
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

def scaleHom {X : Scheme.{u}} {F G : X.Modules} (a : Γ(X, ⊤)) (f : F ⟶ G) : F ⟶ G :=
  ihomGlobalSectionsEquiv F G (a • (ihomGlobalSectionsEquiv F G).symm f)

lemma scaleHom_app {X : Scheme.{u}} {F G : X.Modules} (a : Γ(X, ⊤)) (f : F ⟶ G)
    (U : X.Opens) (x : Γ(F, U)) :
    (scaleHom a f).app U x = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a • f.app U x := by
  unfold scaleHom
  rw [ihomGlobalSectionsEquiv_app_apply, Scheme.Modules.map_smul, ihomEval_smul_right]
  rw [← ihomGlobalSectionsEquiv_app_apply, (ihomGlobalSectionsEquiv F G).apply_symm_apply]

lemma scaleHom_comp {X : Scheme.{u}} {F G H : X.Modules} (a : Γ(X, ⊤))
    (f : F ⟶ G) (g : G ⟶ H) : scaleHom a f ≫ g = scaleHom a (f ≫ g) := by
  apply hom_ext
  intro U
  ext x
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, scaleHom_app]
  exact Hom.app_smul g _ _

lemma scaleHom_dual {X : Scheme.{u}} {F : X.Modules} (a : Γ(X, ⊤))
    (f : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    scaleHom a f = scale a f := rfl

lemma scaleHom_one {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) : scaleHom 1 f = f := by
  unfold scaleHom
  rw [one_smul, (ihomGlobalSectionsEquiv F G).apply_symm_apply]

lemma scaleHom_mul {X : Scheme.{u}} {F G : X.Modules} (a b : Γ(X, ⊤)) (f : F ⟶ G) :
    scaleHom a (scaleHom b f) = scaleHom (a*b) f := by
  unfold scaleHom
  rw [(ihomGlobalSectionsEquiv F G).symm_apply_apply, mul_smul]

open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133

def restrictMap {X Y : Scheme.{u}} (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) (L : X.Modules)
    (q : L ⟶ (Scheme.Modules.pullback f).obj L) :
    (Scheme.Modules.pullback c).obj L ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback c).obj L) :=
  (Scheme.Modules.pullback c).map q ≫ (squareIso f c c g h L).inv

lemma restrictMap_eval {X Y : Scheme.{u}} (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) (L : X.Modules)
    (q : L ⟶ (Scheme.Modules.pullback f).obj L)
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    restrictMap c f g h L q ≫ pulledInclusion g (pulledInclusion c φ) =
      pulledInclusion c (q ≫ pulledInclusion f φ) := by
  rw [← squareIso_inclusion f c c g h L φ]
  simp only [restrictMap, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [pulledInclusion, Functor.map_comp, Category.assoc]

lemma normalized_eval {X : Scheme.{u}} {L Q : X.Modules}
    (q : L ⟶ Q) (φ : Q ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (ψ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (a b : Γ(X, ⊤)) (hab : a*b=1) (hq : q ≫ φ = scale b ψ) :
    scaleHom a q ≫ φ = ψ := by
  rw [scaleHom_comp, hq, ← scaleHom_dual, scaleHom_mul, hab, scaleHom_one]


open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
  (s : baseScheme k ⟶ M.X) (d : ℕ)
  (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
  (ha : Actions k M rot scal inv)

def normalizedMap (a : ℕ)
    (q : powerModule k M s d ⟶
      (Scheme.Modules.pullback (rot.hom ≫ rot.hom)).obj (powerModule k M s d)) :
    genericPower k M s d ⟶
      (Scheme.Modules.pullback (shiftMap k M rot scal inv ha)).obj (genericPower k M s d) :=
  scaleHom (scalarAt k M ⊤ ((algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^a))⁻¹))
    (restrictMap (genericInclusion k M) (rot.hom ≫ rot.hom) (shiftMap k M rot scal inv ha)
      (shiftMap_inclusion k M rot scal inv ha).symm (powerModule k M s d) q)

lemma normalizedMap_eval (a : ℕ)
    (q : powerModule k M s d ⟶
      (Scheme.Modules.pullback (rot.hom ≫ rot.hom)).obj (powerModule k M s d))
    (φ ψ : Dual k M s d)
    (hq : q ≫ pulledInclusion (rot.hom ≫ rot.hom) φ =
      scale (baseScalar k M (PowerSeries.X^a)) ψ) :
    normalizedMap k M s d rot scal inv ha a q ≫
      pulledInclusion (shiftMap k M rot scal inv ha) (restrictDual k M s d φ) =
        restrictDual k M s d ψ := by
  have hx : algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^a) ≠ 0 :=
    by simpa only [map_zero] using ((IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).ne
      (pow_ne_zero a PowerSeries.X_ne_zero))
  apply normalized_eval _ _ _ _ (scalarAt k M ⊤
    (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^a)))
  · let F : LaurentSeries k →+* Γ(genericScheme k M, ⊤) :=
      (genericStructure k M).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom
    have hF : F ((algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^a))⁻¹) *
        F (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^a)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hx, map_one]
    rw [scalarAt_top, scalarAt_top]
    change F _ * F _ = 1
    exact hF
  · have h := restrictMap_eval (genericInclusion k M) (rot.hom ≫ rot.hom)
      (shiftMap k M rot scal inv ha) (shiftMap_inclusion k M rot scal inv ha).symm
      (powerModule k M s d) q φ
    rw [hq, pull_scale, generic_base, ← scalarAt_top] at h
    exact h

#print axioms normalizedMap_eval
#print axioms restrictMap_eval
#print axioms normalized_eval

end RawAction

namespace ModelShift
open CompletedShift
variable (k : Type u) [Field k] [CharZero k]
variable (m : ℕ) (hm : 0 < m) (he : Even m)
  {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
  (MM : Model k TT) (hMM : IsModel k TT MM)
  (ss : baseScheme k ⟶ MM.X)
  (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
  (rr : MM.X ≅ MM.X) (aa : kˣ → (MM.X ≅ MM.X)) (ii : MM.X ≅ MM.X)
  (hh : Actions k MM rr aa ii)

include aa ii hh in
lemma cleared_action (a : ℕ) (α : Dual k MM ss m)
    (f : powerModule k MM ss m ⟶
      (Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m))
    (hnum : ∀ (n : ℕ) (i : Fin (2*m)),
      nums k MM (thetaChartBound m hm he) hMM ss hss m α n i =
        (completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^a *
          completedReduction k n (shiftMultiplier k m hm i)) *
            (equation k (2*m) n (shiftedIndex m hm i))^m)
    (hf : ∀ n, (Scheme.Modules.pullback (MM.inclusion n)).map f ≫
      (Scheme.Modules.pullback (MM.inclusion n)).map
        (pulledInclusion (rr.hom ≫ rr.hom) (idealInclusion (ss.ker^m))) =
      (Scheme.Modules.pullback (MM.inclusion n)).map α)
    (ν : Fin m) :
    f ≫ pulledInclusion (rr.hom ≫ rr.hom) (thetaSection k m hm he MM hMM ss hss ν) =
      scale (baseScalar k MM (PowerSeries.X^(a+m)))
        (thetaSection k m hm he MM hMM ss hss (next m hm ν)) := by
  apply nums_injective k MM (thetaChartBound m hm he) hMM ss hss m
  funext n i
  rw [nums_scale, theta_nums, ActualStages.fullBase_parameter]
  have hfn := stageMap_factor k m hm he MM hMM ss hss rr aa ii hh n f α (hf n)
  have hact := stageMap_eval k m hm he MM hMM ss hss rr aa ii hh n f
    (thetaSection k m hm he MM hMM ss hss ν)
  have hloc := StageLocalShift.factor_numerator k m hm he n (TT.overlap_spec n) (TT.atlas n)
    (ActualStages.shift k MM rr aa ii hh n).hom (ActualStages.shift_chart k MM rr aa ii hh n)
    (AlgebraizedThetaSectionsR0138.reduceDual k (thetaChartBound m hm he) MM hMM ss hss m n α)
    (ActualStages.theta k m hm he MM hMM ss hss n ν)
    (fun i => completedReduction k n (ArithmeticThetaScaledAnnularR0050.tau k 1)^a *
      completedReduction k n (shiftMultiplier k m hm i)) (hnum n) _ hfn i
  dsimp only [ActualStages.theta] at hloc
  rw [hact] at hloc
  have hn := ActualStages.theta_numerator k m hm he MM hMM ss hss n ν (shiftedIndex m hm i)
  dsimp only [ActualStages.theta] at hn
  rw [hn] at hloc
  change nums k MM (thetaChartBound m hm he) hMM ss hss m
      (f ≫ pulledInclusion (rr.hom ≫ rr.hom) (thetaSection k m hm he MM hMM ss hss ν)) n i = _ at hloc
  rw [hloc]
  rw [mul_assoc, ← all_finite_numerators_shift, ← mul_assoc, ← pow_add]


include aa ii hh in
lemma exists_cleared_action :
    ∃ (a : ℕ) (f : powerModule k MM ss m ⟶
      (Scheme.Modules.pullback (rr.hom ≫ rr.hom)).obj (powerModule k MM ss m)),
    ∀ ν : Fin m,
      f ≫ pulledInclusion (rr.hom ≫ rr.hom) (thetaSection k m hm he MM hMM ss hss ν) =
        scale (baseScalar k MM (PowerSeries.X^(a+m)))
          (thetaSection k m hm he MM hMM ss hss (next m hm ν)) := by
  obtain ⟨a, w, f, hnum, hf⟩ := exists_algebraic_cleared_shift k m hm he MM hMM ss hss rr aa ii hh
  exact ⟨a, f, cleared_action k m hm he MM hMM ss hss rr aa ii hh a _ f hnum hf⟩

lemma exists_generic_cyclic_map :
    ∃ q : genericPower k MM ss m ⟶
      (Scheme.Modules.pullback (shiftMap k MM rr aa ii hh)).obj (genericPower k MM ss m),
    ∀ ν : Fin m,
      q ≫ pulledInclusion (shiftMap k MM rr aa ii hh) (genericTheta k m hm he MM hMM ss hss ν) =
        genericTheta k m hm he MM hMM ss hss (next m hm ν) := by
  obtain ⟨a, f, hf⟩ := exists_cleared_action k m hm he MM hMM ss hss rr aa ii hh
  refine ⟨RawAction.normalizedMap k MM ss m rr aa ii hh (a+m) f, ?_⟩
  intro ν
  exact RawAction.normalizedMap_eval k MM ss m rr aa ii hh (a+m) f _ _ (hf ν)

#print axioms exists_generic_cyclic_map
#print axioms cleared_action

end ModelShift

namespace RawIteration
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaModelSymmetriesR0137 (iterateHom)
variable {X : Scheme.{u}} (g : X ⟶ X) (L : X.Modules)

lemma unit_id : unitPullback (𝟙 X) = (Scheme.Modules.pullbackId X).hom.app
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [show ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _)
    (unitPullback (𝟙 X)) = SheafOfModules.unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom from
      Equiv.apply_symm_apply _ _]
  have h := congrArg (fun t => t.app (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (Scheme.Modules.conjugateEquiv_pullbackId_hom (X := X))
  dsimp [conjugateEquiv] at h
  have he : SheafOfModules.unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom =
      (Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf) := by
    rfl
  rw [he, Adjunction.homEquiv_unit]
  simpa using h.symm

lemma pulled_id (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    pulledInclusion (𝟙 X) φ = (Scheme.Modules.pullbackId X).hom.app L ≫ φ := by
  rw [pulledInclusion, unit_id]
  exact (Scheme.Modules.pullbackId X).hom.naturality φ

def basePower : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n+1 => g ≫ basePower n

lemma basePower_add (a b : ℕ) : basePower g (a+b) = basePower g a ≫ basePower g b := by
  induction a with
  | zero => simp [basePower]
  | succ a ih => simpa only [Nat.succ_add, basePower, Category.assoc] using congrArg (g ≫ ·) ih

lemma basePower_eq (n : ℕ) : basePower g n = iterateHom g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=n+1 from rfl, basePower_add, ih]
    simp [basePower, iterateHom]

def power (q : L ⟶ (Scheme.Modules.pullback g).obj L) :
    (n : ℕ) → (L ⟶ (Scheme.Modules.pullback (basePower g n)).obj L)
  | 0 => (Scheme.Modules.pullbackId X).inv.app L
  | n+1 => q ≫ (Scheme.Modules.pullback g).map (power q n) ≫
      (Scheme.Modules.pullbackComp g (basePower g n)).hom.app L

lemma power_eval (q : L ⟶ (Scheme.Modules.pullback g).obj L)
    (φ : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (n : ℕ) :
    power g L q n ≫ pulledInclusion (basePower g n) φ =
      (fun ψ => q ≫ pulledInclusion g ψ)^[n] φ := by
  induction n with
  | zero =>
    simp only [power, basePower, Function.iterate_zero, id_eq]
    rw [pulled_id]
    exact Iso.inv_hom_id_app_assoc (Scheme.Modules.pullbackId X) L φ
  | succ n ih =>
    simp only [power, basePower, Category.assoc]
    rw [pulledInclusion_comp]
    change q ≫ ((Scheme.Modules.pullback g).map (power g L q n) ≫
      ((Scheme.Modules.pullback g).map (pulledInclusion (basePower g n) φ) ≫ _)) = _
    rw [← Category.assoc ((Scheme.Modules.pullback g).map (power g L q n)),
      ← Functor.map_comp, ih, Function.iterate_succ_apply']
    rfl

lemma power_isIso (q : L ⟶ (Scheme.Modules.pullback g).obj L) (n : ℕ)
    (hbase : basePower g n = 𝟙 X)
    (j : L ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Mono j]
    (hj : (fun ψ => q ≫ pulledInclusion g ψ)^[n] j = j) : IsIso (power g L q n) := by
  let e := ((Scheme.Modules.pullbackCongr hbase) ≪≫ Scheme.Modules.pullbackId X).app L
  have he : e.hom ≫ j = pulledInclusion (basePower g n) j := by
    simp only [e, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [← pulled_id, pulledInclusion_congr]
  have hid : power g L q n ≫ e.hom = 𝟙 L := by
    apply (cancel_mono j).mp
    rw [Category.assoc, he, power_eval, hj, Category.id_comp]
  have hq : power g L q n = e.inv := by
    apply (cancel_mono e.hom).mp
    rw [hid, Iso.inv_hom_id]
  rw [hq]
  infer_instance

lemma split_of_power (q : L ⟶ (Scheme.Modules.pullback g).obj L) (n : ℕ)
    [IsIso (power g L q (n+1))] : IsSplitMono q := by
  let rest := (Scheme.Modules.pullback g).map (power g L q n) ≫
    (Scheme.Modules.pullbackComp g (basePower g n)).hom.app L
  apply IsSplitMono.mk'
  refine ⟨rest ≫ inv (power g L q (n+1)), ?_⟩
  change q ≫ rest ≫ inv (power g L q (n+1)) = 𝟙 L
  rw [← Category.assoc]
  exact IsIso.hom_inv_id (power g L q (n+1))

lemma power_split (q : L ⟶ (Scheme.Modules.pullback g).obj L) [IsSplitMono q] (n : ℕ) :
    IsSplitMono (power g L q n) := by
  induction n with
  | zero => dsimp only [power]; infer_instance
  | succ n ih => dsimp only [power]; infer_instance

lemma isIso_of_power (q : L ⟶ (Scheme.Modules.pullback g).obj L) (n : ℕ)
    [IsIso (power g L q (n+1))] : IsIso q := by
  letI := split_of_power g L q n
  letI := power_split g L q n
  let rest := (Scheme.Modules.pullback g).map (power g L q n) ≫
    (Scheme.Modules.pullbackComp g (basePower g n)).hom.app L
  haveI : Mono rest := by dsimp [rest]; infer_instance
  haveI : IsSplitEpi rest := by
    apply IsSplitEpi.mk'
    refine ⟨inv (power g L q (n+1)) ≫ q, ?_⟩
    change (inv (power g L q (n+1)) ≫ q) ≫ rest = _
    rw [Category.assoc]
    exact IsIso.inv_hom_id (power g L q (n+1))
  letI := isIso_of_mono_of_isSplitEpi rest
  have he : q = power g L q (n+1) ≫ inv rest := by
    change q = (q ≫ rest) ≫ inv rest
    simp
  rw [he]
  infer_instance

#print axioms power_eval
#print axioms isIso_of_power

end RawIteration

namespace CyclicMap
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
  (s : baseScheme k ⟶ M.X) (d : ℕ)
  (g : genericScheme k M ⟶ genericScheme k M)
  (hg : g ≫ genericStructure k M = genericStructure k M)
  (q : genericPower k M s d ⟶ (Scheme.Modules.pullback g).obj (genericPower k M s d))

local instance : AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

def action (φ : GenericDual k M s d) : GenericDual k M s d := q ≫ pulledInclusion g φ

include hg in
lemma action_scale (c : LaurentSeries k) (φ : GenericDual k M s d) :
    action k M s d g q (scale (scalarAt k M ⊤ c) φ) =
      scale (scalarAt k M ⊤ c) (action k M s d g q φ) := by
  change q ≫ pulledInclusion g (scale _ φ) = _
  rw [pull_scale, scalarTop_fixed k M g hg, scale_precomp]
  rfl

lemma action_sum {ι : Type*} (S : Finset ι) (φ : ι → GenericDual k M s d) :
    action k M s d g q (∑ i ∈ S, φ i) = ∑ i ∈ S, action k M s d g q (φ i) := by
  change q ≫ pulledInclusion g (∑ i ∈ S, φ i) = _
  rw [pull_sum]
  dsimp only [GenericDual] at φ
  simp only [Preadditive.comp_sum]
  rfl

include hg in
lemma iterate_scale (n : ℕ) (c : LaurentSeries k) (φ : GenericDual k M s d) :
    (action k M s d g q)^[n] (scale (scalarAt k M ⊤ c) φ) =
      scale (scalarAt k M ⊤ c) ((action k M s d g q)^[n] φ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, action_scale k M s d g hg]

lemma iterate_sum (n : ℕ) {ι : Type*} (S : Finset ι) (φ : ι → GenericDual k M s d) :
    (action k M s d g q)^[n] (∑ i ∈ S, φ i) = ∑ i ∈ S, (action k M s d g q)^[n] (φ i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, action_sum]
    simp only [Function.iterate_succ_apply']

include hg in
lemma iterate_basis (m : ℕ) (hm : 0 < m) (b : Fin m → GenericDual k M s d)
    (hb : HasBasis k M s d m b)
    (hq : ∀ ν, action k M s d g q (b ν) = b (next m hm ν))
    (φ : GenericDual k M s d) : (action k M s d g q)^[m] φ = φ := by
  have hi (n : ℕ) (ν : Fin m) : (action k M s d g q)^[n] (b ν) = b ((next m hm)^[n] ν) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hq, Function.iterate_succ_apply']
  obtain ⟨c, hc, _⟩ := hb φ
  rw [(combines_iff k M s d m b c φ).mp hc, iterate_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [iterate_scale k M s d g hg, hi, AlgebraizedActionLawsR0137.next_period]

end CyclicMap

namespace ShiftPeriod
lemma iterate_add {X : Scheme.{u}} (f : X ⟶ X) (a b : ℕ) :
    iterateHom f (a+b) = iterateHom f a ≫ iterateHom f b := by
  induction b with
  | zero => simp [iterateHom]
  | succ b ih =>
    change (iterateHom f (a+b) ≫ f) = iterateHom f a ≫ (iterateHom f b ≫ f)
    rw [ih, Category.assoc]

lemma iterate_double {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) :
    iterateHom (f ≫ f) n = iterateHom f (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterateHom, ih, Nat.mul_succ, iterate_add]
    simp [iterateHom, Category.assoc]

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
  (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
  (ha : Actions k M rot scal inv)

lemma shift_iterate_inclusion (n : ℕ) :
    iterateHom (shiftMap k M rot scal inv ha) n ≫ genericInclusion k M =
      genericInclusion k M ≫ iterateHom (rot.hom ≫ rot.hom) n := by
  induction n with
  | zero => simp [iterateHom]
  | succ n ih =>
    simp only [iterateHom, Category.assoc]
    rw [shiftMap_inclusion, ← Category.assoc (iterateHom (shiftMap k M rot scal inv ha) n), ih]
    simp only [Category.assoc]

lemma shift_iterate_structure (n : ℕ) :
    iterateHom (shiftMap k M rot scal inv ha) n ≫ genericStructure k M = genericStructure k M :=
  AlgebraizedActionLawsR0137.iterate_over _ _ (shiftMap_structure k M rot scal inv ha) n

lemma shift_period (m : ℕ) (hrm : r = 2*m) (hM : IsModel k T M) :
    iterateHom (shiftMap k M rot scal inv ha) m = 𝟙 _ := by
  have hrot := (AlgebraizedActionLawsR0137.laws M hM rot scal inv ha).1
  apply pullback.hom_ext
  · change _ ≫ genericInclusion k M = _
    rw [shift_iterate_inclusion, iterate_double, ← hrm, hrot, Category.comp_id, Category.id_comp]
    rfl
  · change _ ≫ genericStructure k M = _
    rw [shift_iterate_structure, Category.id_comp]
    rfl

end ShiftPeriod
namespace FinalConstruction
variable (k : Type u) [Field k] [CharZero k]
variable (m : ℕ) (hm : 0 < m) (he : Even m)
  {TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
  (MM : Model k TT) (hMM : IsModel k TT MM)
  (ss : baseScheme k ⟶ MM.X)
  (hss : MarkedLift k MM (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 ss)
  (rr : MM.X ≅ MM.X) (aa : kˣ → (MM.X ≅ MM.X)) (ii : MM.X ≅ MM.X)
  (hh : Actions k MM rr aa ii)

lemma exists_lift :
    ∃ e : Lift k MM ss m (shiftMap k MM rr aa ii hh),
      Cyclic k MM ss m m hm (shiftMap k MM rr aa ii hh) e
        (genericTheta k m hm he MM hMM ss hss) := by
  obtain ⟨q, hq⟩ := ModelShift.exists_generic_cyclic_map k m hm he MM hMM ss hss rr aa ii hh
  let g := shiftMap k MM rr aa ii hh
  let L := genericPower k MM ss m
  let j : L ⟶ (SheafOfModules.unit (genericScheme k MM).ringCatSheaf : (genericScheme k MM).Modules) :=
    restrictDual k MM ss m (idealInclusion (ss.ker^m))
  letI := genericInclusion_open k MM
  letI : Mono j := pulled_ideal_mono (genericInclusion k MM) (ss.ker^m)
    (AlgebraizedThetaSectionsR0138.power_invertible k (thetaChartBound m hm he) MM hMM ss hss m)
  have hp : RawIteration.basePower g m = 𝟙 _ :=
    (RawIteration.basePower_eq g m).trans (ShiftPeriod.shift_period k MM rr aa ii hh m rfl hMM)
  have hj : (fun φ => q ≫ pulledInclusion g φ)^[m] j = j :=
    CyclicMap.iterate_basis k MM ss m g (shiftMap_structure k MM rr aa ii hh) q m hm
      (genericTheta k m hm he MM hMM ss hss)
      (generic_theta_basis k m hm he TT MM hMM ss hss) hq j
  have hm' : m-1+1 = m := Nat.sub_add_cancel hm
  letI : IsIso (RawIteration.power g L q (m-1+1)) := by
    rw [hm']
    exact RawIteration.power_isIso g L q m hp j hj
  letI := RawIteration.isIso_of_power g L q (m-1)
  exact ⟨asIso q, hq⟩

#print axioms exists_lift
end FinalConstruction
#print axioms CyclicMap.iterate_basis
#print axioms ShiftPeriod.shift_period

end ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.shiftMap_isIso
#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.shift_marked

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.lift_unique_of_basis

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.cyclic_lift_unique

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.term_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.theta_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.uniform_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.numerator_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.uniform_wrap

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.numerator_wrap

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.CompletedShift.all_finite_numerators_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.factor_ideal_of_cover
#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.ActualStages.localMap_theta

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.ActualStages.exists_finite_cleared_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.FactorCompletion.exists_map

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.ModelShift.exists_algebraic_cleared_shift

#print axioms ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.StageLocalShift.factor_numerator

namespace ArithmeticThetaGeometricLiftsR0141
theorem geometric_shift_lift :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∃! eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha), ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha
  obtain ⟨e, heB⟩ := GeometricShiftLiftR0141.FinalConstruction.exists_lift k m hm he M hM s hs rot scal inv ha
  refine ⟨e, heB, ?_⟩
  intro e' heB'
  exact GeometricShiftLiftR0141.cyclic_lift_unique k m hm he M hM s hs rot scal inv ha e' e heB' heB
#print axioms geometric_shift_lift
end ArithmeticThetaGeometricLiftsR0141
