import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Theorems.Thm_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
import FinitePrincipalSupport
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped nonZeroDivisors

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

/-- The actual weighted orders have finite support; no summability premise is added. -/
theorem finite_weighted_principal_support
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (hg : g ≠ 0) :
    (Function.support (fun x => (placeDegree k f x : ℤ) * principalOrder X g x)).Finite := by
  apply (finite_principal_support X k f hcurve g hg).subset
  intro x hx
  change principalOrder X g x ≠ 0
  intro hzero
  exact hx (by simp [hzero])

/-- A matching divisor's weighted degree is the finite sum of the genuine point orders. -/
theorem weightedDegree_eq_finsum_principalOrder
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (g : X.functionField) (D : X →₀ ℤ) (hD : MatchesPrincipalOrder X g D) :
    weightedDegree k f D = ∑ᶠ x, (placeDegree k f x : ℤ) * principalOrder X g x := by
  classical
  have hs : Function.support (fun x => (placeDegree k f x : ℤ) * principalOrder X g x) ⊆
      (D.support : Set X) := by
    intro x hx
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hzero
    exact hx (by change (placeDegree k f x : ℤ) * principalOrder X g x = 0
                 rw [← hD x, hzero, mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hs]
  unfold weightedDegree Finsupp.sum
  apply Finset.sum_congr rfl
  intro x hx
  rw [hD x]

/-- At a codimension-one point the order of a nonzero stalk element is its quotient length. -/
theorem principalOrder_stalk_eq_length
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : Order.coheight x = 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    principalOrder X (algebraMap (X.presheaf.stalk x) X.functionField a) x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {a})).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [principalOrder, Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change ((Ring.ordFrac (X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField a)).unzeroD 1).toAdd = _
  rw [Ring.ordFrac_eq_ord _ ha]
  rw [← Ring.ordMonoidWithZeroHom_eq_ordMonoidHom
    (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ : (X.presheaf.stalk x)⁰)]
  rfl

/-- The local length formula for a rational function, valid also at singular points. -/
theorem principalOrder_eq_sub_lengths
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : Order.coheight x = 1) (g : X.functionField) (hg : g ≠ 0)
    (a b : X.presheaf.stalk x) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : g * algebraMap (X.presheaf.stalk x) X.functionField b =
      algebraMap (X.presheaf.stalk x) X.functionField a) :
    principalOrder X g x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {a})).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {b})).toNat : ℤ) := by
  have hb' : algebraMap (X.presheaf.stalk x) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hb
  have hmul : principalOrder X g x +
      principalOrder X (algebraMap (X.presheaf.stalk x) X.functionField b) x =
      principalOrder X (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
    change Scheme.ord g x + Scheme.ord _ x = Scheme.ord _ x
    rw [← Scheme.ord_mul hg hb', hab]
  rw [principalOrder_stalk_eq_length X x hx b hb,
    principalOrder_stalk_eq_length X x hx a ha] at hmul
  exact eq_sub_of_add_eq hmul

/-- Every nonzero rational function admits the local numerator/denominator length formula. -/
theorem exists_principalOrder_eq_sub_lengths
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : Order.coheight x = 1) (g : X.functionField) (hg : g ≠ 0) :
    ∃ a b : X.presheaf.stalk x, a ≠ 0 ∧ b ≠ 0 ∧
      g * algebraMap (X.presheaf.stalk x) X.functionField b =
        algebraMap (X.presheaf.stalk x) X.functionField a ∧
      principalOrder X g x =
        ((Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.span {b})).toNat : ℤ) := by
  let R := X.presheaf.stalk x
  obtain ⟨z, hz⟩ := IsLocalization.surj (R⁰ : Submonoid R) g
  have hb : (z.2 : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp z.2.2
  have hb' : algebraMap R X.functionField (z.2 : R) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hb
  have ha : z.1 ≠ 0 := by
    intro hzero
    have : g * algebraMap R X.functionField (z.2 : R) = 0 := by
      simpa [hzero] using hz
    exact (mul_ne_zero hg hb') this
  exact ⟨z.1, z.2, ha, hb, hz,
    principalOrder_eq_sub_lengths X x hx g hg z.1 z.2 ha hb hz⟩

/-- Every point occurring in a matching divisor really has codimension one. -/
theorem coheight_eq_one_of_mem_matching_support
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) (D : X →₀ ℤ) (hD : MatchesPrincipalOrder X g D)
    (x : X) (hx : x ∈ D.support) : Order.coheight x = 1 := by
  by_contra hcodim
  have hz : D x = 0 := (hD x).trans (Scheme.ord_eq_zero_of_coheight_neq_one hcodim g)
  exact (Finsupp.mem_support_iff.mp hx) hz

/-- A finite local-length presentation of the weighted degree, without a DVR assumption. -/
theorem weightedDegree_local_length_presentation
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (g : X.functionField) (D : X →₀ ℤ) (hg : g ≠ 0)
    (hD : MatchesPrincipalOrder X g D) :
    ∃ a b : (x : D.support) → X.presheaf.stalk x.1,
      (∀ x, a x ≠ 0 ∧ b x ≠ 0 ∧
        g * algebraMap (X.presheaf.stalk x.1) X.functionField (b x) =
          algebraMap (X.presheaf.stalk x.1) X.functionField (a x)) ∧
      weightedDegree k f D = ∑ x : D.support, (placeDegree k f x.1 : ℤ) *
        (((Module.length (X.presheaf.stalk x.1)
          ((X.presheaf.stalk x.1) ⧸ Ideal.span {a x})).toNat : ℤ) -
         ((Module.length (X.presheaf.stalk x.1)
          ((X.presheaf.stalk x.1) ⧸ Ideal.span {b x})).toNat : ℤ)) := by
  classical
  have hlocal : ∀ x : D.support, ∃ a b : X.presheaf.stalk x.1,
      a ≠ 0 ∧ b ≠ 0 ∧
      g * algebraMap (X.presheaf.stalk x.1) X.functionField b =
        algebraMap (X.presheaf.stalk x.1) X.functionField a ∧
      principalOrder X g x.1 =
        ((Module.length (X.presheaf.stalk x.1)
          ((X.presheaf.stalk x.1) ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk x.1)
          ((X.presheaf.stalk x.1) ⧸ Ideal.span {b})).toNat : ℤ) := by
    intro x
    exact exists_principalOrder_eq_sub_lengths X x.1
      (coheight_eq_one_of_mem_matching_support X g D hD x.1 x.2) g hg
  choose a b ha hb hab hord using hlocal
  refine ⟨a, b, fun x => ⟨ha x, hb x, hab x⟩, ?_⟩
  unfold weightedDegree Finsupp.sum
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hD x.1, hord x]

end ArithmeticThetaCurveDegree

#print axioms ArithmeticThetaCurveDegree.finite_weighted_principal_support
#print axioms ArithmeticThetaCurveDegree.weightedDegree_eq_finsum_principalOrder
#print axioms ArithmeticThetaCurveDegree.principalOrder_stalk_eq_length

#print axioms ArithmeticThetaCurveDegree.principalOrder_eq_sub_lengths
#print axioms ArithmeticThetaCurveDegree.exists_principalOrder_eq_sub_lengths

#print axioms ArithmeticThetaCurveDegree.coheight_eq_one_of_mem_matching_support
#print axioms ArithmeticThetaCurveDegree.weightedDegree_local_length_presentation

namespace ArithmeticThetaCurveDegree.DegreeCohomology

variable (X : Scheme.{u}) [IsIntegral X] (g : X.functionField)

/-- Pairs of regular sections whose ratio is the prescribed rational function. -/
def regularPairs (U : X.Opens) : Submodule Γ(X,U) (Γ(X,U) × Γ(X,U)) where
  carrier := {p | ∀ h : Nonempty U, g * X.germToFunctionField U p.1 = X.germToFunctionField U p.2}
  zero_mem' := by intro h; simp
  add_mem' := by
    intro p q hp hq h
    simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add, hp h, hq h]
  smul_mem' := by
    intro a p hp h
    change g * X.germToFunctionField U (a * p.1) = X.germToFunctionField U (a * p.2)
    simp only [map_mul]
    rw [← mul_assoc, mul_comm g, mul_assoc, hp h]

lemma germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : U ≤ V) (a : Γ(X,V)) :
    X.germToFunctionField U ((X.presheaf.map (homOfLE h).op) a) =
      X.germToFunctionField V a := by
  change (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField U) a = _
  rw [Scheme.germToFunctionField, TopCat.Presheaf.germ_res]

lemma regularPairs_res {U V : X.Opens} (h : U ≤ V) (p : regularPairs X g V) :
    ((X.presheaf.map (homOfLE h).op) p.1.1,
      (X.presheaf.map (homOfLE h).op) p.1.2) ∈ regularPairs X g U := by
  intro hU
  letI : Nonempty V := Nonempty.map (Set.inclusion h) hU
  have heq (a : Γ(X,V)) : X.germToFunctionField U ((X.presheaf.map (homOfLE h).op) a) =
      X.germToFunctionField V a := by
    change (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField U) a = _
    rw [Scheme.germToFunctionField, TopCat.Presheaf.germ_res]
  rw [heq, heq]
  exact p.2 inferInstance

variable (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))

@[reducible] def pairBaseModule (U : X.Opens) : Module k (regularPairs X g U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  exact Module.compHom (regularPairs X g U) (algebraMap k Γ(X,U))

/-- The denominator relation as an actual module presheaf. -/
def pairsPresheaf : OModulePresheaf f where
  obj U := regularPairs X g U
  module U := pairBaseModule X g k f U
  moduleSections U := inferInstance
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    exact ⟨fun a b p => Subtype.ext (Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _))⟩
  res {U V} h :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
    { toFun := fun p => ⟨_, regularPairs_res X g h p⟩
      map_add' := fun p q => Subtype.ext (Prod.ext (map_add _ _ _) (map_add _ _ _))
      map_smul' := by
        intro a p
        apply Subtype.ext
        apply Prod.ext
        · change (Scheme.TwoAffineOpenCover.restrictAlgHom f h)
            (algebraMap k Γ(X,V) a * p.1.1) =
              algebraMap k Γ(X,U) a * (Scheme.TwoAffineOpenCover.restrictAlgHom f h) p.1.1
          rw [map_mul, AlgHom.commutes]
        · change (Scheme.TwoAffineOpenCover.restrictAlgHom f h)
            (algebraMap k Γ(X,V) a * p.1.2) =
              algebraMap k Γ(X,U) a * (Scheme.TwoAffineOpenCover.restrictAlgHom f h) p.1.2
          rw [map_mul, AlgHom.commutes] }
  res_smul h a p := by
    apply Subtype.ext
    exact Prod.ext (map_mul _ _ _) (map_mul _ _ _)
  res_refl U := by
    letI := pairBaseModule X g k f U
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change ((X.presheaf.map (homOfLE (le_refl U)).op) p.1.1,
      (X.presheaf.map (homOfLE (le_refl U)).op) p.1.2) = p.1
    simp
  res_comp {U V W} h h' := by
    letI := pairBaseModule X g k f U
    letI := pairBaseModule X g k f V
    letI := pairBaseModule X g k f W
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    dsimp
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

theorem pairsPresheaf_coherent [IsLocallyNoetherian X] :
    (pairsPresheaf X g k f).IsCoherent := by
  intro U
  letI : IsNoetherianRing Γ(X,U.1) := IsLocallyNoetherian.component_noetherian U
  exact inferInstanceAs (Module.Finite Γ(X,U.1) (regularPairs X g U.1))

theorem pairsPresheaf_quasicoherent :
    (pairsPresheaf X g k f).IsQuasicoherent := by
  intro U s
  let h := X.basicOpen_le s
  let r := (X.presheaf.map (homOfLE h).op).hom
  have hunit := OModulePresheaf.isQuasicoherent_unit f U s
  constructor
  · intro q
    by_cases hV : Nonempty (X.basicOpen s)
    · letI := hV
      letI : Nonempty U.1 := Nonempty.map (Set.inclusion h) hV
      obtain ⟨m, a, ha⟩ := hunit.1 q.1.1
      obtain ⟨n, b, hb⟩ := hunit.1 q.1.2
      change Γ(X,U.1) at a b
      change r a = r (s ^ m) * q.1.1 at ha
      change r b = r (s ^ n) * q.1.2 at hb
      have hpa : r (s ^ n * a) = r (s ^ (m+n)) * q.1.1 := by
        simp only [map_mul, map_pow, ha]
        ring
      have hpb : r (s ^ m * b) = r (s ^ (m+n)) * q.1.2 := by
        simp only [map_mul, map_pow, hb]
        ring
      have hp : (s ^ n * a, s ^ m * b) ∈ regularPairs X g U.1 := by
        intro hU
        rw [← germ_restrict X h, ← germ_restrict X h]
        change g * X.germToFunctionField (X.basicOpen s) (r (s ^ n * a)) =
          X.germToFunctionField (X.basicOpen s) (r (s ^ m * b))
        rw [hpa, hpb, map_mul, map_mul, ← mul_assoc, mul_comm g, mul_assoc, q.2 hV]
      refine ⟨m+n, ⟨_, hp⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext hpa hpb
    · have hempty : X.basicOpen s = ⊥ := by
        apply SetLike.coe_injective
        exact Set.not_nonempty_iff_eq_empty.mp (by
          rintro ⟨x, hx⟩
          exact hV ⟨⟨x, hx⟩⟩)
      haveI : Subsingleton Γ(X,X.basicOpen s) := hempty ▸ inferInstance
      refine ⟨0, 0, ?_⟩
      apply Subtype.ext
      exact Subsingleton.elim _ _
  · intro p hp
    obtain ⟨m, hm⟩ := hunit.2 p.1.1 (congrArg (fun q => q.1.1) hp)
    obtain ⟨n, hn⟩ := hunit.2 p.1.2 (congrArg (fun q => q.1.2) hp)
    change s ^ m * p.1.1 = 0 at hm
    change s ^ n * p.1.2 = 0 at hn
    refine ⟨m+n, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change s ^ (m+n) * p.1.1 = 0
      rw [Nat.add_comm, pow_add, mul_assoc, hm, mul_zero]
    · change s ^ (m+n) * p.1.2 = 0
      rw [pow_add, mul_assoc, hn, mul_zero]

/-- Projection to the local denominator. -/
def denominatorProjection : (pairsPresheaf X g k f).Hom (OModulePresheaf.unit f) where
  app U :=
    { toFun := fun p => p.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  app_smul _ _ _ := rfl
  naturality _ := LinearMap.ext fun _ => rfl

/-- Projection to the corresponding local numerator. -/
def numeratorProjection : (pairsPresheaf X g k f).Hom (OModulePresheaf.unit f) where
  app U :=
    { toFun := fun p => p.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  app_smul _ _ _ := rfl
  naturality _ := LinearMap.ext fun _ => rfl

private lemma open_eq_bot (U : X.Opens) (hU : ¬ Nonempty U) : U = ⊥ := by
  apply SetLike.coe_injective
  exact Set.not_nonempty_iff_eq_empty.mp (by
    rintro ⟨x, hx⟩
    exact hU ⟨⟨x, hx⟩⟩)

theorem denominatorProjection_injective (U : X.Opens) :
    Function.Injective ((denominatorProjection X g k f).app U) := by
  intro p q hpq
  by_cases hU : Nonempty U
  · letI := hU
    apply Subtype.ext
    apply Prod.ext hpq
    apply X.germToFunctionField_injective U
    rw [← p.2 hU, ← q.2 hU]
    change p.1.1 = q.1.1 at hpq
    rw [hpq]
  · have hbot := open_eq_bot X U hU
    subst U
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

theorem numeratorProjection_injective (hg : g ≠ 0) (U : X.Opens) :
    Function.Injective ((numeratorProjection X g k f).app U) := by
  intro p q hpq
  by_cases hU : Nonempty U
  · letI := hU
    apply Subtype.ext
    apply Prod.ext _ hpq
    apply X.germToFunctionField_injective U
    apply mul_left_cancel₀ hg
    rw [p.2 hU, q.2 hU]
    change p.1.2 = q.1.2 at hpq
    rw [hpq]
  · have hbot := open_eq_bot X U hU
    subst U
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The quotient by regular denominators. -/
def denominatorQuotient : OModulePresheaf f :=
  OModulePresheaf.coker (denominatorProjection X g k f)

/-- The quotient by regular numerators. -/
def numeratorQuotient : OModulePresheaf f :=
  OModulePresheaf.coker (numeratorProjection X g k f)

def denominatorSES : (pairsPresheaf X g k f).SES (OModulePresheaf.unit f)
    (denominatorQuotient X g k f) where
  inc := denominatorProjection X g k f
  proj := (OModulePresheaf.imCokerSES (denominatorProjection X g k f)).proj
  injective := denominatorProjection_injective X g k f
  surjective _ := Submodule.Quotient.mk_surjective _
  exact _ := (Submodule.ker_mkQ _).symm

def numeratorSES (hg : g ≠ 0) : (pairsPresheaf X g k f).SES (OModulePresheaf.unit f)
    (numeratorQuotient X g k f) where
  inc := numeratorProjection X g k f
  proj := (OModulePresheaf.imCokerSES (numeratorProjection X g k f)).proj
  injective := numeratorProjection_injective X g k f hg
  surjective _ := Submodule.Quotient.mk_surjective _
  exact _ := (Submodule.ker_mkQ _).symm

/-- Global cancellation of the two actual quotient Euler characteristics. -/
theorem numerator_denominator_eulerChar_eq [IsLocallyNoetherian X] [IsProper f]
    (hg : g ≠ 0) (K : X.OrderedAffineCover) :
    (numeratorQuotient X g k f).eulerChar K =
      (denominatorQuotient X g k f).eulerChar K := by
  have hu : (OModulePresheaf.unit f).IsCoherent := by
    intro U
    exact inferInstanceAs (Module.Finite Γ(X,U.1) Γ(X,U.1))
  have hqu := OModulePresheaf.isQuasicoherent_unit f
  have hqp := pairsPresheaf_quasicoherent X g k f
  have hfunit := OModulePresheaf.cechFinite_of_isProper _ hu hqu K
  have hfpair := OModulePresheaf.cechFinite_of_isProper _ (pairsPresheaf_coherent X g k f) hqp K
  have hfnum : (numeratorQuotient X g k f).CechFinite K :=
    OModulePresheaf.cechFinite_of_isProper _
      (OModulePresheaf.isCoherent_coker _ hu)
      (OModulePresheaf.isQuasicoherent_coker _ hqu hqp) K
  have hfden : (denominatorQuotient X g k f).CechFinite K :=
    OModulePresheaf.cechFinite_of_isProper _
      (OModulePresheaf.isCoherent_coker _ hu)
      (OModulePresheaf.isQuasicoherent_coker _ hqu hqp) K
  have hnum := OModulePresheaf.eulerChar_eq_add_of_affSES
    (numeratorSES X g k f hg).toAffSES K hfpair hfunit hfnum
  have hden := OModulePresheaf.eulerChar_eq_add_of_affSES
    (denominatorSES X g k f).toAffSES K hfpair hfunit hfden
  exact add_left_cancel (hnum.symm.trans hden)

/-- A finite ordered affine cover in the original universe, supplied by properness. -/
def properOrderedAffineCover [IsProper f] : X.OrderedAffineCover := by
  classical
  letI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let C := X.affineCover.finiteSubcover
  exact
    { ι := C.I₀
      instFintype := inferInstance
      instLinearOrder := LinearOrder.lift' (Fintype.equivFin C.I₀)
        (Fintype.equivFin C.I₀).injective
      U := fun i => (C.f i).opensRange
      isAffineOpen := fun i => isAffineOpen_opensRange (C.f i)
      iSup_eq_top := C.iSup_opensRange }

/-- Properness provides a cover on which the two actual quotient Euler characteristics agree. -/
theorem exists_numerator_denominator_eulerChar_eq [IsLocallyNoetherian X] [IsProper f]
    (hg : g ≠ 0) : ∃ K : X.OrderedAffineCover,
    (numeratorQuotient X g k f).eulerChar K =
      (denominatorQuotient X g k f).eulerChar K :=
  ⟨properOrderedAffineCover X k f, numerator_denominator_eulerChar_eq X g k f hg _⟩

end ArithmeticThetaCurveDegree.DegreeCohomology

#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.numerator_denominator_eulerChar_eq

#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.exists_numerator_denominator_eulerChar_eq


namespace ArithmeticThetaCurveDegree.DegreeCohomology

lemma finite_quotient_of_nonzero
    (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] [Ring.DimensionLEOne R]
    (a : R) (ha : a ≠ 0) : Module.Finite k (R ⧸ Ideal.span {a}) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hlen : IsFiniteLength R (R ⧸ Ideal.span {a}) :=
    isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha)
  haveI : IsArtinian R (R ⧸ Ideal.span {a}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {a}) := isArtinian_of_tower R inferInstance
  exact Module.finite_of_isArtinianRing k _

variable (X : Scheme.{u}) [IsIntegral X]
    (g : X.functionField) (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k))

lemma finite_coker_on_affine [LocallyOfFiniteType f]
    (hcurve : OneDimensionalCharts X)
    (F : OModulePresheaf f) (φ : F.Hom (OModulePresheaf.unit f))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (a : Γ(X,U)) (ha : a ≠ 0) (haφ : a ∈ LinearMap.range (φ.app U)) :
    Module.Finite k ((OModulePresheaf.coker φ).obj U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  haveI := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom f U hU
  haveI := hcurve U hU
  haveI := finite_quotient_of_nonzero k Γ(X,U) a ha
  let ψ : Γ(X,U) →ₗ[Γ(X,U)] (OModulePresheaf.coker φ).obj U :=
    (OModulePresheaf.imCokerSES φ).proj.appSections U
  have hker : Ideal.span {a} ≤ LinearMap.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (Submodule.Quotient.mk_eq_zero _).mpr haφ
  let q := (Ideal.span {a}).liftQ ψ hker
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Ideal.Quotient.mk _ b, rfl⟩
  exact Module.Finite.of_surjective (q.restrictScalars k) hsurj

lemma quotients_finite_on_nonempty_affine [LocallyOfFiniteType f]
    (hcurve : OneDimensionalCharts X) (hg : g ≠ 0)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Module.Finite k ((denominatorQuotient X g k f).obj U) ∧
    Module.Finite k ((numeratorQuotient X g k f).obj U) := by
  let R := Γ(X,U)
  letI : IsFractionRing R X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨z, hz⟩ := IsLocalization.surj (R⁰ : Submonoid R) g
  have hb : (z.2 : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp z.2.2
  have hb' : algebraMap R X.functionField (z.2 : R) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hb
  have ha : z.1 ≠ 0 := by
    intro ha
    have hzero : g * algebraMap R X.functionField (z.2 : R) = 0 := by simpa [ha] using hz
    exact mul_ne_zero hg hb' hzero
  have hp : ((z.2 : R), z.1) ∈ regularPairs X g U := by
    intro h
    exact hz
  let p : regularPairs X g U := ⟨_, hp⟩
  exact ⟨finite_coker_on_affine X k f hcurve _ _ U hU _ hb ⟨p, rfl⟩,
    finite_coker_on_affine X k f hcurve _ _ U hU _ ha ⟨p, rfl⟩⟩

lemma quotients_finite_on_affine [LocallyOfFiniteType f]
    (hcurve : OneDimensionalCharts X) (hg : g ≠ 0)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite k ((denominatorQuotient X g k f).obj U) ∧
    Module.Finite k ((numeratorQuotient X g k f).obj U) := by
  by_cases hne : Nonempty U
  · letI := hne
    exact quotients_finite_on_nonempty_affine X g k f hcurve hg U hU
  · have hbot : U = ⊥ := by
      apply SetLike.coe_injective
      exact Set.not_nonempty_iff_eq_empty.mp (by
        rintro ⟨x, hx⟩
        exact hne ⟨⟨x, hx⟩⟩)
    subst U
    haveI : Subsingleton ((OModulePresheaf.unit f).obj ⊥) :=
      inferInstanceAs (Subsingleton Γ(X,⊥))
    haveI : Subsingleton ((denominatorQuotient X g k f).obj ⊥) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    haveI : Subsingleton ((numeratorQuotient X g k f).obj ⊥) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact ⟨inferInstance, inferInstance⟩

lemma quotient_cochains_finite [LocallyOfFiniteType f] [IsSeparated f]
    (hcurve : OneDimensionalCharts X) (hg : g ≠ 0)
    (K : X.OrderedAffineCover) (n : ℕ) :
    Module.Finite k ((denominatorQuotient X g k f).cochain K n) ∧
    Module.Finite k ((numeratorQuotient X g k f).cochain K n) := by
  haveI (s : K.Idx n) :=
    (quotients_finite_on_affine X g k f hcurve hg (K.inter s) (K.isAffineOpen_inter f s)).1
  haveI (s : K.Idx n) :=
    (quotients_finite_on_affine X g k f hcurve hg (K.inter s) (K.isAffineOpen_inter f s)).2
  exact ⟨inferInstance, inferInstance⟩

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.quotients_finite_on_affine
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.quotient_cochains_finite



namespace ArithmeticThetaCurveDegree.DegreeCohomology
open P2MW.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton.FinSuppLen

/-- The residue-degree-weighted local length formula over an arbitrary field. -/
theorem finrank_eq_sum_weighted_localLength
    (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (T : Finset (MaximalSpectrum S)) (H : Type u)
    [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H]
    [Module.Finite k H]
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T →
      Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    (Module.finrank k H : ℕ∞) = ∑ 𝔪 ∈ T,
      (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime 𝔪.asIdeal)
          (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
  classical
  suffices h : ∀ d : ℕ, ∀ (H : Type u) [AddCommGroup H] [Module S H]
      [Module k H] [IsScalarTower k S H] [Module.Finite k H],
      (∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) →
      Module.finrank k H = d → (Module.finrank k H : ℕ∞) = ∑ 𝔪 ∈ T,
        (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) * loclen 𝔪 H by
    exact h _ H hT rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro H _ _ _ _ _ hT hd
    by_cases hH : Subsingleton H
    · rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
      symm
      apply Finset.sum_eq_zero
      intro 𝔪 h𝔪
      haveI : Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
        have hinj := IsLocalizedModule.map_injective 𝔪.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl H)
          (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl H)
          (0 : H →ₗ[S] H) (fun a b _ => Subsingleton.elim a b)
        refine ⟨fun a b => hinj ?_⟩
        simp
      simp [loclen, Module.length_eq_zero]
    · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
      haveI : IsArtinian S H := isArtinian_of_tower k (inferInstance : IsArtinian k H)
      haveI : IsAtomic (Submodule S H) := isAtomic_of_orderBot_wellFounded_lt
        (wellFounded_lt : WellFounded ((· < ·) : Submodule S H → Submodule S H → Prop))
      obtain ⟨N, hNat⟩ := IsAtomic.exists_atom (Submodule S H)
      haveI hN : IsSimpleModule S N := isSimpleModule_iff_isAtom.mpr hNat
      obtain ⟨𝔪₀, h𝔪₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hN
      haveI : Module.Finite k N := Module.Finite.of_injective
        (N.subtype.restrictScalars k) N.injective_subtype
      have hNdeg : Module.finrank k N = Module.finrank k (S ⧸ 𝔪₀) :=
        (e.restrictScalars k).finrank_eq
      haveI : Nontrivial N := IsSimpleModule.nontrivial S N
      have hNpos : 0 < Module.finrank k N := Module.finrank_pos
      have hmemT : (⟨𝔪₀, h𝔪₀⟩ : MaximalSpectrum S) ∈ T := by
        by_contra hnot
        have hsub := subsingleton_submodule H N ⟨𝔪₀, h𝔪₀⟩ (hT _ hnot)
        have h0 : loclen ⟨𝔪₀, h𝔪₀⟩ N = 0 := @Module.length_eq_zero _ _ _ _ _ hsub
        rw [loclen_eq_one_of_equiv_quotient N 𝔪₀ h𝔪₀ e] at h0
        exact one_ne_zero h0
      haveI : Module.Finite k (H ⧸ N) :=
        Module.Finite.of_surjective (N.mkQ.restrictScalars k) (Submodule.mkQ_surjective N)
      have hq : Module.finrank k (H ⧸ N) = Module.finrank k H - Module.finrank k N :=
        Submodule.finrank_quotient N
      have hlt : Module.finrank k (H ⧸ N) < d := by
        have hpos : 0 < Module.finrank k H := Module.finrank_pos
        rw [hq, ← hd]
        omega
      have ihq := ih _ hlt (H ⧸ N)
        (fun 𝔪 h𝔪 => subsingleton_quotient H N 𝔪 (hT 𝔪 h𝔪)) rfl
      have hsumN : ∑ 𝔪 ∈ T, (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) * loclen 𝔪 N =
          (Module.finrank k N : ℕ∞) := by
        rw [Finset.sum_eq_single_of_mem (⟨𝔪₀, h𝔪₀⟩ : MaximalSpectrum S) hmemT]
        · rw [loclen_eq_one_of_equiv_quotient N 𝔪₀ h𝔪₀ e, mul_one, hNdeg]
        · intro 𝔪 hm hne
          rw [loclen_eq_zero_of_equiv_quotient N 𝔪₀ h𝔪₀ e 𝔪 hne, mul_zero]
      calc
        (Module.finrank k H : ℕ∞) =
            ((Module.finrank k N + Module.finrank k (H ⧸ N) : ℕ) : ℕ∞) := by
          have hle := LinearMap.finrank_le_finrank_of_injective
            (f := N.subtype.restrictScalars k) N.injective_subtype
          congr 1
          rw [hq]
          omega
        _ = (Module.finrank k N : ℕ∞) +
            ∑ 𝔪 ∈ T, (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) * loclen 𝔪 (H ⧸ N) := by
          rw [Nat.cast_add, ihq]
        _ = ∑ 𝔪 ∈ T, (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) * loclen 𝔪 H := by
          rw [← hsumN, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro 𝔪 hm
          rw [loclen_eq_add H N 𝔪, mul_add]

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.finrank_eq_sum_weighted_localLength


namespace ArithmeticThetaCurveDegree.DegreeCohomology
variable {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}

lemma cochain_finrank_eq (F : OModulePresheaf f) (K : X.OrderedAffineCover)
    (hfin : ∀ n, Module.Finite k (F.cochain K n)) (n : ℕ) :
    Module.finrank k (F.HSucc K n) + Module.finrank k (LinearMap.range (F.d K n)) +
      Module.finrank k (LinearMap.range (F.d K (n+1))) =
      Module.finrank k (F.cochain K (n+1)) := by
  letI (i : ℕ) := hfin i
  have hle : LinearMap.range (F.d K n) ≤ LinearMap.ker (F.d K (n+1)) :=
    LinearMap.range_le_ker_iff.mpr (F.d_comp_d K n)
  have hquot := Submodule.finrank_quotient_add_finrank
    ((LinearMap.range (F.d K n)).comap (LinearMap.ker (F.d K (n+1))).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hquot
  change Module.finrank k (F.HSucc K n) + _ = _ at hquot
  have hrank := (F.d K (n+1)).finrank_range_add_finrank_ker
  omega

lemma eulerChar_eq_alternating_cochain_finrank
    (F : OModulePresheaf f) (K : X.OrderedAffineCover)
    (hfin : ∀ n, Module.Finite k (F.cochain K n)) :
    F.eulerChar K = ∑ i ∈ Finset.range (Fintype.card K.ι),
      (-1 : ℤ)^i * (Module.finrank k (F.cochain K i) : ℤ) := by
  letI (i : ℕ) := hfin i
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n+1), (-1 : ℤ)^i * (F.cechFinrank K i : ℤ)) +
        (-1 : ℤ)^n * (Module.finrank k (LinearMap.range (F.d K n)) : ℤ) =
      ∑ i ∈ Finset.range (n+1), (-1 : ℤ)^i *
        (Module.finrank k (F.cochain K i) : ℤ) := by
    intro n
    induction n with
    | zero =>
      have h := (F.d K 0).finrank_range_add_finrank_ker
      simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, one_mul,
        OModulePresheaf.cechFinrank_zero]
      exact_mod_cast (add_comm _ _).trans h
    | succ n ih =>
      simp only [Finset.sum_range_succ (n := n+1)]
      have hd := cochain_finrank_eq F K hfin n
      have hd' : (Module.finrank k (F.HSucc K n) : ℤ) +
          (Module.finrank k (LinearMap.range (F.d K n)) : ℤ) +
          (Module.finrank k (LinearMap.range (F.d K (n+1))) : ℤ) =
          (Module.finrank k (F.cochain K (n+1)) : ℤ) := by exact_mod_cast hd
      rw [OModulePresheaf.cechFinrank_succ]
      simp only [pow_succ] at *
      linear_combination ih + (-1 : ℤ)^n * (-1) * hd'
  unfold OModulePresheaf.eulerChar
  by_cases hc : Fintype.card K.ι = 0
  · simp [hc]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hc
    have hempty := (F.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le K).2.1
      (n+1) (by omega)
    haveI : Subsingleton (F.cochain K (n+1)) := hempty
    have hz : Module.finrank k (LinearMap.range (F.d K n)) = 0 :=
      Module.finrank_zero_of_subsingleton
    simpa [hn, hz] using hsum n

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.eulerChar_eq_alternating_cochain_finrank


namespace ArithmeticThetaCurveDegree.DegreeCohomology

lemma length_coker_comp_of_injective
    {R P Q T : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (α : P →ₗ[R] Q) (β : Q →ₗ[R] T) (hβ : Function.Injective β) :
    Module.length R (T ⧸ LinearMap.range (β ∘ₗ α)) =
      Module.length R (Q ⧸ LinearMap.range α) +
      Module.length R (T ⧸ LinearMap.range β) := by
  let A := LinearMap.range α
  let B := LinearMap.range (β ∘ₗ α)
  let C := LinearMap.range β
  have hBC : B ≤ C := LinearMap.range_comp_le_range _ _
  have hAB : A ≤ B.comap β := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  let l := A.mapQ B β hAB
  let r := Submodule.factor hBC
  have hl : Function.Injective l := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ]
    have heq : B.comap β = A := by
      apply le_antisymm _ hAB
      intro x hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, hβ hy⟩
    rw [heq, Submodule.mkQ_map_self]
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x, rfl⟩ := C.mkQ_surjective y
    exact ⟨B.mkQ x, rfl⟩
  have hex : Function.Exact l r := by
    rw [LinearMap.exact_iff]
    change LinearMap.ker (B.mapQ C LinearMap.id hBC) = LinearMap.range (A.mapQ B β hAB)
    rw [Submodule.ker_mapQ, Submodule.range_mapQ, Submodule.comap_id]
  exact Module.length_eq_add_of_exact l r hl hr hex

lemma length_difference_cokers
    {R P : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    (α : R →ₗ[R] P) (β γ : P →ₗ[R] R)
    (hβ : Function.Injective β) (hγ : Function.Injective γ)
    (hfinβ : IsFiniteLength R (R ⧸ LinearMap.range (β ∘ₗ α)))
    (hfinγ : IsFiniteLength R (R ⧸ LinearMap.range (γ ∘ₗ α))) :
    ((Module.length R (R ⧸ LinearMap.range γ)).toNat : ℤ) -
      ((Module.length R (R ⧸ LinearMap.range β)).toNat : ℤ) =
    ((Module.length R (R ⧸ LinearMap.range (γ ∘ₗ α))).toNat : ℤ) -
      ((Module.length R (R ⧸ LinearMap.range (β ∘ₗ α))).toNat : ℤ) := by
  have hb := length_coker_comp_of_injective α β hβ
  have hc := length_coker_comp_of_injective α γ hγ
  have hbfinite := Module.length_ne_top_iff.mpr hfinβ
  have hcfinite := Module.length_ne_top_iff.mpr hfinγ
  simp only [hb, ne_eq, ENat.add_eq_top, not_or] at hbfinite
  simp only [hc, ne_eq, ENat.add_eq_top, not_or] at hcfinite
  have hbN := congrArg ENat.toNat hb
  have hcN := congrArg ENat.toNat hc
  rw [ENat.toNat_add hbfinite.1 hbfinite.2] at hbN
  rw [ENat.toNat_add hcfinite.1 hcfinite.2] at hcN
  omega

/-- Local denominator and numerator projections have the same cancelled correction term. -/
lemma length_difference_projections
    {R P : Type u} [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [AddCommGroup P] [Module R P]
    (β γ : P →ₗ[R] R) (hβ : Function.Injective β) (hγ : Function.Injective γ)
    (p : P) (hb : β p ∈ R⁰) (hc : γ p ∈ R⁰) :
    ((Module.length R (R ⧸ LinearMap.range γ)).toNat : ℤ) -
      ((Module.length R (R ⧸ LinearMap.range β)).toNat : ℤ) =
    ((Module.length R (R ⧸ Ideal.span {γ p})).toNat : ℤ) -
      ((Module.length R (R ⧸ Ideal.span {β p})).toNat : ℤ) := by
  let α := LinearMap.toSpanSingleton R P p
  have hbcomp : β ∘ₗ α = LinearMap.toSpanSingleton R R (β p) := by
    apply LinearMap.ext
    intro t
    exact β.map_smul t p
  have hccomp : γ ∘ₗ α = LinearMap.toSpanSingleton R R (γ p) := by
    apply LinearMap.ext
    intro t
    exact γ.map_smul t p
  have hbR : LinearMap.range (β ∘ₗ α) = Ideal.span {β p} := by
    rw [hbcomp, LinearMap.range_toSpanSingleton, Ideal.submodule_span_eq]
  have hcR : LinearMap.range (γ ∘ₗ α) = Ideal.span {γ p} := by
    rw [hccomp, LinearMap.range_toSpanSingleton, Ideal.submodule_span_eq]
  have hfinβ : IsFiniteLength R (R ⧸ LinearMap.range (β ∘ₗ α)) := by
    rw [hbR]
    exact isFiniteLength_quotient_span_singleton R hb
  have hfinγ : IsFiniteLength R (R ⧸ LinearMap.range (γ ∘ₗ α)) := by
    rw [hcR]
    exact isFiniteLength_quotient_span_singleton R hc
  have h := length_difference_cokers α β γ hβ hγ hfinβ hfinγ
  rw [hbR, hcR] at h
  exact h

variable (X : Scheme.{u}) [IsIntegral X] (g : X.functionField) (x : X)

/-- The actual local regular-pair module over a scheme stalk. -/
def stalkPairs : Submodule (X.presheaf.stalk x)
    ((X.presheaf.stalk x) × (X.presheaf.stalk x)) where
  carrier := {p | g * algebraMap (X.presheaf.stalk x) X.functionField p.1 =
    algebraMap (X.presheaf.stalk x) X.functionField p.2}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change g * algebraMap (X.presheaf.stalk x) X.functionField p.1 =
      algebraMap (X.presheaf.stalk x) X.functionField p.2 at hp
    change g * algebraMap (X.presheaf.stalk x) X.functionField q.1 =
      algebraMap (X.presheaf.stalk x) X.functionField q.2 at hq
    change g * algebraMap (X.presheaf.stalk x) X.functionField (p.1 + q.1) =
      algebraMap (X.presheaf.stalk x) X.functionField (p.2 + q.2)
    simp only [map_add, mul_add, hp, hq]
  smul_mem' := by
    intro a p hp
    change g * algebraMap (X.presheaf.stalk x) X.functionField (a * p.1) =
      algebraMap (X.presheaf.stalk x) X.functionField (a * p.2)
    simp only [map_mul]
    rw [← mul_assoc, mul_comm g, mul_assoc, hp]

def stalkDenominatorProjection : stalkPairs X g x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (LinearMap.fst _ _ _).domRestrict (stalkPairs X g x)

def stalkNumeratorProjection : stalkPairs X g x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (LinearMap.snd _ _ _).domRestrict (stalkPairs X g x)

lemma stalkDenominatorProjection_injective :
    Function.Injective (stalkDenominatorProjection X g x) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext hpq
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  change algebraMap (X.presheaf.stalk x) X.functionField p.1.2 =
    algebraMap (X.presheaf.stalk x) X.functionField q.1.2
  rw [← p.2, ← q.2]
  change p.1.1 = q.1.1 at hpq
  rw [hpq]

lemma stalkNumeratorProjection_injective (hg : g ≠ 0) :
    Function.Injective (stalkNumeratorProjection X g x) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext _ hpq
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  apply mul_left_cancel₀ hg
  change g * algebraMap (X.presheaf.stalk x) X.functionField p.1.1 =
    g * algebraMap (X.presheaf.stalk x) X.functionField q.1.1
  rw [p.2, q.2]
  change p.1.2 = q.1.2 at hpq
  rw [hpq]

/-- The local order equals the difference of lengths of the two actual local cokernels. -/
theorem principalOrder_eq_stalk_coker_length_difference [IsLocallyNoetherian X]
    (hx : Order.coheight x = 1) (hg : g ≠ 0) :
    principalOrder X g x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ LinearMap.range (stalkNumeratorProjection X g x))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ LinearMap.range (stalkDenominatorProjection X g x))).toNat : ℤ) := by
  let A := X.presheaf.stalk x
  haveI : Ring.KrullDimLE 1 A := krullDimLE_of_coheight_le hx.le
  obtain ⟨a, b, ha, hb, hab, hord⟩ := exists_principalOrder_eq_sub_lengths X x hx g hg
  let p : stalkPairs X g x := ⟨(b,a), hab⟩
  have hlen := length_difference_projections
    (stalkDenominatorProjection X g x) (stalkNumeratorProjection X g x)
    (stalkDenominatorProjection_injective X g x) (stalkNumeratorProjection_injective X g x hg)
    p (mem_nonZeroDivisors_of_ne_zero hb) (mem_nonZeroDivisors_of_ne_zero ha)
  exact hord.trans hlen.symm

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.length_difference_projections
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.principalOrder_eq_stalk_coker_length_difference


namespace ArithmeticThetaCurveDegree.DegreeCohomology
variable (X : Scheme.{u}) [IsIntegral X] (g : X.functionField)
    (U : X.Opens) (x : U)

/-- Take both germs of a regular pair. -/
def pairsGerm :
    letI := X.presheaf.algebra_section_stalk x
    regularPairs X g U →ₗ[Γ(X,U)] stalkPairs X g x.1 := by
  letI := X.presheaf.algebra_section_stalk x
  letI : Nonempty U := ⟨x⟩
  let r := (X.presheaf.germ U x.1 x.2).hom
  refine
    { toFun := fun p => ⟨(r p.1.1, r p.1.2), ?_⟩
      map_add' := fun p q => Subtype.ext (Prod.ext (map_add r _ _) (map_add r _ _))
      map_smul' := ?_ }
  · change g * algebraMap (X.presheaf.stalk x.1) X.functionField (r p.1.1) =
      algebraMap (X.presheaf.stalk x.1) X.functionField (r p.1.2)
    rw [Scheme.algebraMap_germ_eq_germToFunctionField X x.2,
      Scheme.algebraMap_germ_eq_germToFunctionField X x.2]
    exact p.2 inferInstance
  · intro a p
    apply Subtype.ext
    exact Prod.ext (map_mul r _ _) (map_mul r _ _)

lemma pairsGerm_injective : Function.Injective (pairsGerm X g U x) := by
  letI := X.presheaf.algebra_section_stalk x
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (germ_injective_of_isIntegral X x.1 x.2 (congrArg (fun p => p.1.1) hpq))
    (germ_injective_of_isIntegral X x.1 x.2 (congrArg (fun p => p.1.2) hpq))

lemma pairsGerm_isLocalizedModule (hU : IsAffineOpen U) :
    letI := X.presheaf.algebra_section_stalk x
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (pairsGerm X g U x) := by
  letI := X.presheaf.algebra_section_stalk x
  letI : Nonempty U := ⟨x⟩
  haveI := hU.isLocalization_stalk x
  let R := Γ(X,U)
  let A := X.presheaf.stalk x.1
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  let r : R →+* A := algebraMap R A
  constructor
  · intro s
    have hu := IsLocalization.map_units A s
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun p : stalkPairs X g x.1 => (s : R) • p)
    simpa only [algebraMap_smul] using
      (hu.smul_bijective : Function.Bijective (fun p : stalkPairs X g x.1 =>
        algebraMap R A s • p))
  · intro p
    obtain ⟨⟨a,s⟩, ha⟩ := IsLocalization.surj S p.1.1
    obtain ⟨⟨b,t⟩, hb⟩ := IsLocalization.surj S p.1.2
    have hpa : r ((t : R) * a) = r ((s*t : S) : R) * p.1.1 := by
      change p.1.1 * r s = r a at ha
      rw [map_mul, ← ha]
      simp only [Submonoid.coe_mul, map_mul]
      ring
    have hpb : r ((s : R) * b) = r ((s*t : S) : R) * p.1.2 := by
      change p.1.2 * r t = r b at hb
      rw [map_mul, ← hb]
      simp only [Submonoid.coe_mul, map_mul]
      ring
    have hp : ((t : R) * a, (s : R) * b) ∈ regularPairs X g U := by
      intro h
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField X x.2,
        ← Scheme.algebraMap_germ_eq_germToFunctionField X x.2]
      change g * algebraMap A X.functionField (r ((t : R) * a)) =
        algebraMap A X.functionField (r ((s : R) * b))
      rw [hpa, hpb, map_mul, map_mul, ← mul_assoc, mul_comm g, mul_assoc, p.2]
    refine ⟨(⟨_, hp⟩, s*t), ?_⟩
    apply Subtype.ext
    exact Prod.ext hpa.symm hpb.symm
  · intro p q h
    exact ⟨1, by simpa using pairsGerm_injective X g U x h⟩

/-- The range of a compatible projection localizes to its actual stalk range. -/
lemma localized_projection_range (hU : IsAffineOpen U)
    (β : regularPairs X g U →ₗ[Γ(X,U)] Γ(X,U))
    (β' : stalkPairs X g x.1 →ₗ[X.presheaf.stalk x.1] X.presheaf.stalk x.1)
    (hcomm : ∀ p, β' (pairsGerm X g U x p) = X.presheaf.germ U x.1 x.2 (β p)) :
    letI := X.presheaf.algebra_section_stalk x
    letI := hU.isLocalization_stalk x
    (LinearMap.range β).localized' (X.presheaf.stalk x.1)
      (hU.primeIdealOf x).asIdeal.primeCompl (Algebra.linearMap Γ(X,U) (X.presheaf.stalk x.1)) =
      LinearMap.range β' := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  haveI := pairsGerm_isLocalizedModule X g U x hU
  let R := Γ(X,U)
  let A := X.presheaf.stalk x.1
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  have heq : IsLocalizedModule.map S (pairsGerm X g U x) (Algebra.linearMap R A) β =
      β'.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S (pairsGerm X g U x) (Algebra.linearMap R A)
    rw [IsLocalizedModule.map_comp]
    exact LinearMap.ext fun p => (hcomm p).symm
  rw [LinearMap.localized'_range_eq_range_localizedMap A S (pairsGerm X g U x)
    (Algebra.linearMap R A) β]
  congr 1
  apply LinearMap.ext
  intro p
  exact DFunLike.congr_fun heq p

/-- The localized affine cokernel is the actual stalk cokernel. -/
def localized_projection_coker_equiv (hU : IsAffineOpen U)
    (β : regularPairs X g U →ₗ[Γ(X,U)] Γ(X,U))
    (β' : stalkPairs X g x.1 →ₗ[X.presheaf.stalk x.1] X.presheaf.stalk x.1)
    (hcomm : ∀ p, β' (pairsGerm X g U x p) = X.presheaf.germ U x.1 x.2 (β p)) :
    letI := X.presheaf.algebra_section_stalk x
    letI := hU.isLocalization_stalk x
    let S := (hU.primeIdealOf x).asIdeal.primeCompl
    letI : Module (X.presheaf.stalk x.1) (LocalizedModule S (Γ(X,U) ⧸ LinearMap.range β)) :=
      LocalizedModule.moduleOfIsLocalization
    LocalizedModule S (Γ(X,U) ⧸ LinearMap.range β) ≃ₗ[X.presheaf.stalk x.1]
      ((X.presheaf.stalk x.1) ⧸ LinearMap.range β') := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  let R := Γ(X,U)
  let A := X.presheaf.stalk x.1
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  letI : Module A (LocalizedModule S (R ⧸ LinearMap.range β)) :=
    LocalizedModule.moduleOfIsLocalization
  let l := (LinearMap.range β).toLocalizedQuotient' A S (Algebra.linearMap R A)
  let e := (IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (R ⧸ LinearMap.range β)) l).extendScalarsOfIsLocalization S A
  exact e.trans (Submodule.quotEquivOfEq _ _ (localized_projection_range X g U x hU β β' hcomm))

variable (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The denominator quotient used globally has the asserted local cokernel. -/
def denominator_localized_coker_equiv (hU : IsAffineOpen U) :
    letI := X.presheaf.algebra_section_stalk x
    letI := hU.isLocalization_stalk x
    let S := (hU.primeIdealOf x).asIdeal.primeCompl
    letI : Module (X.presheaf.stalk x.1)
        (LocalizedModule S ((denominatorQuotient X g k f).obj U)) :=
      LocalizedModule.moduleOfIsLocalization
    LocalizedModule S ((denominatorQuotient X g k f).obj U) ≃ₗ[X.presheaf.stalk x.1]
      ((X.presheaf.stalk x.1) ⧸ LinearMap.range (stalkDenominatorProjection X g x.1)) := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  exact localized_projection_coker_equiv X g U x hU
    ((denominatorProjection X g k f).appSections U) (stalkDenominatorProjection X g x.1)
    (fun _ => rfl)

/-- The numerator quotient used globally has the asserted local cokernel. -/
def numerator_localized_coker_equiv (hU : IsAffineOpen U) :
    letI := X.presheaf.algebra_section_stalk x
    letI := hU.isLocalization_stalk x
    let S := (hU.primeIdealOf x).asIdeal.primeCompl
    letI : Module (X.presheaf.stalk x.1)
        (LocalizedModule S ((numeratorQuotient X g k f).obj U)) :=
      LocalizedModule.moduleOfIsLocalization
    LocalizedModule S ((numeratorQuotient X g k f).obj U) ≃ₗ[X.presheaf.stalk x.1]
      ((X.presheaf.stalk x.1) ⧸ LinearMap.range (stalkNumeratorProjection X g x.1)) := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  exact localized_projection_coker_equiv X g U x hU
    ((numeratorProjection X g k f).appSections U) (stalkNumeratorProjection X g x.1)
    (fun _ => rfl)

/-- The scheme order is the length difference of localizations of the global quotients. -/
theorem principalOrder_eq_localized_quotient_length_difference [IsLocallyNoetherian X]
    (hU : IsAffineOpen U) (hx : Order.coheight x.1 = 1) (hg : g ≠ 0) :
    letI := X.presheaf.algebra_section_stalk x
    letI := hU.isLocalization_stalk x
    let S := (hU.primeIdealOf x).asIdeal.primeCompl
    letI : Module (X.presheaf.stalk x.1)
        (LocalizedModule S ((numeratorQuotient X g k f).obj U)) :=
      LocalizedModule.moduleOfIsLocalization
    letI : Module (X.presheaf.stalk x.1)
        (LocalizedModule S ((denominatorQuotient X g k f).obj U)) :=
      LocalizedModule.moduleOfIsLocalization
    principalOrder X g x.1 =
      ((Module.length (X.presheaf.stalk x.1)
        (LocalizedModule S ((numeratorQuotient X g k f).obj U))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x.1)
        (LocalizedModule S ((denominatorQuotient X g k f).obj U))).toNat : ℤ) := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  letI : Module (X.presheaf.stalk x.1)
      (LocalizedModule S ((numeratorQuotient X g k f).obj U)) :=
    LocalizedModule.moduleOfIsLocalization
  letI : Module (X.presheaf.stalk x.1)
      (LocalizedModule S ((denominatorQuotient X g k f).obj U)) :=
    LocalizedModule.moduleOfIsLocalization
  change principalOrder X g x.1 = _ - _
  rw [(numerator_localized_coker_equiv X g U x k f hU).length_eq,
    (denominator_localized_coker_equiv X g U x k f hU).length_eq]
  exact principalOrder_eq_stalk_coker_length_difference X g x.1 hx hg

/-- The two actual quotient section dimensions have equal alternating sums. -/
theorem alternating_quotient_section_finrank_eq [IsLocallyNoetherian X] [IsProper f]
    (hcurve : OneDimensionalCharts X) (hg : g ≠ 0) (K : X.OrderedAffineCover) :
    (∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ)^i *
      (∑ s : K.Idx i, (Module.finrank k ((numeratorQuotient X g k f).obj (K.inter s)) : ℤ))) =
    (∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ)^i *
      (∑ s : K.Idx i, (Module.finrank k ((denominatorQuotient X g k f).obj (K.inter s)) : ℤ))) := by
  haveI (i : ℕ) := (quotient_cochains_finite X g k f hcurve hg K i).1
  haveI (i : ℕ) := (quotient_cochains_finite X g k f hcurve hg K i).2
  have hN := eulerChar_eq_alternating_cochain_finrank (numeratorQuotient X g k f) K
    (fun i => (quotient_cochains_finite X g k f hcurve hg K i).2)
  have hD := eulerChar_eq_alternating_cochain_finrank (denominatorQuotient X g k f) K
    (fun i => (quotient_cochains_finite X g k f hcurve hg K i).1)
  have h := numerator_denominator_eulerChar_eq X g k f hg K
  rw [hN, hD] at h
  haveI (i : ℕ) (s : K.Idx i) :=
    (quotients_finite_on_affine X g k f hcurve hg (K.inter s) (K.isAffineOpen_inter f s)).1
  haveI (i : ℕ) (s : K.Idx i) :=
    (quotients_finite_on_affine X g k f hcurve hg (K.inter s) (K.isAffineOpen_inter f s)).2
  simpa only [OModulePresheaf.cochain, Module.finrank_pi_fintype, Nat.cast_sum] using h

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.pairsGerm_isLocalizedModule

#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.localized_projection_range

#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.localized_projection_coker_equiv

#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.denominator_localized_coker_equiv
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.numerator_localized_coker_equiv

#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.principalOrder_eq_localized_quotient_length_difference
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.alternating_quotient_section_finrank_eq


namespace ArithmeticThetaCurveDegree.DegreeCohomology
open P2MW.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton.FinSuppLen

lemma exists_finset_localizedModule_subsingleton
    (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H]
    [Module.Finite k H] :
    ∃ T : Finset (MaximalSpectrum S), ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T →
      Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
  classical
  suffices h : ∀ d : ℕ, ∀ (H : Type u) [AddCommGroup H] [Module S H]
      [Module k H] [IsScalarTower k S H] [Module.Finite k H], Module.finrank k H = d →
      ∃ T : Finset (MaximalSpectrum S), ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T →
        Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H) by
    exact h _ H rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro H _ _ _ _ _ hd
    by_cases hH : Subsingleton H
    · refine ⟨∅, fun 𝔪 _ => ?_⟩
      have hinj := IsLocalizedModule.map_injective 𝔪.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl H)
        (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl H)
        (0 : H →ₗ[S] H) (fun a b _ => Subsingleton.elim a b)
      refine ⟨fun a b => hinj ?_⟩
      simp
    · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
      haveI : IsArtinian S H := isArtinian_of_tower k (inferInstance : IsArtinian k H)
      haveI : IsAtomic (Submodule S H) := isAtomic_of_orderBot_wellFounded_lt
        (wellFounded_lt : WellFounded ((· < ·) : Submodule S H → Submodule S H → Prop))
      obtain ⟨N, hNat⟩ := IsAtomic.exists_atom (Submodule S H)
      haveI hN : IsSimpleModule S N := isSimpleModule_iff_isAtom.mpr hNat
      haveI : Nontrivial N := IsSimpleModule.nontrivial S N
      haveI : Module.Finite k N := Module.Finite.of_injective
        (N.subtype.restrictScalars k) N.injective_subtype
      obtain ⟨𝔪₀, h𝔪₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hN
      haveI : Module.Finite k (H ⧸ N) :=
        Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
      have hlt : Module.finrank k (H ⧸ N) < d := by
        have hNpos : 0 < Module.finrank k N := Module.finrank_pos
        have hHpos : 0 < Module.finrank k H := Module.finrank_pos
        rw [Submodule.finrank_quotient, ← hd]
        omega
      obtain ⟨T, hT⟩ := ih _ hlt (H ⧸ N) rfl
      refine ⟨insert ⟨𝔪₀, h𝔪₀⟩ T, fun 𝔪 h𝔪 => ?_⟩
      have hne : 𝔪 ≠ ⟨𝔪₀, h𝔪₀⟩ := fun h => h𝔪 (by simp [h])
      have hnot : 𝔪 ∉ T := fun h => h𝔪 (Finset.mem_insert_of_mem h)
      haveI := hT 𝔪 hnot
      apply (Module.length_eq_zero_iff (R := Localization.AtPrime 𝔪.asIdeal)).mp
      change loclen 𝔪 H = 0
      rw [loclen_eq_add H N 𝔪, loclen_eq_zero_of_equiv_quotient N 𝔪₀ h𝔪₀ e 𝔪 hne,
        zero_add]
      exact Module.length_eq_zero

/-- A finite-dimensional module's dimension is its weighted sum of local lengths. -/
theorem finrank_eq_finsum_weighted_localLength
    (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H]
    [Module.Finite k H] :
    (Module.finrank k H : ℕ∞) = ∑ᶠ 𝔪 : MaximalSpectrum S,
      (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime 𝔪.asIdeal)
          (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_localizedModule_subsingleton k S H
  have hs : Function.support (fun 𝔪 : MaximalSpectrum S =>
      (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime 𝔪.asIdeal)
          (LocalizedModule 𝔪.asIdeal.primeCompl H)) ⊆ (T : Set (MaximalSpectrum S)) := by
    intro 𝔪 h𝔪
    by_contra hnot
    haveI := hT 𝔪 hnot
    apply h𝔪
    simp only [Module.length_eq_zero, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hs]
  exact finrank_eq_sum_weighted_localLength k S T H hT

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.finrank_eq_finsum_weighted_localLength


namespace ArithmeticThetaCurveDegree.DegreeCohomology
variable (X : Scheme.{u}) (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : U)

lemma evaluation_base_eq (a : k) :
    X.evaluation U x.1 x.2 ((Scheme.TwoAffineOpenCover.algebraOfHom f U).algebraMap a) =
      baseToResidue k f x.1 a := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U le_top ≫
      X.evaluation U x.1 x.2 =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.Γevaluation x.1 := by
    simp only [Scheme.evaluation, Scheme.Hom.appLE, Category.assoc,
      TopCat.Presheaf.germ_res_assoc]
    rfl
  exact ConcreteCategory.congr_hom h a

/-- At a maximal affine point, the chart residue dimension is exactly the frozen place degree. -/
theorem placeDegree_eq_affine_residue_finrank (hU : IsAffineOpen U)
    [hmax : (hU.primeIdealOf x).asIdeal.IsMaximal] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    placeDegree k f x.1 = Module.finrank k (Γ(X,U) ⧸ (hU.primeIdealOf x).asIdeal) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  letI : Algebra k (X.residueField x.1) := (baseToResidue k f x.1).toAlgebra
  let e : (Γ(X,U) ⧸ (hU.primeIdealOf x).asIdeal) ≃+* X.residueField x.1 :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal (hU.primeIdealOf x).asIdeal (X.presheaf.stalk x.1)
  let e' : (Γ(X,U) ⧸ (hU.primeIdealOf x).asIdeal) ≃ₐ[k] X.residueField x.1 :=
    { e with
      commutes' := fun a => evaluation_base_eq X k f U x a }
  exact e'.toLinearEquiv.finrank_eq.symm

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.placeDegree_eq_affine_residue_finrank


namespace ArithmeticThetaCurveDegree.DegreeCohomology

/-- Localized-module length is independent of the chosen realization of the localized ring. -/
theorem localizedModule_length_eq
    (R A H : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A] [AddCommGroup H] [Module R H] :
    letI : Module A (LocalizedModule S H) := LocalizedModule.moduleOfIsLocalization
    Module.length (Localization S) (LocalizedModule S H) =
      Module.length A (LocalizedModule S H) := by
  letI : Module A (LocalizedModule S H) := LocalizedModule.moduleOfIsLocalization
  let σ : Localization S ≃ₐ[R] A := Localization.algEquiv S A
  have hsmul : ∀ (r : Localization S) (m : LocalizedModule S H), σ r • m = r • m := by
    intro r m
    induction r using Localization.induction_on with
    | H p =>
      rcases p with ⟨r,s⟩
      induction m using LocalizedModule.induction_on with
      | h m t =>
        change Localization.algEquiv S A (Localization.mk r s) • LocalizedModule.mk m t = _
        rw [Localization.algEquiv_mk, LocalizedModule.mk'_smul_mk, LocalizedModule.mk_smul_mk]
  let σ₀ : Localization S →+* A := σ.toRingHom
  letI : RingHomSurjective σ₀ := ⟨σ.surjective⟩
  let l : LocalizedModule S H →ₛₗ[σ₀] LocalizedModule S H :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => (hsmul r m).symm }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective l Function.bijective_id)]

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.localizedModule_length_eq


open Classical


namespace ArithmeticThetaCurveDegree.DegreeCohomology
variable (X : Scheme.{u}) [IsIntegral X]
set_option backward.isDefEq.respectTransparency false in
lemma coheight_eq_affine_height (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    Order.coheight x.1 = (hU.primeIdealOf x).asIdeal.height := by
  rw [← hU.fromSpec_primeIdealOf x, coheight_eq_of_isOpenImmersion]
  exact (idealHeight_eq_coheight _ _).symm

lemma coheight_le_one (hcurve : OneDimensionalCharts X) (x : X) :
    Order.coheight x ≤ 1 := by
  obtain ⟨U, hU, hx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial) (show IsOpen ((⊤ : X.Opens) : Set X) from isOpen_univ)
  obtain ⟨U, hU, rfl⟩ := hU
  letI : Nonempty U := ⟨⟨x, hx.1⟩⟩
  letI := hcurve U hU
  rw [coheight_eq_affine_height X U hU ⟨x, hx.1⟩]
  exact WithBot.coe_le_coe.mp ((Ideal.height_le_ringKrullDim_of_isPrime).trans (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 Γ(X,U))))

lemma stalk_projection_ranges_eq_top_of_coheight_zero (g : X.functionField) (hg : g ≠ 0)
    (x : X) (hx : Order.coheight x = 0) :
    LinearMap.range (stalkDenominatorProjection X g x) = ⊤ ∧
    LinearMap.range (stalkNumeratorProjection X g x) = ⊤ := by
  haveI : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hs := (IsFractionRing.surjective_iff_isField (R := X.presheaf.stalk x)
    (K := X.functionField)).mpr Ring.KrullDimLE.isField_of_isDomain
  constructor
  · apply LinearMap.range_eq_top.mpr
    intro b
    obtain ⟨a, ha⟩ := hs (g * algebraMap (X.presheaf.stalk x) X.functionField b)
    exact ⟨⟨(b,a), ha.symm⟩, rfl⟩
  · apply LinearMap.range_eq_top.mpr
    intro a
    obtain ⟨b, hb⟩ := hs (g⁻¹ * algebraMap (X.presheaf.stalk x) X.functionField a)
    refine ⟨⟨(b,a), ?_⟩, rfl⟩
    change g * algebraMap (X.presheaf.stalk x) X.functionField b = _
    rw [hb, ← mul_assoc, mul_inv_cancel₀ hg, one_mul]

/-- The local comparison includes the generic point and zero-dimensional curves. -/
theorem principalOrder_eq_stalk_coker_length_difference_all [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (hg : g ≠ 0) (x : X) :
    principalOrder X g x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ LinearMap.range (stalkNumeratorProjection X g x))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ LinearMap.range (stalkDenominatorProjection X g x))).toNat : ℤ) := by
  rcases Order.le_one_iff.mp (coheight_le_one X hcurve x) with hx | hx
  · obtain ⟨hD, hN⟩ := stalk_projection_ranges_eq_top_of_coheight_zero X g hg x hx
    rw [hD, hN]
    have hz : Order.coheight x ≠ 1 := by simp [hx]
    simp [principalOrder, Scheme.ord_eq_zero_of_coheight_neq_one hz]
  · exact principalOrder_eq_stalk_coker_length_difference X g x hx hg

/-- Standard prime localization gives the same local order formula at every affine point. -/
theorem principalOrder_eq_standard_localized_length_difference [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (hg : g ≠ 0)
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    principalOrder X g x.1 =
      ((Module.length (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
        (LocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
          ((numeratorQuotient X g k f).obj U))).toNat : ℤ) -
      ((Module.length (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
        (LocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
          ((denominatorQuotient X g k f).obj U))).toNat : ℤ) := by
  letI := X.presheaf.algebra_section_stalk x
  letI := hU.isLocalization_stalk x
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  letI : Module (X.presheaf.stalk x.1)
      (LocalizedModule S ((numeratorQuotient X g k f).obj U)) :=
    LocalizedModule.moduleOfIsLocalization
  letI : Module (X.presheaf.stalk x.1)
      (LocalizedModule S ((denominatorQuotient X g k f).obj U)) :=
    LocalizedModule.moduleOfIsLocalization
  rw [localizedModule_length_eq Γ(X,U) (X.presheaf.stalk x.1)
      ((numeratorQuotient X g k f).obj U) S,
    localizedModule_length_eq Γ(X,U) (X.presheaf.stalk x.1)
      ((denominatorQuotient X g k f).obj U) S,
    (numerator_localized_coker_equiv X g U x k f hU).length_eq,
    (denominator_localized_coker_equiv X g U x k f hU).length_eq]
  exact principalOrder_eq_stalk_coker_length_difference_all X hcurve g hg x.1

end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.principalOrder_eq_stalk_coker_length_difference_all



namespace ArithmeticThetaCurveDegree.DegreeCohomology
lemma finrank_eq_sum_weighted_localLength_int
    (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (T : Finset (MaximalSpectrum S)) (H : Type u)
    [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H]
    [Module.Finite k H]
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T →
      Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    (Module.finrank k H : ℤ) = ∑ 𝔪 ∈ T,
      (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℤ) *
        (Module.length (Localization.AtPrime 𝔪.asIdeal)
          (LocalizedModule 𝔪.asIdeal.primeCompl H)).toNat := by
  have heq := finrank_eq_sum_weighted_localLength k S T H hT
  have hne : ∀ 𝔪 ∈ T, (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℕ∞) *
      Module.length (Localization.AtPrime 𝔪.asIdeal)
        (LocalizedModule 𝔪.asIdeal.primeCompl H) ≠ ⊤ := by
    intro 𝔪 hm
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top _) (b := (Module.finrank k H : ℕ∞))
    rw [heq]
    exact Finset.single_le_sum (fun _ _ => (show (0 : ℕ∞) ≤ _ from bot_le)) hm
  have h := congrArg ENat.toNat heq
  rw [ENat.toNat_sum hne] at h
  simp only [ENat.toNat_mul, ENat.toNat_natCast] at h
  exact_mod_cast h

lemma finite_weighted_localLength_int_support
    (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H]
    [Module.Finite k H] :
    Function.HasFiniteSupport (fun 𝔪 : MaximalSpectrum S =>
      (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℤ) *
        (Module.length (Localization.AtPrime 𝔪.asIdeal)
          (LocalizedModule 𝔪.asIdeal.primeCompl H)).toNat) := by
  obtain ⟨T, hT⟩ := exists_finset_localizedModule_subsingleton k S H
  apply T.finite_toSet.subset
  intro 𝔪 hm
  by_contra hnot
  haveI := hT 𝔪 hnot
  exact hm (by simp [Module.length_eq_zero])

lemma finrank_eq_finsum_weighted_localLength_int
    (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H]
    [Module.Finite k H] :
    (Module.finrank k H : ℤ) = ∑ᶠ 𝔪 : MaximalSpectrum S,
      (Module.finrank k (S ⧸ 𝔪.asIdeal) : ℤ) *
        (Module.length (Localization.AtPrime 𝔪.asIdeal)
          (LocalizedModule 𝔪.asIdeal.primeCompl H)).toNat := by
  obtain ⟨T, hT⟩ := exists_finset_localizedModule_subsingleton k S H
  rw [finsum_eq_sum_of_support_subset _ (s := T)]
  · exact finrank_eq_sum_weighted_localLength_int k S T H hT
  · intro 𝔪 hm
    by_contra hnot
    haveI := hT 𝔪 hnot
    exact hm (by simp [Module.length_eq_zero])
end ArithmeticThetaCurveDegree.DegreeCohomology



namespace ArithmeticThetaCurveDegree.DegreeCohomology
variable (X : Scheme.{u}) [IsIntegral X]
set_option backward.isDefEq.respectTransparency false in
lemma affine_prime_bijective (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective hU.primeIdealOf := by
  exact ⟨hU.isoSpec.hom.injective, hU.isoSpec.hom.surjective⟩

lemma principalOrder_zero_of_affine_not_maximal [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (g : X.functionField)
    (U : X.Opens) (hU : IsAffineOpen U) (x : U)
    (hmax : ¬ (hU.primeIdealOf x).asIdeal.IsMaximal) : principalOrder X g x.1 = 0 := by
  haveI : Nonempty U := ⟨x⟩
  haveI := hcurve U hU
  have hp : (hU.primeIdealOf x).asIdeal = ⊥ := by
    by_contra hne
    exact hmax (Ring.DimensionLEOne.maximalOfPrime hne (hU.primeIdealOf x).isPrime)
  have hx : Order.coheight x.1 = 0 := by
    rw [coheight_eq_affine_height X U hU x, Ideal.height_eq_zero_iff_eq_bot]
    exact hp
  exact Scheme.ord_eq_zero_of_coheight_neq_one (by simp [hx]) g

set_option backward.isDefEq.respectTransparency false in
/-- Affine quotient dimension difference equals the actual weighted point orders. -/
theorem affine_quotient_finrank_difference [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (hg : g ≠ 0)
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (Module.finrank k ((numeratorQuotient X g k f).obj U) : ℤ) -
      (Module.finrank k ((denominatorQuotient X g k f).obj U) : ℤ) =
    ∑ᶠ x : U, (placeDegree k f x.1 : ℤ) * principalOrder X g x.1 := by
  classical
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  haveI := (quotients_finite_on_affine X g k f hcurve hg U hU).1
  haveI := (quotients_finite_on_affine X g k f hcurve hg U hU).2
  let R := Γ(X,U)
  let N := (numeratorQuotient X g k f).obj U
  let D := (denominatorQuotient X g k f).obj U
  rw [finrank_eq_finsum_weighted_localLength_int k R N,
    finrank_eq_finsum_weighted_localLength_int k R D,
    ← finsum_sub_distrib (finite_weighted_localLength_int_support k R N)
      (finite_weighted_localLength_int_support k R D)]
  let e : U ≃ PrimeSpectrum R := Equiv.ofBijective hU.primeIdealOf (affine_prime_bijective X U hU)
  let j : MaximalSpectrum R → U := fun m => e.symm m.toPrimeSpectrum
  let w : U → ℤ := fun x => (placeDegree k f x.1 : ℤ) * principalOrder X g x.1
  have hj : Function.Injective j := e.symm.injective.comp MaximalSpectrum.toPrimeSpectrum_injective
  have hej (m : MaximalSpectrum R) : hU.primeIdealOf (j m) = m.toPrimeSpectrum := e.apply_symm_apply _
  have hterm (m : MaximalSpectrum R) :
      (Module.finrank k (R ⧸ m.asIdeal) : ℤ) *
          (Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl N)).toNat -
        (Module.finrank k (R ⧸ m.asIdeal) : ℤ) *
          (Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl D)).toNat =
      w (j m) := by
    have hm : (hU.primeIdealOf (j m)).asIdeal = m.asIdeal := congrArg PrimeSpectrum.asIdeal (hej m)
    haveI : (hU.primeIdealOf (j m)).asIdeal.IsMaximal := hm.symm ▸ m.isMaximal
    dsimp [w]
    rw [placeDegree_eq_affine_residue_finrank X k f U (j m) hU,
      principalOrder_eq_standard_localized_length_difference X hcurve g hg k f U hU (j m)]
    simp only [mul_sub]
    exact (congrArg (fun p : PrimeSpectrum R =>
      (Module.finrank k (R ⧸ p.asIdeal) : ℤ) *
          (Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N)).toNat -
        (Module.finrank k (R ⧸ p.asIdeal) : ℤ) *
          (Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl D)).toNat)
      (hej m)).symm
  rw [finsum_congr hterm, ← finsum_mem_range hj, ← finsum_mem_univ w]
  apply finsum_mem_inter_support_eq'
  intro x hx
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  have hm : (hU.primeIdealOf x).asIdeal.IsMaximal := by
    by_contra hn
    exact hx (by dsimp [w]; rw [principalOrder_zero_of_affine_not_maximal X hcurve g U hU x hn, mul_zero])
  refine ⟨⟨(hU.primeIdealOf x).asIdeal, hm⟩, ?_⟩
  apply e.injective
  exact (hej _).trans rfl
end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.affine_quotient_finrank_difference



namespace ArithmeticThetaCurveDegree.DegreeCohomology
variable {α : Type u} [Fintype α] [LinearOrder α]
lemma sum_strictMono_eq_powersetCard (n : ℕ) (F : Finset α → ℤ) :
    (∑ s : {s : Fin n → α // StrictMono s}, F (Finset.univ.image s.1)) =
      ∑ t ∈ Finset.univ.powersetCard n, F t := by
  classical
  apply Finset.sum_bij (fun s _ => Finset.univ.image s.1)
  · intro s _
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ s.2.injective]
  · intro s _ t _ h
    apply Subtype.ext
    apply s.2.range_inj t.2 |>.mp
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using congrArg (fun t : Finset α => (t : Set α)) h
  · intro t ht
    have hcard := (Finset.mem_powersetCard.mp ht).2
    refine ⟨⟨t.orderEmbOfFin hcard, (t.orderEmbOfFin hcard).strictMono⟩, Finset.mem_univ _, ?_⟩
    exact Finset.image_orderEmbOfFin_univ t hcard
  · intro s _
    rfl

lemma alternating_strictMono_eq_powerset (F : Finset α → ℤ) :
    (∑ n ∈ Finset.range (Fintype.card α), (-1 : ℤ)^n *
      ∑ s : {s : Fin (n+1) → α // StrictMono s}, F (Finset.univ.image s.1)) =
    ∑ t ∈ Finset.univ.powerset with t.Nonempty, (-1 : ℤ)^(t.card+1) * F t := by
  classical
  simp_rw [sum_strictMono_eq_powersetCard]
  rw [Finset.sum_filter]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ]
  rw [Finset.sum_range_succ']
  simp only [Finset.powersetCard_zero, Finset.sum_singleton, Finset.not_nonempty_empty, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hc := (Finset.mem_powersetCard.mp ht).2
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  rw [if_pos htne, hc]
  simp [pow_add]

lemma orderedCover_point_alternating (X : Scheme.{u}) (K : X.OrderedAffineCover) (x : X) :
    (∑ n ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ)^n *
      ∑ s : K.Idx n, if x ∈ K.inter s then (1 : ℤ) else 0) = 1 := by
  classical
  let F : Finset K.ι → ℤ := fun t =>
    Set.indicator (⋂ i ∈ t, (K.U i : Set X)) (fun _ => (1 : ℤ)) x
  have hF (n : ℕ) (s : K.Idx n) :
      (if x ∈ K.inter s then (1 : ℤ) else 0) = F (Finset.univ.image s.1) := by
    have hm : x ∈ K.inter s ↔ ∀ j, x ∈ K.U (s.1 j) := by
      change x ∈ ((⨅ j, K.U (s.1 j) : X.Opens) : Set X) ↔ _
      rw [Opens.coe_iInf]
      simp
    simp [F, Set.indicator_apply, hm]
  simp_rw [hF]
  change (∑ n ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ)^n *
    ∑ s : {s : Fin (n+1) → K.ι // StrictMono s}, F (Finset.univ.image s.1)) = 1
  rw [alternating_strictMono_eq_powerset]
  have h := Finset.indicator_biUnion_eq_sum_powerset
    (Finset.univ : Finset K.ι) (fun i => (K.U i : Set X)) (fun _ => (1 : ℤ)) x
  have hx : x ∈ ⋃ i ∈ (Finset.univ : Finset K.ι), (K.U i : Set X) := by
    have hx' : x ∈ (⨆ i, K.U i) := by rw [K.iSup_eq_top]; trivial
    simpa using hx'
  rw [Set.indicator_of_mem hx] at h
  simpa [F, zsmul_eq_mul] using h.symm
end ArithmeticThetaCurveDegree.DegreeCohomology
#print axioms ArithmeticThetaCurveDegree.DegreeCohomology.orderedCover_point_alternating



namespace ArithmeticThetaCurveDegree.DegreeCohomology
set_option backward.isDefEq.respectTransparency false in
lemma orderedCover_alternating_finsum (X : Scheme.{u}) (K : X.OrderedAffineCover)
    (w : X → ℤ) (hw : Function.HasFiniteSupport w) :
    (∑ n ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ)^n *
      ∑ s : K.Idx n, ∑ᶠ x : K.inter s, w x.1) = ∑ᶠ x, w x := by
  classical
  let T := hw.toFinset
  have hs (U : X.Opens) : (∑ᶠ x : U, w x.1) =
      ∑ x ∈ T, if x ∈ U then w x else 0 := by
    change (∑ᶠ x : (U : Set X), w x.1) = _
    rw [finsum_set_coe_eq_finsum_mem (f := w) (U : Set X), finsum_mem_def]
    rw [finsum_eq_sum_of_support_subset _ (s := T)]
    · simp [Set.indicator_apply]
    · intro x hx
      apply hw.mem_toFinset.mpr
      intro hz
      apply hx
      simp [Set.indicator_apply, hz]
  simp_rw [hs, Finset.sum_comm (s := Finset.univ) (t := T)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [finsum_eq_sum w hw]
  apply Finset.sum_congr rfl
  intro x hx
  have hi (n : ℕ) (s : K.Idx n) :
      (if x ∈ K.inter s then w x else 0) =
        (if x ∈ K.inter s then (1 : ℤ) else 0) * w x := by split_ifs <;> simp
  simp_rw [hi, ← mul_assoc, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  rw [orderedCover_point_alternating, one_mul]

/-- The actual global weighted order sum is the quotient Euler difference. -/
theorem weighted_order_sum_eq_zero
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (hg : g ≠ 0) :
    (∑ᶠ x, (placeDegree k f x : ℤ) * principalOrder X g x) = 0 := by
  let K := properOrderedAffineCover X k f
  have h := alternating_quotient_section_finrank_eq X g k f hcurve hg K
  have heq := sub_eq_zero.mpr h
  rw [← Finset.sum_sub_distrib] at heq
  simp_rw [← mul_sub, ← Finset.sum_sub_distrib] at heq
  have hl (n : ℕ) (s : K.Idx n) := affine_quotient_finrank_difference
    X hcurve g hg k f (K.inter s) (K.isAffineOpen_inter f s)
  simp_rw [hl] at heq
  rw [orderedCover_alternating_finsum X K _
    (finite_weighted_principal_support X k f hcurve g hg)] at heq
  exact heq
end ArithmeticThetaCurveDegree.DegreeCohomology
namespace ArithmeticThetaCurveDegree
/-- A principal divisor on an integral proper curve has residue-degree-weighted degree zero. -/
theorem principal_degree_zero
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (D : X →₀ ℤ) :
    g ≠ 0 → MatchesPrincipalOrder X g D → weightedDegree k f D = 0 := by
  intro hg hD
  rw [weightedDegree_eq_finsum_principalOrder X k f g D hD]
  exact DegreeCohomology.weighted_order_sum_eq_zero X k f hcurve g hg
end ArithmeticThetaCurveDegree
#print axioms ArithmeticThetaCurveDegree.principal_degree_zero
