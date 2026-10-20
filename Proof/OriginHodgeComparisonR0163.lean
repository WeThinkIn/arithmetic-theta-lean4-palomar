module

public import HodgeInitialDefinitionsR0163

@[expose] public section

/-! The differential fiber of the actual identity stalk and the Hodge fiber. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaHodgeInitialR0163
namespace OriginHodgeComparisonR0163
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaConormalInitialR0162
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign

section StalkCoefficient
variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of K))
variable (e : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ f.kaehler) (x : X)

lemma coefficient_germ_eq {U V : X.Opens} (hu : x ∈ U) (hv : x ∈ V)
    (a : Γ(X,U)) (b : Γ(X,V))
    (h : X.presheaf.germ U x hu a = X.presheaf.germ V x hv b) :
    X.presheaf.germ U x hu (coefficient f e U a) =
      X.presheaf.germ V x hv (coefficient f e V b) := by
  obtain ⟨W, hw, i, j, hij⟩ := X.presheaf.germ_eq x hu hv a b h
  have hi : i = homOfLE i.le := Subsingleton.elim _ _
  have hj : j = homOfLE j.le := Subsingleton.elim _ _
  simp only [hi, hj] at hij ⊢
  calc
    _ = X.presheaf.germ W x hw (coefficient f e W (X.presheaf.map (homOfLE i.le).op a)) := by
      rw [← coefficient_restrict f e U W i.le]
      exact (X.presheaf.germ_res_apply i x hw _).symm
    _ = X.presheaf.germ W x hw (coefficient f e W (X.presheaf.map (homOfLE j.le).op b)) := by rw [hij]
    _ = _ := by
      rw [← coefficient_restrict f e V W j.le]
      exact X.presheaf.germ_res_apply j x hw _

def stalkCoefficient (a : X.presheaf.stalk x) : X.presheaf.stalk x :=
  let U := (X.presheaf.exists_germ_eq a).choose
  let hU := (X.presheaf.exists_germ_eq a).choose_spec.choose
  let b := (X.presheaf.exists_germ_eq a).choose_spec.choose_spec.choose
  X.presheaf.germ U x hU (coefficient f e U b)

lemma stalkCoefficient_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X,U)) :
    stalkCoefficient f e x (X.presheaf.germ U x hx a) =
      X.presheaf.germ U x hx (coefficient f e U a) := by
  apply coefficient_germ_eq
  exact (X.presheaf.exists_germ_eq _).choose_spec.choose_spec.choose_spec

lemma stalkCoefficient_add (a b : X.presheaf.stalk x) :
    stalkCoefficient f e x (a+b) = stalkCoefficient f e x a + stalkCoefficient f e x b := by
  obtain ⟨U, hu, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hvU, hv, b, rfl⟩ := X.presheaf.exists_le_germ_eq b hu
  rw [← X.presheaf.germ_res_apply (homOfLE hvU) x hv a]
  rw [← map_add, stalkCoefficient_germ, coefficient_add, map_add,
    stalkCoefficient_germ, stalkCoefficient_germ]

lemma stalkCoefficient_mul (a b : X.presheaf.stalk x) :
    stalkCoefficient f e x (a*b) =
      a * stalkCoefficient f e x b + b * stalkCoefficient f e x a := by
  obtain ⟨U, hu, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hvU, hv, b, rfl⟩ := X.presheaf.exists_le_germ_eq b hu
  rw [← X.presheaf.germ_res_apply (homOfLE hvU) x hv a]
  rw [← map_mul, stalkCoefficient_germ, coefficient_mul, map_add, map_mul, map_mul,
    stalkCoefficient_germ, stalkCoefficient_germ]

def stalkScalar : K →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (by trivial)).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

lemma stalkCoefficient_scalar (c : K) : stalkCoefficient f e x (stalkScalar f x c) = 0 := by
  have hf : (f.constToPresheaf.app (op ⊤)).hom =
      f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
    simp [Scheme.Hom.constToPresheaf, Scheme.Hom.appLE, Scheme.Hom.appTop]
  change stalkCoefficient f e x (X.presheaf.germ ⊤ x _ _) = 0
  rw [stalkCoefficient_germ, ← hf]
  exact (congrArg (X.presheaf.germ ⊤ x (by trivial))
    (coefficient_constant f e ⊤ c)).trans (map_zero _)


variable [Algebra K (X.presheaf.stalk x)]
    (halg : algebraMap K (X.presheaf.stalk x) = stalkScalar f x)

def stalkDerivation : Derivation K (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  Derivation.mk' (R := K) (A := X.presheaf.stalk x)
    { toFun := stalkCoefficient f e x
      map_add' := stalkCoefficient_add f e x
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [stalkCoefficient_mul, halg, stalkCoefficient_scalar, mul_zero, add_zero] }
    (stalkCoefficient_mul f e x)

variable (ε : X.presheaf.stalk x →ₐ[K] K)

/-- Scalar coefficient of the actual stalk differential modulo the augmentation ideal. -/
def fiberCoefficient : DifferentialFiber ε →ₗ[K] K := by
  letI : Algebra (X.presheaf.stalk x) K := ε.toRingHom.toAlgebra
  haveI : IsScalarTower K (X.presheaf.stalk x) K :=
    IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  let d : Derivation K (X.presheaf.stalk x) K :=
    { toLinearMap := ε.toLinearMap.comp (stalkDerivation f e x halg).toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        change ε (stalkCoefficient f e x (a*b)) =
          ε a * ε (stalkCoefficient f e x b) + ε b * ε (stalkCoefficient f e x a)
        rw [stalkCoefficient_mul, map_add, map_mul, map_mul] }
  exact ((AugmentedConormal.fiberSubmodule ε).liftQ d.liftKaehlerDifferential (by
    intro m hm
    change d.liftKaehlerDifferential m = 0
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro a ha m _
      rw [map_smul]
      change ε a * _ = 0
      rw [show ε a = 0 from ha, zero_mul]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero])).restrictScalars K

lemma fiberCoefficient_D (a : X.presheaf.stalk x) :
    fiberCoefficient f e x halg ε (differentialClass ε a) =
      ε (stalkCoefficient f e x a) := by
  letI : Algebra (X.presheaf.stalk x) K := ε.toRingHom.toAlgebra
  haveI : IsScalarTower K (X.presheaf.stalk x) K :=
    IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  exact Derivation.liftKaehlerDifferential_comp_D _ a


lemma fiberCoefficient_ne_zero : fiberCoefficient f e x halg ε ≠ 0 := by
  intro hz
  have hzero (U : X.Opens) (hu : x ∈ U) (a : Γ(X,U)) :
      ε (X.presheaf.germ U x hu (coefficient f e U a)) = 0 := by
    have hh := LinearMap.congr_fun hz (differentialClass ε (X.presheaf.germ U x hu a))
    rw [fiberCoefficient_D, stalkCoefficient_germ] at hh
    exact hh
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (TopologicalSpace.Opens.mem_top x)
  letI := f.sectionsAlgebra U
  let q : KaehlerDifferential K Γ(X,U) →ₗ[Γ(X,U)] Γ(X,U) :=
    ((e.inv.val.app (op U)).hom).comp (f.kaehlerToSectionsₗ U)
  have hq (m : KaehlerDifferential K Γ(X,U)) : ε (X.presheaf.germ U x hx (q m)) = 0 := by
    have hm : m ∈ Submodule.span Γ(X,U) (Set.range (KaehlerDifferential.D K Γ(X,U))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨a, rfl⟩ := hm
      exact hzero U hx a
    | zero => simp only [map_zero]
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul a m _ hm =>
      rw [map_smul]
      change ε (X.presheaf.germ U x hx (a * q m)) = 0
      rw [map_mul, map_mul, hm, mul_zero]
  obtain ⟨m, hm⟩ := (f.kaehlerToSections_bijective_of_isAffineOpen hU).2
    (Scheme.Modules.Hom.app e.hom U (1 : Γ(X,U)))
  have hqm : q m = 1 := by
    change Scheme.Modules.Hom.app e.inv U (f.kaehlerToSections U m) = (1 : Γ(X,U))
    rw [hm, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  have hh := hq m
  rw [hqm, map_one, map_one] at hh
  exact one_ne_zero hh


lemma fiberCoefficient_bijective [IsDomain (X.presheaf.stalk x)]
    (hp : (ideal ε).IsPrincipal) (hn : ideal ε ≠ ⊥) :
    Function.Bijective (fiberCoefficient f e x halg ε) := by
  obtain ⟨t, ht⟩ := hp.principal
  have ht0 : t ≠ 0 := by
    intro h; apply hn; rw [ht, h, Submodule.span_zero_singleton]
  obtain ⟨c, _, _⟩ := augmented_conormal K (X.presheaf.stalk x) ε
  let q : K ≃ₗ[K] DifferentialFiber ε :=
    (CartierGradedTensor.conormalCoord ε t ht ht0).trans c
  haveI : FiniteDimensional K (DifferentialFiber ε) := q.finiteDimensional
  have hd : Module.finrank K (DifferentialFiber ε) = Module.finrank K K := q.finrank_eq.symm
  have hsurj := surjective_of_nonzero_of_finrank_eq_one
    (Module.finrank_self K) (fiberCoefficient_ne_zero f e x halg ε)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj, hsurj⟩

end StalkCoefficient

open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
open ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149
attribute [local instance] sectionModule

section PointFrame
variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of K))
variable (e : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ f.kaehler)
variable (p : Spec (CommRingCat.of K) ⟶ X)

def pointFrame : (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf :
    (Spec (CommRingCat.of K)).Modules) ≅ (Scheme.Modules.pullback p).obj f.kaehler :=
  letI := unitPullback_isIso p
  (asIso (unitPullback p)).symm ≪≫ (Scheme.Modules.pullback p).mapIso e

/-- The field-linear coordinates of global sections use the actual Gamma-Spec map. -/
def frameSections {L : (Spec (CommRingCat.of K)).Modules}
    (E : (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf :
      (Spec (CommRingCat.of K)).Modules) ≅ L) : K ≃ₗ[K] Γ(L,⊤) where
  toFun c := Scheme.Modules.Hom.app E.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
  invFun m := (Scheme.ΓSpecIso (CommRingCat.of K)).hom (Scheme.Modules.Hom.app E.inv ⊤ m)
  map_add' a b := by simp only [map_add]
  map_smul' a b := by
    change Scheme.Modules.Hom.app E.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (a*b)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv a • _
    rw [map_mul]
    exact Scheme.Modules.Hom.app_smul E.hom _ _
  left_inv c := by
    dsimp only
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.hom_inv_id]
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id c)
  right_inv m := by
    dsimp only
    rw [← ConcreteCategory.comp_apply, (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id]
    change Scheme.Modules.Hom.app E.hom ⊤ (Scheme.Modules.Hom.app E.inv ⊤ m) = m
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.inv_hom_id]
    rfl

lemma evaluated_germ (U : X.Opens) (hx : p (IsLocalRing.closedPoint K) ∈ U)
    (a : Γ(X,U)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv
      (Scheme.stalkClosedPointTo p (X.presheaf.germ U _ hx a)) =
      topScalar (Scheme.preimage_eq_top_of_closedPoint_mem p hx) (p.app U a) := by
  have h := ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo p U hx) a
  change Scheme.stalkClosedPointTo p (X.presheaf.germ U _ hx a) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (topScalar (Scheme.preimage_eq_top_of_closedPoint_mem p hx) (p.app U a)) at h
  rw [h, ← ConcreteCategory.comp_apply, (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id]
  rfl

lemma frameSections_differential (U : X.Opens)
    (hx : p (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X,U)) :
    frameSections (pointFrame f e p)
      (Scheme.stalkClosedPointTo p (X.presheaf.germ U _ hx (coefficient f e U a))) =
      topSection (Scheme.preimage_eq_top_of_closedPoint_mem p hx)
        (Scheme.Modules.pullbackLocalSection p (relativeD f U a)) := by
  let hU := Scheme.preimage_eq_top_of_closedPoint_mem p hx
  have hd : relativeD f U a = coefficient f e U a •
      Scheme.Modules.Hom.app e.hom U (1 : Γ(X,U)) := by
    rw [← Scheme.Modules.Hom.app_smul]
    change relativeD f U a = Scheme.Modules.Hom.app e.hom U (coefficient f e U a * (1 : Γ(X,U)))
    rw [mul_one]
    unfold coefficient
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [hd, Scheme.Modules.pullbackLocalSection_smul, topSection_smul,
    pullFrame_local_one p e.hom U hU]
  change Scheme.Modules.Hom.app (pointFrame f e p).hom ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv _) = _
  rw [evaluated_germ]
  have hh : Scheme.Modules.Hom.app (pointFrame f e p).hom ⊤
      (topScalar hU (p.app U (coefficient f e U a))) =
      topScalar hU (p.app U (coefficient f e U a)) •
        Scheme.Modules.Hom.app (pointFrame f e p).hom ⊤
          (1 : Γ(Spec (CommRingCat.of K),⊤)) := by
    rw [← Scheme.Modules.Hom.app_smul]
    apply congrArg (Scheme.Modules.Hom.app (pointFrame f e p).hom ⊤)
    change _ = _ * (1 : Γ(Spec (CommRingCat.of K),⊤))
    exact (mul_one _).symm
  exact hh


lemma restrict_topSection {S : Scheme.{u}} {L : S.Modules} {U : S.Opens}
    (hU : U = ⊤) (m : Γ(L,U)) :
    L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (topSection hU m) = m := by
  subst U
  simp [topSection]

lemma restrict_injective {S : Scheme.{u}} (L : S.Modules) {U : S.Opens}
    (hU : U = ⊤) :
    Function.Injective (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  subst U
  simpa using (Function.injective_id : Function.Injective (id : Γ(L,⊤) → Γ(L,⊤)))

lemma differentialClass_surjective {A : Type u} [CommRing A] [Algebra K A]
    (ε : A →ₐ[K] K) : Function.Surjective (differentialClass ε) := by
  intro m
  obtain ⟨c, hc, _⟩ := augmented_conormal K A ε
  obtain ⟨z, rfl⟩ := c.surjective m
  obtain ⟨a, rfl⟩ := (ideal ε).toCotangent_surjective z
  exact ⟨a.1, (hc a).symm⟩

include e in
lemma comparison
    [Algebra K (X.presheaf.stalk (p (IsLocalRing.closedPoint K)))]
    [IsDomain (X.presheaf.stalk (p (IsLocalRing.closedPoint K)))]
    (halg : algebraMap K (X.presheaf.stalk (p (IsLocalRing.closedPoint K))) =
      stalkScalar f (p (IsLocalRing.closedPoint K)))
    (ε : X.presheaf.stalk (p (IsLocalRing.closedPoint K)) →ₐ[K] K)
    (hε : ε.toRingHom = (Scheme.stalkClosedPointTo p).hom)
    (hp : (ideal ε).IsPrincipal) (hn : ideal ε ≠ ⊥) :
    ∃! E : DifferentialFiber ε ≃ₗ[K] Γ((Scheme.Modules.pullback p).obj f.kaehler,⊤),
      ∀ (U : X.Opens) (hx : p (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X,U)),
        ((Scheme.Modules.pullback p).obj f.kaehler).presheaf.map
          (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op
          (E (differentialClass ε (X.presheaf.germ U _ hx a))) =
        Scheme.Modules.pullbackLocalSection p (relativeD f U a) := by
  let c := LinearEquiv.ofBijective (fiberCoefficient f e _ halg ε)
    (fiberCoefficient_bijective f e _ halg ε hp hn)
  let E := c.trans (frameSections (pointFrame f e p))
  have hE (U : X.Opens) (hx : p (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X,U)) :
      ((Scheme.Modules.pullback p).obj f.kaehler).presheaf.map
        (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (E (differentialClass ε (X.presheaf.germ U _ hx a))) =
      Scheme.Modules.pullbackLocalSection p (relativeD f U a) := by
    have hval : E (differentialClass ε (X.presheaf.germ U _ hx a)) =
        topSection (Scheme.preimage_eq_top_of_closedPoint_mem p hx)
          (Scheme.Modules.pullbackLocalSection p (relativeD f U a)) := by
      change frameSections (pointFrame f e p)
        (fiberCoefficient f e _ halg ε (differentialClass ε _)) = _
      rw [fiberCoefficient_D, stalkCoefficient_germ]
      change frameSections (pointFrame f e p) (ε.toRingHom _) = _
      rw [hε]
      exact frameSections_differential f e p U hx a
    rw [hval]
    exact restrict_topSection _ _
  refine ⟨E, hE, ?_⟩
  intro E' hE'
  apply LinearEquiv.ext
  intro m
  obtain ⟨a, rfl⟩ := differentialClass_surjective ε m
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq a
  apply restrict_injective _ (Scheme.preimage_eq_top_of_closedPoint_mem p hx)
  exact (hE' U hx a).trans (hE U hx a).symm

end PointFrame

end OriginHodgeComparisonR0163

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaConormalInitialR0162 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaAlgebraicCoordinatesR0143 ArithmeticThetaCompactifiedDifferentialR0145
open OriginHodgeComparisonR0163

/-- The actual identity stalk differential fiber is canonically the Hodge fiber,
with the prescribed local differential formula and uniqueness. -/
theorem origin_hodge_comparison :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ArithmeticThetaHodgeInitialR0163.IsHodgeComparison k M s hs.1 := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs.1) :=
    (originScalar k M s hs.1).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs.1) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs.1).toAlgebra
  obtain ⟨ε₀, κ, hε₀, hi, hp, hn, ht⟩ :=
    actual_origin_augmented_taylor k r hr h3 he T M hM s hs G hG
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨δ, hδ, _⟩ := global_normalized_differential k r hr h3 T he M hM s hs X Y hX hY
  intro ε hε
  have heq : ε = ε₀ := by
    apply AlgHom.ext
    intro a
    exact RingHom.congr_fun (hε.trans hε₀.1.symm) a
  have hp' : (ideal ε).IsPrincipal := heq ▸ hp
  have hn' : ideal ε ≠ ⊥ := heq ▸ hn
  exact @comparison (LaurentSeries k) _ (genericScheme k M)
    (genericStructure k M) δ (genericPoint k M s hs.1)
    (originScalar k M s hs.1).toAlgebra inferInstance rfl ε hε hp' hn'

end ArithmeticThetaHodgeInitialR0163

#print axioms ArithmeticThetaHodgeInitialR0163.origin_hodge_comparison
