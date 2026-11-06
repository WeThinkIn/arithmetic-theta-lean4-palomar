import AlgebraizedThetaFaithfulnessR0138
import IdentityPositiveSectionsRankR0138
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Saturation tools for the actual identity-divisor section module. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
namespace AlgebraizedThetaSaturationR0138
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open PolygonCechKernelR0131
open ArithmeticThetaPositiveLineR0134.PositiveSectionBasisR0134
open IdentityPositiveSectionsRankR0138

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
variable (L : B k n true ≃+* LaurentPolynomial (R k n))
  (hL : LaurentPresentation k n L)
  (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)

local instance nodeAlgebra : Algebra (R k n) (A k n) := (base k n).toAlgebra
local instance nodeModule : Module (R k n) (A k n) := nodeAlgebra.toModule
local instance nodeAction : DistribMulAction (R k n) (A k n) := nodeModule.toDistribMulAction
local instance nodeScalar : SMul (R k n) (A k n) := ⟨fun c x => base k n c * x⟩
local instance nodeFamilyScalar (r : ℕ) : SMul (R k n) (Fin r → A k n) :=
  ⟨fun c x i => base k n c * x i⟩

/-- The accepted kernel equivalence reads the free columns of its input. -/
lemma kernelCoordinates_apply (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (d : ℕ) (hd : 0 < d)
    (v : LinearMap.ker (difference L hL E hE r hr d)) (j : Fin d) :
    kernelCoordinates L hL E hE r hr h3 d hd v j =
      (singlePivotBasis L hL E hE r hr d).repr v.val (Sum.inl j) := by
  rfl

lemma free_coordinate (r : ℕ) (hr : 0 < r) (d : ℕ)
    (v : Fin r → A k n) (j : Fin d) :
    (singlePivotBasis L hL E hE r hr d).repr v (Sum.inl j) =
      (nodeExpansionEquiv L hL E hE).symm (v (zeroIndex r hr)) (j : ℤ) := by
  simp only [singlePivotBasis, Module.Basis.repr_unitsSMul,
    inv_one, one_smul, Module.Basis.repr_reindex_apply]
  rfl

/-- The first d normal-form coefficients on chart zero detect every section.
This is the explicit finite-rank provider, rather than a finrank equality. -/
lemma finite_coordinates_injective (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (d : ℕ) (hd : 0 < d) :
    Function.Injective (fun v : Sections k r n hr E d => fun j : Fin d =>
      (nodeExpansionEquiv L hL E hE).symm (v.val (zeroIndex r hr)) (j : ℤ)) := by
  intro v w h
  apply (sectionsKernel L hL E hE r hr h3 d).injective
  apply (kernelCoordinates L hL E hE r hr h3 d hd).injective
  ext j
  simpa only [kernelCoordinates_apply, free_coordinate, sectionsKernel, Equiv.coe_fn_mk] using congrFun h j

lemma node_expansion_reduce {N : ℕ} (h : n ≤ N) (c : ℤ →₀ R k N) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
      (nodeExpansion k N c) =
    nodeExpansion k n
      (c.mapRange (truncReduce (PowerSeries k) PowerSeries.X n N h)
        (map_zero _)) := by
  classical
  simp only [nodeExpansion_apply]
  rw [Finsupp.sum_mapRange_index]
  · simp only [Finsupp.sum, map_sum, map_mul,
    ArithmeticThetaPositiveLineR0134.PositiveSectionsReductionR0134.reduce_base]
    rfl
  · intro j; simp

lemma node_coordinates_reduce {N : ℕ} (h : n ≤ N)
    (L' : B k N true ≃+* LaurentPolynomial (R k N))
    (hL' : LaurentPresentation k N L')
    (E' : B k N false ≃+* B k N true) (hE' : IsAdjacent k N E')
    (x : A k N) (j : ℤ) :
    (nodeExpansionEquiv L hL E hE).symm
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h x) j =
    truncReduce (PowerSeries k) PowerSeries.X n N h
      ((nodeExpansionEquiv L' hL' E' hE').symm x j) := by
  have hx := node_expansion_reduce h ((nodeExpansionEquiv L' hL' E' hE').symm x)
  change truncReduce _ _ n N h
    (nodeExpansionEquiv L' hL' E' hE' ((nodeExpansionEquiv L' hL' E' hE').symm x)) =
    nodeExpansionEquiv L hL E hE _ at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  have hh := congrArg (fun y => (nodeExpansionEquiv L hL E hE).symm y j) hx
  simpa only [LinearEquiv.symm_apply_apply, Finsupp.mapRange_apply] using hh

section FormalCoordinates
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} (T : Tower k r hr)

def laurent (n : ℕ) : B k n true ≃+* LaurentPolynomial (R k n) :=
  Classical.choose (truncated_laurent_presentation k n)

lemma laurent_spec (n : ℕ) : LaurentPresentation k n (laurent k n) :=
  (Classical.choose_spec (truncated_laurent_presentation k n)).1

def nodeCoordinates (n : ℕ) : A k n ≃ₗ[R k n] (ℤ →₀ R k n) :=
  (nodeExpansionEquiv (laurent k n) (laurent_spec k n)
    (T.overlap n) (T.overlap_spec n)).symm

lemma nodeCoordinates_reduce (n N : ℕ) (h : n ≤ N) (x : A k N) (j : ℤ) :
    nodeCoordinates k T n
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h x) j =
    truncReduce (PowerSeries k) PowerSeries.X n N h (nodeCoordinates k T N x j) :=
  node_coordinates_reduce _ _ _ _ h _ _ _ _ x j

open AlgebraizedThetaSectionsR0138

/-- Full coefficients are recovered from compatible genuine base quotients. -/
def formalCoordinates (d : ℕ) (v : FormalNumerators k (T := T) d) (j : Fin d) :
    PowerSeries k :=
  Classical.choose
    (ArithmeticThetaPositiveLineR0134.CompatibleFormalSectionBasisR0134.powerSeries_limit k
      (fun n => nodeCoordinates k T n ((v.val n).val (zeroIndex r hr)) (j : ℤ))
      (by
        intro n N h
        rw [← nodeCoordinates_reduce, v.property n N h]))

lemma formalCoordinates_spec (d : ℕ) (v : FormalNumerators k (T := T) d)
    (j : Fin d) (n : ℕ) :
    trunc (PowerSeries k) PowerSeries.X n (formalCoordinates k T d v j) =
      nodeCoordinates k T n ((v.val n).val (zeroIndex r hr)) (j : ℤ) :=
  (Classical.choose_spec
    (ArithmeticThetaPositiveLineR0134.CompatibleFormalSectionBasisR0134.powerSeries_limit k
      (fun n => nodeCoordinates k T n ((v.val n).val (zeroIndex r hr)) (j : ℤ))
      (by
        intro n N h
        rw [← nodeCoordinates_reduce, v.property n N h]))).1 n

/-- The full formal section module embeds in d copies of the actual base ring.
No nonzero-vector hypothesis and no finite-prefix test is used. -/
lemma formalCoordinates_injective (h3 : 3 ≤ r) (d : ℕ) (hd : 0 < d) :
    Function.Injective (formalCoordinates k T d) := by
  intro v w h
  apply Subtype.ext
  funext n
  apply finite_coordinates_injective (laurent k n) (laurent_spec k n)
    (T.overlap n) (T.overlap_spec n) r hr h3 d hd
  funext j
  have hj := congrArg (trunc (PowerSeries k) PowerSeries.X n) (congrFun h j)
  simpa only [formalCoordinates_spec, nodeCoordinates] using hj

end FormalCoordinates

section Determinant
variable (k : Type u) [Field k] (d : ℕ)

/-- An injective square matrix over k[[t]] has cokernel killed by a single
parameter power. The exponent is independent of the vector to be cleared. -/
lemma square_saturation (f : (Fin d → PowerSeries k) →ₗ[PowerSeries k] (Fin d → PowerSeries k))
    (hf : Function.Injective f) :
    ∃ b : ℕ, ∀ v, ∃ w, f w = (PowerSeries.X : PowerSeries k)^b • v := by
  classical
  let A := LinearMap.toMatrix' f
  have hi : Function.Injective (A.mulVec) := by
    intro x y h
    apply hf
    simpa only [A, LinearMap.toMatrix'_mulVec] using h
  have hd : A.det ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hi))
  obtain ⟨z, hz⟩ := PowerSeries.isUnit_divided_by_X_pow_order hd
  have hdet : A.det = PowerSeries.X^A.det.order.toNat * (z : PowerSeries k) := by
    rw [hz]
    exact PowerSeries.X_pow_order_mul_divXPowOrder.symm
  refine ⟨A.det.order.toNat, fun v => ⟨(↑z⁻¹ : PowerSeries k) • Matrix.cramer A v, ?_⟩⟩
  rw [map_smul]
  rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_cramer, ← show A = LinearMap.toMatrix' f from rfl]
  rw [smul_smul]
  have hzdet : (↑z⁻¹ : PowerSeries k) * A.det = PowerSeries.X^A.det.order.toNat := by
    calc
      _ = (↑z⁻¹ : PowerSeries k) * (PowerSeries.X^A.det.order.toNat * ↑z) := congrArg _ hdet
      _ = _ := by rw [mul_comm (PowerSeries.X^A.det.order.toNat), ← mul_assoc, Units.inv_mul, one_mul]
  rw [hzdet]

end Determinant

section FormalModule
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (h3 : 3 ≤ r) (d : ℕ)
open AlgebraizedThetaSectionsR0138
open ArithmeticThetaPositiveLineR0134.PositiveSectionsReductionR0134 (reduce_base)

def fullBase (n : ℕ) : PowerSeries k →+* A k n :=
  (base k n).comp (trunc (PowerSeries k) PowerSeries.X n)

local instance fullNodeAlgebra (n : ℕ) : Algebra (PowerSeries k) (A k n) :=
  (fullBase k n).toAlgebra
local instance fullNodeModule (n : ℕ) : Module (PowerSeries k) (A k n) :=
  (fullNodeAlgebra k n).toModule
local instance fullNodeAction (n : ℕ) : DistribMulAction (PowerSeries k) (A k n) :=
  (fullNodeModule k n).toDistribMulAction
local instance fullNodeMulAction (n : ℕ) : MulAction (PowerSeries k) (A k n) :=
  (fullNodeAction k n).toMulAction
local instance fullNodeScalar (n : ℕ) : SMul (PowerSeries k) (A k n) :=
  ⟨fun c x => fullBase k n c * x⟩

/-- The structural action uses the given base map at every thickness. -/
def formalModule : Submodule (PowerSeries k) (∀ n, Fin r → A k n) where
  carrier v := (∀ n, Compatible k r n hr (T.overlap n) d (v n)) ∧
    ∀ n N (h : n ≤ N) i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h (v N i) = v n i
  zero_mem' := by
    constructor
    · intro n
      apply (compatible_iff_difference (laurent k n) (laurent_spec k n)
        (T.overlap n) (T.overlap_spec n) r hr h3 d _).mpr
      exact map_zero _
    · intros; exact map_zero _
  add_mem' := by
    intro v w hv hw
    constructor
    · intro n
      rw [compatible_iff_difference (laurent k n) (laurent_spec k n)
        (T.overlap n) (T.overlap_spec n) r hr h3]
      change difference _ _ _ _ _ _ _ (v n + w n) = 0
      rw [map_add,
        (compatible_iff_difference _ _ _ _ r hr h3 d _).mp (hv.1 n),
        (compatible_iff_difference _ _ _ _ r hr h3 d _).mp (hw.1 n), add_zero]
    · intro n N h i
      change truncReduce _ _ n N h (v N i + w N i) = v n i + w n i
      rw [map_add, hv.2 n N h i, hw.2 n N h i]
  smul_mem' := by
    intro c v hv
    constructor
    · intro n
      change Compatible k r n hr (T.overlap n) d
        (fun i => base k n (trunc (PowerSeries k) PowerSeries.X n c) * v n i)
      intro i
      simp only [map_mul]
      have hb : (T.overlap n) (restriction k n false
          (base k n (trunc (PowerSeries k) PowerSeries.X n c))) =
          restriction k n true (base k n (trunc (PowerSeries k) PowerSeries.X n c)) :=
        by
          simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
            using RingHom.congr_fun (adjacent_base (T.overlap_spec n))
              (trunc (PowerSeries k) PowerSeries.X n c)
      rw [hb]
      linear_combination restriction k n true
        (base k n (trunc (PowerSeries k) PowerSeries.X n c)) * hv.1 n i
    · intro n N h i
      change truncReduce _ _ n N h
        (base k N (trunc (PowerSeries k) PowerSeries.X N c) * v N i) =
        base k n (trunc (PowerSeries k) PowerSeries.X n c) * v n i
      rw [map_mul, reduce_base, hv.2 n N h i]
      rfl

local instance formalSMul : SMul (PowerSeries k) (formalModule k T h3 d) :=
  ⟨fun c v => ⟨c • v.val, (formalModule k T h3 d).smul_mem c v.property⟩⟩

def asFormal (v : formalModule k T h3 d) : FormalNumerators k (T := T) d :=
  ⟨fun n => ⟨v.val n, v.property.1 n⟩, v.property.2⟩

def ofFormal (v : FormalNumerators k (T := T) d) : formalModule k T h3 d :=
  ⟨fun n => (v.val n).val, (fun n => (v.val n).property), v.property⟩

lemma powerSeries_ext (x y : PowerSeries k)
    (h : ∀ n, trunc (PowerSeries k) PowerSeries.X n x =
      trunc (PowerSeries k) PowerSeries.X n y) : x = y := by
  obtain ⟨f, hf, hu⟩ :=
    ArithmeticThetaPositiveLineR0134.CompatibleFormalSectionBasisR0134.powerSeries_limit k
      (fun n => trunc (PowerSeries k) PowerSeries.X n y) (by intros; rfl)
  exact (hu x h).trans (hu y (fun _ => rfl)).symm

/-- A linear embedding constructed from the actual chart and truncation maps. -/
def coordinatesLinear : formalModule k T h3 d →ₗ[PowerSeries k] (Fin d → PowerSeries k) where
  toFun v := formalCoordinates k T d (asFormal k T h3 d v)
  map_add' v w := by
    funext j
    apply powerSeries_ext k
    intro n
    simp only [Pi.add_apply, map_add, formalCoordinates_spec]
    change nodeCoordinates k T n (v.val n (zeroIndex r hr) + w.val n (zeroIndex r hr)) _ = _
    rw [map_add]
    rfl
  map_smul' c v := by
    funext j
    apply powerSeries_ext k
    intro n
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, formalCoordinates_spec, RingHom.id_apply]
    change nodeCoordinates k T n
      ((trunc (PowerSeries k) PowerSeries.X n c) • v.val n (zeroIndex r hr)) _ = _
    rw [map_smul]
    rfl

lemma coordinatesLinear_injective (hd : 0 < d) :
    Function.Injective (coordinatesLinear k T h3 d) := by
  intro v w h
  have he := formalCoordinates_injective k T h3 d hd h
  apply Subtype.ext
  exact congrArg (fun z : FormalNumerators k (T := T) d => fun n => (z.val n).val) he

lemma formalModule_finite (hd : 0 < d) : Module.Finite (PowerSeries k) (formalModule k T h3 d) :=
  Module.Finite.of_injective (coordinatesLinear k T h3 d)
    (coordinatesLinear_injective k T h3 d hd)

lemma formalModule_torsionFree (hd : 0 < d) :
    Module.IsTorsionFree (PowerSeries k) (formalModule k T h3 d) :=
  Function.Injective.moduleIsTorsionFree (coordinatesLinear k T h3 d)
    (coordinatesLinear_injective k T h3 d hd)
    (fun c v => (coordinatesLinear k T h3 d).map_smul c v)

lemma completedReduction_base (n : ℕ) (c : PowerSeries k) :
    completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k c) =
      fullBase k n c := by
  have h := RingHom.congr_fun (Classical.choose_spec (Classical.choose_spec
    (finite_stage_completion_comparison k n))).1
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c)
  change completedReduction k n (ArithmeticThetaAnnularTorsionPrereqR0053.base k c) =
    trunc _ (ArithmeticThetaNodeCharts.t k) n
      (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k
        (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c)) at h
  rw [h]
  simp [ArithmeticThetaIndexedOverlapsR0058.nodeEquiv,
    ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase, fullBase]
  rfl

lemma finiteNumerator_add (m : ℕ) (hm : 0 < m) (he : Even m)
    (w v : Fin m → PowerSeries k) (n : ℕ) (i : Fin (2*m)) :
    finiteNumerator k m hm he (w+v) n i =
      finiteNumerator k m hm he w n i + finiteNumerator k m hm he v n i := by
  simp only [finiteNumerator, thetaNumerator, ArithmeticThetaAnnularThetaR0128.uniformSection,
    ArithmeticThetaAnnularThetaR0128.combine, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib, mul_add]

lemma finiteNumerator_smul (m : ℕ) (hm : 0 < m) (he : Even m)
    (c : PowerSeries k) (w : Fin m → PowerSeries k) (n : ℕ) (i : Fin (2*m)) :
    finiteNumerator k m hm he (c • w) n i =
      fullBase k n c * finiteNumerator k m hm he w n i := by
  have hc : ArithmeticThetaAnnularThetaR0128.combine k m hm he i.val (c • w) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k c *
        ArithmeticThetaAnnularThetaR0128.combine k m hm he i.val w := by
    simp only [ArithmeticThetaAnnularThetaR0128.combine, Pi.smul_apply, smul_eq_mul,
      map_mul, Finset.mul_sum, mul_assoc]
  have ht : thetaNumerator k m hm he (c • w) i =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k c * thetaNumerator k m hm he w i := by
    unfold thetaNumerator ArithmeticThetaAnnularThetaR0128.uniformSection
    rw [hc]
    ring
  unfold finiteNumerator
  rw [ht, map_mul, completedReduction_base]

def thetaLinear (m : ℕ) (hm : 0 < m) (he : Even m)
    (TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)) (h3 : 3 ≤ 2*m) :
    (Fin m → PowerSeries k) →ₗ[PowerSeries k] formalModule k TT h3 m where
  toFun w := ofFormal k TT h3 m
    ⟨fun n => ⟨finiteNumerator k m hm he w n,
      (theta_numerator_compatibility k m hm he TT w).1 n⟩,
      (theta_numerator_compatibility k m hm he TT w).2⟩
  map_add' v w := by
    apply Subtype.ext
    funext n i
    exact finiteNumerator_add k m hm he v w n i
  map_smul' c w := by
    apply Subtype.ext
    funext n i
    exact finiteNumerator_smul k m hm he c w n i

lemma thetaLinear_injective (m : ℕ) (hm : 0 < m) (he : Even m)
    (TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)) (h3 : 3 ≤ 2*m) :
    Function.Injective (thetaLinear k m hm he TT h3) := by
  intro v w h
  apply AlgebraizedThetaFaithfulnessR0138.thetaNumerator_injective k m hm he
    (zeroIndex (2*m) (Nat.mul_pos (by decide) hm))
  apply AlgebraizedThetaFaithfulnessR0138.completedReduction_ext
  intro n
  exact congrArg (fun z : formalModule k TT h3 m =>
    z.val n (zeroIndex (2*m) (Nat.mul_pos (by decide) hm))) h

/-- Rank m accompanies a proved finite-generation result over the actual
base action; it is never used as a substitute for finite-dimensionality. -/
lemma formalModule_finrank (m : ℕ) (hm : 0 < m) (he : Even m)
    (TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)) (h3 : 3 ≤ 2*m) :
    Module.finrank (PowerSeries k) (formalModule k TT h3 m) = m := by
  letI := formalModule_finite k TT h3 m hm
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective
      (coordinatesLinear_injective k TT h3 m hm)
    simpa using h
  · have h := LinearMap.finrank_le_finrank_of_injective
      (thetaLinear_injective k m hm he TT h3)
    simpa using h

lemma formal_theta_saturation (m : ℕ) (hm : 0 < m) (he : Even m)
    (TT : Tower k (2*m) (Nat.mul_pos (by decide) hm)) (h3 : 3 ≤ 2*m) :
    ∃ b : ℕ, ∀ v : FormalNumerators k (T := TT) m,
      ∃ w : Fin m → PowerSeries k, ∀ n i,
        base k n (parameter k n ^ b) * (v.val n).val i = finiteNumerator k m hm he w n i := by
  let f := (coordinatesLinear k TT h3 m).comp (thetaLinear k m hm he TT h3)
  have hf : Function.Injective f := (coordinatesLinear_injective k TT h3 m hm).comp
    (thetaLinear_injective k m hm he TT h3)
  obtain ⟨b, hb⟩ := square_saturation k m f hf
  refine ⟨b, fun v => ?_⟩
  let x := ofFormal k TT h3 m v
  obtain ⟨w, hw⟩ := hb (coordinatesLinear k TT h3 m x)
  have hs : thetaLinear k m hm he TT h3 w = (PowerSeries.X : PowerSeries k)^b • x := by
    apply coordinatesLinear_injective k TT h3 m hm
    rw [map_smul]
    exact hw
  refine ⟨w, fun n i => ?_⟩
  have hh := congrArg (fun z : formalModule k TT h3 m => z.val n i) hs.symm
  change fullBase k n (PowerSeries.X^b) * (v.val n).val i = _ at hh
  simpa only [fullBase, RingHom.comp_apply, map_pow, thetaLinear, LinearMap.coe_mk,
    AddHom.coe_mk, ofFormal, parameter] using hh

end FormalModule

section AlgebraicNumerators
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open AlgebraizedThetaSectionsR0138
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (compIso compIso_inclusion witness_iso pull_witness chartReduction_value)
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
variable (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) (d : ℕ)

local instance stage_chart_open (n : ℕ) (i : Fin r) :
    IsOpenImmersion ((T.atlas n).chart i) := (T.atlas n).chart_open i

/-- Reduction of an arbitrary realized numerator tuple, without presupposing
that the tuple already extends to a compatible formal section. -/
lemma finiteReduce_realizes_tuple (n N : ℕ) (h : n ≤ N)
    (v : Fin r → A k N) (φ : StageDual k (T.atlas N) d)
    (hφ : StageRealizes k (T.atlas N) d v φ) :
    StageRealizes k (T.atlas n) d
      (fun i => truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h (v i)) (finiteReduce k h3 M hM s hs d n N h φ) := by
  intro i
  let f := T.transition n N h
  let cn := (T.atlas n).chart i
  let cN := (T.atlas N).chart i
  let g := chartReduction k n N h
  let L := stageModule k (T.atlas N) d
  let Q := stageModule k (T.atlas n) d
  let jL := idealInclusion ((stageIdeal k (T.atlas N))^d)
  let jQ := idealInclusion ((stageIdeal k (T.atlas n))^d)
  let e : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback cN).obj L) ≅
      (Scheme.Modules.pullback cn).obj Q :=
    squareIso f cn cN g ((T.transition_spec n N h).2 i) L ≪≫
      (Scheme.Modules.pullback cn).mapIso (finiteIso k h3 M hM s hs d n N h)
  have hj : e.hom ≫ pulledInclusion cn jQ = pulledInclusion g (pulledInclusion cN jL) :=
    square_comparison f cn cN g ((T.transition_spec n N h).2 i) L Q jL jQ
      (finiteIso k h3 M hM s hs d n N h).hom (finiteIso_inclusion k h3 M hM s hs d n N h)
  have hq : e.hom ≫ pulledInclusion cn (finiteReduce k h3 M hM s hs d n N h φ) =
      pulledInclusion g (pulledInclusion cN φ) := by
    apply square_comparison f cn cN g ((T.transition_spec n N h).2 i) L Q φ
      (finiteReduce k h3 M hM s hs d n N h φ) (finiteIso k h3 M hM s hs d n N h).hom
    simp only [finiteReduce, Iso.hom_inv_id_assoc]
    rfl
  have hw := pull_witness g ((Scheme.Modules.pullback cN).obj L)
    (pulledInclusion cN jL) (pulledInclusion cN φ) _ _ (hφ i)
  have ht := (witness_iso e _ _ _ _ hj hq _ _).mp hw
  dsimp only [g] at ht
  rw [chartReduction_value, chartReduction_value, map_pow,
    AlgebraizedThetaSectionsR0138.reduce_equation] at ht
  exact ht

lemma reduceDual_transition (n N : ℕ) (h : n ≤ N) (φ : Dual k M s d) :
    reduceDual k h3 M hM s hs d n φ =
      finiteReduce k h3 M hM s hs d n N h (reduceDual k h3 M hM s hs d N φ) := by
  apply (cancel_epi (stageIso k h3 M hM s hs d n).hom).mp
  simp only [reduceDual, Iso.hom_inv_id_assoc]
  apply (cancel_epi (compIso (T.transition n N h) (M.inclusion N) (M.inclusion n)
    (hM.2.2.2 n N h) (powerModule k M s d)).hom).mp
  rw [← Category.assoc _ (stageIso k h3 M hM s hs d n).hom,
    stageIso_transition k h3 M hM s hs d n N h]
  simp only [finiteReduce, Category.assoc, Iso.hom_inv_id_assoc,
    pulledInclusion, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [pulledInclusion, CategoryTheory.Functor.map_comp, Category.assoc] using
    compIso_inclusion (T.transition n N h) (M.inclusion N) (M.inclusion n)
    (hM.2.2.2 n N h) (powerModule k M s d) φ

lemma stage_numerator_eq (n : ℕ) (v : Fin r → A k n) (φ : StageDual k (T.atlas n) d)
    (hφ : StageRealizes k (T.atlas n) d v φ) :
    IdentityStageSectionRealizationR0138.numerator k r n hr h3 (T.overlap_spec n)
      (T.atlas n) d φ = v := by
  funext i
  obtain ⟨z, hz, hq⟩ := hφ i
  have hj := pullback_open_realization ((T.atlas n).chart i) ((stageIdeal k (T.atlas n))^d)
    (stageModule k (T.atlas n) d) (idealInclusion _) (ideal_realization _)
  letI := hj.1
  have he : z = IdentityStageSectionRealizationR0138.localGenerator k r n hr h3
      (T.overlap_spec n) (T.atlas n) d i :=
    mono_app_injective (pulledInclusion ((T.atlas n).chart i) (idealInclusion _)) ⊤
      (hz.trans (IdentityStageSectionRealizationR0138.localGenerator_spec k r n hr h3
        (T.overlap_spec n) (T.atlas n) d i).symm)
  unfold IdentityStageSectionRealizationR0138.numerator
  rw [← he]
  change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
    (((Scheme.Modules.pullback ((T.atlas n).chart i)).map φ ≫ unitPullback _).app ⊤ z) = _
  rw [hq]
  exact (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply _

/-- Every algebraic section supplies compatible numerators through its actual
pullbacks. Formal compatibility is a conclusion here. -/
def algebraicFormal (φ : Dual k M s d) : FormalNumerators k (T := T) d :=
  ⟨fun n => IdentityStageSectionRealizationR0138.toSections k r n hr h3
    (T.overlap_spec n) (T.atlas n) d (reduceDual k h3 M hM s hs d n φ), by
    intro n N h i
    have hN := IdentityStageSectionRealizationR0138.toSections_realizes k r N hr h3
      (T.overlap_spec N) (T.atlas N) d (reduceDual k h3 M hM s hs d N φ)
    have hh := finiteReduce_realizes_tuple k h3 M hM s hs d n N h _ _ hN
    rw [← reduceDual_transition k h3 M hM s hs d n N h φ] at hh
    exact (congrFun (stage_numerator_eq k h3 d n _ _ hh) i).symm⟩

lemma algebraicFormal_realizes (φ : Dual k M s d) :
    FormalRealizes k M s d (algebraicFormal k h3 M hM s hs d φ) φ := by
  apply (realizes_iff_reductions k h3 M hM s hs d _ φ).mpr
  intro n
  exact IdentityStageSectionRealizationR0138.toSections_realizes k r n hr h3
    (T.overlap_spec n) (T.atlas n) d (reduceDual k h3 M hM s hs d n φ)

lemma algebraicFormal_eq_of_realizes (v : FormalNumerators k (T := T) d)
    (φ : Dual k M s d) (hφ : FormalRealizes k M s d v φ) :
    algebraicFormal k h3 M hM s hs d φ = v := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact stage_numerator_eq k h3 d n _ _
    ((realizes_iff_reductions k h3 M hM s hs d v φ).mp hφ n)

/-- The formal module used in the rank argument consists exactly of the
numerators of actual algebraic sections, via the specified geometric maps. -/
lemma algebraicFormal_bijective : Function.Bijective (algebraicFormal k h3 M hM s hs d) := by
  constructor
  · intro φ ψ h
    obtain ⟨χ, hχ, hu⟩ := algebraize_formal k h3 M hM s hs d
      (algebraicFormal k h3 M hM s hs d φ)
    have hψ : FormalRealizes k M s d (algebraicFormal k h3 M hM s hs d φ) ψ := by
      rw [h]
      exact algebraicFormal_realizes k h3 M hM s hs d ψ
    exact (hu φ (algebraicFormal_realizes k h3 M hM s hs d φ)).trans (hu ψ hψ).symm
  · intro v
    obtain ⟨φ, hφ, _⟩ := algebraize_formal k h3 M hM s hs d v
    exact ⟨φ, algebraicFormal_eq_of_realizes k h3 M hM s hs d v φ hφ⟩

end AlgebraicNumerators


end AlgebraizedThetaSaturationR0138

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open AlgebraizedThetaSaturationR0138

/-- Every actual identity-divisor dual section becomes a literal theta
combination after multiplication by one common vertical power. -/
theorem algebraized_theta_saturation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m),
    ∀ (T : Tower k (2*m) (Nat.mul_pos (by decide) hm)),
    ∀ (M : Model k T), IsModel k T M →
    ∀ (s : baseScheme k ⟶ M.X), MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s →
    ∀ φ : Dual k M s m, ∃ (b : ℕ) (w : Fin m → PowerSeries k),
      Realizes k (hm := hm) he M s b w φ := by
  intro k _ _ m hm he T M hM s hs φ
  have h3 : 3 ≤ 2*m := by obtain ⟨a, ha⟩ := he; omega
  let v := algebraicFormal k h3 M hM s hs m φ
  obtain ⟨b, hb⟩ := formal_theta_saturation k m hm he T h3
  obtain ⟨w, hw⟩ := hb v
  refine ⟨b, w, fun n i => ?_⟩
  obtain ⟨z, hz, hq⟩ := algebraicFormal_realizes k h3 M hM s hs m φ n i
  refine ⟨z, hz, ?_⟩
  have hv := congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom a) hq
  have hi := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.apply_symm_apply
    ((v.val n).val i)
  have hh := hv.trans hi
  exact (congrArg (fun a => base k n (parameter k n ^ b) * a) hh).trans (hw n i)

end ArithmeticThetaIdentitySectionsR0138

#print axioms ArithmeticThetaIdentitySectionsR0138.algebraized_theta_saturation
