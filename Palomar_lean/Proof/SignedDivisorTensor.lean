module

public import EffectiveDivisorLine
public import LocalTensorFrame
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaCurveDegree
open ArithmeticThetaGeometricPrerequisites ArithmeticThetaSheafTensor

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
namespace ArithmeticThetaCoverComparison

theorem rational_order_inv (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (r : X.functionField) (hr : r ≠ 0) :
    Scheme.ord r⁻¹ x = -Scheme.ord r x := by
  have h := Scheme.ord_mul hr (inv_ne_zero hr) (x := x)
  rw [mul_inv_cancel₀ hr, rational_order_one] at h
  omega

theorem rational_order_zpow (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (r : X.functionField) (hr : r ≠ 0) (n : ℤ) :
    Scheme.ord (r ^ n) x = n * Scheme.ord r x := by
  cases n with
  | ofNat n => simpa using ArithmeticThetaGeometry.function_order_pow X x r hr n
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [rational_order_inv X x _ (pow_ne_zero _ hr),
      ArithmeticThetaGeometry.function_order_pow X x r hr]
    rw [Int.negSucc_eq]
    push_cast
    ring

/-- Every finite signed divisor is locally the order of an actual nonzero rational function. -/
theorem exists_signed_local_equation
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X)
    (D : X →₀ ℤ)
    (hcodim : ∀ x, D x ≠ 0 → Order.coheight x = 1) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ r : X.functionField, r ≠ 0 ∧ ∀ y ∈ U, Scheme.ord r y = D y := by
  classical
  have hclosedD : IsClosed (D.support : Set X) :=
    finite_codimension_one_set_closed X hcurve _ D.support.finite_toSet
      (fun y hy ↦ hcodim y (Finsupp.mem_support_iff.mp hy))
  by_cases hxD : D x = 0
  · let W : X.Opens := ⟨(D.support : Set X)ᶜ, hclosedD.isOpen_compl⟩
    have hxW : x ∈ W := by simpa [W] using hxD
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
    refine ⟨U, hxU, hU, 1, one_ne_zero, ?_⟩
    intro y hy
    have hyD : D y = 0 := by simpa [W] using hUW hy
    rw [rational_order_one, hyD]
  · obtain ⟨W, hxW, a, ha, hordx⟩ := exists_regular_uniformizer X hN x (hcodim x hxD)
    letI : Nonempty W := ⟨⟨x, hxW⟩⟩
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    let b : Γ(X, V) := X.presheaf.map (homOfLE hVW).op a
    have hb : X.germToFunctionField V b = X.germToFunctionField W a :=
      germ_restrict X W V hVW a
    have hb0 : b ≠ 0 := by
      intro hb0
      have hh : X.germToFunctionField W a = 0 := by rw [← hb, hb0, map_zero]
      exact ha ((map_eq_zero_iff _ (X.germToFunctionField_injective W)).mp hh)
    let r : X.functionField := X.germToFunctionField V b
    have hr : r ≠ 0 := (map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr hb0
    have hrx : Scheme.ord r x = 1 := by simpa [r, hb] using hordx
    let Z : Set X := {y | y ∈ V ∧ Scheme.ord r y ≠ 0}
    have hZ : Z.Finite := finite_regular_order_support X hcurve V hV b hb0
    let S : Set X := ((D.support : Set X) ∪ Z) ∩ ({x} : Set X)ᶜ
    have hS : S.Finite := (D.support.finite_toSet.union hZ).inter_of_left _
    have hclosedS : IsClosed S := finite_codimension_one_set_closed X hcurve S hS (by
      intro y hy
      rcases hy.1 with hy | hy
      · exact hcodim y (Finsupp.mem_support_iff.mp hy)
      · by_contra hn
        exact hy.2 (Scheme.ord_eq_zero_of_coheight_neq_one hn r))
    let A : X.Opens := V ⊓ ⟨Sᶜ, hclosedS.isOpen_compl⟩
    have hxA : x ∈ A := ⟨hxV, by simp [S]⟩
    obtain ⟨U, hU, hxU, hUA⟩ := exists_isAffineOpen_mem_and_subset hxA
    refine ⟨U, hxU, hU, r ^ (D x), zpow_ne_zero _ hr, ?_⟩
    intro y hy
    rw [rational_order_zpow X y r hr]
    by_cases hxy : y = x
    · subst y
      rw [hrx, mul_one]
    · have hyA := hUA hy
      have hnot : y ∉ (D.support : Set X) ∪ Z := by
        intro hmem
        exact hyA.2 ⟨hmem, hxy⟩
      have hyD : D y = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hnot (Or.inl h))
      have hyord : Scheme.ord r y = 0 := by
        by_contra hn
        exact hnot (Or.inr ⟨hyA.1, hn⟩)
      rw [hyD, hyord, mul_zero]

theorem signed_divisor_line :
    ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X],
    OneDimensionalCharts X → ∀ (hN : NormalAffine X) (D : X →₀ ℤ),
    (∀ x, D x ≠ 0 → Order.coheight x = 1) → IsLineBundle X (divisorSheaf X hN D) := by
  intro X _ _ hcurve hN D hcodim x
  obtain ⟨U, hxU, _, r, hr, hord⟩ := exists_signed_local_equation X hcurve hN D hcodim x
  refine ⟨U, hxU, ?_⟩
  exact ⟨localFrameIso X _ U (equationFrame X hN D U r hr hord)⟩

/-- Pointwise rational multiplication is a bilinear bounded-pole pairing. -/
def divisorPairing (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D E : X →₀ ℤ) (U : X.Opens) :
    boundedSections X hN D U →ₗ[Γ(X,U)] boundedSections X hN E U →ₗ[Γ(X,U)]
      boundedSections X hN (D + E) U where
  toFun a :=
    { toFun := fun b ↦ ⟨fun h ↦ a.val h * b.val h, by
        intro h x hx
        by_cases ha : a.val h = 0
        · left; simp [ha]
        by_cases hb : b.val h = 0
        · left; simp [hb]
        right
        have hDa := (a.property h x hx).resolve_left ha
        have hEb := (b.property h x hx).resolve_left hb
        rw [Scheme.ord_mul ha hb, Finsupp.add_apply]
        omega⟩
      map_add' := by intros; apply Subtype.ext; funext h; exact mul_add _ _ _
      map_smul' := by
        intro c b
        apply Subtype.ext
        funext h
        change a.val h * (@Scheme.germToFunctionField X _ U h.down c * b.val h) =
          @Scheme.germToFunctionField X _ U h.down c * (a.val h * b.val h)
        ring }
  map_add' := by intros; apply LinearMap.ext; intro b; apply Subtype.ext; funext h; exact add_mul _ _ _
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    funext h
    change (@Scheme.germToFunctionField X _ U h.down c * a.val h) * b.val h =
      @Scheme.germToFunctionField X _ U h.down c * (a.val h * b.val h)
    ring

/-- Multiplication on the presheaf tensor, before sheafification. -/
def divisorTensorPreMap (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D E : X →₀ ℤ) :
    tensorPresheaf X (divisorSheaf X hN D) (divisorSheaf X hN E) ⟶
      (divisorSheaf X hN (D + E)).val where
  app U := ModuleCat.ofHom (TensorProduct.lift (divisorPairing X hN D E U.unop))
  naturality := by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical multiplication map out of the genuine sheaf tensor. -/
def divisorTensorMap (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D E : X →₀ ℤ) :
    sheafTensor X (divisorSheaf X hN D) (divisorSheaf X hN E) ⟶
      divisorSheaf X hN (D + E) :=
  (tensorHomEquiv X _ _ _).symm (divisorTensorPreMap X hN D E)

theorem divisorTensorMap_section (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D E : X →₀ ℤ) (U : X.Opens)
    (a : boundedSections X hN D U) (b : boundedSections X hN E U) :
    (divisorTensorMap X hN D E).app U (tensorSection X _ _ U a b) =
      divisorPairing X hN D E U a b := by
  have h := tensorHomEquiv_symm_unit X _ _ _ (divisorTensorPreMap X hN D E)
  have hh := congrArg (fun f ↦ f.app (op U)) h
  have hh' := ConcreteCategory.congr_hom hh (a ⊗ₜ[Γ(X,U)] b)
  exact hh'

/-- Multiplication carries the tensor of inverse-equation frames to the product-equation frame. -/
theorem divisorTensorMap_frame (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D E : X →₀ ℤ) (U : X.Opens)
    (r s : X.functionField) (hr : r ≠ 0) (hs : s ≠ 0)
    (hD : ∀ x ∈ U, Scheme.ord r x = D x)
    (hE : ∀ x ∈ U, Scheme.ord s x = E x)
    (V : X.Opens) (hVU : V ≤ U) (a : Γ(X,V)) :
    (divisorTensorMap X hN D E).app V
      ((tensorFrame X _ _ U (equationFrame X hN D U r hr hD)
        (equationFrame X hN E U s hs hE)).equiv V hVU a) =
    (equationFrame X hN (D + E) U (r * s) (mul_ne_zero hr hs)
      (fun x hx ↦ by rw [Scheme.ord_mul hr hs, hD x hx, hE x hx, Finsupp.add_apply])).equiv V hVU a := by
  rw [tensorFrame_apply, divisorTensorMap_section]
  apply Subtype.ext
  funext h
  change (@Scheme.germToFunctionField X _ V h.down 1 / r) *
    (@Scheme.germToFunctionField X _ V h.down a / s) =
    @Scheme.germToFunctionField X _ V h.down a / (r * s)
  rw [map_one]
  ring

/-- On every subopen where both divisors have equations, multiplication is bijective. -/
theorem divisorTensorMap_local_bijective (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (D E : X →₀ ℤ) (U : X.Opens)
    (r s : X.functionField) (hr : r ≠ 0) (hs : s ≠ 0)
    (hD : ∀ x ∈ U, Scheme.ord r x = D x)
    (hE : ∀ x ∈ U, Scheme.ord s x = E x)
    (V : X.Opens) (hVU : V ≤ U) :
    Function.Bijective ((divisorTensorMap X hN D E).app V) := by
  let e := (tensorFrame X _ _ U (equationFrame X hN D U r hr hD)
    (equationFrame X hN E U s hs hE)).equiv V hVU
  let f := (equationFrame X hN (D + E) U (r * s) (mul_ne_zero hr hs)
    (fun x hx ↦ by rw [Scheme.ord_mul hr hs, hD x hx, hE x hx, Finsupp.add_apply])).equiv V hVU
  have heq : (fun a ↦ (divisorTensorMap X hN D E).app V (e a)) = f := by
    funext a
    exact divisorTensorMap_frame X hN D E U r s hr hs hD hE V hVU a
  apply (Function.Bijective.of_comp_iff _ e.bijective).mp
  change Function.Bijective (fun a ↦ (divisorTensorMap X hN D E).app V (e a))
  rw [heq]
  exact f.bijective

/-- A neighborhood basis on which the canonical multiplication is bijective. -/
theorem divisorTensorMap_neighborhoods (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X) (D E : X →₀ ℤ)
    (hD : ∀ x, D x ≠ 0 → Order.coheight x = 1)
    (hE : ∀ x, E x ≠ 0 → Order.coheight x = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective ((divisorTensorMap X hN D E).app V) := by
  obtain ⟨U, hxU, _, r, hr, hord⟩ := exists_signed_local_equation X hcurve hN D hD x
  obtain ⟨W, hxW, _, s, hs, hos⟩ := exists_signed_local_equation X hcurve hN E hE x
  exact ⟨U ⊓ W, ⟨hxU, hxW⟩, fun V hV ↦
    divisorTensorMap_local_bijective X hN D E (U ⊓ W) r s hr hs
      (fun y hy ↦ hord y hy.1) (fun y hy ↦ hos y hy.2) V hV⟩

theorem divisorTensorMap_isIso (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hcurve : OneDimensionalCharts X) (hN : NormalAffine X) (D E : X →₀ ℤ)
    (hD : ∀ x, D x ≠ 0 → Order.coheight x = 1)
    (hE : ∀ x, E x ≠ 0 → Order.coheight x = 1) :
    IsIso (divisorTensorMap X hN D E) := by
  let q := divisorTensorMap X hN D E
  let H := sheafTensor X (divisorSheaf X hN D) (divisorSheaf X hN E)
  let P := divisorSheaf X hN (D + E)
  let q' := (SheafOfModules.toSheaf X.ringCatSheaf).map q
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf X.ringCatSheaf)]
  apply (Sheaf.isLocallyBijective_iff_isIso q').mp
  constructor
  · rw [Sheaf.isLocallyInjective_iff_injective]
    intro U a b hab
    apply H.isSheaf.section_ext
    intro x hx
    obtain ⟨W, hxW, hW⟩ := divisorTensorMap_neighborhoods X hcurve hN D E hD hE x
    refine ⟨U.unop ⊓ W, inf_le_left, ⟨hx, hxW⟩, ?_⟩
    apply (hW _ inf_le_right).injective
    change q.app _ (H.presheaf.map (homOfLE inf_le_left).op a) =
      q.app _ (H.presheaf.map (homOfLE inf_le_left).op b)
    exact (PresheafOfModules.naturality_apply q.val (homOfLE inf_le_left).op a).trans
      ((congrArg (P.presheaf.map (homOfLE inf_le_left).op) hab).trans
        (PresheafOfModules.naturality_apply q.val (homOfLE inf_le_left).op b).symm)
  · change TopCat.Presheaf.IsLocallySurjective q'.hom
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U a x hx
    obtain ⟨W, hxW, hW⟩ := divisorTensorMap_neighborhoods X hcurve hN D E hD hE x
    refine ⟨U ⊓ W, inf_le_left, ?_, ⟨hx, hxW⟩⟩
    exact (hW _ inf_le_right).surjective (P.presheaf.map (homOfLE inf_le_left).op a)

/-- The genuine tensor isomorphism of signed divisor lines is rational multiplication. -/
theorem signed_divisor_tensor :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X],
    ArithmeticThetaCurveDegree.OneDimensionalCharts X →
    ∀ (hN : ArithmeticThetaNormalizedSections.NormalAffine X) (D E : X →₀ ℤ),
    (∀ x, D x ≠ 0 → Order.coheight x = 1) →
    (∀ x, E x ≠ 0 → Order.coheight x = 1) →
    ∃ e : CategoryTheory.Iso
      (ArithmeticThetaSheafTensor.sheafTensor X
        (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN D)
        (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN E))
      (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN (D + E)),
    ∀ (U : X.Opens)
      (a : (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN D).presheaf.obj (Opposite.op U))
      (b : (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN E).presheaf.obj (Opposite.op U))
      (h : PLift (Nonempty U)),
    (e.hom.app U (ArithmeticThetaSheafTensor.tensorSection X
      (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN D)
      (ArithmeticThetaGeometricPrerequisites.divisorSheaf X hN E) U a b)).val h = a.val h * b.val h := by
  intro X _ _ hcurve hN D E hD hE
  letI hmult : IsIso (divisorTensorMap X hN D E) :=
    divisorTensorMap_isIso X hcurve hN D E hD hE
  refine ⟨asIso (divisorTensorMap X hN D E), ?_⟩
  intro U a b h
  change ((divisorTensorMap X hN D E).app U (tensorSection X _ _ U a b)).val h = _
  rw [divisorTensorMap_section]
  rfl

end ArithmeticThetaCoverComparison

#print axioms ArithmeticThetaCoverComparison.signed_divisor_line
#print axioms ArithmeticThetaCoverComparison.signed_divisor_tensor
