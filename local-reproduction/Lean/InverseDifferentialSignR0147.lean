import HodgeFourTorsionDefinitionsR0147

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential

section Coefficients
variable {F : Type u} [CommRing F] {C : Scheme.{u}}
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)

def coefficient (U : C.Opens) (a : Γ(C,U)) : Γ(C,U) :=
  Scheme.Modules.Hom.app e.inv U (relativeD p U a)

lemma coefficient_add (U : C.Opens) (a b : Γ(C,U)) :
    coefficient p e U (a+b) = coefficient p e U a + coefficient p e U b := by
  simp only [coefficient, relativeD_add, map_add]

lemma coefficient_mul (U : C.Opens) (a b : Γ(C,U)) :
    coefficient p e U (a*b) = a * coefficient p e U b + b * coefficient p e U a := by
  simp only [coefficient, relativeD_mul, map_add, Scheme.Modules.Hom.app_smul]
  rfl

lemma coefficient_zero (U : C.Opens) : coefficient p e U 0 = 0 := by
  simp only [coefficient, relativeD_zero, map_zero]

lemma coefficient_one (U : C.Opens) : coefficient p e U 1 = 0 := by
  simp only [coefficient, relativeD_one, map_zero]

lemma coefficient_neg (U : C.Opens) (a : Γ(C,U)) :
    coefficient p e U (-a) = -coefficient p e U a := by
  have h := coefficient_add p e U a (-a)
  rw [add_neg_cancel, coefficient_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma coefficient_constant (U : C.Opens) (c : F) :
    coefficient p e U ((p.constToPresheaf.app (Opposite.op U)).hom c) = 0 := by
  letI := p.sectionsAlgebra U
  change (Scheme.Modules.Hom.app e.inv U)
    (p.kaehlerToSectionsₗ U (KaehlerDifferential.D F Γ(C,U) (algebraMap F Γ(C,U) c))) = 0
  rw [Derivation.map_algebraMap, map_zero, map_zero]

lemma coefficient_restrict (U V : C.Opens) (h : V ≤ U) (a : Γ(C,U)) :
    C.presheaf.map (homOfLE h).op (coefficient p e U a) =
      coefficient p e V (C.presheaf.map (homOfLE h).op a) := by
  exact (hom_restrict e.inv U V h _).trans
    (congrArg (Scheme.Modules.Hom.app e.inv V) (relativeD_restrict p U h a))

lemma coefficient_normalization (U : C.Opens) (x q : Γ(C,U))
    (h : relativeD p U x = q • Scheme.Modules.Hom.app e.hom U (1 : Γ(C,U))) :
    coefficient p e U x = q := by
  unfold coefficient
  rw [h, Scheme.Modules.Hom.app_smul]
  have he : Scheme.Modules.Hom.app e.inv U (Scheme.Modules.Hom.app e.hom U (1 : Γ(C,U))) =
      (1 : Γ(C,U)) := by
    exact ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f U) e.hom_inv_id) (1 : Γ(C,U))
  rw [he]
  exact mul_one q
end Coefficients

section AffineAlgebra
open ArithmeticThetaCubicModelR0144
open MvPolynomial
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)

/-- A twisted derivation on the cubic vanishes if it vanishes on X;
the relation and a nonzero image of 2Y force vanishing on Y. -/
lemma cubic_twisted_ext {B : Type u} [CommRing B] [IsDomain B]
    (φ : CubicRing k r →+* B) (E : CubicRing k r →+ B)
    (hprod : ∀ a b, E (a*b) = φ a * E b + φ b * E a)
    (hconst : ∀ c, E (algebraMap (LaurentSeries k) (CubicRing k r) c) = 0)
    (hx : E (cubicCoordinate k r false) = 0)
    (hy : φ (2*cubicCoordinate k r true) ≠ 0) : ∀ a, E a = 0 := by
  have hc (c : LaurentSeries k) :
      E (cubicCoordinate k r false - algebraMap _ _ c) = 0 := by
    rw [map_sub, hx, hconst, sub_self]
  have hyr : E (cubicCoordinate k r true) = 0 := by
    have h := congrArg E (AffineFrame.equation k r)
    rw [pow_two, hprod, hprod, hprod, hc, hc, hc] at h
    simp only [mul_zero, add_zero] at h
    have hh : φ (2*cubicCoordinate k r true) * E (cubicCoordinate k r true) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination h
    exact (mul_eq_zero.mp hh).resolve_left hy
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C c => exact hconst c
  | add a b ha hb => rw [map_add, map_add, ha, hb, zero_add]
  | mul_X a i ha =>
    rw [map_mul, hprod, ha, mul_zero, add_zero]
    have hi : E (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
      fin_cases i
      · exact hx
      · exact hyr
    rw [hi, mul_zero]
end AffineAlgebra

section RationalRestriction
variable {C : Scheme.{u}} [IsIntegral C]

/-- Every section becomes a quotient of functions on any fixed nonempty
affine open; the equality is stated after restriction, without dividing. -/
lemma section_fraction (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (U : C.Opens) [Nonempty U] (a : Γ(C,U)) :
    ∃ b c : Γ(C,W), c ≠ 0 ∧
      C.presheaf.map (homOfLE (show U ⊓ W ≤ U from inf_le_left)).op a *
        C.presheaf.map (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op c =
      C.presheaf.map (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op b := by
  letI : Nonempty (U ⊓ W : C.Opens) := nonempty_inter U W
  letI := functionField_isFractionRing_of_isAffineOpen C W hW
  obtain ⟨⟨b,c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors Γ(C,W))
    (C.germToFunctionField U a)
  refine ⟨b,c,mem_nonZeroDivisors_iff_ne_zero.mp c.property,?_⟩
  apply C.germToFunctionField_injective (U ⊓ W)
  rw [map_mul]
  change C.germToFunctionField U a * C.germToFunctionField W c = C.germToFunctionField W b at hbc
  simpa only [Scheme.germToFunctionField, C.presheaf.germ_res_apply] using hbc
end RationalRestriction

section Defect
variable {F : Type u} [CommRing F] {C : Scheme.{u}}
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable (f : C ⟶ C)

def defect (U : C.Opens) : Γ(C,U) →+ Γ(C,f ⁻¹ᵁ U) where
  toFun a := coefficient p e (f ⁻¹ᵁ U) (f.app U a) + f.app U (coefficient p e U a)
  map_zero' := by simp only [map_zero, coefficient_zero, add_zero]
  map_add' a b := by
    simp only [map_add, coefficient_add]
    abel

lemma defect_mul (U : C.Opens) (a b : Γ(C,U)) :
    defect p e f U (a*b) = f.app U a * defect p e f U b + f.app U b * defect p e f U a := by
  simp only [defect, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, coefficient_mul, map_add]
  ring

lemma app_restrict (U V : C.Opens) (h : V ≤ U) (a : Γ(C,U)) :
    C.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op (f.app U a) =
      f.app V (C.presheaf.map (homOfLE h).op a) := by
  exact (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) a).symm

lemma defect_restrict (U V : C.Opens) (h : V ≤ U) (a : Γ(C,U)) :
    C.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op
      (defect p e f U a) = defect p e f V (C.presheaf.map (homOfLE h).op a) := by
  change C.presheaf.map _ (_ + _) = _
  rw [map_add, coefficient_restrict, app_restrict, app_restrict, coefficient_restrict]
  rfl

/-- An equality of the two derivations on one nonempty affine open extends
to every open by the fraction field of the integral scheme. -/
lemma defect_zero_of_affine [IsIntegral C] [IsIso f]
    (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hzero : ∀ a, defect p e f W a = 0) :
    ∀ (U : C.Opens) (a : Γ(C,U)), defect p e f U a = 0 := by
  intro U a
  by_cases hU : Nonempty U
  · letI := hU
    let V := U ⊓ W
    letI : Nonempty V := nonempty_inter U W
    have hne : Nonempty (f ⁻¹ᵁ V : C.Opens) := by
      obtain ⟨x,hx⟩ := Set.nonempty_coe_sort.mp (inferInstance : Nonempty V)
      obtain ⟨y,hy⟩ := f.homeomorph.surjective x
      refine ⟨⟨y,?_⟩⟩
      change f y ∈ V
      simpa only [Scheme.Hom.homeomorph_apply] using hy ▸ hx
    letI := hne
    apply map_injective_of_isIntegral C
      (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => hx.1))
    rw [map_zero, defect_restrict p e f U V inf_le_left]
    obtain ⟨b,c,hc,heq⟩ := section_fraction W hW U a
    let R := C.presheaf.map (homOfLE (show V ≤ W from inf_le_right)).op
    have hz (z : Γ(C,W)) : defect p e f V (R z) = 0 := by
      rw [← defect_restrict, hzero, map_zero]
    have hh := congrArg (defect p e f V) heq
    rw [defect_mul, hz b, hz c, mul_zero, zero_add] at hh
    apply (mul_eq_zero.mp hh).resolve_left
    have hr : R c ≠ 0 := by
      intro H
      apply hc
      exact map_injective_of_isIntegral C (homOfLE (show V ≤ W from inf_le_right))
        (H.trans (map_zero R.hom).symm)
    intro H
    apply hr
    exact (ConcreteCategory.bijective_of_isIso (f.app V)).1 (H.trans (map_zero (f.app V).hom).symm)
  · have hv : f ⁻¹ᵁ U = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => hU ⟨⟨f x,hx⟩⟩)
    letI : Subsingleton Γ(C,f ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hv)
    exact Subsingleton.elim _ _
end Defect

section StructuralScalars
variable {F : Type u} [CommRing F] {C D : Scheme.{u}}

lemma appLE_constant (p : C ⟶ Spec (CommRingCat.of F)) (g : D ⟶ C)
    (U : C.Opens) (V : D.Opens) (h : V ≤ g ⁻¹ᵁ U) (c : F) :
    g.appLE U V h ((p.constToPresheaf.app (Opposite.op U)).hom c) =
      ((g ≫ p).constToPresheaf.app (Opposite.op V)).hom c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
    p.appLE ⊤ U le_top ≫ g.appLE U V h).hom c = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

lemma app_constant (p : C ⟶ Spec (CommRingCat.of F)) (f : C ⟶ C)
    (hf : f ≫ p = p) (U : C.Opens) (c : F) :
    f.app U ((p.constToPresheaf.app (Opposite.op U)).hom c) =
      (p.constToPresheaf.app (Opposite.op (f ⁻¹ᵁ U))).hom c := by
  rw [f.app_eq_appLE]
  rw [appLE_constant, hf]

lemma topIso_constant (p : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens) (c : F) :
    U.topIso.hom (((U.ι ≫ p).constToPresheaf.app (Opposite.op ⊤)).hom c) =
      (p.constToPresheaf.app (Opposite.op U)).hom c := by
  rw [← appLE_constant p U.ι U ⊤ U.ι_preimage_self.ge c]
  have hh : U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ U.topIso.hom = 𝟙 _ := by
    simp [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom hh _

lemma spec_constant {B : Type u} [CommRing B] [Algebra F B]
    (c : F) :
    ((Spec.map (CommRingCat.ofHom (algebraMap F B))).constToPresheaf.app
      (Opposite.op ⊤)).hom c =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap F B c) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap F B))).appLE ⊤ ⊤ le_top).hom c = _
  have ht : (Spec.map (CommRingCat.ofHom (algebraMap F B))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap F B))).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [ht, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma defect_constant (p : C ⟶ Spec (CommRingCat.of F))
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
    (f : C ⟶ C) (hf : f ≫ p = p) (U : C.Opens) (c : F) :
    defect p e f U ((p.constToPresheaf.app (Opposite.op U)).hom c) = 0 := by
  change coefficient p e _ (f.app U _) + f.app U (coefficient p e U _) = 0
  rw [app_constant p f hf, coefficient_constant, coefficient_constant, map_zero, add_zero]

lemma restricted_app_top {C : Scheme.{u}} (U : C.Opens) (f : C ⟶ C)
    (h : U ≤ f ⁻¹ᵁ U) (g : U.toScheme ⟶ U.toScheme)
    (hg : g ≫ U.ι = U.ι ≫ f) (a : Γ(U.toScheme,⊤)) :
    f.appLE U U h (U.topIso.hom a) = U.topIso.hom (g.appTop a) := by
  have he : g = f.resLE U U h := by
    apply (cancel_mono U.ι).mp
    rw [hg, Scheme.Hom.resLE_comp_ι]
  rw [he]
  change _ = U.topIso.hom ((f.resLE U U h).app ⊤ a)
  rw [Scheme.Hom.resLE_app_top]
  change _ = ((U.topIso.hom ≫ f.appLE U U h ≫ U.topIso.inv) ≫ U.topIso.hom).hom a
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl
end StructuralScalars

section GeometricSign
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
variable (k : Type u) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma geometric_defect_zero (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (e : Frame k M) (heN : IsGlobalDifferentialFrame k M s X Y e)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    ∀ U a, defect (genericStructure k M) e (inversionMap k M rot scal iv ha) U a = 0 := by
  let C := genericScheme k M
  let p : C ⟶ Spec (CommRingCat.of (LaurentSeries k)) := genericStructure k M
  let f : C ⟶ C := inversionMap k M rot scal iv ha
  let W := complement k M s
  letI : IsIntegral C := generic_integral k h3 M hM
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  letI : IsIso f := inversionMap_isIso k M hM rot scal iv ha
  apply defect_zero_of_affine p e f W (complement_isAffineOpen k h3 M hM s hs X hX)
  obtain ⟨a,ha',_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  let q : CubicRing k r →+* Γ(C,W) := W.topIso.hom.hom.comp
    (a.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv.hom)
  have hq (odd : Bool) : q (cubicCoordinate k r odd) =
      W.topIso.hom (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X)) :=
    congrArg W.topIso.hom (coordinateIso_values k M s X Y a ha' odd)
  have hqc (c : LaurentSeries k) : q (algebraMap _ _ c) =
      (p.constToPresheaf.app (Opposite.op W)).hom c := by
    change W.topIso.hom (a.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
      (algebraMap _ _ c))) = _
    rw [← spec_constant]
    have ht : a.hom.appTop = a.hom.appLE ⊤ ⊤ le_top := by
      simp [Scheme.Hom.appTop, Scheme.Hom.appLE]
    rw [ht]
    erw [appLE_constant]
    change W.topIso.hom (((a.hom ≫ cubicStructure k r).constToPresheaf.app (Opposite.op ⊤)).hom c) = _
    rw [ha'.1]
    exact topIso_constant p W c
  have hp : f ≫ p = p := inversionMap_structure k M rot scal iv ha
  have hw : f ⁻¹ᵁ W = W := inversion_complement k h3 M hM s hs rot scal iv ha
  let σ := (f.appLE W W hw.ge).hom
  have hσ (odd : Bool) : σ (q (cubicCoordinate k r odd)) =
      if odd then -q (cubicCoordinate k r odd) else q (cubicCoordinate k r odd) := by
    rw [hq]
    change f.appLE W W hw.ge _ = _
    rw [restricted_app_top W f hw.ge (complementInv k h3 M hM s hs rot scal iv ha)
      (complementInv_inclusion k h3 M hM s hs rot scal iv ha)]
    cases odd
    · exact congrArg W.topIso.hom
        (complement_coordinate_parity k h3 M hM s hs rot scal iv ha false X hX)
    · exact (congrArg W.topIso.hom
        (complement_coordinate_parity k h3 M hM s hs rot scal iv ha true Y hY)).trans
          (map_neg W.topIso.hom.hom _)
  have hx : coefficient p e W (q (cubicCoordinate k r false)) = 2*q (cubicCoordinate k r true) := by
    rw [hq false, hq true]
    exact coefficient_normalization p e W _ _ (normalization_from_predicate k M s X Y e heN)
  have hex : defect p e f W (q (cubicCoordinate k r false)) = 0 := by
    apply map_injective_of_isIntegral C (homOfLE hw.ge)
    change C.presheaf.map (homOfLE hw.ge).op (_ + _) = _
    rw [map_add, map_zero, coefficient_restrict]
    change coefficient p e W (σ (q (cubicCoordinate k r false))) +
      σ (coefficient p e W (q (cubicCoordinate k r false))) = 0
    rw [hσ false, if_neg Bool.false_ne_true, hx, map_mul, map_ofNat, hσ true, if_pos rfl]
    ring
  letI : Nonempty (f ⁻¹ᵁ W : C.Opens) := hw.symm ▸ (inferInstance : Nonempty W)
  let φ := (f.app W).hom.comp q
  have hy : φ (2*cubicCoordinate k r true) ≠ 0 := by
    have hy0 : q (cubicCoordinate k r true) ≠ 0 := by
      rw [hq true]
      exact complement_y_nonzero k h3 he M hM s hs X Y hX hY
    have h2 : (2 : Γ(C,W)) ≠ 0 := by
      letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
      have hu : IsUnit (2 : Γ(C,W)) := by
        simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
          ((p.constToPresheaf.app (Opposite.op W)).hom)
      exact hu.ne_zero
    intro H
    have HH : q (2*cubicCoordinate k r true) = 0 :=
      (ConcreteCategory.bijective_of_isIso (f.app W)).1 (H.trans (map_zero (f.app W).hom).symm)
    rw [map_mul, map_ofNat] at HH
    exact (mul_ne_zero h2 hy0) HH
  have hall := cubic_twisted_ext k r φ ((defect p e f W).comp q.toAddMonoidHom)
    (fun b c => by
      change defect p e f W (q (b*c)) = _
      rw [map_mul]
      exact defect_mul p e f W (q b) (q c))
    (fun c => by
      change defect p e f W (q (algebraMap _ _ c)) = 0
      rw [hqc, defect_constant p e f hp]) hex hy
  intro z
  have hsurj : Function.Surjective q :=
    (ConcreteCategory.bijective_of_isIso W.topIso.hom).2.comp
      ((ConcreteCategory.bijective_of_isIso a.hom.appTop).2.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv).2)
  obtain ⟨b,rfl⟩ := hsurj z
  exact hall b
end GeometricSign

end ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign

namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaGenericEvaluationR0140
open InverseDifferentialSign
open ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141

/-- The actual group inverse has weight -1 on the normalized relative differential,
with the chain rule on every open and every regular function. -/
theorem inverse_differential_sign :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ArithmeticThetaHodgeFourTorsionR0147.DifferentialWeight k M δ (ArithmeticThetaHodgeFourTorsionR0147.inverse k M G) (-1) := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY G hG δ hδ
  obtain ⟨rot,scal,iv,ha⟩ := algebraized_annular_actions k r hr h3 T M hM
  have hf : inverse k M G = inversionMap k M rot scal iv ha := by
    have hi := actual_inverse_comparison k r hr h3 T he M hM s hs G hG
      rot scal iv ha _ (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)
      (universalPoint k M)
    simpa only [inverse, universalPoint, Category.id_comp] using hi
  rw [hf]
  refine ⟨inversionMap_structure k M rot scal iv ha, ?_⟩
  intro U a
  have h := geometric_defect_zero k h3 he M hM s hs X Y hX hY δ hδ rot scal iv ha U a
  change coefficient _ δ _ _ + _ = 0 at h
  change coefficient _ δ _ _ = scalarAt k M _ (-1) *
    (inversionMap k M rot scal iv ha).app U (coefficient _ δ U a)
  have hc : scalarAt k M ((inversionMap k M rot scal iv ha) ⁻¹ᵁ U) (-1) = -1 := by
    simp [scalarAt]
  rw [hc, neg_one_mul]
  exact eq_neg_of_add_eq_zero_left h

#print axioms inverse_differential_sign
end ArithmeticThetaHodgeFourTorsionR0147
