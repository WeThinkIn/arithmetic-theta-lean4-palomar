module

public import GeneralKatoExistenceR0168

@[expose] public section

/-! Regular units on arbitrary opens avoiding the actual multiplication kernel. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace GeneralKatoUnitLocus

lemma section_of_ord_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : Type u) [Field F] (p : X ⟶ Spec (CommRingCat.of F))
    [SmoothOfRelativeDimension 1 p] (U : X.Opens) [Nonempty U]
    (q : X.functionField) (hq : q ≠ 0)
    (hord : ∀ x ∈ U, Scheme.ord q x = 0) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = q := by
  suffices h : q ∈ (algebraMap Γ(X, U) X.functionField).range from h
  rw [Scheme.Opens.range_algebraMap_functionField_eq_iInf]
  refine Subring.mem_iInf.mpr fun x => Subring.mem_iInf.mpr fun hx => ?_
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set X) ∩ (U : Set X))
    ⟨x, subset_closure (Set.mem_singleton x), hx⟩
    (isClosed_closure.isLocallyClosed.inter U.isOpen.isLocallyClosed)
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy.1
  letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed p y hyclosed
  have hyco : Order.coheight y = 1 := by
    have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk y)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hm : q ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk y)) :=
    (Scheme.ord_eq_iff hyco hq).mp (hord y hy.2)
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hm
  obtain ⟨a, _, ha⟩ := hm
  refine ⟨X.presheaf.stalkSpecializes hxy a, ?_⟩
  change (X.presheaf.stalkSpecializes ((_root_.genericPoint_spec X).specializes trivial))
    (X.presheaf.stalkSpecializes hxy a) = q
  rw [← ConcreteCategory.comp_apply, X.presheaf.stalkSpecializes_comp]
  exact ha

lemma unit_section_of_ord_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : Type u) [Field F] (p : X ⟶ Spec (CommRingCat.of F))
    [SmoothOfRelativeDimension 1 p] (U : X.Opens) [Nonempty U]
    (q : X.functionField) (hq : q ≠ 0)
    (hord : ∀ x ∈ U, Scheme.ord q x = 0) :
    ∃! a : Γ(X, U), X.germToFunctionField U a = q ∧ IsUnit a := by
  obtain ⟨a, ha⟩ := section_of_ord_zero F p U q hq hord
  have hinv : ∀ x ∈ U, Scheme.ord q⁻¹ x = 0 := by
    intro x hx
    have h := Scheme.ord_mul (x := x) hq (inv_ne_zero hq)
    have hone : Scheme.ord (1 : X.functionField) x = 0 := by
      have h := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField))
        (one_ne_zero (α := X.functionField))
      rw [one_mul] at h
      omega
    rw [mul_inv_cancel₀ hq, hone, hord x hx, zero_add] at h
    exact h.symm
  obtain ⟨b, hb⟩ := section_of_ord_zero F p U q⁻¹ (inv_ne_zero hq) hinv
  have hab : a * b = 1 := by
    apply X.germToFunctionField_injective U
    change (X.germToFunctionField U).hom (a * b) = (X.germToFunctionField U).hom 1
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hq]
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, rfl⟩
  · intro a' ha'
    exact X.germToFunctionField_injective U (ha'.1.trans ha.symm)

end GeneralKatoUnitLocus

/-- The normalized Kato function is a unique regular unit on every nonempty
open avoiding the actual multiplication kernel. -/
theorem general_kato_unit_locus :
∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (G : ArithmeticThetaGeneralEllipticKatoR0168.Law F W) (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)], ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∀ (g : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField), ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction F W G c g → ∀ (U : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).Opens) [Nonempty U], (∀ x ∈ U, G.schemeNsmul c x ≠ ArithmeticThetaGeneralEllipticKatoR0168.originPoint F W) → ∃! a : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).presheaf.obj (Opposite.op U), (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).germToFunctionField U a = g ∧ IsUnit a := by
  intro F _ _ W _ G hG _ _ c hc hc6 g hg U _ hU
  letI : SmoothOfRelativeDimension 1 (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  apply GeneralKatoUnitLocus.unit_section_of_ord_zero F (structureMap F W) U g hg.1.1
  intro x hx
  have hcomp : origin F W ≫ G.schemeNsmul c = origin F W := by
    have ho : (G.one (𝟙 _)).val = origin F W := by
      simpa only [Category.id_comp] using hG.1 (𝟙 _)
    rw [← ho, ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      G.nsmul_unit]
  have horigin : G.schemeNsmul c (originPoint F W) = originPoint F W :=
    congrArg (fun f => f (IsLocalRing.closedPoint F)) hcomp
  have hxo : x ≠ originPoint F W := by
    intro h
    exact hU x hx (h ▸ horigin)
  rw [hg.1.2 x]
  simp only [katoOrder, if_neg hxo, if_neg (hU x hx), sub_self]

#print axioms general_kato_unit_locus
end ArithmeticThetaGeneralEllipticKatoR0168
