module

public import KatoCharacterizationDefinitionsR0254

@[expose] public section

/-! Extension of equal-Cartier-divisor ratios over arbitrary scheme bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaKatoCharacterizationR0254
namespace CartierUnitRatioExtension
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeKatoUnitR0250
open ArithmeticThetaArbitraryKatoUnitR0249 (restrict)
open ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor

lemma common_chart {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I)
    (hJ : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal J) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a b : Γ(X, U.1),
      IsRegular a ∧ IsRegular b ∧ I.ideal U = Ideal.span {a} ∧
        J.ideal U = Ideal.span {b} := by
  obtain ⟨U, hxU, a, ha, hIa⟩ := hI x
  obtain ⟨V, hxV, b, hb, hJb⟩ := hJ x
  obtain ⟨T, hT, hxT, he⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
  have eU : T ≤ U.1 := he.trans inf_le_left
  have eV : T ≤ V.1 := he.trans inf_le_right
  refine ⟨⟨T, hT⟩, hxT, restrict U.1 T eU a, restrict V.1 T eV b,
    regular_restrict U ⟨T, hT⟩ eU a ha, regular_restrict V ⟨T, hT⟩ eV b hb, ?_, ?_⟩
  · rw [← I.map_ideal (U := ⟨T, hT⟩) eU, hIa, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← J.map_ideal (U := ⟨T, hT⟩) eV, hJb, Ideal.map_span, Set.image_singleton]
    rfl

/-- Cartier-complement restriction is injective on every open, without a
reducedness or quasi-compactness hypothesis. -/
lemma restrict_injective {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I) (U : X.Opens) :
    Function.Injective (restrict U (U ⊓ I.support.compl) inf_le_left) := by
  intro s t h
  apply TopCat.Presheaf.section_ext X.sheaf U s t
  intro x hx
  change X.presheaf.germ U x hx s = X.presheaf.germ U x hx t
  obtain ⟨V, hxV, b, hb, hIb⟩ := hI x
  obtain ⟨T, hT, hxT, e⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V.1 ⊓ U from ⟨hxV, hx⟩)
  have eV : T ≤ V.1 := e.trans inf_le_left
  have eU : T ≤ U := e.trans inf_le_right
  have hIT : I.ideal ⟨T, hT⟩ = Ideal.span {restrict V.1 T eV b} := by
    rw [← I.map_ideal (U := ⟨T, hT⟩) eV, hIb, Ideal.map_span, Set.image_singleton]
    rfl
  have hh := congrArg (restrict (U ⊓ I.support.compl) (T ⊓ I.support.compl)
    (inf_le_inf eU le_rfl)) h
  have he : restrict U T eU s = restrict U T eU t := by
    apply complement_restrict_injective I ⟨T, hT⟩ _ (regular_restrict V ⟨T, hT⟩ eV b hb) hIT
    simpa only [restrict_trans] using hh
  have H := congrArg (X.presheaf.germ T x hxT) he
  simpa only [restrict, TopCat.Presheaf.germ_res_apply] using H

def Ratio {X : Scheme.{u}} (C : X.Opens) (v w : Γ(X, C)) (U : X.Opens)
    (s : Γ(X, U)) : Prop :=
  restrict C (U ⊓ C) inf_le_right v =
    restrict U (U ⊓ C) inf_le_left s * restrict C (U ⊓ C) inf_le_right w

lemma ratio_restrict {X : Scheme.{u}} (C : X.Opens) (v w : Γ(X, C))
    (U V : X.Opens) (e : V ≤ U) (s : Γ(X, U)) (h : Ratio C v w U s) :
    Ratio C v w V (restrict U V e s) := by
  have H := congrArg (restrict (U ⊓ C) (V ⊓ C) (inf_le_inf e le_rfl)) h
  simpa only [Ratio, restrict_mul, restrict_trans] using H

lemma ratio_unique {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I)
    (v : Γ(X, I.support.compl)) (w : (Γ(X, I.support.compl))ˣ)
    (U : X.Opens) (s t : Γ(X, U))
    (hs : Ratio I.support.compl v (w : _) U s)
    (ht : Ratio I.support.compl v (w : _) U t) : s = t := by
  apply restrict_injective I hI U
  have hw := w.isUnit.map (X.presheaf.map
    (homOfLE (show U ⊓ I.support.compl ≤ I.support.compl from inf_le_right)).op).hom
  exact hw.isRegular.right (hs.symm.trans ht)

lemma local_ratio {S : Scheme.{u}} (E : Family S) (c : ℕ)
    (v w : UnitSection E c) (hv : HasCartierDivisor E c v)
    (hw : HasCartierDivisor E c w) (x : E.curve) :
    ∃ U : E.curve.affineOpens, x ∈ U.1 ∧ ∃ ε : (Γ(E.curve, U.1))ˣ,
      Ratio (complement E c) (v : _) (w : _) U.1 (ε : _) := by
  obtain ⟨U, hxU, a, b, ha, hb, hIa, hIb⟩ :=
    common_chart (identityIdeal E) (torsionIdeal E c) hv.1 hv.2.1 x
  obtain ⟨ε, hε⟩ := hv.2.2 U a b ha hb hIa hIb
  obtain ⟨η, hη⟩ := hw.2.2 U a b ha hb hIa hIb
  refine ⟨U, hxU, ε * η⁻¹, ?_⟩
  have hbunit : IsUnit (restrict U.1 (U.1 ⊓ complement E c) inf_le_left b) := by
    have he := complement_inter_basicOpen (torsionIdeal E c) U b hIb
    change U.1 ⊓ complement E c = E.curve.basicOpen b at he
    generalize_proofs e
    revert e
    rw [he]
    intro e
    exact E.curve.toRingedSpace.isUnit_res_basicOpen b
  apply hbunit.isRegular.right
  change restrict (complement E c) _ _ (v : _) * restrict U.1 _ _ b =
    (restrict U.1 _ _ (↑(ε * η⁻¹) : Γ(E.curve, U.1)) *
      restrict (complement E c) _ _ (w : _)) * restrict U.1 _ _ b
  rw [hε, mul_assoc, hη, ← restrict_mul]
  congr 1
  simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

lemma glue_ratio {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I)
    (v w : (Γ(X, I.support.compl))ˣ)
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ ε : (Γ(X, U.1))ˣ,
      Ratio I.support.compl (v : _) (w : _) U.1 (ε : _)) :
    ∃! a : (Γ(X, ⊤))ˣ,
      (v : Γ(X, I.support.compl)) = restrict ⊤ I.support.compl le_top (a : _) * (w : _) := by
  classical
  choose U hx ε hε using h
  have hcover : (⊤ : X.Opens) ≤ ⨆ x : X, (U x).1 := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun x => (U x).1)
      (fun x => (ε x : Γ(X, (U x).1))) := by
    intro i j
    exact ratio_unique I hI (v : _) w ((U i).1 ⊓ (U j).1) _ _
      (ratio_restrict _ _ _ _ _ inf_le_left _ (hε i))
      (ratio_restrict _ _ _ _ _ inf_le_right _ (hε j))
  obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' (fun x => (U x).1) ⊤
    (fun _ => homOfLE le_top) hcover (fun x => (ε x : Γ(X, (U x).1))) hcompat
  change ∀ i, X.presheaf.map (homOfLE (show (U i).1 ≤ ⊤ from le_top)).op s =
    (ε i : Γ(X, (U i).1)) at hs
  have hu : IsUnit s := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ s
    intro x hxTop
    change IsUnit (X.presheaf.germ ⊤ x hxTop s)
    have H := (ε x).isUnit.map (X.presheaf.germ (U x).1 x (hx x)).hom
    rw [← hs x] at H
    simpa only [TopCat.Presheaf.germ_res_apply] using H
  have he : (v : Γ(X, I.support.compl)) =
      restrict ⊤ I.support.compl le_top s * (w : _) := by
    apply TopCat.Presheaf.section_ext X.sheaf I.support.compl
    intro x hxC
    change X.presheaf.germ I.support.compl x hxC _ =
      X.presheaf.germ I.support.compl x hxC _
    have H := hε x
    rw [← hs x] at H
    have H' := congrArg (X.presheaf.germ ((U x).1 ⊓ I.support.compl) x ⟨hx x, hxC⟩) H
    simpa only [Ratio, restrict, map_mul, TopCat.Presheaf.germ_res_apply] using H'
  refine ⟨hu.unit, by simpa only [hu.unit_spec] using he, ?_⟩
  intro a ha
  apply Units.ext
  have hh : restrict ⊤ I.support.compl le_top (a : _) =
      restrict ⊤ I.support.compl le_top hu.unit.val := by
    apply w.isUnit.isRegular.right
    exact ha.symm.trans (by simpa only [hu.unit_spec] using he)
  apply restrict_injective I hI ⊤
  have H := congrArg (restrict I.support.compl (⊤ ⊓ I.support.compl) inf_le_right) hh
  simpa only [restrict_trans] using H

end CartierUnitRatioExtension
open AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeKatoUnitR0250

theorem cartier_unit_ratio_extension :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (Base k)) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∀ v w : UnitSection E c, HasCartierDivisor E c v → HasCartierDivisor E c w →
      ∃! a : GlobalUnits E,
        (v : E.curve.presheaf.obj (Opposite.op (complement E c))) =
          restrictGlobal E c a * (w : _) := by
  intro k _ _ S _σ E c _hc _hc6 v w hv hw
  exact CartierUnitRatioExtension.glue_ratio (torsionIdeal E c) hv.2.1 v w
    (CartierUnitRatioExtension.local_ratio E c v w hv hw)

#print axioms cartier_unit_ratio_extension
end ArithmeticThetaKatoCharacterizationR0254
