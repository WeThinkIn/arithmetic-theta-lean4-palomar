import RamifiedGenericBaseChangeR0155
import RamifiedAcceptedLeavesR0155

/-! Origin-preserving ramified base change and all multiplication maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0155
namespace RamifiedKatoBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open WeierstrassProjModel

section CartesianLaw
variable {R S : Type u} [CommRing R] [CommRing S]
variable {X Y : Scheme.{u}} {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of S)}
variable {b : Y ⟶ X} {i : Spec (.of S) ⟶ Spec (.of R)}
variable (H : IsPullback b q p i)

def points {V : Scheme.{u}} (t : V ⟶ Spec (.of S)) :
    SchemeHomOver t q ≃ SchemeHomOver (t ≫ i) p where
  toFun x := ⟨x.val ≫ b, by rw [Category.assoc, H.w, ← Category.assoc, x.property]⟩
  invFun x := ⟨H.lift x.val t x.property, H.lift_snd ..⟩
  left_inv x := Subtype.ext (H.hom_ext (H.lift_fst ..) ((H.lift_snd ..).trans x.property.symm))
  right_inv x := Subtype.ext (H.lift_fst ..)

lemma points_natural {V V' : Scheme.{u}} (t : V ⟶ Spec (.of S))
    (t' : V' ⟶ Spec (.of S)) (ψ : V' ⟶ V) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t q) :
    points H t' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (points H t x) :=
  Subtype.ext (Category.assoc _ _ _)

def law (G : RelativeGroupLaw R p) : RelativeGroupLaw S q where
  mul t x y := (points H t).symm (G.mul (t ≫ i) (points H t x) (points H t y))
  one t := (points H t).symm (G.one (t ≫ i))
  inv t x := (points H t).symm (G.inv (t ≫ i) (points H t x))
  mul_assoc t x y z := by simp only [Equiv.apply_symm_apply, G.mul_assoc]
  one_mul t x := by simp only [Equiv.apply_symm_apply, G.one_mul, Equiv.symm_apply_apply]
  mul_one t x := by simp only [Equiv.apply_symm_apply, G.mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (points H t').injective
    rw [points_natural]
    simp only [Equiv.apply_symm_apply, G.mul_natural, points_natural]

lemma points_nsmul (G : RelativeGroupLaw R p) {V : Scheme.{u}}
    (t : V ⟶ Spec (.of S)) (x : SchemeHomOver t q) (n : ℕ) :
    points H t ((law H G).nsmul t n x) = G.nsmul (t ≫ i) n (points H t x) := by
  induction n with
  | zero => exact (points H t).apply_symm_apply _
  | succ n ih =>
    change points H t ((points H t).symm (G.mul _ _ _)) = _
    rw [Equiv.apply_symm_apply]
    change G.mul _ (points H t ((law H G).nsmul t n x)) _ = _
    rw [ih]
    rfl
end CartesianLaw

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaRamifiedPeriodR0154

lemma multiplication_compatible (k : Type u) [Field k] [CharZero k]
    {r rb : ℕ} {hr : 0 < r} {hrb : 0 < rb}
    {T : Tower k r hr} {Tb : Tower k rb hrb}
    (h3b : 3 ≤ rb) (heb : Even rb)
    (M : Model k T) (Mb : Model k Tb) (hMb : IsModel k Tb Mb)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (sb : baseScheme k ⟶ Mb.X) (hsb : MarkedLift k Mb (zeroIndex rb hrb) 1 sb)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (Gb : Law k Mb) (hGb : IsOriginLaw k Mb sb hsb.1 Gb)
    (i : Spec (.of (LaurentSeries k)) ⟶ Spec (.of (LaurentSeries k)))
    (b : genericScheme k Mb ⟶ genericScheme k M)
    (H : IsPullback b (genericStructure k Mb) (genericStructure k M) i)
    (ho : genericPoint k Mb sb hsb.1 ≫ b = i ≫ genericPoint k M s hs.1) :
    ∀ n, multiplication k Mb Gb n ≫ b = b ≫ multiplication k M G n := by
  have hL : IsOriginLaw k Mb sb hsb.1 (law H G) := by
    constructor
    · intro V t
      apply (points H t).injective
      change points H t ((points H t).symm _) = _
      rw [Equiv.apply_symm_apply, hG.1]
      apply Subtype.ext
      change (t ≫ i) ≫ genericPoint k M s hs.1 =
        (t ≫ genericPoint k Mb sb hsb.1) ≫ b
      rw [Category.assoc, Category.assoc, ho]
    · intro V t x y
      change (points H t).symm (G.mul _ _ _) = (points H t).symm (G.mul _ _ _)
      rw [hG.2]
  obtain ⟨L, hL', hu⟩ := actual_generic_group_law k rb hrb h3b Tb heb Mb hMb sb hsb
  have heq : Gb = law H G := (hu Gb hGb).trans (hu _ hL).symm
  intro n
  rw [heq]
  have hn := congrArg Subtype.val (points_nsmul H G (genericStructure k Mb) (universalPoint k Mb) n)
  change multiplication k Mb (law H G) n ≫ b = _ at hn
  rw [hn]
  have hc := MultiplicationDifferential.comp_schemeNsmul G
    (genericStructure k Mb ≫ i) (points H (genericStructure k Mb) (universalPoint k Mb)) n
  change (𝟙 _ ≫ b) ≫ multiplication k M G n = _ at hc
  simpa only [Category.id_comp] using hc.symm

end RamifiedKatoBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaRamifiedPeriodR0154


theorem ramified_kato_base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d) (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (hrd : 0 < r*d) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (Tb : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (r*d) hrd) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (Mb : ArithmeticThetaProjectiveEffectivityR0135.Model k Tb) (hMb : ArithmeticThetaProjectiveEffectivityR0135.IsModel k Tb Mb) (ρ : Fin d → (ArithmeticThetaKatoAnnularR0152.Chart k →+* ArithmeticThetaKatoAnnularR0152.Chart k)) (hρ : ∀ q, ArithmeticThetaRamifiedPeriodR0154.IsChartRamification k d hd q (ρ q)) (χ : Fin r → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) (M.X)) (hχ : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) (χb : Fin (r*d) → Quiver.Hom (ArithmeticThetaKatoAnnularR0152.chartScheme k) (Mb.X)) (hχb : ∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k Mb j (χb j)) (F : Quiver.Hom (Mb.X) (M.X)) (hF : ArithmeticThetaRamifiedPeriodR0154.IsModelRamification k (hd := hd) T Tb M Mb ρ χ χb F) (ell : LaurentSeries k →+* LaurentSeries k) (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell) (f : Quiver.Hom (ArithmeticThetaGenericEvaluationR0140.genericScheme k Mb) (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (hf : ArithmeticThetaRamifiedPeriodR0154.IsGenericLift k T Tb M Mb F f) (he : Even r) (heb : Even (r*d)) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) (M.X)) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (sb : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) (Mb.X)) (hsb : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k Mb (ArithmeticThetaIdentitySectionsR0138.zeroIndex (r*d) hrd) 1 sb) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) (Gb : ArithmeticThetaMarkedGroupLawR0146.Law k Mb) (hGb : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k Mb sb hsb.1 Gb), ArithmeticThetaKatoExistenceR0151.IsTateBaseChange k k M Mb s hs.1 sb hsb.1 G Gb ell f := by
  intro k _ _ d hd r hr h3 hrd T Tb M hM Mb hMb ρ hρ χ hχ χb hχb F hF ell hell f hf he heb s hs sb hsb G hG Gb hGb
  obtain ⟨f₀, hf₀, hu⟩ := ramified_generic_base_change k d hd r hr h3 hrd T Tb M hM Mb hMb
    ρ hρ χ hχ χb hχb F hF ell hell
  have heq : f = f₀ := by
    rw [RamifiedGenericBaseChange.lift_unique k T Tb M Mb F hF.1 ell hell f hf,
      RamifiedGenericBaseChange.lift_unique k T Tb M Mb F hF.1 ell hell f₀ hf₀.1]
  have H := heq.symm ▸ hf₀.2
  have hi : markedIndex r d hd (zeroIndex r hr) = zeroIndex (r*d) hrd := by
    apply Fin.ext
    simp [markedIndex, zeroIndex]
  have hsb' : MarkedLift k Mb (markedIndex r d hd (zeroIndex r hr)) 1 sb := by
    rw [hi]
    exact hsb
  have hsF := ramified_marked_sections k d hd r hr h3 hrd T Tb M hM Mb hMb
    ρ hρ χ hχ χb hχb F hF (zeroIndex r hr) 1 s hs sb hsb'
  have ho : genericPoint k Mb sb hsb.1 ≫ f =
      Spec.map (CommRingCat.ofHom ell) ≫ genericPoint k M s hs.1 := by
    letI : IsOpenImmersion (genericInclusion k M) :=
      AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
    apply (cancel_mono (genericInclusion k M)).mp
    rw [Category.assoc, hf]
    change genericPoint k Mb sb hsb.1 ≫ pullback.fst Mb.p (genericBase k) ≫ F =
      Spec.map (CommRingCat.ofHom ell) ≫ genericPoint k M s hs.1 ≫ pullback.fst M.p (genericBase k)
    simp only [ArithmeticThetaGenericEvaluationR0140.genericPoint, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [Category.assoc, hsF, ← Category.assoc,
      ← RamifiedGenericBaseChange.base_square k d hd ell hell, Category.assoc]
  exact ⟨H, ho, RamifiedKatoBaseChange.multiplication_compatible k
    (h3.trans (Nat.le_mul_of_pos_right r hd)) heb M Mb hMb s hs sb hsb G hG Gb hGb
    (Spec.map (CommRingCat.ofHom ell)) f H ho⟩

end ArithmeticThetaRamifiedPeriodR0155
#print axioms ArithmeticThetaRamifiedPeriodR0155.ramified_kato_base_change
