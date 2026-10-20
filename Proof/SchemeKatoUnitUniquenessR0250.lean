module

public import SchemeTorsionCartesianR0250

@[expose] public section

/-! Uniqueness on the entire torsion complement by actual open charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoUnitR0250
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeDiscriminantR0244
open SchemeDiscriminantExistence

namespace SchemeKatoUnitUniqueness

lemma weierstrass_multiple (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : NeronModelInfra.SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap R W))
    (n : ℕ) :
    ArithmeticThetaSchemeLevelR0204.multiple (weierstrassFamily R W G hG) t n x =
      G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.mul t (ArithmeticThetaSchemeLevelR0204.multiple (weierstrassFamily R W G hG) t n x) x =
      G.mul t (G.nsmul t n x) x
    rw [ih]

lemma weierstrass_complement (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (n : ℕ) :
    complement (weierstrassFamily R W G hG) n =
      ArithmeticThetaArbitraryKatoUnitR0249.complement R W G n := by
  have hm : multiplication (weierstrassFamily R W G hG) n = G.schemeNsmul n :=
    congrArg Subtype.val (weierstrass_multiple R W G hG _ _ n)
  unfold complement torsionIdeal identityIdeal
  rw [weierstrass_zero, hm]
  rfl

end SchemeKatoUnitUniqueness

/-- All affine normalizations determine the full unit section. -/
theorem scheme_kato_unit_uniqueness :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S),
    ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v w : UnitSection E c,
      IsKatoUnit E k σ c v → IsKatoUnit E k σ c w → v = w := by
  intro k _ _ S σ E c hc hc6 v w hv hw
  apply Units.ext
  change (v.val : E.curve.presheaf.obj (Opposite.op (complement E c))) = w.val
  apply TopCat.Presheaf.section_ext E.curve.sheaf (complement E c) v.val w.val
  intro x hx
  change E.curve.presheaf.germ (complement E c) x hx v.val =
    E.curve.presheaf.germ (complement E c) x hx w.val
  obtain ⟨P, z, hz⟩ := scheme_local_weierstrass k S σ E (E.p x)
  letI := P.commRing
  letI := P.algebra
  letI := P.elliptic
  letI := P.openImmersion
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  let C := chartComparison P
  letI : IsOpenImmersion C.map :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.cartesian.flip inferInstance
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback C.cartesian x z hz.symm
  have hcomp := (scheme_torsion_cartesian k S σ E (Base P.ring)
    (P.base ≫ σ) (chartFamily P) P.base rfl C c).2.2.2
  have hWeier := SchemeKatoUnitUniqueness.weierstrass_complement
    P.ring P.equation P.law P.originLaw c
  change complement (chartFamily P) c = _ at hWeier
  rw [hWeier] at hcomp
  obtain ⟨a, ha, ea, hva⟩ := hv P.ring P.equation P.law P.originLaw P.base P.base_eq C
  obtain ⟨b, hb, eb, hwb⟩ := hw P.ring P.equation P.law P.originLaw P.base P.base_eq C
  obtain ⟨d, hd, hu⟩ := ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_unit_existence
    P.ring P.equation P.law P.originLaw c hc hc6
  have hab : a = b := (hu a ha).trans (hu b hb).symm
  have he : C.map.appLE _ _ ea (v : _) = C.map.appLE _ _ ea (w : _) := by
    exact hva.symm.trans ((congrArg Units.val hab).trans hwb)
  have hres := congrArg ((C.map.appIso _).inv) he
  have heq := C.map.appLE_appIso_inv ea
  have hrestriction := congrArg (fun f => f (v : _)) heq
  have hrestriction' := congrArg (fun f => f (w : _)) heq
  have he' := hrestriction.symm.trans (hres.trans hrestriction')
  have hyU : y ∈ ArithmeticThetaArbitraryKatoUnitR0249.complement
      P.ring P.equation P.law c := by
    rw [hcomp]
    change C.map y ∈ complement E c
    rw [hy]
    exact hx
  have hxU : x ∈ C.map ''ᵁ ArithmeticThetaArbitraryKatoUnitR0249.complement
      P.ring P.equation P.law c := ⟨y, hyU, hy⟩
  have H := congrArg (E.curve.presheaf.germ _ x hxU) he'
  simpa only [TopCat.Presheaf.germ_res_apply] using H

#print axioms scheme_kato_unit_uniqueness
end ArithmeticThetaSchemeKatoUnitR0250
