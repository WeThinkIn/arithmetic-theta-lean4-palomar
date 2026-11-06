import SchemeKatoUnitExistenceR0250
import SchemeKatoUnitUniquenessR0250

/-! Naturality of the complete Kato unit through the specified Cartesian map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaSchemeKatoUnitR0250
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeDiscriminantR0244
open SchemeDiscriminantExistence

/-- Composition of every affine test preserves normalization of the pulled-back
unit. Uniqueness then identifies it with the normalized unit on the target. -/
theorem scheme_kato_unit_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S),
    ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S),
      b ≫ σ = τ → ∀ C : Comparison E H b, ∀ c : ℕ,
      1 < c → Nat.Coprime c 6 → ∀ (v : UnitSection E c) (w : UnitSection H c),
      IsKatoUnit E k σ c v → IsKatoUnit H k τ c w →
      ∃ e : complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (complement E c),
        (w : H.curve.presheaf.obj (Opposite.op (complement H c))) =
          C.map.appLE _ _ e (v : _) := by
  intro k _ _ S σ E T τ H b hb C c hc hc6 v w hv hw
  have e : complement H c ≤ C.map ⁻¹ᵁ complement E c :=
    (scheme_torsion_cartesian k S σ E T τ H b hb C c).2.2.2.le
  let v' : UnitSection H c :=
    Units.map (C.map.appLE _ _ e).hom.toMonoidHom v
  have hv' : IsKatoUnit H k τ c v' := by
    intro R _ _ W _ G hG a ha D
    have hab : (a ≫ b) ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
      rw [Category.assoc, hb, ha]
    obtain ⟨z, hz, ez, hez⟩ := hv R W G hG (a ≫ b) hab (comparisonComp C D)
    have eD := (SchemeKatoUnitExistence.test_complement τ H R W G hG D c).le
    refine ⟨z, hz, eD, ?_⟩
    have hcomp := ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_comp_appLE D.map C.map (complement E c)
        (complement H c) (ArithmeticThetaArbitraryKatoUnitR0249.complement R W G c)
        e eD) (v : E.curve.presheaf.obj (Opposite.op (complement E c)))
    exact hez.trans hcomp.symm
  refine ⟨e, ?_⟩
  exact congrArg Units.val (scheme_kato_unit_uniqueness k T τ H c hc hc6 w v' hw hv')

#print axioms scheme_kato_unit_naturality
end ArithmeticThetaSchemeKatoUnitR0250
