module

public import SchemePushforwardIntertwiningR0262
public import SchemeEvaluationNaturalityR0262

@[expose] public section

/-! The actual fixed kernels, orbit inclusions and identity evaluations are
compared through the same canonical pushforward isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeSchrodingerR0261

namespace InvariantComponentNaturality

/-- Intertwining extends to every power, without an invertibility hypothesis. -/
lemma powers {C : Type*} [Category C] {X Y : C} (a : End X) (b : End Y)
    (p : X ⟶ Y) (h : a ≫ p = p ≫ b) (n : ℕ) :
    (a ^ n) ≫ p = p ≫ (b ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_def, Category.assoc]
    rw [ih, ← Category.assoc a p, h, Category.assoc]

end InvariantComponentNaturality

/-- The unique comparison of actual invariant kernels respects every orbit
inclusion and every identity-evaluation component. -/
theorem scheme_invariant_component_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hc : CategoryTheory.IsPullback f F.p E.p b) (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), ∀ (m : ℕ), 0 < m → ∀ (A B : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V E m)) (A' B' : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V F m)), A ^ m = 1 → ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines E F b f hc hz m A A' → ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines E F b f hc hz m B B' → ArithmeticThetaSchemeThetaNaturalityR0262.InvariantComponents E F b f hc hz m A B A' B' := by
  intro k _ _ S σ E T F b f hc hz m hm A B A' B' hA hAA hBB
  let P := Scheme.Modules.pullback b
  let p := pushforwardMap E F b f hc hz m
  let _ : IsIso p := (scheme_pushforward_intertwining k S σ E T F b f hc hz m hm).1
  obtain ⟨e₀, he₀⟩ := scheme_fixed_line_base_change k S σ (V E m) m hm A hA T b
  have hs : (P.map A - 𝟙 (P.obj (V E m))) ≫ p = p ≫ (A' - 1) := by
    have hright := Preadditive.comp_sub p (show V F m ⟶ V F m from A') (𝟙 _)
    erw [hright]
    rw [Preadditive.sub_comp, Category.id_comp, Category.comp_id]
    exact congrArg (fun z => z - p) hAA
  let e₁ : fixed (P.map A) ≅ fixed A' :=
    kernel.mapIso (P.map A - 𝟙 (P.obj (V E m))) (A' - 1) (asIso p) (asIso p) hs
  let e := e₀ ≪≫ e₁
  have he : e.hom ≫ fixedι A' = P.map (fixedι A) ≫ p := by
    change e₀.hom ≫ e₁.hom ≫ fixedι A' = _
    have he₁ : e₁.hom ≫ fixedι A' = fixedι (P.map A) ≫ p :=
      kernel.lift_ι _ _ _
    rw [he₁, ← Category.assoc, he₀]
  have hp (n : ℕ) : P.map (B ^ n) ≫ p = p ≫ (B' ^ n) := by
    have hpow : P.map (B ^ n) = ((P.mapEnd (V E m) B) ^ n) :=
      (P.mapEnd (V E m)).map_pow B n
    rw [hpow]
    exact InvariantComponentNaturality.powers (P.map B) B' p hBB n
  have ho (i : Fin m) : e.hom ≫ fixedι A' ≫ (B' ^ i.val) =
      P.map (fixedι A ≫ (B ^ i.val)) ≫ p := by
    rw [← Category.assoc, he, Category.assoc, ← hp, P.map_comp, Category.assoc]
  refine ⟨e, ⟨he, ho, ?_⟩, ?_⟩
  · intro i
    change P.map (fixedι A ≫ (B ^ i.val) ≫ evaluation E m) ≫
      (fiberComparison E F b f hc hz m).hom =
      e.hom ≫ fixedι A' ≫ (B' ^ i.val) ≫ evaluation F m
    simp only [P.map_comp, Category.assoc]
    rw [scheme_evaluation_naturality k S σ E T F b f hc hz m]
    have hi := congrArg (fun z => z ≫ evaluation F m) (ho i)
    simpa only [P.map_comp, Category.assoc] using hi.symm
  · intro d hd
    apply Iso.ext
    apply (cancel_mono (fixedι A')).mp
    exact hd.1.trans he.symm

#print axioms scheme_invariant_component_naturality
end ArithmeticThetaSchemeThetaNaturalityR0262
