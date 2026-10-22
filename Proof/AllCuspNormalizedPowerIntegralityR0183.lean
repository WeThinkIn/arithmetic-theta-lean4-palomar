module

public import TateTorsionNormalizedIntegralityR0183
public import RelativeMultiplicationHodgeWeightR0172
import Lean

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
noncomputable section

open Lean Meta Elab Tactic in
elab "split_eval_exact " term:term : tactic => withMainContext do
  let h ← elabTerm term none
  let ht ← whnf (← inferType h)
  let goal ← whnf (← getMainTarget)
  unless ht.isAppOfArity `Eq 3 && goal.isAppOfArity `Eq 3 do
    throwError "Expected equality proofs"
  let aa := ht.getAppArgs
  let bb := goal.getAppArgs
  let lhs := aa[1]!
  let rhs := aa[2]!
  let wanted := bb[1]!
  unless lhs.isApp && wanted.isApp do throwError "Expected applied left sides"
  let f := lhs.appFn!
  let g := wanted.appFn!
  let x := lhs.appArg!
  let y := wanted.appArg!
  let hf ← mkEqRefl f
  let hx ← mkEqRefl x
  let same ← mkAppOptM `congr #[none, none, some f, some g, some x, some y, some hf, some hx]
  let back ← mkEqSymm same
  let hr ← mkEqRefl rhs
  let tail ← mkAppOptM `Eq.trans #[some aa[0]!, some lhs, some rhs, some bb[2]!, some h, some hr]
  let proof ← mkAppOptM `Eq.trans #[some bb[0]!, some wanted, some lhs, some bb[2]!, some back, some tail]
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "Unresolved congruence parameters"
  (← getMainGoal).assign proof
  replaceMainGoal []

namespace ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality

open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182

/-- Changing the differential factor from the globally prescribed degree to
the toric degree changes the coefficient by their ratio to the Hodge weight.
This scalar calculation does not assume those degrees are equal. -/
lemma differential_scalar {K : Type} [Field K] (w e : ℕ)
    (μ c v Δ : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0) :
    (μ⁻¹)^w * (((μ*c)^w*v*Δ^e)/Δ^e) = c^w*v := by
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hΔ), mul_pow]
  calc
    (μ⁻¹)^w * (μ^w*c^w*v) = ((μ⁻¹)^w*μ^w)*(c^w*v) := by ring
    _ = c^w*v := by rw [← mul_pow, inv_mul_cancel₀ hμ, one_pow, one_mul]

/-- A nonzero constant differential factor preserves the full integral series,
including the case where its valuation is zero. -/
lemma integral_constant_factor (k : Type) [Field k] (c : k) (hc : c ≠ 0)
    (w : ℕ) (v : LaurentSeries k)
    (hv : ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = v) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = (HahnSeries.C c)^w*v := by
  obtain ⟨f, hf, hfv⟩ := hv
  refine ⟨PowerSeries.C c ^ w * f,
    mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr hc)) hf, ?_⟩
  change HahnSeries.ofPowerSeries ℤ k _ = _
  rw [map_mul, map_pow, HahnSeries.ofPowerSeries_C]
  exact congrArg (fun x => (HahnSeries.C c)^w*x) hfv

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
/-- Exact normalization through a given Cartesian quotient comparison. The
global normalization constant `c` and the actual differential factor `μ`
are kept separate, as required at an arbitrary cusp. -/
lemma test_formula_differential_factor {S : Type} [CommRing S]
    (E T : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (f : Pointed S E T)
    (K : Type) [Field K] (W Wt : WeierstrassCurve K)
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (Gt : ArithmeticThetaRelativeKatoR0169.Law K Wt)
    (Cs : ArithmeticThetaOpenHodgeR0180.Test S E K W G)
    (Ct : ArithmeticThetaOpenHodgeR0180.Test S T K Wt Gt)
    (hscalar : Ct.scalar = Cs.scalar)
    (ψ : Curve K W ⟶ Curve K Wt) (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) (hψmap : Cs.map ≫ f.map = ψ ≫ Ct.map)
    (e w : ℕ) (hw : 24*e = w) (d : Γ(power T 24,⊤)) (F : Γ(power E w,⊤))
    (r : Γ(Base S,⊤))
    (hF : ∀ (U : (Base S).Opens) (η : Γ(hodge T,U)) (a : Γ(Base S,U)),
      IsFrame (hodge T) U η →
      res (power T 24) le_top d = a • tensorPowerSection (Base S) (hodge T) 24 U η →
      res (power E w) le_top F =
        ((Base S).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) •
          tensorPowerSection (Base S) (hodge E) w U ((familyHodgeMap f).app U η))
    (η : Γ(Hodge K Wt,⊤)) (ω : Γ(Hodge K W,⊤)) (hη : IsFrame (Hodge K Wt) ⊤ η)
    (μ c Δ v : K) (hμ : μ ≠ 0) (hΔ : Δ ≠ 0)
    (hr : (baseMap S K Cs.scalar).appLE ⊤ ⊤ (by simp) r = scalar K (c^w*v))
    (hd : pullSection Ct 24 d =
      scalar K Δ • tensorPowerSection (Base K) (Hodge K Wt) 24 ⊤ η)
    (hweight : (PeriodDifferential.pointMap (structureMap K W) (structureMap K Wt)
      ψ hψ (origin K W) (origin K Wt) hψo).app ⊤ η = scalar K μ • ω) :
    pullSection Cs w F =
      scalar K ((μ*c)^w*v*Δ^e) • tensorPowerSection (Base K) (Hodge K W) w ⊤ ω := by
  apply NormalizedSection.test_formula_tests E T f K W Wt G Gt Cs Ct hscalar
    ψ hψ hψo hψmap e w hw d F r hF η ω hη μ Δ
    ((μ*c)^w*v*Δ^e) (((μ*c)^w*v*Δ^e)/Δ^e) hμ hΔ rfl
  · rw [differential_scalar w e μ c v Δ hμ hΔ]
    exact hr
  · exact hd
  · exact hweight

#print axioms integral_constant_factor
#print axioms test_formula_differential_factor

/-- The specified target point stays nonzero N-torsion on every base change.
This uses the actual cyclic kernel of the given quotient, including nonprimitive
nonzero coordinate pairs. -/
lemma open_target_point (k : Type) [Field k] [CharZero k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hmN : m ∣ N)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N))
    (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) (A : OpenPower k m N D a b) :
    let p := liftPoint k (level N) D.atlas m N a.val b.val ≫ A.quotient.arrow.map
    p ≫ A.quotient.target.projection = 𝟙 _ ∧
    p ≫ A.quotient.target.law.schemeNsmul N = zero A.quotient.target ∧
    Disjoint (Set.range p) (Set.range (zero A.quotient.target)) := by
  have hL : 0 < level N := by dsimp [level]; positivity
  have hdiv : m*N ∣ level N := by
    obtain ⟨d, hd⟩ := hmN
    refine ⟨24*d, ?_⟩
    dsimp [level]
    rw [hd]
    ring
  have hmL : m ∣ level N := dvd_trans (dvd_mul_right m N) hdiv
  let E := D.atlas.descent.family
  obtain ⟨P, hP⟩ := GlobalLevelCyclicQuotientR0180.cyclic_of_level E hL
    D.atlas.marking m hm hmL
  have hl := OpenLevelNormalizedHodgePowerR0180.level_lift_conditions E hL
    D.atlas.marking m N hm hN hdiv a b hab
  have hp : liftPoint k (level N) D.atlas m N a.val b.val ≫ E.projection = 𝟙 _ :=
    (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (level N/(m*N)*b.val) D.atlas.marking.x)
      (E.law.nsmul (𝟙 _) (level N/N*a.val) D.atlas.marking.y)).property
  have hP' : P.point = kernelPoint k (level N) D.atlas m := hP
  have h := OpenLevelNormalizedHodgePowerR0180.quotient_lift E hm P
    (kernelPoint k (level N) D.atlas m) hP' A.quotient N
    (liftPoint k (level N) D.atlas m N a.val b.val) hp
    (by simpa only [hP', kernelPoint, liftPoint] using hl.1)
    (by simpa only [hP', kernelPoint, liftPoint] using hl.2)
  refine ⟨?_, h⟩
  rw [Category.assoc, A.quotient.arrow.over_eq]
  exact hp

/-- The accepted arbitrary-torsion theorem applies to the actual Cartesian
transport of a family point and its globally chosen Kato value. -/
lemma test_value_integral (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (r N : ℕ) (hr : 3 ≤ r) (heven : Even r) (hN : 0 < N) (heN : Even N)
    {S : Type} [CommRing S] (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S)
    (P : Base S ⟶ E.curve) (hP : P ≫ E.projection = 𝟙 _)
    (hPN : P ≫ E.law.schemeNsmul N = zero E)
    (hne : Disjoint (Set.range P) (Set.range (zero E)))
    (v : S) (hv : IsKatoValue E (1+12*N) P v)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (C : ArithmeticThetaOpenHodgeR0180.Test S E (LaurentSeries k) (TateCurve k r) G) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        C.scalar v * ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ dExponent N := by
  letI := TateFullLevelMarking.elliptic k r hr heven
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have geom := relative_curve_geometry (LaurentSeries k) (TateCurve k r)
  letI := geom.1
  letI := geom.2.1
  letI := geom.2.2.2.1
  letI := geom.2.2.2.2.1
  letI := geom.2.2.2.2.2.1
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    rw [show 12*N = (2*N)*6 by omega]
    exact (Nat.coprime_add_mul_right_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  obtain ⟨g, hg⟩ := GlobalFamilyTorsionValueR0180.normalized_exists
    (LaurentSeries k) (TateCurve k r) G hG (1+12*N) (by omega) hc6
  let p := GlobalFamilyTorsionValueR0180.testPoint C P hP
  have hp := GlobalFamilyTorsionValueR0180.testPoint_over C P hP
  have hpt := GlobalFamilyTorsionValueR0180.testPoint_torsion C P hP N hPN
  have hpn := GlobalFamilyTorsionValueR0180.testPoint_ne_zero C P hP hne
  have hvp := hv.2 (LaurentSeries k) (TateCurve k r) G hG C p hp
    (GlobalFamilyTorsionValueR0180.testPoint_map C P hP) g hg
  exact tate_torsion_normalized_integrality k r N hr heven hN heN G hG
    p hp hpt hpn g (C.scalar v) hg hvp

#print axioms open_target_point
#print axioms test_value_integral

/-- Every actual Tate comparison of the quotient transports the specified
point and its value to a nonzero integral target coefficient. No canonical
marking or exact-order assumption is used. -/
lemma open_target_integral (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (heN : Even N) (hmN : m ∣ N)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N))
    (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) (A : OpenPower k m N D a b)
    (r : ℕ) (hr : 3 ≤ r) (heven : Even r)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (C : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring A.quotient.target
      (LaurentSeries k) (TateCurve k r) G) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        C.scalar A.value * ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ^ dExponent N := by
  obtain ⟨hp, hpt, hpn⟩ := open_target_point k m N hm hN hmN D a b hab A
  exact test_value_integral k r N hr heven hN heN A.quotient.target
    (liftPoint k (level N) D.atlas m N a.val b.val ≫ A.quotient.arrow.map)
    hp hpt hpn A.value A.value_spec G hG C

/-- A typed presentation of the same pointed differential map. Keeping both
Weierstrass equations as parameters avoids unfolding their cubic coefficients
when the map is specialized. -/
def cubicHodgeMap {K : Type} [Field K] (W Wt : WeierstrassCurve K)
    (ψ : Curve K W ⟶ Curve K Wt)
    (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) : Hodge K Wt ⟶ Hodge K W :=
  PeriodDifferential.pointMap (K := K) (structureMap K W) (structureMap K Wt)
    ψ hψ (origin K W) (origin K Wt) hψo

lemma cubicHodgeMap_eq {K : Type} [Field K] (W Wt : WeierstrassCurve K)
    (ψ : Curve K W ⟶ Curve K Wt)
    (hψ : ψ ≫ structureMap K Wt = structureMap K W)
    (hψo : origin K W ≫ ψ = origin K Wt) :
    cubicHodgeMap W Wt ψ hψ hψo =
      PeriodDifferential.pointMap (K := K) (structureMap K W) (structureMap K Wt)
        ψ hψ (origin K W) (origin K Wt) hψo := rfl

section ConcreteComparison
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
/- The analytic consumer for an actual quotient comparison. Constructing the
comparison and proving its constant differential factor at an arbitrary cusp
remain separate geometric obligations; this conditional lemma is not the
all-cusp theorem. -/
variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
variable (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (heN : Even N) (hmN : m ∣ N)
variable (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N))
variable (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) (A : OpenPower k m N D a b)
variable (V : ArithmeticThetaBoundaryHodgeR0182.Test k (level N) D)
variable (r : ℕ) (hr : 3 ≤ r) (heven : Even r)
variable (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
variable (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
variable (C : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring A.quotient.target
      (LaurentSeries k) (TateCurve k r) G)
variable (hscalar : C.scalar = (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom)
variable (ψ : Curve (LaurentSeries k) (TateCurve k (level N)) ⟶
      Curve (LaurentSeries k) (TateCurve k r))
variable (hψ : ψ ≫ structureMap (LaurentSeries k) (TateCurve k r) =
      structureMap (LaurentSeries k) (TateCurve k (level N)))
variable (hψo : origin (LaurentSeries k) (TateCurve k (level N)) ≫ ψ =
      origin (LaurentSeries k) (TateCurve k r))
variable (hψmap : V.map ≫ A.quotient.arrow.map = ψ ≫ C.map)
variable (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ)
variable (μ : k) (hμ : μ ≠ 0)
variable (hweight : (cubicHodgeMap (TateCurve k (level N)) (TateCurve k r)
      ψ hψ hψo).app ⊤
      (hodgeGenerator k r δ) = scalar (LaurentSeries k) (HahnSeries.C μ) •
        hodgeGenerator k (level N) V.differential)

include hm hN heN hmN hab hr heven hG hscalar hψmap hδ hμ hweight in
lemma integral_of_tate_comparison : IntegralAtTest k m N A V := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  let Cs := OpenDiscriminantFullTateExpansionR0182.affineTest k (level N) V
  let coef : D.atlas.quotient.ring :=
    (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)^(weight N)*A.value
  have hcoef : (baseMap D.atlas.quotient.ring (LaurentSeries k) Cs.scalar).appLE
      ⊤ ⊤ (by simp) (scalar D.atlas.quotient.ring coef) =
      scalar (LaurentSeries k) (((m : LaurentSeries k)⁻¹)^(weight N)*(Cs.scalar A.value)) := by
    rw [NormalizedSection.base_scalar]
    congr 1
    dsimp only [coef]
    rw [map_mul, map_pow]
    congr 2
    exact (map_inv₀ (Cs.scalar.comp (algebraMap k D.atlas.quotient.ring)) (m : k)).trans
      (congrArg Inv.inv (by simp))
  have hD := TargetDiscriminant.exact k r hr heven A.quotient.target G hG C δ hδ
    A.discriminant A.intrinsic
  have hη := CubicComparison.generator_frame (K := LaurentSeries k)
    (structureMap (LaurentSeries k) (TateCurve k r))
    (origin (LaurentSeries k) (TateCurve k r)) δ
  obtain ⟨E, hE, hED⟩ := TateTorsionNormalizedIntegrality.discriminant_factor k r (by omega)
  have hΔ : ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ≠ 0 := by
    rw [hED]
    apply mul_ne_zero
    · exact pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)
    · exact pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))).mpr hE)
  have hμK : (HahnSeries.C μ : LaurentSeries k) ≠ 0 := by
    exact HahnSeries.single_ne_zero hμ
  have hf0 := test_formula_differential_factor (S := D.atlas.quotient.ring)
    D.atlas.descent.family A.quotient.target A.quotient.arrow
    (LaurentSeries k) (TateCurve k (level N)) (TateCurve k r)
    V.level.law G Cs C hscalar ψ hψ hψo hψmap
  have hf1 := hf0 (dExponent N) (weight N)
    (OpenLevelNormalizedHodgePowerR0180.exponents N heN).2
    A.discriminant A.section_ (scalar D.atlas.quotient.ring coef)
  have hf2 := hf1 A.normalized
  have hf3 := hf2 (hodgeGenerator k r δ) (hodgeGenerator k (level N) V.differential) hη
    (HahnSeries.C μ) (m : LaurentSeries k)⁻¹
    (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) (Cs.scalar A.value)
    hμK hΔ hcoef
  have hf := hf3 hD (by
    dsimp only [cubicHodgeMap] at hweight
    with_reducible exact hweight)
  have hv := open_target_integral k m N hm hN heN hmN D a b hab A r hr heven G hG C
  rw [hscalar] at hv
  have hmK : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  obtain ⟨f, hf0, hfv⟩ := integral_constant_factor k (μ*(m : k)⁻¹)
    (mul_ne_zero hμ (inv_ne_zero hmK)) (weight N) _ hv
  refine ⟨f, hf0, ?_⟩
  have hconst : (HahnSeries.C (μ*(m : k)⁻¹) : LaurentSeries k) =
      HahnSeries.C μ * (m : LaurentSeries k)⁻¹ := by
    rw [map_mul, map_inv₀, map_natCast]
  rw [hconst, ← mul_assoc] at hfv
  rw [hfv]
  exact (OpenDiscriminantFullTateExpansionR0182.pullAmbientPower_eq_pullSection
    k (level N) V (weight N) A.section_).trans hf

end ConcreteComparison

#print axioms open_target_integral
#print axioms integral_of_tate_comparison

/-- The actual change of disk parameter t ↦ a*t, with its inverse. -/
def powerRescale (k : Type) [Field k] (a : kˣ) : PowerSeries k ≃+* PowerSeries k where
  toFun := PowerSeries.rescale (a : k)
  invFun := PowerSeries.rescale (↑a⁻¹ : k)
  left_inv f := by rw [PowerSeries.rescale_rescale]; simp
  right_inv f := by rw [PowerSeries.rescale_rescale]; simp
  map_mul' := map_mul _
  map_add' := map_add _

/-- The same parameter change extended through the actual fraction-ring map. -/
def laurentRescale (k : Type) [Field k] (a : kˣ) : LaurentSeries k ≃+* LaurentSeries k :=
  IsFractionRing.ringEquivOfRingEquiv (powerRescale k a)

lemma laurentRescale_powerSeries (k : Type) [Field k] (a : kˣ) (f : PowerSeries k) :
    laurentRescale k a (algebraMap (PowerSeries k) (LaurentSeries k) f) =
      algebraMap (PowerSeries k) (LaurentSeries k) (powerRescale k a f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (powerRescale k a) f

/-- Integrality and nonvanishing descend through an invertible constant change
of parameter; the witness is a full power series on the original disk. -/
lemma rescale_integrality_iff (k : Type) [Field k] (a : kˣ) (v : LaurentSeries k) :
    (∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = laurentRescale k a v) ↔
    (∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = v) := by
  constructor
  · rintro ⟨f, hf, hfv⟩
    refine ⟨(powerRescale k a).symm f, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (powerRescale k a).symm.injective).mpr hf
    · apply (laurentRescale k a).injective
      rw [laurentRescale_powerSeries, RingEquiv.apply_symm_apply, hfv]
  · rintro ⟨f, hf, hfv⟩
    refine ⟨powerRescale k a f, (map_ne_zero_iff _ (powerRescale k a).injective).mpr hf, ?_⟩
    rw [← laurentRescale_powerSeries, hfv]

/-- Constant rescaling followed by positive ramification does not change the
integrality question on the original disk. -/
lemma rescaled_ramified_integrality_descent (k : Type) [Field k] [CharZero k]
    (a : kˣ) (d : ℕ) (hd : 0 < d) (ell : LaurentSeries k →+* LaurentSeries k)
    (hell : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k d hd ell)
    (v : LaurentSeries k)
    (hv : ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        laurentRescale k a (ell v)) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f = v := by
  exact TateTorsionNormalizedIntegrality.ramified_integrality_descent k d hd ell hell v
    ((rescale_integrality_iff k a (ell v)).mp hv)

#print axioms rescale_integrality_iff
#print axioms rescaled_ramified_integrality_descent

namespace ModelCoordinates
open NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146

/-- Extract literal marked coordinates for a rational torsion section of the
actual cubic through the specified pointed model isomorphism. The cubic point
and its marking are arbitrary. -/
lemma torsion_section_marked (k : Type) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : Tower k r hr)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (Gm : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hGm : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 Gm)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)
    (hO : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k r))
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) r)
    (p : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k r))
    (hp : p ≫ structureMap (LaurentSeries k) (TateCurve k r) = 𝟙 _)
    (ht : p ≫ G.schemeNsmul r = origin (LaurentSeries k) (TateCurve k r)) :
    ∃ ij : Fin r × Fin r,
      (MarkedPointAddition.point k h3 M hM ij.1 (ζ^ij.2.val)).val ≫ E.hom = p := by
  have hn := CubicComparison.model_nsmul_of_origin k h3 he M hM s hs Gm hGm
    (TateCurve k r) G hG E hE hO
  have hEinv : E.inv ≫ genericStructure k M = structureMap (LaurentSeries k) (TateCurve k r) := by
    rw [← hE, Iso.inv_hom_id_assoc]
  let x : SchemeHomOver (𝟙 _) (genericStructure k M) :=
    ⟨p ≫ E.inv, by rw [Category.assoc, hEinv, hp]⟩
  have hxe : x.val ≫ E.hom = p := by simp [x]
  have hx : Gm.nsmul (𝟙 _) r x = Gm.one (𝟙 _) := by
    apply Subtype.ext
    apply (cancel_mono E.hom).mp
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul
      Gm (𝟙 _) x r, Category.assoc, hn r, ← Category.assoc, hxe, ht, hGm.1]
    simpa only [pointOver, Category.id_comp] using hO.symm
  let ps := MarkedPointAddition.sectionAt k h3 M hM
  have hps := MarkedPointAddition.sectionAt_spec k h3 M hM
  have hbase : extensionBase k (LaurentSeries k) = 𝟙 _ := by simp [extensionBase]
  have hc := split_marked_torsion_completeness k r hr h3 T he M hM s hs
    Gm hGm ζ hζ ps hps (LaurentSeries k)
  rw [hbase] at hc
  obtain ⟨ij, hij, _⟩ := (hc x).mp hx
  refine ⟨ij, ?_⟩
  exact (congrArg (fun y : SchemeHomOver (𝟙 _) (genericStructure k M) => y.val ≫ E.hom)
    hij.symm).trans hxe

#print axioms torsion_section_marked
end ModelCoordinates

namespace ParameterAction
open ArithmeticThetaTateSeries

lemma rescale_constant (k : Type) [Field k] (c a : k) :
    PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

lemma rescale_constantCoeff (k : Type) [Field k] (c : k) (f : PowerSeries k) :
    PowerSeries.constantCoeff (PowerSeries.rescale c f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
  simp

lemma rescale_inv (k : Type) [Field k] (c : k) (f : PowerSeries k) :
    PowerSeries.rescale c f⁻¹ = (PowerSeries.rescale c f)⁻¹ := by
  by_cases hf : PowerSeries.constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr hf, map_zero,
      PowerSeries.inv_eq_zero.mpr ((rescale_constantCoeff k c f).trans hf)]
  · apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa only [rescale_constantCoeff] using hf)).mpr
    rw [← map_mul, PowerSeries.inv_mul_cancel f hf, map_one]

lemma rescale_monomial (k : Type) [Field k] (c a : k) (n : ℕ) :
    PowerSeries.rescale c (monomial a n) = monomial (a*c^n) n := by
  simp only [monomial, map_mul, map_pow, rescale_constant, PowerSeries.rescale_X]
  rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul]

lemma rescale_xTerm (k : Type) [Field k] (c : k) (f : PowerSeries k) :
    PowerSeries.rescale c (xTerm f) = xTerm (PowerSeries.rescale c f) := by
  simp only [xTerm, map_mul, map_pow, rescale_inv, map_sub, map_one]

lemma rescale_yTerm (k : Type) [Field k] (c : k) (f : PowerSeries k) :
    PowerSeries.rescale c (yTerm f) = yTerm (PowerSeries.rescale c f) := by
  simp only [yTerm, map_mul, map_pow, rescale_inv, map_sub, map_add, map_one]

lemma period_power (k : Type) [Field k] (α : kˣ) (d : ℕ) (hα : (α : k)^d = 1)
    (n : ℕ) : (α : k)^(d*n) = 1 := by rw [pow_mul, hα, one_pow]

lemma period_power_add (k : Type) [Field k] (α : kˣ) (d : ℕ) (hα : (α : k)^d = 1)
    (i n : ℕ) : (α : k)^(d*n+i) = (α : k)^i := by
  rw [pow_add, period_power k α d hα n, one_mul]

lemma period_power_sub (k : Type) [Field k] (α : kˣ) (d : ℕ) (hα : (α : k)^d = 1)
    (i n : ℕ) (hi : i ≤ d*n) : (α : k)^(d*n-i) = ((α : k)^i)⁻¹ := by
  apply (mul_right_cancel₀ (pow_ne_zero _ (Units.ne_zero α)))
  rw [← pow_add, Nat.sub_add_cancel hi, period_power k α d hα n, inv_mul_cancel₀]
  exact pow_ne_zero _ (Units.ne_zero α)

lemma rescale_partialX (k : Type) [Field k] (α : kˣ) (d i : ℕ)
    (hi : i < d) (hα : (α : k)^d = 1) (a : k) (n : ℕ) :
    PowerSeries.rescale (α : k) (partialX d i a n) =
      partialX d i (a*(α : k)^i) n := by
  have hle (j : ℕ) : i ≤ d*(j+1) := by nlinarith
  simp only [partialX, map_sub, map_add, map_mul, map_sum, map_ofNat,
    rescale_xTerm, rescale_monomial, rescale_inv, map_one, rescale_constant,
    period_power_add k α d hα, period_power_sub k α d hα _ _ (hle _),
    period_power k α d hα, mul_one, one_mul, mul_inv_rev]
  simp only [mul_comm a⁻¹]

lemma rescale_partialY (k : Type) [Field k] (α : kˣ) (d i : ℕ)
    (hi : i < d) (hα : (α : k)^d = 1) (a : k) (n : ℕ) :
    PowerSeries.rescale (α : k) (partialY d i a n) =
      partialY d i (a*(α : k)^i) n := by
  have hle (j : ℕ) : i ≤ d*(j+1) := by nlinarith
  simp only [partialY, map_sub, map_add, map_mul, map_sum,
    rescale_yTerm, rescale_monomial, rescale_constant,
    period_power_add k α d hα, period_power_sub k α d hα _ _ (hle _), mul_inv_rev]
  simp only [mul_comm a⁻¹]

/-- Full coordinate-series covariance, including all coefficients at valuation
zero. The automorphism fixes the period and changes the literal toric label. -/
lemma rescale_tateX (k : Type) [Field k] (α : kˣ) (d i : ℕ)
    (hi : i < d) (hα : (α : k)^d = 1) (a : k) :
    PowerSeries.rescale (α : k) (tateX d i a) = tateX d i (a*(α : k)^i) := by
  ext n
  simp only [PowerSeries.coeff_rescale, tateX, PowerSeries.coeff_mk]
  rw [← PowerSeries.coeff_rescale, rescale_partialX k α d i hi hα]

lemma rescale_tateY (k : Type) [Field k] (α : kˣ) (d i : ℕ)
    (hi : i < d) (hα : (α : k)^d = 1) (a : k) :
    PowerSeries.rescale (α : k) (tateY d i a) = tateY d i (a*(α : k)^i) := by
  ext n
  simp only [PowerSeries.coeff_rescale, tateY, PowerSeries.coeff_mk]
  rw [← PowerSeries.coeff_rescale, rescale_partialY k α d i hi hα]

lemma laurentRescale_tateX (k : Type) [Field k] (α : kˣ) (r i : ℕ)
    (hi : i < r) (hα : (α : k)^r = 1) (a : k) :
    laurentRescale k α (algebraMap (PowerSeries k) (LaurentSeries k) (tateX r i a)) =
      algebraMap (PowerSeries k) (LaurentSeries k) (tateX r i (a*(α : k)^i)) := by
  rw [laurentRescale_powerSeries]
  change algebraMap (PowerSeries k) (LaurentSeries k)
    (PowerSeries.rescale (α : k) (tateX r i a)) = _
  rw [rescale_tateX k α r i hi hα]

lemma laurentRescale_tateY (k : Type) [Field k] (α : kˣ) (r i : ℕ)
    (hi : i < r) (hα : (α : k)^r = 1) (a : k) :
    laurentRescale k α (algebraMap (PowerSeries k) (LaurentSeries k) (tateY r i a)) =
      algebraMap (PowerSeries k) (LaurentSeries k) (tateY r i (a*(α : k)^i)) := by
  rw [laurentRescale_powerSeries]
  change algebraMap (PowerSeries k) (LaurentSeries k)
    (PowerSeries.rescale (α : k) (tateY r i a)) = _
  rw [rescale_tateY k α r i hi hα]

open ArithmeticThetaCompactifiedDifferentialR0145 ArithmeticThetaCubicModelR0144

lemma rescale_root_zero (k : Type) [Field k] [CharZero k] (α : kˣ)
    (r : ℕ) (hr : 0 < r) (hα : (α : k)^r = 1) :
    laurentRescale k α (root k r 0) = root k r 0 := by
  simp only [root, rootSeries, Fin.val_zero, ite_true]
  rw [laurentRescale_tateX k α r 0 hr hα]
  simp

lemma rescale_root_one (k : Type) [Field k] [CharZero k] (α : kˣ)
    (r : ℕ) (hr : 0 < r) (hα : (α : k)^r = 1) :
    laurentRescale k α (root k r 1) =
      algebraMap (PowerSeries k) (LaurentSeries k) (tateX r (r/2) ((α : k)^(r/2))) := by
  simp only [root, rootSeries, Fin.val_one, show ¬(1 : ℕ) = 0 by omega, ite_false, ite_true]
  rw [laurentRescale_tateX k α r (r/2) (Nat.div_lt_self hr (by omega)) hα, one_mul]

lemma rescale_root_two (k : Type) [Field k] [CharZero k] (α : kˣ)
    (r : ℕ) (hr : 0 < r) (hα : (α : k)^r = 1) :
    laurentRescale k α (root k r 2) =
      algebraMap (PowerSeries k) (LaurentSeries k) (tateX r (r/2) (-((α : k)^(r/2)))) := by
  change laurentRescale k α (algebraMap (PowerSeries k) (LaurentSeries k)
    (tateX r (r/2) (-1))) = _
  rw [laurentRescale_tateX k α r (r/2) (Nat.div_lt_self hr (by omega)) hα, neg_one_mul]

/-- Fixing the Tate period fixes its actual cubic, even when the half-period
labels are exchanged. This is equality of the five Weierstrass coefficients. -/
lemma tateCurve_rescale (k : Type) [Field k] [CharZero k] (α : kˣ)
    (r : ℕ) (hr : 0 < r) (he : Even r) (hα : (α : k)^r = 1) :
    (TateCurve k r).map (laurentRescale k α).toRingHom = TateCurve k r := by
  have hhalf : ((α : k)^(r/2))^2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp he)]
    exact hα
  have hz := rescale_root_zero k α r hr hα
  have h₁ := rescale_root_one k α r hr hα
  have h₂ := rescale_root_two k α r hr hα
  rcases sq_eq_one_iff.mp hhalf with hpos | hneg
  · have h₁' : laurentRescale k α (root k r 1) = root k r 1 := by
      rw [hpos] at h₁
      exact h₁
    have h₂' : laurentRescale k α (root k r 2) = root k r 2 := by
      rw [hpos] at h₂
      exact h₂
    ext <;> simp only [TateCurve, curve, WeierstrassCurve.map,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_zero, map_neg, map_add, map_mul,
      hz, h₁', h₂']
  · have h₁' : laurentRescale k α (root k r 1) = root k r 2 := by
      rw [hneg] at h₁
      exact h₁
    have h₂' : laurentRescale k α (root k r 2) = root k r 1 := by
      rw [hneg, neg_neg] at h₂
      exact h₂
    ext <;> simp only [TateCurve, curve, WeierstrassCurve.map,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_zero, map_neg, map_add, map_mul,
      hz, h₁', h₂'] <;> ring

#print axioms tateCurve_rescale

#print axioms rescale_tateX
#print axioms rescale_tateY
end ParameterAction

namespace CoefficientMap
open CategoryTheory.Limits
open P2MW.S_WeierstrassProjModel_projModel_isPullback_baseChange_ring.WeierstrassProjModel

/-- The canonical projective morphism induced by the specified coefficient
homomorphism. Its graded map fixes each homogeneous coordinate. -/
def map {R S : Type} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (ι : R →+* S) :
    Curve S (W.map ι) ⟶ Curve R W := by
  letI : Algebra R S := ι.toAlgebra
  exact ProjBaseChange.projModelMap W S

lemma cartesian {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    IsPullback (map W ι) (structureMap S (W.map ι))
      (structureMap R W) (baseMap R S ι) := by
  letI : Algebra R S := ι.toAlgebra
  exact ProjBaseChange.isPullback W S (fun i => by
    fin_cases i <;> simp only [Fin.isValue]
    · exact kw_bc_awayIsPushout_Y_univ W S
    · exact kw_bc_awayIsPushout_Z_univ W S)

open HomogeneousLocalization WeierstrassCurve.DrinfeldGlobal

/-- The canonical coefficient map fixes projective coordinate ratios on every
standard chart. The square uses that exact scheme morphism. -/
lemma chart_coordinates_algebra {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (W : WeierstrassCurve R) (i : Fin 3) :
    ∃ χ : Away (WeierstrassProjModel.projModelGradingCR W.toProjective) (coord W.toProjective i) →+*
      Away (WeierstrassProjModel.projModelGradingCR (W.map (algebraMap R S)).toProjective)
        (coord (W.map (algebraMap R S)).toProjective i),
      Proj.awayι (WeierstrassProjModel.projModelGradingCR (W.map (algebraMap R S)).toProjective)
          (coord (W.map (algebraMap R S)).toProjective i) (coord_mem _ _) one_pos ≫ map W (algebraMap R S) =
        Spec.map (CommRingCat.ofHom χ) ≫
          Proj.awayι (WeierstrassProjModel.projModelGradingCR W.toProjective)
            (coord W.toProjective i) (coord_mem _ _) one_pos ∧
      ∀ j : Fin 3,
        χ (Away.mk _ (coord_mem W.toProjective i) 1 (coord W.toProjective j)
          (by simpa using coord_mem W.toProjective j)) =
        Away.mk _ (coord_mem (W.map (algebraMap R S)).toProjective i) 1 (coord (W.map (algebraMap R S)).toProjective j)
          (by simpa using coord_mem (W.map (algebraMap R S)).toProjective j) := by
  let f := ProjBaseChange.gradedRingHom W S
  have hf (j : Fin 3) : f (coord W.toProjective j) = coord (W.map (algebraMap R S)).toProjective j :=
    ProjBaseChange.gradedRingHom_mk_X W S j
  have haux (g : WeierstrassProjModel.ProjModelRingCR (W.map (algebraMap R S)).toProjective)
      (hg : g ∈ WeierstrassProjModel.projModelGradingCR (W.map (algebraMap R S)).toProjective 1)
      (heq : f (coord W.toProjective i) = g) :
      ∃ χ : Away (WeierstrassProjModel.projModelGradingCR W.toProjective)
        (coord W.toProjective i) →+*
        Away (WeierstrassProjModel.projModelGradingCR (W.map (algebraMap R S)).toProjective) g,
        Proj.awayι (WeierstrassProjModel.projModelGradingCR (W.map (algebraMap R S)).toProjective)
            g hg one_pos ≫ map W (algebraMap R S) =
          Spec.map (CommRingCat.ofHom χ) ≫
            Proj.awayι (WeierstrassProjModel.projModelGradingCR W.toProjective)
              (coord W.toProjective i) (coord_mem _ _) one_pos ∧
        ∀ j : Fin 3,
          χ (Away.mk _ (coord_mem W.toProjective i) 1 (coord W.toProjective j)
            (by simpa using coord_mem W.toProjective j)) =
          Away.mk _ hg 1 (coord (W.map (algebraMap R S)).toProjective j)
            (by simpa using coord_mem (W.map (algebraMap R S)).toProjective j) := by
    subst g
    refine ⟨Away.map f (coord W.toProjective i), ?_, ?_⟩
    · exact Proj.awayι_comp_map f (ProjBaseChange.irrelevant_le W S) one_pos
        (coord W.toProjective i) (coord_mem _ _)
    · intro j
      simpa only [hf] using (Away.map_mk f (coord W.toProjective i) (coord_mem _ _) 1
        (coord W.toProjective j) (by simpa using coord_mem W.toProjective j))
  exact haux _ (coord_mem _ _) (hf i)

lemma affine_coordinates {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    ∃ χ : ZChartRing W.toProjective →+* ZChartRing (W.map ι).toProjective,
      zChartι (W.map ι).toProjective ≫ map W ι =
        Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective ∧
      χ (xOverZ W.toProjective) = xOverZ (W.map ι).toProjective ∧
      χ (yOverZ W.toProjective) = yOverZ (W.map ι).toProjective := by
  letI : Algebra R S := ι.toAlgebra
  obtain ⟨χ, hχ, hc⟩ := chart_coordinates_algebra (S := S) W 2
  exact ⟨χ, hχ, hc 0, hc 1⟩

open WeierstrassProjModel

private def chartEval {B T : Type} [CommRing B] [CommRing T]
    {σ : Type*} [SetLike σ B] [AddSubgroupClass σ B]
    (ℬ : ℕ → σ) [GradedRing ℬ] (e : B →+* T) (x : B) (hx : IsUnit (e x)) :
    Away ℬ x →+* T :=
  (IsLocalization.Away.lift x hx).comp (algebraMap (Away ℬ x) (Localization.Away x))

private lemma chartEval_mk {B T : Type} [CommRing B] [CommRing T]
    {σ : Type*} [SetLike σ B] [AddSubgroupClass σ B]
    (ℬ : ℕ → σ) [GradedRing ℬ] (e : B →+* T)
    {x : B} {d : ℕ} (hx : x ∈ ℬ d) (he : e x = 1)
    (n : ℕ) (a : B) (ha : a ∈ ℬ (n • d)) :
    chartEval ℬ e x (he ▸ isUnit_one) (Away.mk ℬ hx n a ha) = e a := by
  simp only [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  simpa using Localization.awayLift_mk e x a 1 (by simpa using he) n

lemma origin_eval_naturality {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (W : WeierstrassCurve R) :
    (kwYEvalRingHom S (W.map (algebraMap R S))).comp
        (ProjBaseChange.gradedRingHom W S).toRingHom =
      (algebraMap R S).comp (kwYEvalRingHom R W) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change MvPolynomial.eval ![(0 : S), 1, 0]
      (MvPolynomial.map (algebraMap R S) (MvPolynomial.C r)) =
      algebraMap R S (MvPolynomial.eval ![(0 : R), 1, 0] (MvPolynomial.C r))
    simp
  · intro i
    change MvPolynomial.eval ![(0 : S), 1, 0]
      (MvPolynomial.map (algebraMap R S) (MvPolynomial.X i)) =
      algebraMap R S (MvPolynomial.eval ![(0 : R), 1, 0] (MvPolynomial.X i))
    fin_cases i <;> simp

/-- The specified coefficient morphism takes the actual zero section to the
zero section over the specified base map. -/
lemma origin_map_algebra {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (W : WeierstrassCurve R) :
    origin S (W.map (algebraMap R S)) ≫ map W (algebraMap R S) =
      baseMap R S (algebraMap R S) ≫ origin R W := by
  let f := ProjBaseChange.gradedRingHom W S
  have hf : f (coord W.toProjective 1) = coord (W.map (algebraMap R S)).toProjective 1 :=
    ProjBaseChange.gradedRingHom_mk_X W S 1
  have he : kwYEvalRingHom S (W.map (algebraMap R S)) (f (coord W.toProjective 1)) = 1 := by
    rw [hf]
    exact kwYEvalRingHom_mk_X1 S _
  have hchart :
      (chartEval (projModelGradingCR (W.map (algebraMap R S)).toProjective)
        (kwYEvalRingHom S (W.map (algebraMap R S))) (f (coord W.toProjective 1))
          (he ▸ isUnit_one)).comp (Away.map f (coord W.toProjective 1)) =
        (algebraMap R S).comp (kwYChartEval R W) := by
    apply RingHom.ext
    intro z
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (projModelGradingCR W.toProjective)
      (coord_mem W.toProjective 1) z
    change chartEval _ _ _ (he ▸ isUnit_one) (Away.map f _ (Away.mk _ _ n a ha)) =
      algebraMap R S (chartEval _ (kwYEvalRingHom R W) _
        ((kwYEvalRingHom_mk_X1 R W) ▸ isUnit_one) (Away.mk _ _ n a ha))
    rw [Away.map_mk, chartEval_mk _ _ _ he,
      chartEval_mk _ _ _ (kwYEvalRingHom_mk_X1 R W)]
    exact RingHom.congr_fun (origin_eval_naturality (S := S) W) a
  have haux (y : ProjModelRingCR (W.map (algebraMap R S)).toProjective)
      (hy : y ∈ projModelGradingCR (W.map (algebraMap R S)).toProjective 1)
      (hey : kwYEvalRingHom S (W.map (algebraMap R S)) y = 1)
      (hfy : f (coord W.toProjective 1) = y) :
      (Spec.map (CommRingCat.ofHom (chartEval _ (kwYEvalRingHom S (W.map (algebraMap R S)))
          y (hey ▸ isUnit_one))) ≫ Proj.awayι _ y hy one_pos) ≫ map W (algebraMap R S) =
        baseMap R S (algebraMap R S) ≫ origin R W := by
    subst y
    have hsq : Proj.awayι _ (f (coord W.toProjective 1)) hy one_pos ≫
        map W (algebraMap R S) =
        Spec.map (CommRingCat.ofHom (Away.map f (coord W.toProjective 1))) ≫
          Proj.awayι _ (coord W.toProjective 1) (coord_mem _ _) one_pos :=
      Proj.awayι_comp_map f (ProjBaseChange.irrelevant_le W S)
        one_pos (coord W.toProjective 1) (coord_mem _ _)
    rw [Category.assoc, hsq]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hchart,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  exact haux _ (coord_mem _ _) (kwYEvalRingHom_mk_X1 S _) hf

lemma origin_map {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (ι : R →+* S) :
    origin S (W.map ι) ≫ map W ι = baseMap R S ι ≫ origin R W := by
  letI : Algebra R S := ι.toAlgebra
  exact origin_map_algebra (S := S) W

/-- The coefficient map of a ring equivalence is itself an isomorphism. -/
lemma map_isIso {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (e : R ≃+* S) : IsIso (map W e.toRingHom) := by
  haveI : IsIso (baseMap R S e.toRingHom) :=
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_hom
  exact (cartesian W e.toRingHom).isIso_fst_of_isIso

lemma base_inverse {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    baseMap S R e.symm.toRingHom ≫ baseMap R S e.toRingHom = 𝟙 (Base R) :=
  (Scheme.Spec.mapIso e.toCommRingCatIso.op).inv_hom_id

/-- Transport an actual affine point through the canonical coefficient map.
The inverse base map is retained, and hence the coordinates are transformed
by the inverse ring equivalence. -/
lemma point_coordinates {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (e : R ≃+* S)
    (p : Base S ⟶ Curve S (W.map e.toRingHom)) (x y : S)
    (hp : ArithmeticThetaLegendreComparisonR0177.HasCoordinates S (W.map e.toRingHom) p x y) :
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates R W
      (baseMap S R e.symm.toRingHom ≫ p ≫ map W e.toRingHom) (e.symm x) (e.symm y) := by
  obtain ⟨hp, ψ, hψ, hψx, hψy⟩ := hp
  obtain ⟨χ, hχ, hχx, hχy⟩ := affine_coordinates W e.toRingHom
  refine ⟨?_, e.symm.toRingHom.comp (ψ.comp χ), ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, (cartesian W e.toRingHom).w,
      ← Category.assoc p, hp, Category.id_comp, base_inverse]
  · rw [hψ]
    change baseMap S R e.symm.toRingHom ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map e.toRingHom).toProjective) ≫
        map W e.toRingHom = _
    rw [Category.assoc, hχ]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      baseMap, ArithmeticThetaLegendreComparisonR0177.chartInclusion]
  · change e.symm (ψ (χ (xOverZ W.toProjective))) = e.symm x
    rw [hχx, hψx]
  · change e.symm (ψ (χ (yOverZ W.toProjective))) = e.symm y
    rw [hχy, hψy]

/-- Origin preservation identifies the transported group law with the given
elliptic law. This upgrades the specified Cartesian map itself to multiplication
compatibility; no alternative Cartesian morphism is selected. -/
lemma multiplication_of_cartesian {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (Ws : WeierstrassCurve S) [Ws.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws)
    (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs)
    (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsPullback b (structureMap S Ws) (structureMap R W) (baseMap R S ι))
    (ho : origin S Ws ≫ b = baseMap R S ι ≫ origin R W) :
    ∀ n, Gs.schemeNsmul n ≫ b = b ≫ G.schemeNsmul n := by
  obtain ⟨H, hm, hH⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι (structureMap R W) (structureMap S Ws) b hb G
  have hone : (Gs.one (𝟙 _)).val = (H.one (𝟙 _)).val := by
    apply hb.hom_ext
    · rw [hGs.1, Category.id_comp, ho, hH, Category.id_comp, hG.1]
      rfl
    · exact (Gs.one (𝟙 _)).property.trans (H.one (𝟙 _)).property.symm
  have hlaw : Gs = H :=
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext Gs H
      (fun t x y => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic Ws.toProjective Gs H hone t x y)
      (by
        intro T t
        apply Subtype.ext
        have h1 := congrArg Subtype.val (Gs.one_natural (𝟙 _) t t (Category.comp_id t))
        have h2 := congrArg Subtype.val (H.one_natural (𝟙 _) t t (Category.comp_id t))
        exact h1.symm.trans ((congrArg (fun z => t ≫ z) hone).trans h2))
  intro n
  rw [hlaw]
  exact ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
    ι (structureMap S Ws) b hb G H hm hH n

/-- A typed presentation of the same coefficient map after a checked equality
of Weierstrass equations. -/
def mapOfEq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (ι : R →+* S)
    (h : W.map ι = W') : Curve S W' ⟶ Curve R W := by
  subst W'
  exact map W ι

lemma mapOfEq_eq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (ι : R →+* S)
    (h : W.map ι = W') :
    mapOfEq W W' ι h = eqToHom (congrArg (Curve S) h.symm) ≫ map W ι := by
  subst W'
  simp [mapOfEq]

lemma cartesian_of_eq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (ι : R →+* S)
    (h : W.map ι = W') :
    IsPullback (mapOfEq W W' ι h) (structureMap S W') (structureMap R W) (baseMap R S ι) := by
  subst W'
  exact cartesian W ι

lemma origin_of_eq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (ι : R →+* S)
    (h : W.map ι = W') :
    origin S W' ≫ mapOfEq W W' ι h = baseMap R S ι ≫ origin R W := by
  subst W'
  exact origin_map W ι

lemma isIso_of_eq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (e : R ≃+* S)
    (h : W.map e.toRingHom = W') : IsIso (mapOfEq W W' e.toRingHom h) := by
  subst W'
  exact map_isIso W e

lemma coordinates_of_eq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (e : R ≃+* S)
    (h : W.map e.toRingHom = W') (p : Base S ⟶ Curve S W') (x y : S)
    (hp : ArithmeticThetaLegendreComparisonR0177.HasCoordinates S W' p x y) :
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates R W
      (baseMap S R e.symm.toRingHom ≫ p ≫ mapOfEq W W' e.toRingHom h)
      (e.symm x) (e.symm y) := by
  subst W'
  exact point_coordinates W e p x y hp

#print axioms map_isIso
#print axioms point_coordinates

#print axioms origin_map

#print axioms affine_coordinates

#print axioms cartesian
end CoefficientMap

namespace ParameterGeometry
open CategoryTheory.Limits ArithmeticThetaTateSeries

variable (k : Type) [Field k] [CharZero k] (α : kˣ) (r : ℕ)
  (hr : 0 < r) (heven : Even r) (hα : (α : k)^r = 1)

/-- The actual semilinear automorphism of the Tate cubic. It retains the
parameter automorphism on the base, even when its cubic coefficients are fixed. -/
def map : Curve (LaurentSeries k) (TateCurve k r) ⟶ Curve (LaurentSeries k) (TateCurve k r) :=
  CoefficientMap.mapOfEq (TateCurve k r) (TateCurve k r) (laurentRescale k α).toRingHom
    (ParameterAction.tateCurve_rescale k α r hr heven hα)

lemma cartesian : IsPullback (map k α r hr heven hα)
    (structureMap (LaurentSeries k) (TateCurve k r))
    (structureMap (LaurentSeries k) (TateCurve k r))
    (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).toRingHom) :=
  CoefficientMap.cartesian_of_eq _ _ _ _

lemma origin_map : origin (LaurentSeries k) (TateCurve k r) ≫ map k α r hr heven hα =
    baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).toRingHom ≫
      origin (LaurentSeries k) (TateCurve k r) :=
  CoefficientMap.origin_of_eq _ _ _ _

lemma map_isIso : IsIso (map k α r hr heven hα) :=
  CoefficientMap.isIso_of_eq _ _ _ _

lemma multiplication [(TateCurve k r).IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G) :
    ∀ n, G.schemeNsmul n ≫ map k α r hr heven hα =
      map k α r hr heven hα ≫ G.schemeNsmul n :=
  CoefficientMap.multiplication_of_cartesian _ _ G hG G hG _ _
    (cartesian k α r hr heven hα) (origin_map k α r hr heven hα)

lemma isBaseChange [(TateCurve k r).IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G) :
    ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange (LaurentSeries k) (TateCurve k r) G
      (LaurentSeries k) (TateCurve k r) G (laurentRescale k α).toRingHom (map k α r hr heven hα) :=
  ⟨cartesian k α r hr heven hα, origin_map k α r hr heven hα,
    multiplication k α r hr heven hα G hG⟩

#print axioms isBaseChange

include hα in
private lemma inverse_X (i : ℕ) (hi : i < r) (a : k) :
    (laurentRescale k α).symm
        (algebraMap (PowerSeries k) (LaurentSeries k) (tateX r i a)) =
      algebraMap (PowerSeries k) (LaurentSeries k) (tateX r i (a * ((α : k)^i)⁻¹)) := by
  apply (laurentRescale k α).injective
  rw [RingEquiv.apply_symm_apply, ParameterAction.laurentRescale_tateX k α r i hi hα]
  rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero i α.ne_zero), mul_one]

include hα in
private lemma inverse_Y (i : ℕ) (hi : i < r) (a : k) :
    (laurentRescale k α).symm
        (algebraMap (PowerSeries k) (LaurentSeries k) (tateY r i a)) =
      algebraMap (PowerSeries k) (LaurentSeries k) (tateY r i (a * ((α : k)^i)⁻¹)) := by
  apply (laurentRescale k α).injective
  rw [RingEquiv.apply_symm_apply, ParameterAction.laurentRescale_tateY k α r i hi hα]
  rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero i α.ne_zero), mul_one]

/-- The same semilinear morphism acts on the full coordinates of every affine
marked point. Both the point and its base map occur in the asserted equation. -/
lemma marked_coordinates (i : Fin r) (a : k)
    (p : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k r))
    (hp : ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r) p
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX r i.val a))
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateY r i.val a))) :
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
      (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).symm.toRingHom ≫
        p ≫ map k α r hr heven hα)
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX r i.val (a * ((α : k)^i.val)⁻¹)))
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateY r i.val (a * ((α : k)^i.val)⁻¹))) := by
  have h := CoefficientMap.coordinates_of_eq (TateCurve k r) (TateCurve k r) (laurentRescale k α)
    (ParameterAction.tateCurve_rescale k α r hr heven hα) p _ _ hp
  rw [inverse_X k α r hα i.val i.isLt a, inverse_Y k α r hα i.val i.isLt a] at h
  exact h

include hr in
/-- A scalar in the component kernel is removed by a root-of-unity parameter
change that fixes the intermediate period. The root-of-unity coefficient is
retained in both defining equations. -/
lemma exists_component_rescaling [IsAlgClosed k] (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r)
    (ξ : kˣ) (hξ : (ξ : k)^d = 1) :
    ∃ β : kˣ, (β : k)^r = 1 ∧ (β : k)^(r/d) = (ξ : k) := by
  have hrd : 0 < r/d := Nat.div_pos (Nat.le_of_dvd hr hdiv) hd
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (ξ : k) hrd
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hrd.ne'] at hb
    exact ξ.ne_zero hb.symm
  refine ⟨Units.mk0 b hb0, ?_, hb⟩
  change b^r = 1
  rw [← Nat.div_mul_cancel hdiv, pow_mul, hb, hξ]

/-- The constructed semilinear map removes the residual scalar on each
component label, using the same parameter choice for the whole subgroup. -/
lemma component_coordinates (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r)
    (ξ : kˣ) (hroot : (α : k)^(r/d) = (ξ : k)) (j : Fin d)
    (p : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k r))
    (hp : ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r) p
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX r (r/d*j.val) ((ξ : k)^j.val)))
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateY r (r/d*j.val) ((ξ : k)^j.val)))) :
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
      (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k α).symm.toRingHom ≫
        p ≫ map k α r hr heven hα)
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateX r (r/d*j.val) 1))
      (algebraMap (PowerSeries k) (LaurentSeries k) (tateY r (r/d*j.val) 1)) := by
  have hrd : 0 < r/d := Nat.div_pos (Nat.le_of_dvd hr hdiv) hd
  have hij : r/d*j.val < r := by
    have h := Nat.mul_lt_mul_of_pos_left j.isLt hrd
    simpa only [Nat.div_mul_cancel hdiv] using h
  have h := marked_coordinates k α r hr heven hα ⟨r/d*j.val, hij⟩ ((ξ : k)^j.val) p hp
  have hlabel : (ξ : k)^j.val * ((α : k)^(r/d*j.val))⁻¹ = 1 := by
    rw [pow_mul, hroot, mul_inv_cancel₀ (pow_ne_zero j.val ξ.ne_zero)]
  simpa only [hlabel] using h

#print axioms exists_component_rescaling
#print axioms component_coordinates

#print axioms cartesian
#print axioms origin_map
#print axioms map_isIso
#print axioms marked_coordinates
end ParameterGeometry

namespace TwistedQuotient
open CategoryTheory.Limits

variable {R : Type} [CommRing R] (Ws Wt : WeierstrassCurve R)
  (e : R ≃+* R) (hs : Ws.map e.toRingHom = Ws)

/-- Base change of a quotient along a parameter automorphism fixing the
source equation. The target retains its transformed coefficients. -/
def arrow (f : Curve R Ws ⟶ Curve R Wt) : Curve R Ws ⟶ Curve R (Wt.map e.toRingHom) := by
  letI := CoefficientMap.map_isIso Wt e
  exact CoefficientMap.mapOfEq Ws Ws e.toRingHom hs ≫ f ≫ inv (CoefficientMap.map Wt e.toRingHom)

lemma square (f : Curve R Ws ⟶ Curve R Wt) :
    arrow Ws Wt e hs f ≫ CoefficientMap.map Wt e.toRingHom =
      CoefficientMap.mapOfEq Ws Ws e.toRingHom hs ≫ f := by
  letI := CoefficientMap.map_isIso Wt e
  simp [arrow]

lemma arrow_over (f : Curve R Ws ⟶ Curve R Wt)
    (hf : f ≫ structureMap R Wt = structureMap R Ws) :
    arrow Ws Wt e hs f ≫ structureMap R (Wt.map e.toRingHom) = structureMap R Ws := by
  haveI : IsIso (baseMap R R e.toRingHom) :=
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_hom
  apply (cancel_mono (baseMap R R e.toRingHom)).mp
  rw [Category.assoc, ← (CoefficientMap.cartesian Wt e.toRingHom).w,
    ← Category.assoc, square, Category.assoc, hf]
  exact (CoefficientMap.cartesian_of_eq Ws Ws e.toRingHom hs).w

lemma origin_arrow (f : Curve R Ws ⟶ Curve R Wt)
    (ho : origin R Ws ≫ f = origin R Wt) :
    origin R Ws ≫ arrow Ws Wt e hs f = origin R (Wt.map e.toRingHom) := by
  letI := CoefficientMap.map_isIso Wt e
  apply (cancel_mono (CoefficientMap.map Wt e.toRingHom)).mp
  rw [Category.assoc, square, ← Category.assoc, CoefficientMap.origin_of_eq,
    Category.assoc, ho, CoefficientMap.origin_map]

/-- The twisted arrow is the actual Cartesian base change of the original
arrow, not merely a map with matching rational point values. -/
lemma cartesian (f : Curve R Ws ⟶ Curve R Wt) :
    IsPullback (CoefficientMap.mapOfEq Ws Ws e.toRingHom hs)
      (arrow Ws Wt e hs f) f (CoefficientMap.map Wt e.toRingHom) := by
  letI := CoefficientMap.map_isIso Wt e
  letI := CoefficientMap.isIso_of_eq Ws Ws e hs
  exact IsPullback.of_horiz_isIso ⟨(square Ws Wt e hs f).symm⟩

lemma finite (f : Curve R Ws ⟶ Curve R Wt) [IsFinite f] :
    IsFinite (arrow Ws Wt e hs f) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (cartesian Ws Wt e hs f) inferInstance

lemma etale (f : Curve R Ws ⟶ Curve R Wt) [Etale f] :
    Etale (arrow Ws Wt e hs f) :=
  MorphismProperty.of_isPullback (P := @Etale) (cartesian Ws Wt e hs f) inferInstance

lemma surjective (f : Curve R Ws ⟶ Curve R Wt) [Surjective f] :
    Surjective (arrow Ws Wt e hs f) :=
  MorphismProperty.of_isPullback (P := @Surjective) (cartesian Ws Wt e hs f) inferInstance

lemma finrank (f : Curve R Ws ⟶ Curve R Wt) [Flat f] [IsFinite f]
    (y : Curve R (Wt.map e.toRingHom)) :
    (arrow Ws Wt e hs f).finrank y = f.finrank (CoefficientMap.map Wt e.toRingHom y) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian Ws Wt e hs f) y

#print axioms finrank

/-- Kernel membership is tested on the very point transported by the same
semilinear source map, with the inverse base map displayed. -/
lemma kernel_iff (f : Curve R Ws ⟶ Curve R Wt) (p : Base R ⟶ Curve R Ws) :
    p ≫ arrow Ws Wt e hs f = origin R (Wt.map e.toRingHom) ↔
    (baseMap R R e.symm.toRingHom ≫ p ≫ CoefficientMap.mapOfEq Ws Ws e.toRingHom hs) ≫ f =
      origin R Wt := by
  letI := CoefficientMap.map_isIso Wt e
  haveI : IsIso (baseMap R R e.symm.toRingHom) :=
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_inv
  constructor
  · intro h
    rw [Category.assoc, Category.assoc, ← square, ← Category.assoc p, h,
      CoefficientMap.origin_map, ← Category.assoc, CoefficientMap.base_inverse,
      Category.id_comp]
  · intro h
    apply (cancel_mono (CoefficientMap.map Wt e.toRingHom)).mp
    apply (cancel_epi (baseMap R R e.symm.toRingHom)).mp
    rw [Category.assoc p, square, CoefficientMap.origin_map,
      ← Category.assoc (baseMap R R e.symm.toRingHom) (baseMap R R e.toRingHom),
      CoefficientMap.base_inverse, Category.id_comp]
    simpa only [Category.assoc] using h

lemma multiplication [Ws.IsElliptic] [(Wt.map e.toRingHom).IsElliptic]
    (Gs : ArithmeticThetaRelativeKatoR0169.Law R Ws)
    (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R Ws Gs)
    (Gt : ArithmeticThetaRelativeKatoR0169.Law R Wt)
    (hGt : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R Wt Gt)
    (Gt' : ArithmeticThetaRelativeKatoR0169.Law R (Wt.map e.toRingHom))
    (hGt' : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R (Wt.map e.toRingHom) Gt')
    (f : Curve R Ws ⟶ Curve R Wt)
    (hf : ∀ n, Gs.schemeNsmul n ≫ f = f ≫ Gt.schemeNsmul n) :
    ∀ n, Gs.schemeNsmul n ≫ arrow Ws Wt e hs f =
      arrow Ws Wt e hs f ≫ Gt'.schemeNsmul n := by
  letI := CoefficientMap.map_isIso Wt e
  have hsource := CoefficientMap.multiplication_of_cartesian Ws Ws Gs hGs Gs hGs e.toRingHom
    (CoefficientMap.mapOfEq Ws Ws e.toRingHom hs)
    (CoefficientMap.cartesian_of_eq Ws Ws e.toRingHom hs)
    (CoefficientMap.origin_of_eq Ws Ws e.toRingHom hs)
  have htarget := CoefficientMap.multiplication_of_cartesian Wt (Wt.map e.toRingHom)
    Gt hGt Gt' hGt' e.toRingHom (CoefficientMap.map Wt e.toRingHom)
    (CoefficientMap.cartesian Wt e.toRingHom) (CoefficientMap.origin_map Wt e.toRingHom)
  intro n
  apply (cancel_mono (CoefficientMap.map Wt e.toRingHom)).mp
  rw [Category.assoc, square, ← Category.assoc, hsource n, Category.assoc, hf n,
    Category.assoc, htarget n, ← Category.assoc (arrow Ws Wt e hs f), square, Category.assoc]

#print axioms multiplication

#print axioms cartesian
#print axioms arrow_over
#print axioms origin_arrow
#print axioms kernel_iff
end TwistedQuotient

namespace KernelArithmetic

/-- For the actual component/scalar labels of a cyclic generator, the
component order divides its total order. -/
lemma component_dvd {C : Type*} [Group C] {k : Type*} [Field k]
    (x : C) (a : kˣ) (m : ℕ) (horder : orderOf (x, a) = m) : orderOf x ∣ m := by
  rw [← horder]
  exact orderOf_fst_dvd_orderOf (x := (x, a))

/-- The toric intersection is generated by the d-th power, and that scalar
has exact order m/d. No primitive assumption on the component label occurs. -/
lemma toric_order {C : Type*} [Group C] {k : Type*} [Field k]
    (x : C) (a : kˣ) (m : ℕ) (hm : 0 < m) (horder : orderOf (x, a) = m) :
    IsPrimitiveRoot ((a : k)^orderOf x) (m/orderOf x) := by
  have hdvd := component_dvd x a m horder
  have hd : orderOf x ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hdvd
    omega
  have hpow := orderOf_pow_of_dvd (x := (x, a)) hd
    (show orderOf x ∣ orderOf (x, a) by rw [horder]; exact hdvd)
  have ha : orderOf (a ^ orderOf x) = m / orderOf x := by
    simpa only [Prod.pow_mk, pow_orderOf_eq_one, Prod.orderOf, orderOf_one,
      Nat.lcm_one_left, horder] using hpow
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [← Units.val_pow_eq_pow_val, orderOf_units]
  exact ha

/-- After quotienting the toric part, the remaining scalar is d-torsion.
This is the scalar that must be retained in the component quotient. -/
lemma residual_scalar {C : Type*} [Group C] {k : Type*} [Field k]
    (x : C) (a : kˣ) (m : ℕ) (horder : orderOf (x, a) = m) :
    ((a : k)^(m/orderOf x))^orderOf x = 1 := by
  have hdvd := component_dvd x a m horder
  have ha : a^m = 1 := by
    have h := congrArg Prod.snd (pow_orderOf_eq_one (x, a))
    simpa only [Prod.pow_mk, Prod.snd_one, horder] using h
  rw [← pow_mul, Nat.div_mul_cancel hdvd]
  exact congrArg Units.val ha

/-- The toric powers are precisely the multiples of the component order. -/
lemma toric_powers_iff {C : Type*} [Group C] {k : Type*} [Field k]
    (x : C) (a : kˣ) (n : ℕ) :
    (x, a)^n = (1, a^n) ↔ orderOf x ∣ n := by
  simp only [Prod.pow_mk, Prod.mk.injEq, and_true]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-- Exact order follows from the actual disjoint cyclic sections, using the
point group of the specified elliptic law. -/
lemma cyclic_section_order (F : Type) [Field F] (W : WeierstrassCurve F)
    (G : ArithmeticThetaRelativeKatoR0169.Law F W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw F W G)
    (m : ℕ) (hm : 0 < m)
    (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection F W G m) :
    letI := G.pointGroup (𝟙 (Base F))
    orderOf (⟨P.point, P.over_eq⟩ : NeronModelInfra.SchemeHomOver (𝟙 (Base F)) (structureMap F W)) = m := by
  letI := G.pointGroup (𝟙 (Base F))
  let p : NeronModelInfra.SchemeHomOver (𝟙 (Base F)) (structureMap F W) := ⟨P.point, P.over_eq⟩
  have hp (n : ℕ) : (p^n).val = P.point ≫ G.schemeNsmul n := by
    have hn : G.nsmul (𝟙 (Base F)) n p = p^n := by
      induction n with
      | zero => rfl
      | succ n ih => rw [G.nsmul_succ, ih]; exact (pow_succ p n).symm
    rw [← hn]
    exact (ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul
      G (𝟙 (Base F)) p n).symm
  have hone : (1 : NeronModelInfra.SchemeHomOver (𝟙 (Base F)) (structureMap F W)).val = origin F W := by
    change (G.one (𝟙 _)).val = _
    simpa only [Category.id_comp] using hG.1 (𝟙 (Base F))
  apply (orderOf_eq_iff hm).mpr
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [hp m, hone, P.killed]
  · intro n hnm hn hpow
    have heq : P.point ≫ G.schemeNsmul n = P.point ≫ G.schemeNsmul 0 := by
      rw [← hp n, ← hp 0, hpow, pow_zero]
    have hd := P.disjoint ⟨n, hnm⟩ ⟨0, hm⟩ (by intro h; exact hn.ne' (congrArg Fin.val h))
    let z := IsLocalRing.closedPoint F
    exact Set.disjoint_iff_forall_ne.mp hd ⟨z, rfl⟩ ⟨z, rfl⟩
      (congrArg (fun f : Base F ⟶ Curve F W => f z) heq)

lemma cyclic_torsion_iff (F : Type) [Field F] (W : WeierstrassCurve F)
    (G : ArithmeticThetaRelativeKatoR0169.Law F W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw F W G)
    (m : ℕ) (hm : 0 < m)
    (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection F W G m) (n : ℕ) :
    P.point ≫ G.schemeNsmul n = origin F W ↔ m ∣ n := by
  letI := G.pointGroup (𝟙 (Base F))
  let p : NeronModelInfra.SchemeHomOver (𝟙 (Base F)) (structureMap F W) := ⟨P.point, P.over_eq⟩
  have hn : G.nsmul (𝟙 (Base F)) n p = p^n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih]; exact (pow_succ p n).symm
  have hpow : p^n = 1 ↔ P.point ≫ G.schemeNsmul n = origin F W := by
    rw [← hn, Subtype.ext_iff]
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul]
    change P.point ≫ G.schemeNsmul n = (G.one (𝟙 (Base F))).val ↔ _
    rw [hG.1, Category.id_comp]
  rw [← hpow, ← cyclic_section_order F W G hG m hm P]
  exact orderOf_dvd_iff_pow_eq_one.symm

#print axioms cyclic_torsion_iff

lemma label_power_eq_one {k : Type*} [Field k] (r : ℕ) (i : Fin r) (a : kˣ) (n : ℕ) :
    (Multiplicative.ofAdd (i.val : ZMod r), a)^n = 1 ↔ r ∣ n*i.val ∧ a^n = 1 := by
  change ((Multiplicative.ofAdd (i.val : ZMod r))^n, a^n) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  change (n • (i.val : ZMod r) = 0 ∧ a^n = 1) ↔ _
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]

lemma component_order (r : ℕ) (hr : 0 < r) (i : Fin r) :
    orderOf (Multiplicative.ofAdd (i.val : ZMod r)) = r / r.gcd i.val :=
  ZMod.addOrderOf_coe i.val hr.ne'

lemma label_order_of_torsion_iff {k : Type*} [Field k]
    (r m : ℕ) (i : Fin r) (a : kˣ)
    (h : ∀ n : ℕ, (r ∣ n*i.val ∧ a^n = 1) ↔ m ∣ n) :
    orderOf (Multiplicative.ofAdd (i.val : ZMod r), a) = m := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    exact (label_power_eq_one r i a m).mpr ((h m).mpr dvd_rfl)
  · apply (h _).mp
    exact (label_power_eq_one r i a _).mp (pow_orderOf_eq_one _)

#print axioms label_power_eq_one
#print axioms label_order_of_torsion_iff

#print axioms cyclic_section_order

/-- A component scalar of the necessary finite order can be removed without
changing the intermediate period, even when the component index is not its
minimal positive generator. This includes index zero. -/
lemma exists_label_rescaling (k : Type) [Field k] [IsAlgClosed k]
    (r i : ℕ) (hr : 0 < r) (a : kˣ) (ha : (a : k)^(r/r.gcd i) = 1) :
    ∃ β : kˣ, (β : k)^r = 1 ∧ (β : k)^i = (a : k) := by
  let g := r.gcd i
  let d := r/g
  let j := i/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left i hr
  have hcop : Nat.Coprime j d := (Nat.coprime_div_gcd_div_gcd hg).symm
  let n : ℕ := ((j : ZMod d)⁻¹).val
  have hnj : n*j ≡ 1 [MOD d] := by
    apply (ZMod.natCast_eq_natCast_iff (n*j) 1 d).mp
    simpa only [Nat.cast_mul, Nat.cast_one] using ZMod.val_inv_mul hcop
  have hai : ((a : k)^n)^j = (a : k) := by
    rw [← pow_mul]
    simpa only [pow_one] using pow_eq_pow_of_modEq hnj ha
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq ((a : k)^n) hg
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, zero_pow hg.ne'] at hb
    exact (pow_ne_zero n a.ne_zero) hb.symm
  refine ⟨Units.mk0 b hb0, ?_, ?_⟩
  · change b^r = 1
    have hrg : g*d = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r i)
    rw [← hrg, pow_mul, hb, pow_right_comm]
    change ((a : k)^d)^n = 1
    rw [ha, one_pow]
  · change b^i = (a : k)
    have hig : g*j = i := Nat.mul_div_cancel' (Nat.gcd_dvd_right r i)
    rw [← hig, pow_mul, hb]
    exact hai

/-- The exact cyclic labels determine the toric degree and a parameter change
that removes the residual scalar after the toric power map. -/
lemma mixed_rescaling (k : Type) [Field k] [IsAlgClosed k]
    (r m : ℕ) (hr : 0 < r) (hm : 0 < m) (i : Fin r) (a : kˣ)
    (horder : orderOf (Multiplicative.ofAdd (i.val : ZMod r), a) = m) :
    let d := r/r.gcd i.val
    let e := m/d
    0 < d ∧ 0 < e ∧ d ∣ m ∧ e*d = m ∧
      IsPrimitiveRoot ((a : k)^d) e ∧
      ∃ β : kˣ, (β : k)^(e*r) = 1 ∧ (β : k)^(e*i.val) = (a : k)^e := by
  dsimp only
  let x := Multiplicative.ofAdd (i.val : ZMod r)
  let d := r/r.gcd i.val
  let e := m/d
  have hx : orderOf x = d := component_order r hr i
  have hdvd : d ∣ m := by simpa only [hx] using component_dvd x a m horder
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left i.val hr) (Nat.gcd_pos_of_pos_left i.val hr)
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd hm hdvd) hd
  have htoric : IsPrimitiveRoot ((a : k)^d) e := by
    simpa only [hx] using toric_order x a m hm horder
  have hres : ((a : k)^e)^d = 1 := by
    simpa only [hx] using residual_scalar x a m horder
  refine ⟨hd, he, hdvd, Nat.div_mul_cancel hdvd, htoric, ?_⟩
  have hindex : (e*r)/(e*r).gcd (e*i.val) = d := by
    rw [Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ he]
  obtain ⟨β, hβ, hβi⟩ := exists_label_rescaling k (e*r) (e*i.val) (Nat.mul_pos he hr) (a^e)
    (by simpa only [Units.val_pow_eq_pow_val, hindex] using hres)
  exact ⟨β, hβ, by simpa only [Units.val_pow_eq_pow_val] using hβi⟩

#print axioms mixed_rescaling

#print axioms exists_label_rescaling

#print axioms toric_order
#print axioms residual_scalar
#print axioms toric_powers_iff
end KernelArithmetic

namespace ModelCoordinates
open NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146

/-- The component/scalar pair extracted through the actual pointed model
isomorphism has the exact order of the given geometric cyclic section. -/
lemma cyclic_label_order (k : Type) [Field k] [CharZero k]
    (r m : ℕ) (hr : 0 < r) (hm : 0 < m) (h3 : 3 ≤ r) (he : Even r)
    (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (Gm : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (hGm : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 Gm)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) (TateCurve k r))
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k M)
    (hO : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k r))
    (P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection (LaurentSeries k) (TateCurve k r) G m)
    (i : Fin r) (a : kˣ)
    (hp : (MarkedPointAddition.point k h3 M hM i a).val ≫ E.hom = P.point) :
    orderOf (Multiplicative.ofAdd (i.val : ZMod r), a) = m := by
  have hn := CubicComparison.model_nsmul_of_origin k h3 he M hM s hs Gm hGm
    (TateCurve k r) G hG E hE hO
  apply KernelArithmetic.label_order_of_torsion_iff r m i a
  intro n
  have hcrit := marked_exact_torsion k r hr h3 T he M hM s hs Gm hGm i a
    (MarkedPointAddition.sectionAt k h3 M hM i a)
    (MarkedPointAddition.sectionAt_spec k h3 M hM i a) n
  change (Gm.nsmul (𝟙 _) n (MarkedPointAddition.point k h3 M hM i a) = Gm.one (𝟙 _)) ↔ _ at hcrit
  rw [← hcrit]
  have htrans :
      (Gm.nsmul (𝟙 _) n (MarkedPointAddition.point k h3 M hM i a) = Gm.one (𝟙 _)) ↔
        P.point ≫ G.schemeNsmul n = origin (LaurentSeries k) (TateCurve k r) := by
    rw [Subtype.ext_iff,
      ← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      ← cancel_mono E.hom, Category.assoc, hn n, ← Category.assoc, hp, hGm.1]
    have hzero : (pointOver k M (𝟙 _) s hs.1).val ≫ E.hom =
        origin (LaurentSeries k) (TateCurve k r) := by
      simpa only [pointOver, Category.id_comp] using hO
    rw [hzero]
  exact htrans.trans (KernelArithmetic.cyclic_torsion_iff (LaurentSeries k) (TateCurve k r) G hG m hm P n)

#print axioms cyclic_label_order
end ModelCoordinates

namespace Models
open NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146

/-- Actual model, pointed cubic comparison and differential transport chosen
jointly from the accepted providers. Every field is a specified construction
or a proof about it. -/
structure Presentation (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) where
  three_le : 3 ≤ r
  even : Even r
  tower : Tower k r hr
  model : Model k tower
  isModel : IsModel k tower model
  zero : baseScheme k ⟶ model.X
  markedZero : MarkedLift k model (zeroIndex r hr) 1 zero
  law : ArithmeticThetaMarkedGroupLawR0146.Law k model
  originLaw : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k model zero markedZero.1 law
  x : Dual k model zero 2
  y : Dual k model zero 3
  realizesX : RealizesCoordinate k false model zero x
  realizesY : RealizesCoordinate k true model zero y
  cubic : genericScheme k model ≅ Curve (LaurentSeries k) (TateCurve k r)
  cubic_over : cubic.hom ≫ structureMap (LaurentSeries k) (TateCurve k r) = genericStructure k model
  cubic_zero : genericPoint k model zero markedZero.1 ≫ cubic.hom =
    origin (LaurentSeries k) (TateCurve k r)
  coordinates : ∀ (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ model.X) (hp : MarkedLift k model i a p),
    i.val ≠ 0 ∨ (a : k) ≠ 1 →
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
      (genericPoint k model p hp.1 ≫ cubic.hom)
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val a))
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val a))
  frames : ∀ (δ : CurveFrame k r), ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ →
    ∃ δM : ArithmeticThetaHodgeFourTorsionR0147.Frame k model,
      IsGlobalDifferentialFrame k model zero x y δM ∧
      (PeriodDifferential.pointMap (genericStructure k model)
        (structureMap (LaurentSeries k) (TateCurve k r)) cubic.hom cubic_over
        (genericPoint k model zero markedZero.1) (origin (LaurentSeries k) (TateCurve k r)) cubic_zero).app ⊤
          (hodgeGenerator k r δ) =
        ArithmeticThetaHodgeFourTorsionR0147.hodgeSection k model zero markedZero.1 δM 1

lemma presentation_exists (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
    (h3 : 3 ≤ r) (he : Even r) : Nonempty (Presentation k r hr) := by
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k r h3 hr
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k r hr h3 T M hM (zeroIndex r hr) 1
  obtain ⟨G, hG, _⟩ := actual_generic_group_law k r hr h3 T he M hM s hs
  obtain ⟨X, Y, hX, hY, E, hE, hO, hcoord, hframe⟩ :=
    CubicComparison.model_iso_framed k r hr h3 he T M hM s hs
  exact ⟨⟨h3, he, T, M, hM, s, hs, G, hG, X, Y, hX, hY, E, hE, hO, hcoord, hframe⟩⟩

variable {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}

abbrev point (P : Presentation k r hr) (i : Fin r) (a : kˣ) :
    Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k r) :=
  (MarkedPointAddition.point k P.three_le P.model P.isModel i a).val ≫ P.cubic.hom

lemma point_zero (P : Presentation k r hr) : point P (zeroIndex r hr) 1 =
    origin (LaurentSeries k) (TateCurve k r) := by
  rw [point, MarkedPointAddition.point_eq k P.three_le P.model P.isModel _ _ P.zero P.markedZero]
  simpa only [pointOver, Category.id_comp] using P.cubic_zero

lemma point_coordinates (P : Presentation k r hr) (i : Fin r) (a : kˣ)
    (hne : i.val ≠ 0 ∨ (a : k) ≠ 1) :
    ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r)
      (point P i a)
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val a))
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val a)) :=
  P.coordinates i a (MarkedPointAddition.sectionAt k P.three_le P.model P.isModel i a)
    (MarkedPointAddition.sectionAt_spec k P.three_le P.model P.isModel i a) hne

lemma point_eq_of_coordinates (P : Presentation k r hr)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (i : Fin r) (a : kˣ) (hne : i.val ≠ 0 ∨ (a : k) ≠ 1)
    (p : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k r))
    (hp : ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k r) p
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX r i.val a))
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY r i.val a))) :
    p = point P i a := by
  letI := TateFullLevelMarking.elliptic k r P.three_le P.even
  exact CubicComparison.coordinates_unique (TateCurve k r) G hG hp (point_coordinates P i a hne)

abbrev sections (P : Presentation k r hr) (i : Fin r) : baseScheme k ⟶ P.model.X :=
  MarkedPointAddition.sectionAt k P.three_le P.model P.isModel i 1

lemma sections_marked (P : Presentation k r hr) (i : Fin r) :
    MarkedLift k P.model i 1 (sections P i) :=
  MarkedPointAddition.sectionAt_spec k P.three_le P.model P.isModel i 1

lemma sections_zero (P : Presentation k r hr) : sections P (zeroIndex r hr) = P.zero :=
  ActualRotationTranslation.markedLift_unique k P.model (zeroIndex r hr) 1 _ _
    (sections_marked P _) P.markedZero

lemma sections_originLaw (P : Presentation k r hr) :
    ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k P.model (sections P (zeroIndex r hr))
      (sections_marked P _).1 P.law := by
  simpa only [sections_zero] using P.originLaw

lemma cubic_inv_over (P : Presentation k r hr) :
    P.cubic.inv ≫ genericStructure k P.model = structureMap (LaurentSeries k) (TateCurve k r) := by
  rw [← P.cubic_over, Iso.inv_hom_id_assoc]

lemma cubic_inv_zero (P : Presentation k r hr) :
    origin (LaurentSeries k) (TateCurve k r) ≫ P.cubic.inv =
      genericPoint k P.model P.zero P.markedZero.1 := by
  rw [← P.cubic_zero, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {s : ℕ} {hs : 0 < s}

/-- The accepted period-collapse morphism, transported through the fixed
coordinate isomorphisms of the two actual models. -/
def collapse (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr) :
    Curve (LaurentSeries k) (TateCurve k s) ⟶ Curve (LaurentSeries k) (TateCurve k r) :=
  P.cubic.inv ≫ PeriodCollapse.generic k hdiv P.model P.isModel Q.model Q.isModel ≫ Q.cubic.hom

lemma collapse_over (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr) :
    collapse hdiv P Q ≫ structureMap (LaurentSeries k) (TateCurve k r) =
      structureMap (LaurentSeries k) (TateCurve k s) := by
  rw [collapse, Category.assoc, Category.assoc, Q.cubic_over, PeriodCollapse.generic_over, cubic_inv_over]

lemma collapse_point (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr)
    (i : Fin s) (a : kˣ) :
    point P i a ≫ collapse hdiv P Q = point Q (PeriodCollapse.index hr i) a := by
  simp only [point, collapse, Category.assoc, Iso.hom_inv_id_assoc]
  have h := PeriodCollapse.generic_marked k hdiv P.model P.isModel Q.model Q.isModel i a
    (MarkedPointAddition.sectionAt k P.three_le P.model P.isModel i a)
    (MarkedPointAddition.sectionAt_spec k P.three_le P.model P.isModel i a)
    (MarkedPointAddition.sectionAt k Q.three_le Q.model Q.isModel (PeriodCollapse.index hr i) a)
    (MarkedPointAddition.sectionAt_spec k Q.three_le Q.model Q.isModel (PeriodCollapse.index hr i) a)
  simpa only [MarkedPointAddition.point, pointOver, Category.id_comp, Category.assoc] using
    congrArg (fun f => f ≫ Q.cubic.hom) h

lemma collapse_zero (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr) :
    origin (LaurentSeries k) (TateCurve k s) ≫ collapse hdiv P Q =
      origin (LaurentSeries k) (TateCurve k r) := by
  rw [← point_zero P, collapse_point, PeriodCollapse.index_zero, point_zero]

lemma collapse_finite (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr) :
    IsFinite (collapse hdiv P Q) := by
  letI := PeriodCollapse.generic_finite k hdiv Q.three_le P.three_le P.model P.isModel Q.model Q.isModel
  unfold collapse
  infer_instance

lemma collapse_flat_surjective (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr) :
    Flat (collapse hdiv P Q) ∧ Surjective (collapse hdiv P Q) := by
  have h := PeriodCollapse.generic_flat_surjective k hdiv Q.three_le P.three_le
    P.model P.isModel Q.model Q.isModel P.zero P.markedZero Q.zero Q.markedZero
  letI := h.1
  letI := h.2
  unfold collapse
  exact ⟨inferInstance, inferInstance⟩

lemma collapse_degree (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr)
    (y : Curve (LaurentSeries k) (TateCurve k r)) :
    (collapse hdiv P Q).finrank y = s/r := by
  obtain ⟨m, rfl⟩ := hdiv
  let f := PeriodCollapse.generic k (dvd_mul_right r m) P.model P.isModel Q.model Q.isModel
  letI : IsFinite f := PeriodCollapse.generic_finite k (dvd_mul_right r m)
    Q.three_le P.three_le P.model P.isModel Q.model Q.isModel
  letI : Flat f := (PeriodCollapse.generic_flat_surjective k (dvd_mul_right r m)
    Q.three_le P.three_le P.model P.isModel Q.model Q.isModel P.zero P.markedZero Q.zero Q.markedZero).1
  have hf : ∀ z, f.finrank z = m := PeriodCollapse.generic_finrank k Q.three_le P.three_le
    P.model P.isModel Q.model Q.isModel (sections P) (sections_marked P) Q.zero Q.markedZero
  change (P.cubic.inv ≫ f ≫ Q.cubic.hom).finrank y = _
  rw [Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_comp_of_finrank_eq_const f Q.cubic.hom m hf,
    Scheme.Hom.finrank_eq_one_of_isIso, Pi.one_apply, mul_one, Nat.mul_div_cancel_left _ hr]

section Toric
variable {m : ℕ} {hs : 0 < r*m}

/-- The unique accepted dual period map between the chosen actual models. -/
def toricModel (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    genericScheme k Q.model ⟶ genericScheme k P.model :=
  Classical.choose (PeriodCollapse.dual_exists k Q.three_le P.three_le P.even
    P.model P.isModel Q.model Q.isModel (sections P) (sections_marked P)
    Q.zero Q.markedZero P.law (sections_originLaw P) Q.law Q.originLaw).exists

lemma toricModel_spec (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    toricModel P Q ≫ genericStructure k P.model = genericStructure k Q.model ∧
    PeriodCollapse.generic k (dvd_mul_right r m) P.model P.isModel Q.model Q.isModel ≫ toricModel P Q =
      P.law.schemeNsmul m ∧
    toricModel P Q ≫ PeriodCollapse.generic k (dvd_mul_right r m) P.model P.isModel Q.model Q.isModel =
      Q.law.schemeNsmul m :=
  Classical.choose_spec (PeriodCollapse.dual_exists k Q.three_le P.three_le P.even
    P.model P.isModel Q.model Q.isModel (sections P) (sections_marked P)
    Q.zero Q.markedZero P.law (sections_originLaw P) Q.law Q.originLaw).exists

/-- The actual toric map z ↦ z^m on the fixed cubic presentations. -/
def toric (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    Curve (LaurentSeries k) (TateCurve k r) ⟶ Curve (LaurentSeries k) (TateCurve k (r*m)) :=
  Q.cubic.inv ≫ toricModel P Q ≫ P.cubic.hom

lemma toric_over (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    toric P Q ≫ structureMap (LaurentSeries k) (TateCurve k (r*m)) =
      structureMap (LaurentSeries k) (TateCurve k r) := by
  rw [toric, Category.assoc, Category.assoc, P.cubic_over, (toricModel_spec P Q).1, cubic_inv_over]

lemma toric_point (hm : 0 < m) (P : Presentation k (r*m) hs) (Q : Presentation k r hr)
    (i : Fin r) (a : kˣ) :
    point Q i a ≫ toric P Q =
      point P ⟨m*i.val, by simpa only [Nat.mul_comm r m] using Nat.mul_lt_mul_of_pos_left i.isLt hm⟩ (a^m) := by
  simp only [point, toric, Category.assoc, Iso.hom_inv_id_assoc]
  have h := PeriodCollapse.dual_marked k hm P.three_le P.even P.model P.isModel Q.model Q.isModel
    (sections P (zeroIndex (r*m) hs)) (sections_marked P _) P.law (sections_originLaw P)
    (toricModel P Q) (toricModel_spec P Q).2.1 i a
    (MarkedPointAddition.sectionAt k Q.three_le Q.model Q.isModel i a)
    (MarkedPointAddition.sectionAt_spec k Q.three_le Q.model Q.isModel i a)
    (MarkedPointAddition.sectionAt k P.three_le P.model P.isModel _ (a^m))
    (MarkedPointAddition.sectionAt_spec k P.three_le P.model P.isModel _ (a^m))
  simpa only [MarkedPointAddition.point, pointOver, Category.id_comp, Category.assoc] using
    congrArg (fun f => f ≫ P.cubic.hom) h

lemma toric_zero (hm : 0 < m) (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    origin (LaurentSeries k) (TateCurve k r) ≫ toric P Q =
      origin (LaurentSeries k) (TateCurve k (r*m)) := by
  rw [← point_zero Q, toric_point hm]
  simpa only [zeroIndex, Nat.mul_zero, one_pow] using point_zero P

lemma toric_geometry (hm : 0 < m) (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    IsFinite (toric P Q) ∧ Etale (toric P Q) ∧ Surjective (toric P Q) ∧
      ∀ y, (toric P Q).finrank y = m := by
  have h := PeriodCollapse.dual_geometry k hm Q.three_le P.three_le Q.even P.even
    P.model P.isModel Q.model Q.isModel (sections P) (sections_marked P) Q.zero Q.markedZero
    P.law (sections_originLaw P) Q.law Q.originLaw (toricModel P Q)
    (toricModel_spec P Q).2.1 (toricModel_spec P Q).2.2
  letI := h.1
  letI := h.2.1
  letI := h.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold toric; infer_instance
  · unfold toric; infer_instance
  · unfold toric; infer_instance
  · intro y
    rw [toric, Scheme.Hom.finrank_comp_left_of_isIso,
      Scheme.Hom.finrank_comp_of_finrank_eq_const (toricModel P Q) P.cubic.hom m h.2.2.2,
      Scheme.Hom.finrank_eq_one_of_isIso, Pi.one_apply, mul_one]

end Toric


/-- The component quotient is étale, since its composite with its actual
étale dual is multiplication by a positive integer in characteristic zero. -/
lemma collapse_etale (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr) :
    Etale (collapse hdiv P Q) := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : 0 < m := Nat.pos_of_mul_pos_left hs
  let f := PeriodCollapse.generic k (dvd_mul_right r m) P.model P.isModel Q.model Q.isModel
  have hd := PeriodCollapse.dual_geometry k hm Q.three_le P.three_le Q.even P.even
    P.model P.isModel Q.model Q.isModel (sections P) (sections_marked P) Q.zero Q.markedZero
    P.law (sections_originLaw P) Q.law Q.originLaw (toricModel P Q)
    (toricModel_spec P Q).2.1 (toricModel_spec P Q).2.2
  letI : Etale (toricModel P Q) := hd.2.1
  have hmul := ArithmeticThetaHodgeFourTorsionR0147.multiplication_finite_etale_degree
    k (r*m) hs P.three_le P.tower P.even P.model P.isModel P.zero P.markedZero
    P.law P.originLaw m hm
  letI : Etale (f ≫ toricModel P Q) := by
    rw [(toricModel_spec P Q).2.1]
    exact hmul.2.1
  letI : Etale f := Etale.of_comp f (toricModel P Q)
  change Etale (P.cubic.inv ≫ f ≫ Q.cubic.hom)
  infer_instance

lemma collapse_weight (hdiv : r ∣ s) (P : Presentation k s hs) (Q : Presentation k r hr)
    (δP : CurveFrame k s) (hδP : ArithmeticThetaBoundaryHodgeR0182.Normalized k s δP)
    (δQ : CurveFrame k r) (hδQ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δQ) :
    (PeriodDifferential.pointMap
      (structureMap (LaurentSeries k) (TateCurve k s))
      (structureMap (LaurentSeries k) (TateCurve k r))
      (collapse hdiv P Q) (collapse_over hdiv P Q)
      (origin (LaurentSeries k) (TateCurve k s)) (origin (LaurentSeries k) (TateCurve k r))
      (collapse_zero hdiv P Q)).app ⊤ (hodgeGenerator k r δQ) = hodgeGenerator k s δP := by
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k P.three_le P.model P.isModel
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k Q.three_le Q.model Q.isModel
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k P.three_le P.model P.isModel P.zero P.markedZero
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k Q.three_le Q.model Q.isModel Q.zero Q.markedZero
  letI : IsLocallyNoetherian (genericScheme k P.model) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k P.model)
  letI : IsLocallyNoetherian (genericScheme k Q.model) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k Q.model)
  letI := TateFullLevelMarking.elliptic k s P.three_le P.even
  letI := TateFullLevelMarking.elliptic k r Q.three_le Q.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k s)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k s).toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  obtain ⟨δM, hδM, hgenM⟩ := P.frames δP hδP
  obtain ⟨δN, hδN, hgenN⟩ := Q.frames δQ hδQ
  obtain ⟨hzero, hw⟩ := PeriodDifferential.collapse_hodge k hdiv Q.three_le P.three_le Q.even P.even
    P.model P.isModel Q.model Q.isModel P.zero P.markedZero Q.zero Q.markedZero
    P.law P.originLaw Q.law Q.originLaw P.x P.y P.realizesX P.realizesY
    Q.x Q.y Q.realizesX Q.realizesY δM hδM δN hδN
  have h := PeriodDifferential.transfer_weight
    (structureMap (LaurentSeries k) (TateCurve k s))
    (structureMap (LaurentSeries k) (TateCurve k r))
    (genericStructure k P.model) (genericStructure k Q.model)
    P.cubic P.cubic_over Q.cubic Q.cubic_over (collapse hdiv P Q) (collapse_over hdiv P Q)
    (PeriodCollapse.generic k hdiv P.model P.isModel Q.model Q.isModel)
    (PeriodCollapse.generic_over k hdiv P.model P.isModel Q.model Q.isModel)
    _ _ _ _ P.cubic_zero Q.cubic_zero (collapse_zero hdiv P Q) hzero
    (by simp only [collapse, Iso.hom_inv_id_assoc])
    (hodgeGenerator k s δP) (hodgeGenerator k r δQ) _ _ hgenM hgenN 1
    (by simpa only [one_smul] using hw)
  simpa only [one_smul] using h

section ToricWeight
variable {m : ℕ} {hs : 0 < r*m}

lemma toricModel_zero (hm : 0 < m) (P : Presentation k (r*m) hs) (Q : Presentation k r hr) :
    genericPoint k Q.model Q.zero Q.markedZero.1 ≫ toricModel P Q =
      genericPoint k P.model P.zero P.markedZero.1 := by
  apply PeriodCollapse.dual_marked k hm P.three_le P.even P.model P.isModel Q.model Q.isModel
    P.zero P.markedZero P.law P.originLaw (toricModel P Q) (toricModel_spec P Q).2.1
    (zeroIndex r hr) 1 Q.zero Q.markedZero P.zero
  simpa only [zeroIndex, Nat.mul_zero, one_pow] using P.markedZero

lemma toric_weight (hm : 0 < m) (P : Presentation k (r*m) hs) (Q : Presentation k r hr)
    (δP : CurveFrame k (r*m)) (hδP : ArithmeticThetaBoundaryHodgeR0182.Normalized k (r*m) δP)
    (δQ : CurveFrame k r) (hδQ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δQ) :
    (PeriodDifferential.pointMap
      (structureMap (LaurentSeries k) (TateCurve k r))
      (structureMap (LaurentSeries k) (TateCurve k (r*m)))
      (toric P Q) (toric_over P Q)
      (origin (LaurentSeries k) (TateCurve k r)) (origin (LaurentSeries k) (TateCurve k (r*m)))
      (toric_zero hm P Q)).app ⊤ (hodgeGenerator k (r*m) δP) =
      scalar (LaurentSeries k) (m : LaurentSeries k) • hodgeGenerator k r δQ := by
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k P.three_le P.model P.isModel
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k Q.three_le Q.model Q.isModel
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k P.three_le P.model P.isModel P.zero P.markedZero
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k Q.three_le Q.model Q.isModel Q.zero Q.markedZero
  letI : IsLocallyNoetherian (genericScheme k P.model) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k P.model)
  letI : IsLocallyNoetherian (genericScheme k Q.model) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k Q.model)
  letI := TateFullLevelMarking.elliptic k (r*m) P.three_le P.even
  letI := TateFullLevelMarking.elliptic k r Q.three_le Q.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k (r*m))) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k (r*m)).toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  obtain ⟨δM, hδM, hgenM⟩ := P.frames δP hδP
  obtain ⟨δN, hδN, hgenN⟩ := Q.frames δQ hδQ
  have hw := PeriodDifferential.dual_hodge k Q.three_le P.three_le Q.even P.even
    P.model P.isModel Q.model Q.isModel P.zero P.markedZero Q.zero Q.markedZero
    P.law P.originLaw Q.law Q.originLaw P.x P.y P.realizesX P.realizesY
    Q.x Q.y Q.realizesX Q.realizesY δM hδM δN hδN
    (toricModel P Q) (toricModel_spec P Q).1 (toricModel_zero hm P Q) (toricModel_spec P Q).2.2
  rw [ArithmeticThetaHodgeFourTorsionR0147.ActualFourTorsionHodgeRoot.hodgeSection_smul
    k Q.model Q.zero Q.markedZero.1 δN (m : LaurentSeries k)] at hw
  exact PeriodDifferential.transfer_weight
    (structureMap (LaurentSeries k) (TateCurve k r))
    (structureMap (LaurentSeries k) (TateCurve k (r*m)))
    (genericStructure k Q.model) (genericStructure k P.model)
    Q.cubic Q.cubic_over P.cubic P.cubic_over (toric P Q) (toric_over P Q)
    (toricModel P Q) (toricModel_spec P Q).1
    _ _ _ _ Q.cubic_zero P.cubic_zero (toric_zero hm P Q) (toricModel_zero hm P Q)
    (by simp only [toric, Iso.hom_inv_id_assoc])
    (hodgeGenerator k r δQ) (hodgeGenerator k (r*m) δP) _ _ hgenN hgenM
    (scalar (LaurentSeries k) (m : LaurentSeries k)) hw

end ToricWeight


/-- The actual group law on the fixed cubic, transported from this presentation. -/
def cubicLaw (P : Presentation k r hr) :
    ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r) :=
  ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport P.cubic.symm (cubic_inv_over P) P.law

lemma cubicLaw_origin (P : Presentation k r hr) :
    ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) (cubicLaw P) := by
  constructor
  · intro V t
    change (P.law.one t).val ≫ P.cubic.hom = _
    rw [P.originLaw.1]
    change (t ≫ genericPoint k P.model P.zero P.markedZero.1) ≫ P.cubic.hom = _
    rw [Category.assoc, P.cubic_zero]
  · intro V t x y
    change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv
      P.cubic.symm (cubic_inv_over P) t).symm (P.law.mul t _ _) =
      (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv
      P.cubic.symm (cubic_inv_over P) t).symm (P.law.mul t _ _)
    rw [P.originLaw.2]

/-- The semilinear map removes the actual scalar label. The identity component
case uses the origin square, so this includes pure toric kernels. -/
lemma rescale_point (P : Presentation k r hr) (β : kˣ) (hβ : (β : k)^r = 1)
    (i : Fin r) (a : kˣ) (ha : (β : k)^i.val = (a : k)) :
    baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k β).symm.toRingHom ≫
      point P i a ≫ ParameterGeometry.map k β r hr P.even hβ = point P i 1 := by
  by_cases hi : i.val = 0
  · have hi' : i = zeroIndex r hr := Fin.ext hi
    have ha' : a = 1 := Units.ext (by simpa only [hi, pow_zero, Units.val_one] using ha.symm)
    subst i
    subst a
    rw [point_zero, ParameterGeometry.origin_map, ← Category.assoc,
      CoefficientMap.base_inverse, Category.id_comp]
  · apply point_eq_of_coordinates P (cubicLaw P) (cubicLaw_origin P) i 1 (Or.inl hi)
    have h := ParameterGeometry.marked_coordinates k β r hr P.even hβ i (a : k)
      (point P i a) (point_coordinates P i a (Or.inl hi))
    simpa only [ha, mul_inv_cancel₀ a.ne_zero, Units.val_one] using h

section Mixed
variable {e t : ℕ} {ht : 0 < t} {hs : 0 < r*e}

/-- First the toric power map, then the coefficient-transformed component
quotient. The resulting target equation is retained literally. -/
def mixed (P : Presentation k (r*e) hs) (Q : Presentation k r hr)
    (R : Presentation k t ht) (hdiv : t ∣ r*e) (β : kˣ) (hβ : (β : k)^(r*e) = 1) :
    Curve (LaurentSeries k) (TateCurve k r) ⟶
      Curve (LaurentSeries k) ((TateCurve k t).map (laurentRescale k β).toRingHom) :=
  toric P Q ≫ TwistedQuotient.arrow (TateCurve k (r*e)) (TateCurve k t)
    (laurentRescale k β) (ParameterAction.tateCurve_rescale k β (r*e) hs P.even hβ)
    (collapse hdiv P R)

lemma mixed_over (P : Presentation k (r*e) hs) (Q : Presentation k r hr)
    (R : Presentation k t ht) (hdiv : t ∣ r*e) (β : kˣ) (hβ : (β : k)^(r*e) = 1) :
    mixed P Q R hdiv β hβ ≫
      structureMap (LaurentSeries k) ((TateCurve k t).map (laurentRescale k β).toRingHom) =
      structureMap (LaurentSeries k) (TateCurve k r) := by
  rw [mixed, Category.assoc, TwistedQuotient.arrow_over _ _ _ _ _ (collapse_over hdiv P R), toric_over]

lemma mixed_zero (he : 0 < e) (P : Presentation k (r*e) hs) (Q : Presentation k r hr)
    (R : Presentation k t ht) (hdiv : t ∣ r*e) (β : kˣ) (hβ : (β : k)^(r*e) = 1) :
    origin (LaurentSeries k) (TateCurve k r) ≫ mixed P Q R hdiv β hβ =
      origin (LaurentSeries k) ((TateCurve k t).map (laurentRescale k β).toRingHom) := by
  rw [mixed, ← Category.assoc, toric_zero he, TwistedQuotient.origin_arrow _ _ _ _ _ (collapse_zero hdiv P R)]

lemma mixed_geometry (he : 0 < e) (P : Presentation k (r*e) hs) (Q : Presentation k r hr)
    (R : Presentation k t ht) (hdiv : t ∣ r*e) (β : kˣ) (hβ : (β : k)^(r*e) = 1) :
    IsFinite (mixed P Q R hdiv β hβ) ∧ Etale (mixed P Q R hdiv β hβ) ∧
      Surjective (mixed P Q R hdiv β hβ) ∧ ∀ y, (mixed P Q R hdiv β hβ).finrank y = e*((r*e)/t) := by
  have htor := toric_geometry he P Q
  letI := htor.1
  letI := htor.2.1
  letI := htor.2.2.1
  letI := collapse_finite hdiv P R
  letI := collapse_etale hdiv P R
  letI := (collapse_flat_surjective hdiv P R).2
  let hEq := ParameterAction.tateCurve_rescale k β (r*e) hs P.even hβ
  let f := TwistedQuotient.arrow (TateCurve k (r*e)) (TateCurve k t) (laurentRescale k β) hEq (collapse hdiv P R)
  letI : IsFinite f := TwistedQuotient.finite _ _ _ _ _
  letI : Etale f := TwistedQuotient.etale _ _ _ _ _
  letI : Surjective f := TwistedQuotient.surjective _ _ _ _ _
  change IsFinite (toric P Q ≫ f) ∧ Etale (toric P Q ≫ f) ∧ Surjective (toric P Q ≫ f) ∧ _
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro y
  change (toric P Q ≫ f).finrank y = _
  rw [Scheme.Hom.finrank_comp_of_finrank_eq_const (toric P Q) f e htor.2.2.2,
    TwistedQuotient.finrank, collapse_degree]

lemma mixed_kills (he : 0 < e) (P : Presentation k (r*e) hs) (Q : Presentation k r hr)
    (R : Presentation k t ht) (hdiv : t ∣ r*e) (β : kˣ) (hβ : (β : k)^(r*e) = 1)
    (i : Fin r) (a : kˣ) (ha : (β : k)^(e*i.val) = (a : k)^e) (hi : t ∣ e*i.val) :
    point Q i a ≫ mixed P Q R hdiv β hβ =
      origin (LaurentSeries k) ((TateCurve k t).map (laurentRescale k β).toRingHom) := by
  rw [mixed, ← Category.assoc, toric_point he]
  apply (TwistedQuotient.kernel_iff _ _ _ _ _ _).mpr
  change (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k β).symm.toRingHom ≫
    point P _ (a^e) ≫ ParameterGeometry.map k β (r*e) hs P.even hβ) ≫ collapse hdiv P R = _
  rw [rescale_point P β hβ _ (a^e) (by simpa only [Units.val_pow_eq_pow_val] using ha), collapse_point]
  have hind : PeriodCollapse.index ht
      (⟨e*i.val, by simpa only [Nat.mul_comm r e] using Nat.mul_lt_mul_of_pos_left i.isLt he⟩ : Fin (r*e)) =
      zeroIndex t ht := by
    apply Fin.ext
    exact Nat.mod_eq_zero_of_dvd hi
  rw [hind, point_zero]

end Mixed


/-- The numerical quotient exponents are forced by the original label order.
The lower bound and parity descend from the original level divided by m. -/
lemma factor_exponents (m : ℕ) (hm : 0 < m) (hmr : m ∣ r)
    (hbase : 3 ≤ r/m) (hebase : Even (r/m)) (i : Fin r)
    (hdm : r/r.gcd i.val ∣ m) :
    let d := r/r.gcd i.val
    let e := m/d
    let t := e*r.gcd i.val
    0 < e ∧ 3 ≤ t ∧ Even t ∧ t ∣ r*e ∧ t ∣ e*i.val ∧ (r*e)/t = d ∧ e*d = m := by
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  dsimp only
  let g := r.gcd i.val
  let d := r/g
  let e := m/d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left i.val hr
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left i.val hr) hg
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd hm hdm) hd
  have hed : e*d = m := Nat.div_mul_cancel hdm
  have hgd : g*d = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r i.val)
  have hrm : r/m*m = r := Nat.div_mul_cancel hmr
  have hge : g = (r/m)*e := by nlinarith
  have hbound : 3 ≤ e*g := by
    rw [hge]
    have h1 : r/m ≤ (r/m)*e := Nat.le_mul_of_pos_right (r/m) he
    have h2 : (r/m)*e ≤ e*((r/m)*e) := Nat.le_mul_of_pos_left _ he
    omega
  have hparity : Even (e*g) := by
    rw [hge]
    exact (hebase.mul_right e).mul_left e
  have hprod : e*g*d = r*e := by rw [Nat.mul_assoc, hgd, Nat.mul_comm]
  refine ⟨he, hbound, hparity, ⟨d, hprod.symm⟩, ?_, ?_, hed⟩
  · exact Nat.mul_dvd_mul_left e (Nat.gcd_dvd_right r i.val)
  · rw [← hprod, Nat.mul_div_cancel_left _ (by omega : 0 < e*g)]

/-- All data for an actual mixed cyclic quotient, including the literal
coefficient-transformed target and the original generator's labels. -/
structure Factorization (Q : Presentation k r hr) (m : ℕ) (i : Fin r) (a : kˣ) where
  d : ℕ
  e : ℕ
  t : ℕ
  positive_e : 0 < e
  positive_s : 0 < r*e
  positive_t : 0 < t
  intermediate : Presentation k (r*e) positive_s
  target : Presentation k t positive_t
  componentDiv : t ∣ r*e
  indexDiv : t ∣ e*i.val
  componentDegree : (r*e)/t = d
  totalDegree : e*d = m
  beta : kˣ
  periodRoot : (beta : k)^(r*e) = 1
  labelRoot : (beta : k)^(e*i.val) = (a : k)^e

lemma factorization_exists [IsAlgClosed k] (Q : Presentation k r hr)
    (m : ℕ) (hm : 0 < m) (hmr : m ∣ r) (hbase : 3 ≤ r/m) (hebase : Even (r/m))
    (i : Fin r) (a : kˣ) (ho : orderOf (Multiplicative.ofAdd (i.val : ZMod r), a) = m) :
    Nonempty (Factorization Q m i a) := by
  obtain ⟨hd, he, hdm, hed, htor, β, hβ, hβi⟩ := KernelArithmetic.mixed_rescaling k r m hr hm i a ho
  obtain ⟨he', ht3, hteven, htdiv, hidiv, hdeg, htotal⟩ := factor_exponents m hm hmr hbase hebase i hdm
  let e := m/(r/r.gcd i.val)
  let t := e*r.gcd i.val
  have hs : 0 < r*e := Nat.mul_pos hr he
  have ht : 0 < t := lt_of_lt_of_le (by decide : 0 < 3) ht3
  obtain ⟨P⟩ := presentation_exists k (r*e) hs (Q.three_le.trans (Nat.le_mul_of_pos_right r he))
    (Q.even.mul_right e)
  obtain ⟨R⟩ := presentation_exists k t ht ht3 hteven
  refine ⟨⟨r/r.gcd i.val, e, t, he, hs, ht, P, R, htdiv, hidiv, hdeg, htotal, β, ?_, hβi⟩⟩
  simpa only [e, Nat.mul_comm] using hβ

namespace Factorization
variable {Q : Presentation k r hr} {m : ℕ} {i : Fin r} {a : kˣ}
variable (F : Factorization Q m i a)

def equation : WeierstrassCurve (LaurentSeries k) :=
  (TateCurve k F.t).map (laurentRescale k F.beta).toRingHom

def map : Curve (LaurentSeries k) (TateCurve k r) ⟶ Curve (LaurentSeries k) F.equation :=
  mixed F.intermediate Q F.target F.componentDiv F.beta F.periodRoot

lemma map_over : F.map ≫ structureMap (LaurentSeries k) F.equation =
    structureMap (LaurentSeries k) (TateCurve k r) :=
  mixed_over F.intermediate Q F.target F.componentDiv F.beta F.periodRoot

lemma origin : ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r) ≫ F.map =
    ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) F.equation :=
  mixed_zero F.positive_e F.intermediate Q F.target F.componentDiv F.beta F.periodRoot

lemma kills : point Q i a ≫ F.map = ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) F.equation :=
  mixed_kills F.positive_e F.intermediate Q F.target F.componentDiv F.beta F.periodRoot i a F.labelRoot F.indexDiv

lemma geometry : IsFinite F.map ∧ Etale F.map ∧ Surjective F.map ∧ ∀ y, F.map.finrank y = m := by
  have h := mixed_geometry F.positive_e F.intermediate Q F.target F.componentDiv F.beta F.periodRoot
  simpa only [map, equation, F.componentDegree, F.totalDegree] using h

end Factorization


/-- Apply the construction to the actual cyclic section on the cubic. Its
marking is arbitrary; disjoint multiples supply its exact label order. -/
lemma cyclic_factorization_exists [IsAlgClosed k] (Q : Presentation k r hr)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (m : ℕ) (hm : 0 < m) (hmr : m ∣ r) (hbase : 3 ≤ r/m) (hebase : Even (r/m))
    (C : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection (LaurentSeries k) (TateCurve k r) G m) :
    ∃ (i : Fin r) (a : kˣ), point Q i a = C.point ∧ Nonempty (Factorization Q m i a) := by
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero (r : k) := ⟨Nat.cast_ne_zero.mpr hr.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k r
  let ζ : kˣ := (hz.isUnit hr.ne').unit
  have hζ : IsPrimitiveRoot (ζ : k) r := by simpa only [ζ, (hz.isUnit hr.ne').unit_spec] using hz
  have hkill := (KernelArithmetic.cyclic_torsion_iff (LaurentSeries k) (TateCurve k r) G hG m hm C r).mpr hmr
  obtain ⟨ij, hij⟩ := ModelCoordinates.torsion_section_marked k r hr Q.three_le Q.even
    Q.tower Q.model Q.isModel Q.zero Q.markedZero Q.law Q.originLaw G hG
    Q.cubic Q.cubic_over Q.cubic_zero ζ hζ C.point C.over_eq hkill
  have ho := ModelCoordinates.cyclic_label_order k r m hr hm Q.three_le Q.even
    Q.tower Q.model Q.isModel Q.zero Q.markedZero Q.law Q.originLaw G hG
    Q.cubic Q.cubic_over Q.cubic_zero C ij.1 (ζ^ij.2.val) hij
  exact ⟨ij.1, ζ^ij.2.val, hij, factorization_exists Q m hm hmr hbase hebase _ _ ho⟩

#print axioms cyclic_factorization_exists

#print axioms factorization_exists
#print axioms Factorization.kills
#print axioms Factorization.geometry

#print axioms cubicLaw_origin
#print axioms rescale_point
#print axioms mixed_geometry
#print axioms mixed_kills

#print axioms collapse_etale
#print axioms collapse_weight
#print axioms toric_weight

#print axioms toric_point
#print axioms toric_zero
#print axioms toric_geometry

#print axioms collapse_point
#print axioms collapse_zero
#print axioms collapse_degree

#print axioms presentation_exists
#print axioms point_eq_of_coordinates
end Models


namespace CoefficientMap
open WeierstrassProjModel

/-- The origin law on the coefficient transform is constructed through the
same canonical Cartesian map used throughout the quotient construction. -/
lemma origin_law_exists {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (ι : R →+* S) :
    ∃ H : ArithmeticThetaRelativeKatoR0169.Law S (W.map ι),
      ArithmeticThetaRelativeKatoR0169.IsOriginLaw S (W.map ι) H := by
  let f := map W ι
  have hb := cartesian W ι
  have he := origin_map W ι
  obtain ⟨H, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι (structureMap R W) (structureMap S (W.map ι)) f hb G
  refine ⟨H, ?_, ?_⟩
  · intro T t
    apply hb.hom_ext
    · change (H.one t).val ≫ f = (t ≫ origin S (W.map ι)) ≫ f
      rw [ho, hG.1]
      dsimp only [f]
      simp only [Category.assoc, he]
      rfl
    · exact (H.one t).property.trans (by
        rw [Category.assoc]
        exact ((congrArg (fun z => t ≫ z) (kwZeroSect S (W.map ι)).property).trans
          (Category.comp_id t)).symm)
  · intro T t x y
    apply Subtype.ext
    apply hb.hom_ext
    · rw [hm, hm, hG.2]
    · exact (H.mul t x y).property.trans (H.mul t y x).property.symm

#print axioms origin_law_exists
end CoefficientMap

namespace CyclicKernel
open CategoryTheory.Limits ArithmeticThetaRelativeCyclicQuotientR0173
open ArithmeticThetaRelativeIsogenyHodgeR0172

/-- The m specified disjoint multiples exhaust the actual scheme-theoretic
fiber of a finite étale degree-m pointed map killing the generator. -/
lemma cartesian {K : Type} [Field K] [CharZero K]
    (W V : WeierstrassCurve K) [W.IsElliptic] [V.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K W G)
    (H : ArithmeticThetaRelativeKatoR0169.Law K V)
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K V H)
    (m : ℕ) (C : CyclicSection K W G m) (f : PointedMap K W V)
    [IsFinite f.map] [Etale f.map] (hdegree : ∀ y, f.map.finrank y = m)
    (hkill : C.point ≫ f.map = origin K V) :
    IsPullback (Sigma.desc (fun j : Fin m => C.point ≫ G.schemeNsmul j.val))
      (Sigma.desc (fun _ : Fin m => 𝟙 (Base K))) f.map (origin K V) := by
  have hn := (pointed_relative_group_hom K W G hG V H hH f).2
  apply PeriodCollapse.split_fibre_cartesian (structureMap K W) (structureMap K V) f.map
    (origin K V) (WeierstrassProjModel.kwZeroSect K V).property (Fin m)
    (fun j => C.point ≫ G.schemeNsmul j.val)
  · intro j
    rw [Category.assoc, G.schemeNsmul_over, C.over_eq]
  · intro i j hij
    by_contra hne
    exact Set.disjoint_iff_forall_ne.mp (C.disjoint i j hne) ⟨_, rfl⟩ ⟨_, rfl⟩
      (congrArg (fun p : Base K ⟶ Curve K W => p (IsLocalRing.closedPoint K)) hij)
  · intro j
    rw [Category.assoc, hn, ← Category.assoc, hkill,
      ArithmeticThetaRelativeIsogenyHodgeR0172.RelativeMultiplicationHodgeWeight.multiplication_origin K V H hH]
  · intro y
    simpa only [Fintype.card_fin] using hdegree y


open ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open QuotientComparison

/-- Any constructed pointed degree-m quotient killing the transported actual
cyclic generator compares to the specified global quotient through a genuine
isomorphism. The given Cartesian test and every labeled kernel section remain
in the comparison square. -/
lemma compare {K S : Type} [Field K] [CharZero K] [CommRing S]
    (E : EllipticFamily S) (m : ℕ) (P : Cyclic E m) (Q : Quotient S E m P.point)
    (W V : WeierstrassCurve K) [W.IsElliptic] [V.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K W G)
    (H : ArithmeticThetaRelativeKatoR0169.Law K V)
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K V H)
    (C : ArithmeticThetaOpenHodgeR0180.Test S E K W G)
    (f : PointedMap K W V) [IsFinite f.map] [Etale f.map] [Surjective f.map]
    (hdegree : ∀ y, f.map.finrank y = m)
    (hkill : (testCyclic C P).point ≫ f.map = origin K V) :
    ∃ e : (baseChangeFamily Q.target (baseMap S K C.scalar)).curve ≅ Curve K V,
      baseChangeArrow E Q.target Q.arrow (baseMap S K C.scalar)
        (structureMap K W) C.map C.cartesian ≫ e.hom = f.map ∧
      e.hom ≫ structureMap K V = (baseChangeFamily Q.target (baseMap S K C.scalar)).projection ∧
      zero (baseChangeFamily Q.target (baseMap S K C.scalar)) ≫ e.hom = origin K V := by
  let F := weierstrassFamily W G hG
  let J := weierstrassFamily V H hH
  let B := baseMap S K C.scalar
  let Y := baseChangeFamily Q.target B
  have hF0 : zero F = origin K W := by
    change (G.one (𝟙 (Base K))).val = origin K W
    simpa only [Category.id_comp] using hG.1 (𝟙 (Base K))
  have hJ0 : zero J = origin K V := by
    change (H.one (𝟙 (Base K))).val = origin K V
    simpa only [Category.id_comp] using hH.1 (𝟙 (Base K))
  let a := baseChangeArrow E Q.target Q.arrow B (structureMap K W) C.map C.cartesian
  have hao : a ≫ Y.projection = F.projection := baseChangeArrow_over _ _ _ _ _ _ _
  have ha0 : zero F ≫ a = zero Y := by
    rw [hF0]
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeArrow_fst, ← Category.assoc, C.origin_eq,
        Category.assoc, Q.arrow.zero_eq]
      exact (baseChange_zero Q.target B).symm
    · rw [Category.assoc, hao]
      exact (WeierstrassProjModel.kwZeroSect K W).property.trans (Y.law.one (𝟙 _)).property.symm
  let u : Pointed K F Y := ⟨a, hao, ha0⟩
  let v : Pointed K F J := ⟨f.map, f.over_eq, by rw [hF0, hJ0]; exact f.origin_eq⟩
  letI : IsFinite Q.arrow.map := Q.finite
  letI : Etale Q.arrow.map := Q.etale
  letI : Surjective Q.arrow.map := Q.surjective
  have hgeo := baseChangeArrow_geometry E Q.target Q.arrow B (structureMap K W) C.map C.cartesian Q.degree
  letI : IsFinite u.map := hgeo.1
  letI : Etale u.map := hgeo.2.1
  letI : Surjective u.map := hgeo.2.2.1
  have hKf := quotient_split_baseChange E P Q B (structureMap K W) C.map C.cartesian
    (fun j : Fin m => (testCyclic C P).point ≫ G.schemeNsmul j.val)
    (fun j => by rw [Category.assoc, G.schemeNsmul_over, (testCyclic C P).over_eq])
    (fun j => by simpa only [B, GlobalLevelCyclicQuotientR0180.multiple, Category.assoc] using testCyclic_multiple C P j)
  have hKg := cartesian W V G hG H hH m (testCyclic C P) f hdegree hkill
  have hKg' : IsPullback (Sigma.desc (fun j : Fin m => (testCyclic C P).point ≫ G.schemeNsmul j.val))
      (Sigma.desc (fun _ : Fin m => 𝟙 (Base K))) v.map (zero J) := by
    rw [hJ0]
    exact hKg
  obtain ⟨e, he, heOver, he0⟩ := iso_of_split_kernel F Y J u v
    (pointed_hom F u) (pointed_hom F v) _ _ hKf hKg'
  exact ⟨e, he, heOver, he0.trans hJ0⟩

#print axioms compare

#print axioms cartesian
end CyclicKernel


namespace EveryTestGeometry
open CategoryTheory.Limits ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open QuotientComparison Models ArithmeticThetaRelativeIsogenyHodgeR0172

/-- The actual level has enough even period after division by every allowed
cyclic order, including m=N=2. -/
lemma level_bounds (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hmN : m ∣ N) :
    0 < level N ∧ 3 ≤ level N ∧ Even (level N) ∧
      m ∣ level N ∧ 3 ≤ level N/m ∧ Even (level N/m) := by
  obtain ⟨q, rfl⟩ := hmN
  have hq : 0 < q := Nat.pos_of_mul_pos_left hN
  have heq : level (m*q) = m*(24*m*q^2) := by dsimp only [level]; ring
  have hbound : 3 ≤ 24*m*q^2 := by nlinarith [sq_pos_of_pos hq]
  have hL : 0 < level (m*q) := by rw [heq]; exact Nat.mul_pos hm (by omega)
  refine ⟨hL, ?_, ?_, ⟨24*m*q^2, heq⟩, ?_, ?_⟩
  · rw [heq]
    exact hbound.trans (Nat.le_mul_of_pos_left _ hm)
  · exact (show Even 24 by decide).mul_right ((m*q)^2)
  · rw [heq, Nat.mul_div_cancel_left _ hm]
    exact hbound
  · rw [heq, Nat.mul_div_cancel_left _ hm]
    exact ((show Even 24 by decide).mul_right m).mul_right (q^2)

/-- Construct the mixed quotient comparison for every actual test and every
full marking. Both the target test and its map come from the isomorphism of
scheme-theoretic quotients, while the source map is the constructed factorization. -/
lemma comparison_exists (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r)
    (m : ℕ) (hm : 0 < m) (hmr : m ∣ r) (hbase : 3 ≤ r/m) (hebase : Even (r/m))
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k r)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k r D)
    (Q : Quotient D.atlas.quotient.ring D.atlas.descent.family m (kernelPoint k r D.atlas m)) :
    let Cs := OpenDiscriminantFullTateExpansionR0182.affineTest k r V
    ∃ (P : Presentation k r hr) (i : Fin r) (a : kˣ) (F : Factorization P m i a)
      (Gt : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) F.equation)
      (hGt : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) F.equation Gt)
      (Ct : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring Q.target
        (LaurentSeries k) F.equation Gt),
      Ct.scalar = Cs.scalar ∧ V.map ≫ Q.arrow.map = F.map ≫ Ct.map := by
  dsimp only
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := V.level.elliptic
  let Cs := OpenDiscriminantFullTateExpansionR0182.affineTest k r V
  let PC := levelCyclic k r hr D m hm hmr
  obtain ⟨P⟩ := presentation_exists k r hr h3 he
  obtain ⟨i, a, hia, ⟨F⟩⟩ := cyclic_factorization_exists P V.level.law V.level.originLaw
    m hm hmr hbase hebase (testCyclic Cs PC)
  letI := TateFullLevelMarking.elliptic k F.t F.target.three_le F.target.even
  letI : F.equation.IsElliptic := by unfold Factorization.equation; infer_instance
  obtain ⟨H, hH⟩ := CoefficientMap.origin_law_exists (TateCurve k F.t)
    (cubicLaw F.target) (cubicLaw_origin F.target) (laurentRescale k F.beta).toRingHom
  let f : PointedMap (LaurentSeries k) (TateCurve k r) F.equation :=
    ⟨F.map, F.map_over, F.origin⟩
  have hg := F.geometry
  letI : IsFinite f.map := hg.1
  letI : Etale f.map := hg.2.1
  letI : Surjective f.map := hg.2.2.1
  obtain ⟨E, hE, hEover, hEzero⟩ := CyclicKernel.compare D.atlas.descent.family m PC Q
    (TateCurve k r) F.equation V.level.law V.level.originLaw H hH Cs f hg.2.2.2
    (by rw [← hia]; exact F.kills)
  obtain ⟨Gt, hGt, Ct, hscalar, hmap⟩ := TargetTest.of_iso_over Q.target
    (baseMap D.atlas.quotient.ring (LaurentSeries k) Cs.scalar) Cs.scalar rfl
    F.equation E hEover hEzero
  refine ⟨P, i, a, F, Gt, hGt, Ct, hscalar, ?_⟩
  change Cs.map ≫ Q.arrow.map = f.map ≫ Ct.map
  rw [hmap, ← hE, Category.assoc, Iso.hom_inv_id_assoc]
  exact (baseChangeArrow_fst _ _ _ _ _ _ _).symm

#print axioms level_bounds
#print axioms comparison_exists
end EveryTestGeometry


namespace CartesianFrames
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaPullback
open OpenDiscriminantFullTateExpansionR0182

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme} (f : Y ⟶ Base A) (g : X ⟶ Base B) (φ : X ⟶ Y)
    (hc : IsPullback φ g f (baseMap A B (algebraMap A B)))
    [SmoothOfRelativeDimension 1 f]

def frame (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ g.kaehler := by
  letI := differentialMap_isIso f g φ hc.w hc
  exact (pullback_unit_iso X Y φ).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso δ ≪≫ asIso (differentialMap f g φ hc.w)

lemma frame_one (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (U : Y.Opens) :
    Scheme.Modules.Hom.app (frame f g φ hc δ).hom (φ ⁻¹ᵁ U) (1 : Γ(X, φ ⁻¹ᵁ U)) =
      (differentialMap f g φ hc.w).app _
        (Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.Hom.app δ.hom U (1 : Γ(Y,U)))) := by
  change (differentialMap f g φ hc.w).app _
    (((Scheme.Modules.pullback φ).map δ.hom).app _
      ((pullback_unit_iso X Y φ).inv.app _ (1 : Γ(X,φ ⁻¹ᵁ U)))) = _
  have hunit : (pullback_unit_iso X Y φ).inv.app (φ ⁻¹ᵁ U) (1 : Γ(X,φ ⁻¹ᵁ U)) =
      Scheme.Modules.pullbackLocalSection φ
        (L := (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (1 : Γ(Y,U)) := by
    apply (ConcreteCategory.bijective_of_isIso ((pullback_unit_iso X Y φ).hom.app (φ ⁻¹ᵁ U))).1
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply, pullback_unit_local_section]
  rw [hunit, ← Scheme.Modules.pullbackLocalSection_app]

lemma normalized_on (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (U : Y.Opens) (x y : Γ(Y,U))
    (hn : relativeD f U x = (2*y) • Scheme.Modules.Hom.app δ.hom U (1 : Γ(Y,U)))
    (V : X.Opens) (hV : V ≤ φ ⁻¹ᵁ U) :
    relativeD g V (φ.appLE U V hV x) =
      (2 * φ.appLE U V hV y) • Scheme.Modules.Hom.app (frame f g φ hc δ).hom V (1 : Γ(X,V)) := by
  have h : relativeD g (φ ⁻¹ᵁ U) (φ.app U x) =
      (2 * φ.app U y) • Scheme.Modules.Hom.app (frame f g φ hc δ).hom _ (1 : Γ(X,φ ⁻¹ᵁ U)) := by
    rw [← differentialMap_D f g φ hc.w, hn, Scheme.Modules.pullbackLocalSection_smul,
      Scheme.Modules.Hom.app_smul, frame_one]
    congr 1
    exact (φ.app U).hom.map_mul 2 y |>.trans (by rw [map_ofNat])
  have hh := relativeD_normalization_restrict g (φ ⁻¹ᵁ U) hV _ _ _ h
  erw [map_mul, map_ofNat, frame_section_restrict] at hh
  exact hh

omit [Algebra A B] [SmoothOfRelativeDimension 1 f] in
/-- Coordinate functions transport through the actual square of affine charts,
with distinct coefficient rings allowed. -/
lemma chartSection_pullback {X Y : Scheme}
    (φ : X ⟶ Y) (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j] (χ : A →+* B)
    (hj : j ≫ φ = Spec.map (CommRingCat.ofHom χ) ≫ i)
    (h : j ''ᵁ ⊤ ≤ φ ⁻¹ᵁ (i ''ᵁ ⊤)) (a : A) :
    φ.appLE (i ''ᵁ ⊤) (j ''ᵁ ⊤) h ((chartRingEquiv i).symm a) =
      (chartRingEquiv j).symm (χ a) := by
  apply (chartRingEquiv j).injective
  rw [RingEquiv.apply_symm_apply]
  have hmaps : φ.appLE (i ''ᵁ ⊤) (j ''ᵁ ⊤) h ≫ (j.appIso ⊤).hom =
      (i.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom χ)).appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom',
      show (Spec.map (CommRingCat.ofHom χ)).appTop =
        (Spec.map (CommRingCat.ofHom χ)).appLE ⊤ ⊤ (by simp) by
          simp [Scheme.Hom.appLE, Scheme.Hom.appTop],
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    have app_congr (u v : Spec (CommRingCat.of B) ⟶ Y) (huv : u = v)
        (hu : ⊤ ≤ u ⁻¹ᵁ (i ''ᵁ ⊤)) (hv : ⊤ ≤ v ⁻¹ᵁ (i ''ᵁ ⊤)) :
        u.appLE (i ''ᵁ ⊤) ⊤ hu = v.appLE (i ''ᵁ ⊤) ⊤ hv := by
      subst v
      rfl
    exact app_congr _ _ hj _ _
  have hh := congrArg (fun q : Γ(Y,i ''ᵁ ⊤) ⟶ CommRingCat.of B => q.hom ((chartRingEquiv i).symm a))
    (show φ.appLE (i ''ᵁ ⊤) (j ''ᵁ ⊤) h ≫ (j.appIso ⊤).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (i.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom χ by
      rw [← Category.assoc, hmaps, Category.assoc, Scheme.ΓSpecIso_naturality])
  exact hh.trans (congrArg χ ((chartRingEquiv i).apply_symm_apply a))


/-- The same Cartesian differential comparison on arbitrary local sections,
now allowing the nonidentity coefficient homomorphism on the base. -/
lemma pointed_section (q : Base A ⟶ Y) (p : Base B ⟶ X)
    (hp : p ≫ φ = baseMap A B (algebraMap A B) ≫ q)
    (U : Y.Opens) (ω : Γ(f.kaehler,U)) (V : (Base B).Opens)
    (h₁ : V ≤ baseMap A B (algebraMap A B) ⁻¹ᵁ (q ⁻¹ᵁ U))
    (h₂ : V ≤ p ⁻¹ᵁ (φ ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₁
      ((pointedDifferentialIso f g φ hc q p hp).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap A B (algebraMap A B))
          (Scheme.Modules.pullbackLocalSection q ω))) =
      res ((Scheme.Modules.pullback p).obj g.kaehler) h₂
        (Scheme.Modules.pullbackLocalSection p
          ((differentialMap f g φ hc.w).app _ (Scheme.Modules.pullbackLocalSection φ ω))) := by
  change res _ h₁ (((Scheme.Modules.pullback p).map (differentialMap f g φ hc.w)).app _
    ((squarePullbackIso _ q p φ hp.symm f.kaehler).hom.app _
      (Scheme.Modules.pullbackLocalSection _ (Scheme.Modules.pullbackLocalSection q ω)))) = _
  rw [hom_res, squarePullbackIso_section _ q p φ hp.symm f.kaehler U ω V h₁ h₂,
    ← hom_res, ← Scheme.Modules.pullbackLocalSection_app]

lemma pointed_frame (q : Base A ⟶ Y) (p : Base B ⟶ X)
    (hp : p ≫ φ = baseMap A B (algebraMap A B) ≫ q)
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    transportSection (baseMap A B (algebraMap A B)) _ _ (pointedDifferentialIso f g φ hc q p hp)
      (res _ (by simp) (Scheme.Modules.pullbackLocalSection q (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))))) =
      res _ (by simp) (Scheme.Modules.pullbackLocalSection p
        (Scheme.Modules.Hom.app (frame f g φ hc δ).hom ⊤ (1 : Γ(X,⊤)))) := by
  have hg : res _ (show (⊤ : (Base A).Opens) ≤ q ⁻¹ᵁ ⊤ by simp)
      (Scheme.Modules.pullbackLocalSection q (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤)))) =
      Scheme.Modules.pullbackLocalSection q (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))) :=
    InitialHodgeSection.res_self _ _
  rw [hg]
  have h := pointed_section f g φ hc q p hp ⊤ (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))) ⊤ (by simp) (by simp)
  rw [← frame_one] at h
  exact h

#print axioms pointed_frame

#print axioms normalized_on
#print axioms chartSection_pullback
end CartesianFrames

namespace Models
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaCubicModelR0144

lemma normalized_generator_unique {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
    (P : Presentation k r hr) (δ ε : CurveFrame k r)
    (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ)
    (hε : ArithmeticThetaBoundaryHodgeR0182.Normalized k r ε) :
    hodgeGenerator k r ε = hodgeGenerator k r δ := by
  letI := TateFullLevelMarking.elliptic k r P.three_le P.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  obtain ⟨δM, hδM, hgenδ⟩ := P.frames δ hδ
  obtain ⟨εM, hεM, hgenε⟩ := P.frames ε hε
  have heq := normalized_frame_unique k P.three_le P.even P.model P.isModel P.zero P.markedZero
    P.x P.y P.realizesX P.realizesY δM εM hδM hεM
  let f := PeriodDifferential.pointMap (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k P.model)
    (structureMap (LaurentSeries k) (TateCurve k r)) P.cubic.hom P.cubic_over
    (ArithmeticThetaGenericEvaluationR0140.genericPoint k P.model P.zero P.markedZero.1)
    (origin (LaurentSeries k) (TateCurve k r)) P.cubic_zero
  letI : IsIso f := PeriodDifferential.pointMap_isIso _ _ _ _ _ _ _
  apply (ConcreteCategory.bijective_of_isIso (f.app ⊤)).1
  change _ = _
  rw [hgenε, hgenδ, heq]

#print axioms normalized_generator_unique
end Models


namespace CoefficientMap
open WeierstrassCurve.DrinfeldGlobal

lemma affine_coordinates_of_eq {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (W' : WeierstrassCurve S) (ι : R →+* S) (h : W.map ι = W') :
    ∃ χ : ZChartRing W.toProjective →+* ZChartRing W'.toProjective,
      zChartι W'.toProjective ≫ mapOfEq W W' ι h = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective ∧
      χ (xOverZ W.toProjective) = xOverZ W'.toProjective ∧
      χ (yOverZ W.toProjective) = yOverZ W'.toProjective := by
  subst W'
  exact affine_coordinates W ι
end CoefficientMap

namespace ParameterFrames
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open OpenDiscriminantFullTateExpansionR0182
open WeierstrassCurve.DrinfeldGlobal

variable {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
    (P : Models.Presentation k r hr) (β : kˣ) (hβ : (β : k)^r = 1)

/-- The frame obtained from the canonical coefficient map, with its actual
nontrivial scalar homomorphism on the base. -/
def frame (δ : CurveFrame k r) : CurveFrame k r := by
  letI : Algebra (LaurentSeries k) (LaurentSeries k) := (laurentRescale k β).toRingHom.toAlgebra
  letI := TateFullLevelMarking.elliptic k r P.three_le P.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  exact CartesianFrames.frame (structureMap (LaurentSeries k) (TateCurve k r))
    (structureMap (LaurentSeries k) (TateCurve k r))
    (ParameterGeometry.map k β r hr P.even hβ) (ParameterGeometry.cartesian k β r hr P.even hβ) δ

set_option maxHeartbeats 800000 in
/-- Canonical coefficient pullback preserves dx/(2y), as an equality of
actual relative differential sections on the specified affine chart. -/
lemma normalized (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    ArithmeticThetaBoundaryHodgeR0182.Normalized k r (frame P β hβ δ) := by
  letI : Algebra (LaurentSeries k) (LaurentSeries k) := (laurentRescale k β).toRingHom.toAlgebra
  letI := TateFullLevelMarking.elliptic k r P.three_le P.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  let f := ParameterGeometry.map k β r hr P.even hβ
  let i := zLeg k r (Iso.refl (projectiveCurve k r))
  let U := zOpen k r (Iso.refl (projectiveCurve k r))
  obtain ⟨χ, hχ, hx, hy⟩ := CoefficientMap.affine_coordinates_of_eq
    (TateCurve k r) (TateCurve k r) (laurentRescale k β).toRingHom
    (ParameterAction.tateCurve_rescale k β r hr P.even hβ)
  have hi : i ≫ f = Spec.map (CommRingCat.ofHom χ) ≫ i := by
    dsimp only [i, zLeg, Iso.refl_inv]
    rw [Category.comp_id]
    change zChartι (TateCurve k r).toProjective ≫
      CoefficientMap.mapOfEq (TateCurve k r) (TateCurve k r) (laurentRescale k β).toRingHom _ =
      Spec.map (CommRingCat.ofHom χ) ≫ zChartι (TateCurve k r).toProjective
    exact hχ
  have hU : U ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom χ) x, by trivial, ?_⟩
    exact (congrArg (fun q => q x) hi).symm
  have hh := CartesianFrames.normalized_on
    (structureMap (LaurentSeries k) (TateCurve k r)) (structureMap (LaurentSeries k) (TateCurve k r))
    f (ParameterGeometry.cartesian k β r hr P.even hβ) δ U
      ((chartRingEquiv i).symm (xOverZ (TateCurve k r).toProjective))
      ((chartRingEquiv i).symm (yOverZ (TateCurve k r).toProjective)) hδ U hU
  change relativeD _ U (f.appLE U U hU ((chartRingEquiv i).symm (xOverZ (TateCurve k r).toProjective))) = _ at hh
  rw [CartesianFrames.chartSection_pullback f i i χ hi hU, hx] at hh
  change _ = (2 * f.appLE U U hU ((chartRingEquiv i).symm (yOverZ (TateCurve k r).toProjective))) • _ at hh
  rw [CartesianFrames.chartSection_pullback f i i χ hi hU, hy] at hh
  exact hh

lemma generator (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    hodgeGenerator k r (frame P β hβ δ) = hodgeGenerator k r δ :=
  Models.normalized_generator_unique P δ (frame P β hβ δ) hδ (normalized P β hβ δ hδ)


/-- The canonical Hodge comparison attached to the period-fixing coefficient map. -/
def comparison :
    (Scheme.Modules.pullback (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k β).toRingHom)).obj
      (Hodge (LaurentSeries k) (TateCurve k r)) ≅ Hodge (LaurentSeries k) (TateCurve k r) := by
  letI : Algebra (LaurentSeries k) (LaurentSeries k) := (laurentRescale k β).toRingHom.toAlgebra
  letI := TateFullLevelMarking.elliptic k r P.three_le P.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  exact pointedDifferentialIso (structureMap (LaurentSeries k) (TateCurve k r))
    (structureMap (LaurentSeries k) (TateCurve k r))
    (ParameterGeometry.map k β r hr P.even hβ) (ParameterGeometry.cartesian k β r hr P.even hβ)
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r))
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r))
    (ParameterGeometry.origin_map k β r hr P.even hβ)

lemma transport_generator (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    transportSection (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k β).toRingHom)
      _ _ (comparison P β hβ) (hodgeGenerator k r δ) = hodgeGenerator k r δ := by
  letI : Algebra (LaurentSeries k) (LaurentSeries k) := (laurentRescale k β).toRingHom.toAlgebra
  letI := TateFullLevelMarking.elliptic k r P.three_le P.even
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k r).toProjective
  have h := CartesianFrames.pointed_frame
    (structureMap (LaurentSeries k) (TateCurve k r)) (structureMap (LaurentSeries k) (TateCurve k r))
    (ParameterGeometry.map k β r hr P.even hβ) (ParameterGeometry.cartesian k β r hr P.even hβ)
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r))
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k r))
    (ParameterGeometry.origin_map k β r hr P.even hβ) δ
  change transportSection _ _ _ (comparison P β hβ) (hodgeGenerator k r δ) =
    hodgeGenerator k r (frame P β hβ δ) at h
  exact h.trans (generator P β hβ δ hδ)

#print axioms transport_generator

#print axioms normalized
#print axioms generator
end ParameterFrames


namespace CoefficientMap
open CategoryTheory.Limits
variable {K : Type} [Field K] (W : WeierstrassCurve K) (e : K ≃+* K)

lemma inverse_cartesian :
    letI := map_isIso W e
    IsPullback (inv (map W e.toRingHom)) (structureMap K W)
      (structureMap K (W.map e.toRingHom)) (baseMap K K e.symm.toRingHom) := by
  letI := map_isIso W e
  haveI : IsIso (baseMap K K e.symm.toRingHom) := (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_inv
  haveI : IsIso (baseMap K K e.toRingHom) := (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_hom
  apply IsPullback.of_horiz_isIso
  constructor
  apply (cancel_mono (baseMap K K e.toRingHom)).mp
  rw [Category.assoc, ← (cartesian W e.toRingHom).w, IsIso.inv_hom_id_assoc,
    Category.assoc, base_inverse, Category.comp_id]

lemma inverse_origin :
    letI := map_isIso W e
    origin K W ≫ inv (map W e.toRingHom) = baseMap K K e.symm.toRingHom ≫ origin K (W.map e.toRingHom) := by
  letI := map_isIso W e
  apply (cancel_mono (map W e.toRingHom)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Category.assoc, origin_map, ← Category.assoc, base_inverse, Category.id_comp]

lemma inverse_baseChange [W.IsElliptic] [(W.map e.toRingHom).IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K W G)
    (H : ArithmeticThetaRelativeKatoR0169.Law K (W.map e.toRingHom))
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K (W.map e.toRingHom) H) :
    letI := map_isIso W e
    ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange K (W.map e.toRingHom) H K W G
      e.symm.toRingHom (inv (map W e.toRingHom)) := by
  letI := map_isIso W e
  refine ⟨inverse_cartesian W e, inverse_origin W e, ?_⟩
  intro n
  apply (cancel_mono (map W e.toRingHom)).mp
  have hn := multiplication_of_cartesian W (W.map e.toRingHom) G hG H hH
    e.toRingHom (map W e.toRingHom) (cartesian W e.toRingHom) (origin_map W e.toRingHom) n
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc, hn, IsIso.inv_hom_id_assoc]

/-- Pull the given target test back through the inverse canonical coefficient
map. This supplies a pure Tate test while retaining the exact scalar map. -/
def inverseTest {S : Type} [CommRing S] {E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S}
    [W.IsElliptic] [(W.map e.toRingHom).IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law K W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K W G)
    (H : ArithmeticThetaRelativeKatoR0169.Law K (W.map e.toRingHom))
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw K (W.map e.toRingHom) H)
    (C : ArithmeticThetaOpenHodgeR0180.Test S E K (W.map e.toRingHom) H) :
    ArithmeticThetaOpenHodgeR0180.Test S E K W G := by
  letI := map_isIso W e
  have hb := inverse_baseChange W e G hG H hH
  have hbase : baseMap S K (e.symm.toRingHom.comp C.scalar) = baseMap K K e.symm.toRingHom ≫ baseMap S K C.scalar :=
    Spec.map_comp (CommRingCat.ofHom C.scalar) (CommRingCat.ofHom e.symm.toRingHom)
  exact {
    scalar := e.symm.toRingHom.comp C.scalar
    map := inv (map W e.toRingHom) ≫ C.map
    cartesian := by rw [hbase]; exact hb.1.paste_horiz C.cartesian
    origin_eq := by
      rw [← Category.assoc, hb.2.1, Category.assoc, C.origin_eq, ← Category.assoc, hbase]
      rfl
    nsmul_eq := by
      intro n
      rw [← Category.assoc, hb.2.2 n, Category.assoc, C.nsmul_eq, Category.assoc] }

#print axioms inverseTest
end CoefficientMap

namespace HodgeTransport
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182

/-- A commutative square of canonical Hodge maps transports its equality on
actual global sections through the same base morphism. -/
lemma square_section {X Y : Scheme} (b : X ⟶ Y) (H J : Y.Modules) (H' J' : X.Modules)
    (a : H ⟶ J) (a' : H' ⟶ J')
    (E : (Scheme.Modules.pullback b).obj H ≅ H')
    (F : (Scheme.Modules.pullback b).obj J ≅ J')
    (hsq : (Scheme.Modules.pullback b).map a ≫ F.hom = E.hom ≫ a') (s : Γ(H,⊤)) :
    transportSection b J J' F (a.app ⊤ s) = a'.app ⊤ (transportSection b H H' E s) := by
  unfold transportSection
  rw [Scheme.Modules.pullbackLocalSection_app, ← hom_res]
  have h := congrArg (fun f => f.app (b ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection b s)) hsq
  exact congrArg (res J' (by simp)) h

/-- Canonical Hodge power comparisons in a refinement give the full transported
section identity, at every tensor exponent. -/
lemma refinement_section {S K : Type} [CommRing S] [Field K]
    {E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S}
    (W W' : WeierstrassCurve K) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law K W) (G' : ArithmeticThetaRelativeKatoR0169.Law K W')
    (C : ArithmeticThetaOpenHodgeR0180.Test S E K W G)
    (C' : ArithmeticThetaOpenHodgeR0180.Test S E K W' G')
    (ρ : K →+* K) (b : Curve K W' ⟶ Curve K W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange K W G K W' G' ρ b)
    (hm : b ≫ C.map = C'.map)
    (hbase : baseMap S K C'.scalar = baseMap K K ρ ≫ baseMap S K C.scalar)
    (n : ℕ) (d : Γ(power E n,⊤)) :
    pullSection C' n d = transportSection (baseMap K K ρ) _ _
      (hodgePowerIso K W G K W' G' ρ b hb n) (pullSection C n d) :=
  GlobalFamilyDiscriminantR0180.testPull_refinement C C' ρ b hb hm hbase n ⊤ ⊤ ⊤
    (by simp) (by simp) (by simp) d

#print axioms square_section
#print axioms refinement_section
end HodgeTransport


namespace CoefficientMap
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- The canonical target Hodge comparison uses the same coefficient morphism. -/
def hodgeComparison {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (e : K ≃+* K) :
    (Scheme.Modules.pullback (baseMap K K e.toRingHom)).obj (Hodge K W) ≅ Hodge K (W.map e.toRingHom) := by
  letI : Algebra K K := e.toRingHom.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap K W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact pointedDifferentialIso (structureMap K W) (structureMap K (W.map e.toRingHom))
    (map W e.toRingHom) (cartesian W e.toRingHom) (origin K W) (origin K (W.map e.toRingHom))
    (origin_map W e.toRingHom)
end CoefficientMap

namespace HodgeTransport
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182

lemma frame {X Y : Scheme} (b : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (E : (Scheme.Modules.pullback b).obj M ≅ N) (s : Γ(M,⊤)) (hs : IsFrame M ⊤ s) :
    IsFrame N ⊤ (transportSection b M N E s) := by
  exact frame_restrict N (by simp) _
    (GlobalFamilyDiscriminantR0180.frame_iso E _ (pullback_frame b M s hs))

/-- The abstract canonical Hodge square transports a weight-one equation.
All four curves and pointed maps are retained explicitly, avoiding unfolding
concrete Tate coefficients while assembling the square. -/
lemma baseChange_weight_one {A B : Type} [CommRing A] [Field B] [Algebra A B]
    {X Y X' Y' : Scheme} (f : X ⟶ Base A) (g : Y ⟶ Base A)
    (f' : X' ⟶ Base B) (g' : Y' ⟶ Base B)
    [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 g]
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (ha : IsPullback a f' f (baseMap A B (algebraMap A B)))
    (hb : IsPullback b g' g (baseMap A B (algebraMap A B)))
    (p : Base A ⟶ X) (q : Base A ⟶ Y) (p' : Base B ⟶ X') (q' : Base B ⟶ Y')
    (hpa : p' ≫ a = baseMap A B (algebraMap A B) ≫ p)
    (hqb : q' ≫ b = baseMap A B (algebraMap A B) ≫ q)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (hpq : p ≫ φ = q)
    (ψ : X' ⟶ Y') (hψ : ψ ≫ g' = f') (hpq' : p' ≫ ψ = q')
    (hsq : a ≫ φ = ψ ≫ b)
    (ω : Γ((Scheme.Modules.pullback p).obj f.kaehler,⊤))
    (η : Γ((Scheme.Modules.pullback q).obj g.kaehler,⊤))
    (hweight : (PeriodDifferential.pointMap f g φ hφ p q hpq).app ⊤ η = ω) :
    (PeriodDifferential.pointMap f' g' ψ hψ p' q' hpq').app ⊤
      (transportSection (baseMap A B (algebraMap A B)) _ _
        (pointedDifferentialIso g g' b hb q q' hqb) η) =
      transportSection (baseMap A B (algebraMap A B)) _ _
        (pointedDifferentialIso f f' a ha p p' hpa) ω := by
  have H := PeriodDifferential.pointMap_baseChange_naturality f g f' g' a b ha hb p q p' q'
    hpa hqb φ hφ hpq ψ hψ hpq' hsq
  have h := square_section (baseMap A B (algebraMap A B)) _ _ _ _
    (PeriodDifferential.pointMap f g φ hφ p q hpq)
    (PeriodDifferential.pointMap f' g' ψ hψ p' q' hpq')
    (pointedDifferentialIso g g' b hb q q' hqb) (pointedDifferentialIso f f' a ha p p' hpa) H η
  rw [hweight] at h
  exact h.symm

#print axioms baseChange_weight_one
end HodgeTransport


namespace CoefficientMap
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- Typed version of the canonical Hodge comparison through an equality of
coefficient equations; its defining map is still mapOfEq. -/
def hodgeComparisonOfEq {K : Type} [Field K] (W W' : WeierstrassCurve K)
    [W.IsElliptic] (e : K ≃+* K) (h : W.map e.toRingHom = W') :
    (Scheme.Modules.pullback (baseMap K K e.toRingHom)).obj (Hodge K W) ≅ Hodge K W' := by
  letI : Algebra K K := e.toRingHom.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap K W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact pointedDifferentialIso (structureMap K W) (structureMap K W')
    (mapOfEq W W' e.toRingHom h) (cartesian_of_eq W W' e.toRingHom h)
    (origin K W) (origin K W') (origin_of_eq W W' e.toRingHom h)
end CoefficientMap

namespace TwistedQuotient
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182
variable {K : Type} [Field K] (Ws Wt : WeierstrassCurve K) (e : K ≃+* K)
    (hs : Ws.map e.toRingHom = Ws)
    (f : Curve K Ws ⟶ Curve K Wt)
    (hf : f ≫ structureMap K Wt = structureMap K Ws)
    (ho : origin K Ws ≫ f = origin K Wt)

/-- Typed canonical Hodge map of the exact transformed arrow. -/
def hodgeMap : Hodge K (Wt.map e.toRingHom) ⟶ Hodge K Ws :=
  cubicHodgeMap Ws (Wt.map e.toRingHom) (arrow Ws Wt e hs f)
    (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho)

lemma hodgeMap_eq : hodgeMap Ws Wt e hs f hf ho =
    cubicHodgeMap Ws (Wt.map e.toRingHom) (arrow Ws Wt e hs f)
      (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho) := rfl

end TwistedQuotient

namespace CoefficientTarget
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182

variable (k : Type) [Field k] [CharZero k] (r : ℕ)
  [(TateCurve k r).IsElliptic] (β : kˣ)

def generator (δ : CurveFrame k r) :
    Γ(Hodge (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom),⊤) :=
  transportSection (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k β).toRingHom)
    _ _ (CoefficientMap.hodgeComparison (TateCurve k r) (laurentRescale k β)) (hodgeGenerator k r δ)

lemma generator_frame (δ : CurveFrame k r) :
    IsFrame (Hodge (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom)) ⊤
      (generator k r β δ) :=
  HodgeTransport.frame _ _ _ _ _
    (CubicComparison.generator_frame (K := LaurentSeries k)
      (structureMap (LaurentSeries k) (TateCurve k r))
      (origin (LaurentSeries k) (TateCurve k r)) δ)

lemma integral [IsAlgClosed k]
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (heN : Even N) (hmN : m ∣ N)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N))
    (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) (A : OpenPower k m N D a b)
    (hr : 3 ≤ r) (he : Even r)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k)
      ((TateCurve k r).map (laurentRescale k β).toRingHom))
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k)
      ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
    (C : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring A.quotient.target
      (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom) H) :
    ∃ f : PowerSeries k, f ≠ 0 ∧
      algebraMap (PowerSeries k) (LaurentSeries k) f =
        C.scalar A.value * (laurentRescale k β
          (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r)) ^ dExponent N := by
  let C₀ := CoefficientMap.inverseTest (TateCurve k r) (laurentRescale k β) G hG H hH C
  have hv := open_target_integral k m N hm hN heN hmN D a b hab A r hr he G hG C₀
  have hv' := (rescale_integrality_iff k β _).mpr hv
  simpa only [map_mul, map_pow, C₀, CoefficientMap.inverseTest, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] using hv'

set_option maxHeartbeats 400000 in
lemma discriminant {S : Type} [CommRing S]
    (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily S) (hr : 3 ≤ r) (he : Even r)
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
    (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k)
      ((TateCurve k r).map (laurentRescale k β).toRingHom))
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k)
      ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
    (C : ArithmeticThetaOpenHodgeR0180.Test S E (LaurentSeries k)
      ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
    (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ)
    (d : Γ(power E 24,⊤)) (hd : IsD2 E d) :
    pullSection C 24 d =
      scalar (LaurentSeries k) (laurentRescale k β (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r)) •
        tensorPowerSection (Puncture k)
          (Hodge (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom))
          24 ⊤ (generator k r β δ) := by
  let e := laurentRescale k β
  let W := TateCurve k r
  let C₀ := CoefficientMap.inverseTest W e G hG H hH C
  let b := CoefficientMap.map W e.toRingHom
  letI := CoefficientMap.map_isIso W e
  have hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      (LaurentSeries k) W G (LaurentSeries k) (W.map e.toRingHom) H e.toRingHom b :=
    ⟨CoefficientMap.cartesian W e.toRingHom, CoefficientMap.origin_map W e.toRingHom,
      CoefficientMap.multiplication_of_cartesian W (W.map e.toRingHom) G hG H hH
        e.toRingHom b (CoefficientMap.cartesian W e.toRingHom) (CoefficientMap.origin_map W e.toRingHom)⟩
  have hm : b ≫ C₀.map = C.map := by
    dsimp only [C₀, CoefficientMap.inverseTest, b]
    rw [IsIso.hom_inv_id_assoc]
  have hs : baseMap S (LaurentSeries k) C.scalar =
      baseMap (LaurentSeries k) (LaurentSeries k) e.toRingHom ≫ baseMap S (LaurentSeries k) C₀.scalar := by
    unfold baseMap
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (e.apply_symm_apply (C.scalar x)).symm
  have h := HodgeTransport.refinement_section W (W.map e.toRingHom) G H C₀ C
    e.toRingHom b hb hm hs 24 d
  rw [TargetDiscriminant.exact k r hr he E G hG C₀ δ hδ d hd] at h
  have heq : hodgeIso (LaurentSeries k) W G (LaurentSeries k) (W.map e.toRingHom) H
      e.toRingHom b hb = CoefficientMap.hodgeComparison W e := rfl
  unfold hodgePowerIso at h
  rw [heq, transportSection_smul, transportSection_tensor, NormalizedSection.base_scalar] at h
  exact h

#print axioms integral
#print axioms discriminant
end CoefficientTarget

namespace HodgeTransport
open OpenDiscriminantFullTateExpansionR0182

set_option backward.isDefEq.respectTransparency true in
lemma cubic_comp {K : Type} [Field K] (W U T : WeierstrassCurve K) [T.IsElliptic]
    (f : Curve K W ⟶ Curve K U) (hf : f ≫ structureMap K U = structureMap K W)
    (ho : origin K W ≫ f = origin K U)
    (g : Curve K U ⟶ Curve K T) (hg : g ≫ structureMap K T = structureMap K U)
    (hgo : origin K U ≫ g = origin K T) :
    cubicHodgeMap W T (f ≫ g) (by rw [Category.assoc, hg, hf]) (by rw [← Category.assoc, ho, hgo]) =
      cubicHodgeMap U T g hg hgo ≫ cubicHodgeMap W U f hf ho := by
  letI : SmoothOfRelativeDimension 1 (structureMap K T) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one T.toProjective
  exact PeriodDifferential.pointMap_comp (structureMap K W) (structureMap K U) (structureMap K T)
    f hf g hg (origin K W) (origin K U) (origin K T) ho hgo

#print axioms cubic_comp
end HodgeTransport


section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open OpenDiscriminantFullTateExpansionR0182
def cubicHodgeApply {K : Type} [Field K] (W Wt : WeierstrassCurve K)
    (f : Curve K W ⟶ Curve K Wt) (hf : f ≫ structureMap K Wt = structureMap K W)
    (ho : origin K W ≫ f = origin K Wt) (η : Γ(Hodge K Wt,⊤)) : Γ(Hodge K W,⊤) :=
  (cubicHodgeMap W Wt f hf ho).app ⊤ η

namespace CoefficientMap

def transport {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (e : K ≃+* K) (η : Γ(Hodge K W,⊤)) : Γ(Hodge K (W.map e.toRingHom),⊤) :=
  transportSection (baseMap K K e.toRingHom) _ _ (hodgeComparison W e) η
def transportOfEq {K : Type} [Field K] (W W' : WeierstrassCurve K) [W.IsElliptic]
    (e : K ≃+* K) (h : W.map e.toRingHom = W') (ω : Γ(Hodge K W,⊤)) : Γ(Hodge K W',⊤) :=
  transportSection (baseMap K K e.toRingHom) _ _ (hodgeComparisonOfEq W W' e h) ω
end CoefficientMap
namespace CoefficientTarget
set_option maxHeartbeats 100000 in
lemma generator_eq_transport (k : Type) [Field k] [CharZero k] (r : ℕ)
    [(TateCurve k r).IsElliptic] (β : kˣ) (δ : CurveFrame k r) :
    generator k r β δ = CoefficientMap.transport (TateCurve k r) (laurentRescale k β)
      (hodgeGenerator k r δ) := by
  rfl
#print axioms generator_eq_transport
end CoefficientTarget
namespace ParameterFrames
set_option maxHeartbeats 200000 in
lemma transportOfEq_generator {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
    (P : Models.Presentation k r hr) [(TateCurve k r).IsElliptic]
    (β : kˣ) (hβ : (β : k)^r = 1)
    (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    CoefficientMap.transportOfEq (TateCurve k r) (TateCurve k r) (laurentRescale k β)
      (ParameterAction.tateCurve_rescale k β r hr P.even hβ) (hodgeGenerator k r δ) =
      hodgeGenerator k r δ := by
  have heq : CoefficientMap.transportOfEq (TateCurve k r) (TateCurve k r) (laurentRescale k β)
      (ParameterAction.tateCurve_rescale k β r hr P.even hβ) (hodgeGenerator k r δ) =
      transportSection (baseMap (LaurentSeries k) (LaurentSeries k) (laurentRescale k β).toRingHom)
        _ _ (comparison P β hβ) (hodgeGenerator k r δ) := rfl
  exact heq.trans (transport_generator P β hβ δ hδ)
#print axioms transportOfEq_generator
end ParameterFrames

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
lemma cubicHodgeApply_pointMap_743 {K : Type} [Field K] (W Wt : WeierstrassCurve K)
    (f : Curve K W ⟶ Curve K Wt) (hf : f ≫ structureMap K Wt = structureMap K W)
    (ho : origin K W ≫ f = origin K Wt) (η : Γ(Hodge K Wt,⊤)) :
    cubicHodgeApply W Wt f hf ho η =
      (PeriodDifferential.pointMap (K := K) (structureMap K W) (structureMap K Wt)
        f hf (origin K W) (origin K Wt) ho).app ⊤ η := rfl

namespace TwistedQuotient
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182
variable {K : Type} [Field K] (Ws Wt : WeierstrassCurve K) (e : K ≃+* K)
    (hs : Ws.map e.toRingHom = Ws)
    (f : Curve K Ws ⟶ Curve K Wt)
    (hf : f ≫ structureMap K Wt = structureMap K Ws)
    (ho : origin K Ws ≫ f = origin K Wt)
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
lemma weight_one [Ws.IsElliptic] [Wt.IsElliptic]
    (ω : Γ(Hodge K Ws,⊤)) (η : Γ(Hodge K Wt,⊤))
    (hw : (PeriodDifferential.pointMap (structureMap K Ws) (structureMap K Wt) f hf
      (origin K Ws) (origin K Wt) ho).app ⊤ η = ω) :
    cubicHodgeApply Ws (Wt.map e.toRingHom) (arrow Ws Wt e hs f)
      (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho)
      (CoefficientMap.transport Wt e η) =
      CoefficientMap.transportOfEq Ws Ws e hs ω := by
  letI : Algebra K K := e.toRingHom.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap K Ws) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one Ws.toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap K Wt) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one Wt.toProjective
  have h := HodgeTransport.baseChange_weight_one (A := K) (B := K)
    (X := Curve K Ws) (Y := Curve K Wt)
    (X' := Curve K Ws) (Y' := Curve K (Wt.map e.toRingHom))
    (structureMap K Ws) (structureMap K Wt) (structureMap K Ws) (structureMap K (Wt.map e.toRingHom))
    (CoefficientMap.mapOfEq Ws Ws e.toRingHom hs) (CoefficientMap.map Wt e.toRingHom)
    (CoefficientMap.cartesian_of_eq Ws Ws e.toRingHom hs) (CoefficientMap.cartesian Wt e.toRingHom)
    (origin K Ws) (origin K Wt) (origin K Ws) (origin K (Wt.map e.toRingHom))
    (CoefficientMap.origin_of_eq Ws Ws e.toRingHom hs) (CoefficientMap.origin_map Wt e.toRingHom)
    f hf ho (arrow Ws Wt e hs f) (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho)
    (square Ws Wt e hs f).symm ω η (by with_reducible exact hw)
  have ht : CoefficientMap.transport Wt e η =
      transportSection (baseMap K K (algebraMap K K)) _ _
        (pointedDifferentialIso (structureMap K Wt) (structureMap K (Wt.map e.toRingHom))
          (CoefficientMap.map Wt e.toRingHom) (CoefficientMap.cartesian Wt e.toRingHom)
          (origin K Wt) (origin K (Wt.map e.toRingHom)) (CoefficientMap.origin_map Wt e.toRingHom)) η := rfl
  let φ := PeriodDifferential.pointMap (structureMap K Ws) (structureMap K (Wt.map e.toRingHom))
    (arrow Ws Wt e hs f) (arrow_over Ws Wt e hs f hf)
    (origin K Ws) (origin K (Wt.map e.toRingHom)) (origin_arrow Ws Wt e hs f ho)
  have hc : ∀ ξ : Γ(Hodge K (Wt.map e.toRingHom),⊤),
      cubicHodgeApply Ws (Wt.map e.toRingHom) (arrow Ws Wt e hs f)
        (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho) ξ = φ.app ⊤ ξ :=
    fun ξ => cubicHodgeApply_pointMap_743 Ws (Wt.map e.toRingHom) (arrow Ws Wt e hs f)
      (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho) ξ
  apply (hc _).trans
  apply (congrArg (fun ξ => φ.app ⊤ ξ) ht).trans
  split_eval_exact h


#print axioms weight_one
end TwistedQuotient

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace TwistedQuotient
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open OpenDiscriminantFullTateExpansionR0182
variable {k : Type} [Field k]
variable (Ws Wt : WeierstrassCurve (LaurentSeries k)) (e : (LaurentSeries k) ≃+* (LaurentSeries k))
    (hs : Ws.map e.toRingHom = Ws)
    (f : Curve (LaurentSeries k) Ws ⟶ Curve (LaurentSeries k) Wt)
    (hf : f ≫ structureMap (LaurentSeries k) Wt = structureMap (LaurentSeries k) Ws)
    (ho : origin (LaurentSeries k) Ws ≫ f = origin (LaurentSeries k) Wt)
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
lemma weight_one_laurent [Ws.IsElliptic] [Wt.IsElliptic]
    (ω : Γ(Hodge (LaurentSeries k) Ws,⊤)) (η : Γ(Hodge (LaurentSeries k) Wt,⊤))
    (hw : (PeriodDifferential.pointMap (structureMap (LaurentSeries k) Ws) (structureMap (LaurentSeries k) Wt) f hf
      (origin (LaurentSeries k) Ws) (origin (LaurentSeries k) Wt) ho).app ⊤ η = ω) :
    cubicHodgeApply Ws (Wt.map e.toRingHom) (arrow Ws Wt e hs f)
      (arrow_over Ws Wt e hs f hf) (origin_arrow Ws Wt e hs f ho)
      (CoefficientMap.transport Wt e η) =
      CoefficientMap.transportOfEq Ws Ws e hs ω := by
  have h := weight_one Ws Wt e hs f hf ho ω η (by with_reducible exact hw)
  dsimp only [Base, Hodge] at h ⊢
  with_reducible exact h
#print axioms weight_one_laurent
end TwistedQuotient

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace HodgeTransport
open OpenDiscriminantFullTateExpansionR0182
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
lemma twisted_collapse_weight {k : Type} [Field k] [CharZero k]
    {s t : ℕ} {hs : 0 < s} {ht : 0 < t}
    (P : Models.Presentation k s hs) (R : Models.Presentation k t ht)
    [(TateCurve k s).IsElliptic] [(TateCurve k t).IsElliptic]
    (hdiv : t ∣ s) (β : kˣ) (hβ : (β : k)^s = 1)
    (δP : CurveFrame k s) (hδP : ArithmeticThetaBoundaryHodgeR0182.Normalized k s δP)
    (δR : CurveFrame k t) (hδR : ArithmeticThetaBoundaryHodgeR0182.Normalized k t δR) :
    cubicHodgeApply (TateCurve k s) ((TateCurve k t).map (laurentRescale k β).toRingHom)
      (TwistedQuotient.arrow (TateCurve k s) (TateCurve k t) (laurentRescale k β)
        (ParameterAction.tateCurve_rescale k β s hs P.even hβ) (Models.collapse hdiv P R))
      (TwistedQuotient.arrow_over (TateCurve k s) (TateCurve k t) (laurentRescale k β)
        (ParameterAction.tateCurve_rescale k β s hs P.even hβ) (Models.collapse hdiv P R)
        (Models.collapse_over hdiv P R))
      (TwistedQuotient.origin_arrow (TateCurve k s) (TateCurve k t) (laurentRescale k β)
        (ParameterAction.tateCurve_rescale k β s hs P.even hβ) (Models.collapse hdiv P R)
        (Models.collapse_zero hdiv P R))
      (CoefficientMap.transport (TateCurve k t) (laurentRescale k β) (hodgeGenerator k t δR)) = hodgeGenerator k s δP := by
  have hw := Models.collapse_weight hdiv P R δP hδP δR hδR
  have h := TwistedQuotient.weight_one_laurent
    (TateCurve k s) (TateCurve k t) (laurentRescale k β)
    (ParameterAction.tateCurve_rescale k β s hs P.even hβ)
    (Models.collapse hdiv P R) (Models.collapse_over hdiv P R) (Models.collapse_zero hdiv P R)
    (hodgeGenerator k s δP) (hodgeGenerator k t δR) (by with_reducible exact hw)
  have hfinal := h.trans (ParameterFrames.transportOfEq_generator P β hβ δP hδP)
  with_reducible exact hfinal

#print axioms twisted_collapse_weight
end HodgeTransport


end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace Models.Factorization
variable {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
variable {Q : Models.Presentation k r hr} {m : ℕ} {i : Fin r} {a : kˣ}
variable (F : Models.Factorization Q m i a)

def componentMap : Curve (LaurentSeries k) (TateCurve k (r*F.e)) ⟶ Curve (LaurentSeries k) F.equation :=
  TwistedQuotient.arrow (TateCurve k (r*F.e)) (TateCurve k F.t) (laurentRescale k F.beta)
    (ParameterAction.tateCurve_rescale k F.beta (r*F.e) F.positive_s F.intermediate.even F.periodRoot)
    (Models.collapse F.componentDiv F.intermediate F.target)
lemma componentMap_over : F.componentMap ≫ structureMap (LaurentSeries k) F.equation =
    structureMap (LaurentSeries k) (TateCurve k (r*F.e)) :=
  TwistedQuotient.arrow_over _ _ _ _ _ (Models.collapse_over F.componentDiv F.intermediate F.target)
lemma componentMap_origin : ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k (r*F.e)) ≫ F.componentMap =
    ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) F.equation :=
  TwistedQuotient.origin_arrow _ _ _ _ _ (Models.collapse_zero F.componentDiv F.intermediate F.target)
lemma map_eq_components : F.map = Models.toric F.intermediate Q ≫ F.componentMap := rfl
#print axioms map_eq_components
end Models.Factorization

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace Models.Factorization
variable {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
variable {Q : Models.Presentation k r hr} {m : ℕ} {i : Fin r} {a : kˣ}
variable (F : Models.Factorization Q m i a)

set_option maxHeartbeats 400000 in
lemma componentMap_weight [(TateCurve k F.t).IsElliptic]
    (δI : CurveFrame k (r*F.e)) (hδI : ArithmeticThetaBoundaryHodgeR0182.Normalized k (r*F.e) δI)
    (δT : CurveFrame k F.t) (hδT : ArithmeticThetaBoundaryHodgeR0182.Normalized k F.t δT) :
    cubicHodgeApply (TateCurve k (r*F.e)) F.equation F.componentMap F.componentMap_over F.componentMap_origin
      (CoefficientMap.transport (TateCurve k F.t) (laurentRescale k F.beta) (hodgeGenerator k F.t δT)) =
      hodgeGenerator k (r*F.e) δI := by
  letI := TateFullLevelMarking.elliptic k (r*F.e) F.intermediate.three_le F.intermediate.even
  dsimp only [equation, componentMap]
  exact HodgeTransport.twisted_collapse_weight F.intermediate F.target F.componentDiv F.beta F.periodRoot
    δI hδI δT hδT
#print axioms componentMap_weight
end Models.Factorization

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace HodgeTransport
set_option maxHeartbeats 400000 in
lemma cubic_comp_section {K : Type} [Field K] (W U T : WeierstrassCurve K) [T.IsElliptic]
    (f : Curve K W ⟶ Curve K U) (hf : f ≫ structureMap K U = structureMap K W)
    (ho : origin K W ≫ f = origin K U)
    (g : Curve K U ⟶ Curve K T) (hg : g ≫ structureMap K T = structureMap K U)
    (hgo : origin K U ≫ g = origin K T)
    (ω : Γ(Hodge K W,⊤)) (ξ : Γ(Hodge K U,⊤)) (η : Γ(Hodge K T,⊤)) (ζ : Γ(Hodge K W,⊤))
    (hgw : cubicHodgeApply U T g hg hgo η = ξ)
    (hfw : (PeriodDifferential.pointMap (structureMap K W) (structureMap K U)
      f hf (origin K W) (origin K U) ho).app ⊤ ξ = ζ) :
    cubicHodgeApply W T (f ≫ g) (by rw [Category.assoc, hg, hf])
      (by rw [← Category.assoc, ho, hgo]) η = ζ := by
  unfold cubicHodgeApply at hgw ⊢
  rw [cubic_comp W U T f hf ho g hg hgo]
  rw [Scheme.Modules.Hom.comp_app]
  rw [ConcreteCategory.comp_apply]
  rw [hgw]
  rw [cubicHodgeMap_eq W U f hf ho]
  dsimp only [Base, Hodge] at hfw ⊢
  with_reducible exact hfw
#print axioms cubic_comp_section
end HodgeTransport

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace HodgeTransport
set_option maxHeartbeats 400000 in
lemma cubic_comp_section_laurent {k : Type} [Field k] (W U T : WeierstrassCurve (LaurentSeries k)) [T.IsElliptic]
    (f : Curve (LaurentSeries k) W ⟶ Curve (LaurentSeries k) U) (hf : f ≫ structureMap (LaurentSeries k) U = structureMap (LaurentSeries k) W)
    (ho : origin (LaurentSeries k) W ≫ f = origin (LaurentSeries k) U)
    (g : Curve (LaurentSeries k) U ⟶ Curve (LaurentSeries k) T) (hg : g ≫ structureMap (LaurentSeries k) T = structureMap (LaurentSeries k) U)
    (hgo : origin (LaurentSeries k) U ≫ g = origin (LaurentSeries k) T)
    (ω : Γ(Hodge (LaurentSeries k) W,⊤)) (ξ : Γ(Hodge (LaurentSeries k) U,⊤)) (η : Γ(Hodge (LaurentSeries k) T,⊤)) (ζ : Γ(Hodge (LaurentSeries k) W,⊤))
    (hgw : cubicHodgeApply U T g hg hgo η = ξ)
    (hfw : (PeriodDifferential.pointMap (structureMap (LaurentSeries k) W) (structureMap (LaurentSeries k) U)
      f hf (origin (LaurentSeries k) W) (origin (LaurentSeries k) U) ho).app ⊤ ξ = ζ) :
    cubicHodgeApply W T (f ≫ g) (by rw [Category.assoc, hg, hf])
      (by rw [← Category.assoc, ho, hgo]) η = ζ := by
  have h := cubic_comp_section W U T f hf ho g hg hgo ω ξ η ζ hgw (by with_reducible exact hfw)
  dsimp only [Base, Hodge] at h ⊢
  with_reducible exact h
#print axioms cubic_comp_section_laurent
end HodgeTransport

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace HodgeTransport
set_option maxHeartbeats 400000 in
lemma cubic_comp_section_arrow {k : Type} [Field k] (W U T : WeierstrassCurve (LaurentSeries k)) [T.IsElliptic]
    (f : Curve (LaurentSeries k) W ⟶ Curve (LaurentSeries k) U) (hf : f ≫ structureMap (LaurentSeries k) U = structureMap (LaurentSeries k) W)
    (ho : origin (LaurentSeries k) W ≫ f = origin (LaurentSeries k) U)
    (g : Curve (LaurentSeries k) U ⟶ Curve (LaurentSeries k) T) (hg : g ≫ structureMap (LaurentSeries k) T = structureMap (LaurentSeries k) U)
    (hgo : origin (LaurentSeries k) U ≫ g = origin (LaurentSeries k) T)
    (ψ : Curve (LaurentSeries k) W ⟶ Curve (LaurentSeries k) T)
    (hψ : ψ ≫ structureMap (LaurentSeries k) T = structureMap (LaurentSeries k) W)
    (hψo : origin (LaurentSeries k) W ≫ ψ = origin (LaurentSeries k) T)
    (hcomp : ψ = f ≫ g)
    (ω : Γ(Hodge (LaurentSeries k) W,⊤)) (ξ : Γ(Hodge (LaurentSeries k) U,⊤)) (η : Γ(Hodge (LaurentSeries k) T,⊤)) (ζ : Γ(Hodge (LaurentSeries k) W,⊤))
    (hgw : cubicHodgeApply U T g hg hgo η = ξ)
    (hfw : (PeriodDifferential.pointMap (structureMap (LaurentSeries k) W) (structureMap (LaurentSeries k) U)
      f hf (origin (LaurentSeries k) W) (origin (LaurentSeries k) U) ho).app ⊤ ξ = ζ) :
    cubicHodgeApply W T ψ hψ hψo η = ζ := by
  subst ψ
  exact cubic_comp_section_laurent W U T f hf ho g hg hgo ω ξ η ζ hgw hfw
#print axioms cubic_comp_section_arrow
end HodgeTransport

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
namespace Models.Factorization
open OpenDiscriminantFullTateExpansionR0182
variable {k : Type} [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
variable {Q : Models.Presentation k r hr} {m : ℕ} {i : Fin r} {a : kˣ}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
lemma weight (F : Models.Factorization Q m i a) [(TateCurve k F.t).IsElliptic]
    (δQ : CurveFrame k r) (hδQ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δQ)
    (δT : CurveFrame k F.t) (hδT : ArithmeticThetaBoundaryHodgeR0182.Normalized k F.t δT) :
    cubicHodgeApply (TateCurve k r) F.equation F.map F.map_over F.origin
      (CoefficientMap.transport (TateCurve k F.t) (laurentRescale k F.beta) (hodgeGenerator k F.t δT)) =
      scalar (LaurentSeries k) (F.e : LaurentSeries k) • hodgeGenerator k r δQ := by
  letI : F.equation.IsElliptic := by unfold Models.Factorization.equation; infer_instance
  letI := TateFullLevelMarking.elliptic k (r*F.e) F.intermediate.three_le F.intermediate.even
  obtain ⟨δI, hδI⟩ := CubicComparison.normalized_tate_frame k (r*F.e)
    F.intermediate.three_le F.intermediate.even
  have hwg := F.componentMap_weight δI hδI δT hδT
  have hwf := Models.toric_weight F.positive_e F.intermediate Q δI hδI δQ hδQ
  have h := HodgeTransport.cubic_comp_section_arrow
    (TateCurve k r) (TateCurve k (r*F.e)) F.equation
    (Models.toric F.intermediate Q) (Models.toric_over F.intermediate Q)
    (Models.toric_zero F.positive_e F.intermediate Q)
    F.componentMap F.componentMap_over F.componentMap_origin F.map F.map_over F.origin F.map_eq_components
    (hodgeGenerator k r δQ) (hodgeGenerator k (r*F.e) δI)
    (CoefficientMap.transport (TateCurve k F.t) (laurentRescale k F.beta) (hodgeGenerator k F.t δT))
    (scalar (LaurentSeries k) (F.e : LaurentSeries k) • hodgeGenerator k r δQ) hwg (by with_reducible exact hwf)
  with_reducible exact h

#print axioms weight
end Models.Factorization

end

section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
section CoefficientComparison
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
/- The analytic consumer for an actual quotient comparison. Constructing the
comparison and proving its constant differential factor at an arbitrary cusp
remain separate geometric obligations; this conditional lemma is not the
all-cusp theorem. -/
variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
variable (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (heN : Even N) (hmN : m ∣ N)
variable (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N))
variable (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) (A : OpenPower k m N D a b)
variable (V : ArithmeticThetaBoundaryHodgeR0182.Test k (level N) D)
variable (r : ℕ) (hr : 3 ≤ r) (heven : Even r)
variable [(TateCurve k r).IsElliptic] (β : kˣ)
variable (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (TateCurve k r))
variable (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (TateCurve k r) G)
variable (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k)
  ((TateCurve k r).map (laurentRescale k β).toRingHom))
variable (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k)
  ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
variable (C : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring A.quotient.target
      (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom) H)
variable (hscalar : C.scalar = (Spec.preimage (V.base ≫ D.quotient.inclusion)).hom)
variable (ψ : Curve (LaurentSeries k) (TateCurve k (level N)) ⟶
      Curve (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom))
variable (hψ : ψ ≫ structureMap (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom) =
      structureMap (LaurentSeries k) (TateCurve k (level N)))
variable (hψo : origin (LaurentSeries k) (TateCurve k (level N)) ≫ ψ =
      origin (LaurentSeries k) ((TateCurve k r).map (laurentRescale k β).toRingHom))
variable (hψmap : V.map ≫ A.quotient.arrow.map = ψ ≫ C.map)
variable (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ)
variable (μ : k) (hμ : μ ≠ 0)
variable (hweight : cubicHodgeApply (TateCurve k (level N)) ((TateCurve k r).map (laurentRescale k β).toRingHom)
      ψ hψ hψo
      (CoefficientMap.transport (TateCurve k r) (laurentRescale k β) (hodgeGenerator k r δ)) = scalar (LaurentSeries k) (HahnSeries.C μ) •
        hodgeGenerator k (level N) V.differential)

include hm hN heN hmN hab hr heven hG hH hscalar hψmap hδ hμ hweight in
lemma integral_of_coefficient_comparison : IntegralAtTest k m N A V := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  let Cs := OpenDiscriminantFullTateExpansionR0182.affineTest k (level N) V
  let coef : D.atlas.quotient.ring :=
    (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)^(weight N)*A.value
  have hcoef : (baseMap D.atlas.quotient.ring (LaurentSeries k) Cs.scalar).appLE
      ⊤ ⊤ (by simp) (scalar D.atlas.quotient.ring coef) =
      scalar (LaurentSeries k) (((m : LaurentSeries k)⁻¹)^(weight N)*(Cs.scalar A.value)) := by
    rw [NormalizedSection.base_scalar]
    congr 1
    dsimp only [coef]
    rw [map_mul, map_pow]
    congr 2
    exact (map_inv₀ (Cs.scalar.comp (algebraMap k D.atlas.quotient.ring)) (m : k)).trans
      (congrArg Inv.inv (by simp))
  have hD := CoefficientTarget.discriminant k r β A.quotient.target hr heven G hG H hH C δ hδ
    A.discriminant A.intrinsic
  have hη := CoefficientTarget.generator_frame k r β δ
  obtain ⟨E, hE, hED⟩ := TateTorsionNormalizedIntegrality.discriminant_factor k r (by omega)
  have hpure : ArithmeticThetaUnaryKatoPowerR0160.discriminant k r ≠ 0 := by
    rw [hED]
    apply mul_ne_zero
    · exact pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)
    · exact pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))).mpr hE)
  have hΔ : laurentRescale k β (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) ≠ 0 :=
    (map_ne_zero_iff _ (laurentRescale k β).injective).mpr hpure
  have hμK : (HahnSeries.C μ : LaurentSeries k) ≠ 0 := by
    exact HahnSeries.single_ne_zero hμ
  have hf0 := test_formula_differential_factor (S := D.atlas.quotient.ring)
    D.atlas.descent.family A.quotient.target A.quotient.arrow
    (LaurentSeries k) (TateCurve k (level N)) ((TateCurve k r).map (laurentRescale k β).toRingHom)
    V.level.law H Cs C hscalar ψ hψ hψo hψmap
  have hf1 := hf0 (dExponent N) (weight N)
    (OpenLevelNormalizedHodgePowerR0180.exponents N heN).2
    A.discriminant A.section_ (scalar D.atlas.quotient.ring coef)
  have hf2 := hf1 A.normalized
  have hf3 := hf2 (CoefficientTarget.generator k r β δ) (hodgeGenerator k (level N) V.differential) hη
    (HahnSeries.C μ) (m : LaurentSeries k)⁻¹
    (laurentRescale k β (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r)) (Cs.scalar A.value)
    hμK hΔ hcoef
  have hf := hf3 hD (by
    rw [CoefficientTarget.generator_eq_transport k r β δ]
    dsimp only [cubicHodgeApply, cubicHodgeMap] at hweight
    with_reducible exact hweight)
  have hv := CoefficientTarget.integral k r β m N hm hN heN hmN D a b hab A hr heven G hG H hH C
  rw [hscalar] at hv
  have hmK : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  obtain ⟨f, hf0, hfv⟩ := integral_constant_factor k (μ*(m : k)⁻¹)
    (mul_ne_zero hμ (inv_ne_zero hmK)) (weight N) _ hv
  refine ⟨f, hf0, ?_⟩
  have hconst : (HahnSeries.C (μ*(m : k)⁻¹) : LaurentSeries k) =
      HahnSeries.C μ * (m : LaurentSeries k)⁻¹ := by
    rw [map_mul, map_inv₀, map_natCast]
  rw [hconst, ← mul_assoc] at hfv
  rw [hfv]
  exact (OpenDiscriminantFullTateExpansionR0182.pullAmbientPower_eq_pullSection
    k (level N) V (weight N) A.section_).trans hf

end CoefficientComparison
#print axioms integral_of_coefficient_comparison

end

end ArithmeticThetaCompactUnaryR0183.AllCuspNormalizedPowerIntegrality

section
set_option backward.isDefEq.respectTransparency true
namespace ArithmeticThetaCompactUnaryR0183
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open AllCuspNormalizedPowerIntegrality

set_option maxHeartbeats 800000 in
/-- The same normalized open section has a full nonzero integral coefficient
at every actual boundary test, with arbitrary marking. -/
theorem all_cusp_normalized_power_integrality
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (level N)) (a b : Fin N)
    (hab : a.val ≠ 0 ∨ b.val ≠ 0) (A : OpenPower k m N D a b)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k (level N) D) : IntegralAtTest k m N A V := by
  obtain ⟨hL, h3, he, hmL, hb, heb⟩ := EveryTestGeometry.level_bounds m N hm hN hmN
  obtain ⟨P, i, c, F, H, hH, C, hscalar, hmap⟩ := EveryTestGeometry.comparison_exists
    k (level N) hL h3 he m hm hmL hb heb D V A.quotient
  letI := TateFullLevelMarking.elliptic k F.t F.target.three_le F.target.even
  obtain ⟨δ, hδ⟩ := CubicComparison.normalized_tate_frame k F.t F.target.three_le F.target.even
  have hw := F.weight V.differential V.normalized δ hδ
  have he0 : (F.e : k) ≠ 0 := Nat.cast_ne_zero.mpr F.positive_e.ne'
  apply integral_of_coefficient_comparison k m N hm hN hNeven hmN D a b hab A V
    F.t F.target.three_le F.target.even F.beta (Models.cubicLaw F.target)
    (Models.cubicLaw_origin F.target) H hH C hscalar F.map F.map_over F.origin hmap
    δ hδ (F.e : k) he0
  simpa only [Models.Factorization.equation, map_natCast] using hw

#print axioms all_cusp_normalized_power_integrality
end ArithmeticThetaCompactUnaryR0183

end
