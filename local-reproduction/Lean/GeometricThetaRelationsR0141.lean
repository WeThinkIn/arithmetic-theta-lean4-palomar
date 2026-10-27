import GeometricScalarLiftR0141
import GeometricShiftLiftR0141
import GeometricInversionLiftR0141

/-! Relations for the genuine pullback actions on all generic dual sections. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
noncomputable section
universe u
namespace ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open GenericThetaBasisR0140

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
  (s : baseScheme k ⟶ M.X) (d : ℕ)

local instance : AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

abbrev sc (c : LaurentSeries k) (φ : GenericDual k M s d) :=
  scale (scalarAt k M ⊤ c) φ

lemma sc_app (c : LaurentSeries k) (φ : GenericDual k M s d)
    (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)) :
    (sc k M s d c φ).app U x = scalarHom k M U c *
      (show Γ(genericScheme k M, U) from φ.app U x) :=
  GeometricShiftLiftR0141.scale_scalarAt_app k M s d c φ U x

lemma sc_one (φ : GenericDual k M s d) : sc k M s d 1 φ = φ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rw [sc_app, map_one, one_mul]
  rfl

lemma sc_mul (a b : LaurentSeries k) (φ : GenericDual k M s d) :
    sc k M s d a (sc k M s d b φ) = sc k M s d (a*b) φ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rw [sc_app]
  erw [sc_app]
  rw [sc_app, map_mul, mul_assoc]

lemma sc_sum (m : ℕ) (c : LaurentSeries k) (φ : Fin m → GenericDual k M s d) :
    sc k M s d c (∑ ν, φ ν) = ∑ ν, sc k M s d c (φ ν) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rw [sum_app, sc_app, sum_app]
  change scalarHom k M U c * (∑ ν, (show Γ(genericScheme k M, U) from (φ ν).app U x)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  exact (sc_app k M s d c (φ ν) U x).symm

lemma scaled_iff (c : LaurentSeries k) (φ ψ : GenericDual k M s d) :
    ScaledEq k M s d c φ ψ ↔ ψ = sc k M s d c φ := by
  constructor
  · intro h
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    exact (h U x).symm.trans (sc_app k M s d c φ U x).symm
  · intro h U x
    rw [h]
    exact (sc_app k M s d c φ U x).symm

/-- The two properties used to extend identities, with the actual structural scalars. -/
structure LinearAction (m : ℕ) (F : GenericDual k M s d → GenericDual k M s d) : Prop where
  sum : ∀ v : Fin m → GenericDual k M s d, F (∑ ν, v ν) = ∑ ν, F (v ν)
  scale : ∀ c φ, F (sc k M s d c φ) = sc k M s d c (F φ)

variable {k M s d}
lemma linear_id (m : ℕ) : LinearAction k M s d m id := ⟨fun _ => rfl, fun _ _ => rfl⟩

lemma linear_comp {m : ℕ} {F G : GenericDual k M s d → GenericDual k M s d}
    (hF : LinearAction k M s d m F) (hG : LinearAction k M s d m G) :
    LinearAction k M s d m (fun φ => F (G φ)) := by
  constructor
  · intro v
    rw [hG.sum, hF.sum]
  · intro c φ
    rw [hG.scale, hF.scale]

lemma linear_iterate {m : ℕ} {F : GenericDual k M s d → GenericDual k M s d}
    (hF : LinearAction k M s d m F) (n : ℕ) : LinearAction k M s d m (F^[n]) := by
  induction n with
  | zero => exact linear_id m
  | succ n ih =>
    rw [Function.iterate_succ']
    exact linear_comp (F := F) (G := F^[n]) hF ih

lemma linear_scale (m : ℕ) (a : LaurentSeries k) :
    LinearAction k M s d m (sc k M s d a) := by
  constructor
  · exact sc_sum k M s d m a
  · intro c φ
    rw [sc_mul, sc_mul, mul_comm a c]

lemma linear_act (m : ℕ) (f : genericScheme k M ⟶ genericScheme k M)
    (hf : f ≫ genericStructure k M = genericStructure k M) (e : Lift k M s d f) :
    LinearAction k M s d m (act k M s d f e) :=
  ⟨GeometricScalarLiftR0141.act_sum k M s d m f e,
    GeometricScalarLiftR0141.act_scale k M s d f hf e⟩

lemma extend {m : ℕ} (b : Fin m → GenericDual k M s d) (hb : HasBasis k M s d m b)
    {F G : GenericDual k M s d → GenericDual k M s d}
    (hF : LinearAction k M s d m F) (hG : LinearAction k M s d m G)
    (h : ∀ ν, F (b ν) = G (b ν)) (φ : GenericDual k M s d) : F φ = G φ := by
  obtain ⟨c, hc, _⟩ := hb φ
  rw [GeometricScalarLiftR0141.combines_eq k M s d m b c φ hc, hF.sum, hG.sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [hF.scale, hG.scale, h ν]

variable (k)
lemma phase_pow (ζ : kˣ) (n : ℕ) : phase k ζ n = (phase k ζ 1)^n := by
  simp only [phase, pow_one, map_pow]

lemma phase_period (m : ℕ) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) m) :
    (phase k ζ 1)^m = 1 := by
  rw [← phase_pow]
  simp [phase, hζ.pow_eq_one]

lemma phase_next (m : ℕ) (hm : 0 < m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m) (ν : Fin m) :
    phase k ζ (next m hm ν).val = phase k ζ 1 * phase k ζ ν.val := by
  rw [phase_pow k ζ (next m hm ν).val, phase_pow k ζ ν.val]
  have hp := phase_period k m ζ hζ
  change (phase k ζ 1)^((ν.val+1)%m) = _
  rw [← pow_eq_pow_mod _ hp, pow_succ, mul_comm]

lemma neg_neg (m : ℕ) (hm : 0 < m) (ν : Fin m) :
    negIndex m hm (negIndex m hm ν) = ν := by
  apply Fin.ext
  dsimp [negIndex]
  have hn := ν.isLt
  by_cases h : ν.val = 0
  · simp [h]
  · rw [Nat.mod_eq_of_lt (show m - ν.val < m by omega)]
    rw [Nat.sub_sub_self (by omega), Nat.mod_eq_of_lt hn]

lemma neg_next_neg_next (m : ℕ) (hm : 0 < m) (ν : Fin m) :
    negIndex m hm (next m hm (negIndex m hm (next m hm ν))) = ν := by
  apply Fin.ext
  dsimp [negIndex, next]
  have hn := ν.isLt
  by_cases h1 : m = 1
  · subst m
    simp
  have h2 : 1 < m := by omega
  by_cases h : ν.val + 1 = m
  · rw [h]
    simp only [Nat.mod_self, Nat.sub_zero, Nat.zero_add, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt (show m-1 < m by omega)]
    omega
  have hv : ν.val+1 < m := by omega
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (show m-(ν.val+1) < m by omega)]
  by_cases hz : ν.val = 0
  · simp [hz, Nat.sub_add_cancel (show 1 ≤ m by omega)]
  have hx : m-(ν.val+1)+1 < m := by omega
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show m-(m-(ν.val+1)+1) < m by omega)]
  omega

lemma phase_neg_mul (m : ℕ) (hm : 0 < m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m) (ν : Fin m) :
    phase k ζ ν.val * phase k ζ (negIndex m hm ν).val = 1 := by
  rw [phase_pow k ζ ν.val, phase_pow k ζ (negIndex m hm ν).val]
  change (phase k ζ 1)^ν.val * (phase k ζ 1)^((m-ν.val)%m) = 1
  rw [← pow_eq_pow_mod _ (phase_period k m ζ hζ), ← pow_add,
    Nat.add_sub_of_le (Nat.le_of_lt ν.isLt), phase_period k m ζ hζ]

variable (M s)
/-- Basis identities extend using the verified linearity of the original maps. -/
lemma relations_of_basis (m : ℕ) (hm : 0 < m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m)
    (b : Fin m → GenericDual k M s m) (hb : HasBasis k M s m m b)
    (A B S : GenericDual k M s m → GenericDual k M s m)
    (hA : LinearAction k M s m m A) (hB : LinearAction k M s m m B)
    (hS : LinearAction k M s m m S)
    (a : ∀ ν, A (b ν) = sc k M s m (phase k ζ ν.val) (b ν))
    (bb : ∀ ν, B (b ν) = b (next m hm ν))
    (ss : ∀ ν, S (b ν) = b (negIndex m hm ν)) : Relations k M s m ζ A B S := by
  have ai (n : ℕ) (ν : Fin m) :
      (A^[n]) (b ν) = sc k M s m ((phase k ζ ν.val)^n) (b ν) := by
    induction n with
    | zero => exact (sc_one k M s m (b ν)).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hA.scale, a, sc_mul, pow_succ]
  have bi (n : ℕ) (ν : Fin m) : (B^[n]) (b ν) = b ((next m hm)^[n] ν) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, bb, Function.iterate_succ_apply']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply extend b hb (linear_iterate hA m) (linear_id m)
    intro ν
    rw [ai, phase_pow k ζ ν.val, ← pow_mul, Nat.mul_comm ν.val m, pow_mul,
      phase_period k m ζ hζ, one_pow, sc_one]
    rfl
  · apply extend b hb (linear_iterate hB m) (linear_id m)
    intro ν
    rw [bi, AlgebraizedActionLawsR0137.next_period]
    rfl
  · intro φ
    apply (scaled_iff k M s m _ _ _).mpr
    apply extend b hb (linear_comp (F := A) (G := B) hA hB)
      (linear_comp (F := sc k M s m (phase k ζ 1)) (G := fun φ => B (A φ))
        (linear_scale m _) (linear_comp (F := B) (G := A) hB hA)) ?_ φ
    intro ν
    rw [bb, a, a, hB.scale, bb, sc_mul, phase_next k m hm ζ hζ]
  · apply extend b hb (linear_comp (F := S) (G := S) hS hS) (linear_id m)
    intro ν
    rw [ss, ss, neg_neg]
    rfl
  · apply extend b hb
      (linear_comp (F := S) (G := fun φ => A (S (A φ))) hS
        (linear_comp (F := A) (G := fun φ => S (A φ)) hA
          (linear_comp (F := S) (G := A) hS hA))) (linear_id m)
    intro ν
    rw [a, hS.scale, ss, hA.scale, a, hS.scale, hS.scale, ss,
      neg_neg, sc_mul, phase_neg_mul k m hm ζ hζ, sc_one]
    rfl
  · apply extend b hb
      (linear_comp (F := S) (G := fun φ => B (S (B φ))) hS
        (linear_comp (F := B) (G := fun φ => S (B φ)) hB
          (linear_comp (F := S) (G := B) hS hB))) (linear_id m)
    intro ν
    rw [bb, ss, bb, ss, neg_next_neg_next]
    rfl

end ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141

namespace ArithmeticThetaGeometricLiftsR0141
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140
open GeometricThetaRelationsR0141
/-- The normalized geometric theta lifts satisfy the full operator relations
on every actual generic dual section. -/
theorem geometric_theta_relations :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∀ (eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ∀ (eS : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Relations k M s m ζ (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA) (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB) (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ eA eB hA hB eS hS
  apply relations_of_basis k M s m hm ζ hζ
    (genericTheta k m hm he M hM s hs)
    (generic_theta_basis k m hm he T M hM s hs)
  · exact linear_act m _ (GeometricScalarLiftR0141.scalarMap_over k M rot scal inv ha ζ) eA
  · exact linear_act m _ (GeometricShiftLiftR0141.shiftMap_structure k M rot scal inv ha) eB
  · exact linear_act m _ (GeometricInversionLiftR0141.inversionMap_structure k M rot scal inv ha) eS
  · intro ν
    exact (scaled_iff k M s m _ _ _).mp (hA ν)
  · exact hB
  · exact hS
end ArithmeticThetaGeometricLiftsR0141
#print axioms ArithmeticThetaGeometricLiftsR0141.geometric_theta_relations
