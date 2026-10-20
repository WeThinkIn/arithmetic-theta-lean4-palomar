module

public import SymmetricMarkingDefinitionsR0142

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaSymmetricMarkingR0142.FiniteSignMarkingRealizationR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaModelSymmetriesR0137
open GenericThetaBasisR0140 GeometricThetaRelationsR0141

open GeometricShiftLiftR0141.RawAction

lemma scaleHom_precomp {X : Scheme.{u}} {F G H : X.Modules} (a : Γ(X, ⊤))
    (f : F ⟶ G) (g : G ⟶ H) : f ≫ scaleHom a g = scaleHom a (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, scaleHom_app]

def signedIso {X : Scheme.{u}} {F G : X.Modules} (a : Γ(X, ⊤))
    (ha : a*a=1) (e : F ≅ G) : F ≅ G where
  hom := scaleHom a e.hom
  inv := scaleHom a e.inv
  hom_inv_id := by
    rw [scaleHom_comp, scaleHom_precomp, scaleHom_mul, e.hom_inv_id, ha, scaleHom_one]
  inv_hom_id := by
    rw [scaleHom_comp, scaleHom_precomp, scaleHom_mul, e.inv_hom_id, ha, scaleHom_one]

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ)

lemma constant_mul (a b : k) : constant k (a*b) = constant k a * constant k b := by
  simp only [constant, map_mul]
lemma constant_one : constant k 1 = 1 := by simp [constant]
lemma constant_pow (a : k) (n : ℕ) : constant k (a^n) = (constant k a)^n := by
  simp only [constant, map_pow]
lemma constant_sq (a : k) (ha : a^2=1) : constant k a * constant k a = 1 := by
  rw [← constant_mul, ← pow_two, ha, constant_one]

lemma scalar_restrict (c : LaurentSeries k) (U : (genericScheme k M).Opens) :
    (genericScheme k M).presheaf.map (homOfLE le_top).op (scalarAt k M ⊤ c) =
      scalarAt k M U c := by
  rw [GeometricShiftLiftR0141.scalarAt_top]
  rfl

lemma scalar_square (a : k) (ha : a^2=1) :
    scalarAt k M ⊤ (constant k a) * scalarAt k M ⊤ (constant k a) = 1 := by
  change scalarHom k M ⊤ (constant k a) * scalarHom k M ⊤ (constant k a) = 1
  rw [← map_mul, constant_sq k a ha, map_one]

def signedLift (f : genericScheme k M ⟶ genericScheme k M)
    (e : Lift k M s d f) (a : k) (ha : a^2=1) : Lift k M s d f :=
  signedIso (scalarAt k M ⊤ (constant k a)) (scalar_square k M a ha) e

lemma signedLift_scaled (f : genericScheme k M ⟶ genericScheme k M)
    (e : Lift k M s d f) (a : k) (ha : a^2=1) :
    LiftScaled k M s d f (constant k a) e (signedLift k M s d f e a ha) := by
  intro U x
  change (scaleHom _ e.hom).app U x = _
  rw [scaleHom_app, scalar_restrict]

lemma scaled_unique (f : genericScheme k M ⟶ genericScheme k M)
    (e e' e'' : Lift k M s d f) (a : LaurentSeries k)
    (h' : LiftScaled k M s d f a e e') (h'' : LiftScaled k M s d f a e e'') : e' = e'' := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact (h' U x).trans (h'' U x).symm

lemma signedLift_act (f : genericScheme k M ⟶ genericScheme k M)
    (e : Lift k M s d f) (a : k) (ha : a^2=1) (φ : GenericDual k M s d) :
    act k M s d f (signedLift k M s d f e a ha) φ =
      sc k M s d (constant k a) (act k M s d f e φ) := by
  unfold act signedLift signedIso
  rw [scaleHom_comp, scaleHom_dual]

lemma sign_period (m : ℕ) (he : Even m) (a : k) (ha : a^2=1) : a^m=1 := by
  obtain ⟨n, hn⟩ := he
  rw [hn, ← two_mul, pow_mul, ha, one_pow]

lemma sign_nonzero (a : k) (ha : a^2=1) : a ≠ 0 := by
  intro h
  simp [h] at ha

lemma sign_residue (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m) (a : k) (ha : a^2=1) :
    ∃ j : Fin m, (ζ : k)^j.val = a ∧ (j.val+j.val)%m=0 := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨i, hi, hia⟩ := hζ.eq_pow_of_pow_eq_one (sign_period k m he a ha)
  refine ⟨⟨i,hi⟩, hia, ?_⟩
  apply hζ.pow_inj (Nat.mod_lt _ hm) hm
  rw [← pow_eq_pow_mod _ hζ.pow_eq_one, pow_add, hia, ← pow_two, ha, pow_zero]

lemma shift_involution (m : ℕ) (hm : 0 < m) (j : Fin m)
    (hj : (j.val+j.val)%m=0) : Function.Involutive (shiftIndex m hm j) := by
  intro ν
  apply Fin.ext
  dsimp [shiftIndex]
  rw [Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_mod_mod, hj, Nat.add_zero,
    Nat.mod_eq_of_lt ν.isLt]

lemma shift_next (m : ℕ) (hm : 0 < m) (j ν : Fin m) :
    shiftIndex m hm j (next m hm ν) = next m hm (shiftIndex m hm j ν) := by
  apply Fin.ext
  dsimp [shiftIndex, next]
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

lemma shift_neg (m : ℕ) (hm : 0 < m) (j ν : Fin m)
    (hj : (j.val+j.val)%m=0) :
    shiftIndex m hm j (negIndex m hm ν) = negIndex m hm (shiftIndex m hm j ν) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hjj : j+j = (0 : Fin m) := Fin.ext hj
  have hjneg : -j = j := (eq_neg_of_add_eq_zero_left hjj).symm
  change -ν+j = -(ν+j)
  rw [neg_add, hjneg]

lemma sign_next (m : ℕ) (hm : 0 < m) (he : Even m)
    (a : k) (ha : a^2=1) (ν : Fin m) :
    a^(next m hm ν).val = a^ν.val*a := by
  change a^((ν.val+1)%m) = _
  rw [← pow_eq_pow_mod _ (sign_period k m he a ha), pow_succ]

lemma sign_neg (m : ℕ) (hm : 0 < m) (he : Even m)
    (a : k) (ha : a^2=1) (ν : Fin m) :
    a^(negIndex m hm ν).val = a^ν.val := by
  have ha0 := sign_nonzero k a ha
  have h1 : a^ν.val * a^(negIndex m hm ν).val = 1 := by
    change a^ν.val * a^((m-ν.val)%m) = 1
    rw [← pow_eq_pow_mod _ (sign_period k m he a ha), ← pow_add,
      Nat.add_sub_of_le (Nat.le_of_lt ν.isLt), sign_period k m he a ha]
  have h2 : a^ν.val * a^ν.val=1 := by
    rw [← mul_pow, ← pow_two, ha, one_pow]
  exact mul_left_cancel₀ (pow_ne_zero _ ha0) (h1.trans h2.symm)

local instance : AddCommGroup (GenericDual k M s d) :=
  inferInstanceAs (AddCommGroup (genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)))

def coordinateChange (m : ℕ) (t : Fin m → Fin m) (ht : Function.Involutive t)
    (a : Fin m → LaurentSeries k) (ha : ∀ ν, a ν * a ν = 1) :
    (Fin m → LaurentSeries k) ≃ (Fin m → LaurentSeries k) where
  toFun c ν := c (t ν) * a (t ν)
  invFun c ν := c (t ν) * a ν
  left_inv c := by funext ν; simp only [ht ν, mul_assoc, ha, mul_one]
  right_inv c := by funext ν; simp only [ht ν, mul_assoc, ha, mul_one]

lemma basis_rephase (m : ℕ) (b : Fin m → GenericDual k M s d)
    (hb : HasBasis k M s d m b) (t : Fin m → Fin m) (ht : Function.Involutive t)
    (a : Fin m → LaurentSeries k) (ha : ∀ ν, a ν * a ν=1) :
    HasBasis k M s d m (fun ν => sc k M s d (a ν) (b (t ν))) := by
  let E := coordinateChange k m t ht a ha
  have hc (c : Fin m → LaurentSeries k) (φ : GenericDual k M s d) :
      Combines k M s d m (fun ν => sc k M s d (a ν) (b (t ν))) c φ ↔
        Combines k M s d m b (E c) φ := by
    rw [GeometricShiftLiftR0141.combines_iff, GeometricShiftLiftR0141.combines_iff]
    have hsum : (∑ ν, sc k M s d (c ν) (sc k M s d (a ν) (b (t ν)))) =
        ∑ ν, sc k M s d (E c ν) (b ν) := by
      simp only [sc_mul]
      apply Fintype.sum_equiv (ht.toPerm t)
      intro ν
      change sc k M s d (c ν * a ν) (b (t ν)) =
        sc k M s d (c (t (t ν)) * a (t (t ν))) (b (t ν))
      rw [ht ν]
    rw [hsum]
  intro φ
  obtain ⟨c, hc', hu⟩ := hb φ
  refine ⟨E.symm c, (hc _ _).mpr ?_, ?_⟩
  · simpa only [E.apply_symm_apply] using hc'
  · intro v hv
    apply E.injective
    rw [E.apply_symm_apply]
    exact hu _ ((hc _ _).mp hv)

lemma phase_shift (m : ℕ) (hm : 0 < m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m) (j ν : Fin m) (ε : k)
    (hj : (ζ : k)^j.val=ε) :
    phase k ζ (shiftIndex m hm j ν).val = phase k ζ ν.val * constant k ε := by
  change constant k ((ζ : k)^((ν.val+j.val)%m)) = _
  rw [← pow_eq_pow_mod _ hζ.pow_eq_one, pow_add, hj, constant_mul]
  rfl

lemma phase_shift_sign (m : ℕ) (hm : 0 < m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) m) (j ν : Fin m) (ε : k)
    (hj : (ζ : k)^j.val=ε) (hε : ε^2=1) :
    constant k ε * phase k ζ (shiftIndex m hm j ν).val = phase k ζ ν.val := by
  rw [phase_shift k m hm ζ hζ j ν ε hj, mul_left_comm,
    constant_sq k ε hε, mul_one]

end ArithmeticThetaSymmetricMarkingR0142.FiniteSignMarkingRealizationR0142


namespace ArithmeticThetaSymmetricMarkingR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaModelSymmetriesR0137
open GenericThetaBasisR0140 GeometricThetaRelationsR0141
open FiniteSignMarkingRealizationR0142

/-- Every pair of signs is realized by genuine sheaf lifts, with full relations
and an actual equivariant basis, over the original Laurent-series field. -/
theorem finite_sign_marking_realization :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∀ (eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)) (eS : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ∀ ε δ : k, ε ^ 2 = 1 → δ ^ 2 = 1 → ∃! p : (ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) × (ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)), ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) (ArithmeticThetaSymmetricMarkingR0142.constant k ε) eA p.1 ∧ ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) (ArithmeticThetaSymmetricMarkingR0142.constant k δ) eB p.2 ∧ ArithmeticThetaGeometricLiftsR0141.Relations k M s m ζ (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) p.1) (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) p.2) (ArithmeticThetaGeometricLiftsR0141.act k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS) ∧ ∃ β : Fin m → ArithmeticThetaGenericEvaluationR0140.GenericDual k M s m, ArithmeticThetaGeometricLiftsR0141.HasBasis k M s m m β ∧ ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) p.1 β ∧ ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) p.2 β ∧ ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS β := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ eA eB eS hA hB hS ε δ hε hδ
  let b := genericTheta k m hm he M hM s hs
  let fA := scalarMap k M rot scal inv ha ζ
  let fB := shiftMap k M rot scal inv ha
  let fS := inversionMap k M rot scal inv ha
  let eA' := signedLift k M s m fA eA ε hε
  let eB' := signedLift k M s m fB eB δ hδ
  obtain ⟨j, hj, hj2⟩ := sign_residue k m hm he ζ hζ ε hε
  let β : Fin m → GenericDual k M s m := fun ν =>
    sc k M s m (constant k (δ^ν.val)) (b (shiftIndex m hm j ν))
  have hb : HasBasis k M s m m b := generic_theta_basis k m hm he T M hM s hs
  have hβ : HasBasis k M s m m β := by
    apply basis_rephase k M s m m b hb (shiftIndex m hm j)
      (shift_involution m hm j hj2) (fun ν => constant k (δ^ν.val))
    intro ν
    rw [← constant_mul, ← mul_pow, ← pow_two, hδ, one_pow, constant_one]
  have la := linear_act (k := k) (M := M) (s := s) (d := m) m fA
    (GeometricScalarLiftR0141.scalarMap_over k M rot scal inv ha ζ) eA
  have lb := linear_act (k := k) (M := M) (s := s) (d := m) m fB
    (GeometricShiftLiftR0141.shiftMap_structure k M rot scal inv ha) eB
  have ls := linear_act (k := k) (M := M) (s := s) (d := m) m fS
    (GeometricInversionLiftR0141.inversionMap_structure k M rot scal inv ha) eS
  have aβ : Eigen k M s m m ζ fA eA' β := by
    intro ν
    apply (scaled_iff k M s m _ _ _).mpr
    change act k M s m fA (signedLift k M s m fA eA ε hε)
      (sc k M s m (constant k (δ^ν.val)) (b (shiftIndex m hm j ν))) = _
    rw [signedLift_act, la.scale, (scaled_iff k M s m _ _ _).mp (hA (shiftIndex m hm j ν))]
    change sc k M s m (constant k ε)
      (sc k M s m (constant k (δ^ν.val))
        (sc k M s m (phase k ζ (shiftIndex m hm j ν).val) (b (shiftIndex m hm j ν)))) =
      sc k M s m (phase k ζ ν.val)
        (sc k M s m (constant k (δ^ν.val)) (b (shiftIndex m hm j ν)))
    rw [sc_mul, sc_mul, sc_mul]
    congr 1
    rw [mul_assoc, mul_left_comm, phase_shift_sign k m hm ζ hζ j ν ε hj hε, mul_comm]
  have bβ : Cyclic k M s m m hm fB eB' β := by
    intro ν
    change act k M s m fB (signedLift k M s m fB eB δ hδ)
      (sc k M s m (constant k (δ^ν.val)) (b (shiftIndex m hm j ν))) = _
    rw [signedLift_act, lb.scale, hB (shiftIndex m hm j ν), sc_mul]
    change sc k M s m (constant k δ * constant k (δ^ν.val))
      (b (next m hm (shiftIndex m hm j ν))) =
      sc k M s m (constant k (δ^(next m hm ν).val))
        (b (shiftIndex m hm j (next m hm ν)))
    rw [shift_next, sign_next k m hm he δ hδ ν, constant_mul, mul_comm (constant k δ)]
  have sβ : Reverses k M s m m hm fS eS β := by
    intro ν
    change act k M s m fS eS
      (sc k M s m (constant k (δ^ν.val)) (b (shiftIndex m hm j ν))) = _
    rw [ls.scale, hS (shiftIndex m hm j ν)]
    change sc k M s m (constant k (δ^ν.val)) (b (negIndex m hm (shiftIndex m hm j ν))) =
      sc k M s m (constant k (δ^(negIndex m hm ν).val))
        (b (shiftIndex m hm j (negIndex m hm ν)))
    rw [shift_neg m hm j ν hj2, sign_neg k m hm he δ hδ ν]
  have hr : Relations k M s m ζ (act k M s m fA eA')
      (act k M s m fB eB') (act k M s m fS eS) := by
    apply relations_of_basis k M s m hm ζ hζ β hβ
    · exact linear_act m fA (GeometricScalarLiftR0141.scalarMap_over k M rot scal inv ha ζ) eA'
    · exact linear_act m fB (GeometricShiftLiftR0141.shiftMap_structure k M rot scal inv ha) eB'
    · exact ls
    · intro ν
      exact (scaled_iff k M s m _ _ _).mp (aβ ν)
    · exact bβ
    · exact sβ
  refine ⟨(eA', eB'), ⟨signedLift_scaled k M s m fA eA ε hε,
    signedLift_scaled k M s m fB eB δ hδ, hr, β, hβ, aβ, bβ, sβ⟩, ?_⟩
  intro p hp
  apply Prod.ext
  · exact scaled_unique k M s m fA eA p.1 eA' (constant k ε) hp.1
      (signedLift_scaled k M s m fA eA ε hε)
  · exact scaled_unique k M s m fB eB p.2 eB' (constant k δ) hp.2.1
      (signedLift_scaled k M s m fB eB δ hδ)

end ArithmeticThetaSymmetricMarkingR0142
#print axioms ArithmeticThetaSymmetricMarkingR0142.finite_sign_marking_realization
