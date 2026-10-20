module

public import SymmetricMarkingFiniteSignsR0142
public import FiniteSignMarkingRealizationR0142

@[expose] public section

/-! Finite correction of arbitrary symmetric markings and actual fiber values. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaSymmetricMarkingR0142
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaModelSymmetriesR0137
open GeometricThetaRelationsR0141 FiniteSignMarkingRealizationR0142

namespace AlignedMarkingProjectiveValuesR0142
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ)

lemma act_scaled_back (f : genericScheme k M ⟶ genericScheme k M)
    (e e' : Lift k M s d f) (a : k) (ha : a^2=1)
    (h : LiftScaled k M s d f (constant k a) e e') (φ : GenericDual k M s d) :
    act k M s d f e φ = sc k M s d (constant k a) (act k M s d f e' φ) := by
  rw [SymmetricMarkingFiniteSignsR0142.act_scaled k M s d f e e' _ h,
    sc_mul, constant_sq k a ha, sc_one]

lemma rephase_zero (m : ℕ) (hm : 0 < m) (δ : k) (j : Fin m)
    (β : Fin m → GenericDual k M s m) :
    rephase k M s m hm δ j β (zeroIndex m hm) = β j := by
  change sc k M s m (constant k (δ^0)) (β _) = _
  rw [pow_zero, constant_one, sc_one]
  congr 1
  apply Fin.ext
  simpa only [shiftIndex, zeroIndex, Nat.zero_add] using Nat.mod_eq_of_lt j.isLt

end AlignedMarkingProjectiveValuesR0142
open AlignedMarkingProjectiveValuesR0142

/-- Every equivariant basis for a symmetric marking has the complete normalized
unary ratios after the specified finite sign and residue correction. -/
theorem aligned_marking_projective_values :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∀ (eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)) (eS : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ∀ (eA' : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB' : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)), ArithmeticThetaSymmetricMarkingR0142.Symmetric k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS eA' → ArithmeticThetaSymmetricMarkingR0142.Symmetric k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS eB' → ∀ β : Fin m → ArithmeticThetaGenericEvaluationR0140.GenericDual k M s m, ArithmeticThetaGeometricLiftsR0141.HasBasis k M s m m β → ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA' β → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB' β → ∃ (ε δ : k) (j : Fin m), ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ (ζ : k) ^ j.val = ε ∧ ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) (ArithmeticThetaSymmetricMarkingR0142.constant k ε) eA eA' ∧ ArithmeticThetaSymmetricMarkingR0142.LiftScaled k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) (ArithmeticThetaSymmetricMarkingR0142.constant k δ) eB eB' ∧ ArithmeticThetaGeometricLiftsR0141.HasBasis k M s m m (ArithmeticThetaSymmetricMarkingR0142.rephase k M s m hm δ j β) ∧ ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaSymmetricMarkingR0142.rephase k M s m hm δ j β) ∧ ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaSymmetricMarkingR0142.rephase k M s m hm δ j β) ∧ ArithmeticThetaGeometricLiftsR0141.Reverses k M s m m hm (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) eS (ArithmeticThetaSymmetricMarkingR0142.rephase k M s m hm δ j β) ∧ Nonempty (ArithmeticThetaGenericEvaluationR0140.GenericFrame k M s hs.1 m) ∧ ∀ frame : ArithmeticThetaGenericEvaluationR0140.GenericFrame k M s hs.1 m, ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m frame (β j) ≠ 0 ∧ ∀ ν : Fin m, ArithmeticThetaSymmetricMarkingR0142.constant k (δ ^ ν.val) * ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m frame (β (ArithmeticThetaSymmetricMarkingR0142.shiftIndex m hm j ν)) / ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m frame (β j) = (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ν)) / (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm))) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ eA eB eS hA hB hS
    eA' eB' symA symB β hβ hAβ hBβ
  obtain ⟨⟨ε, δ⟩, ⟨hε, hδ, hAA, hBB, _⟩, _⟩ :=
    symmetric_marking_finite_signs k m hm he T M hM s hs rot scal inv ha ζ hζ
      eA eB eS hA hB hS eA' eB' symA symB
  obtain ⟨j, hj, hj2⟩ := sign_residue k m hm he ζ hζ ε hε
  let γ := rephase k M s m hm δ j β
  let fA := scalarMap k M rot scal inv ha ζ
  let fB := shiftMap k M rot scal inv ha
  let fS := inversionMap k M rot scal inv ha
  have hγ : HasBasis k M s m m γ := by
    apply basis_rephase k M s m m β hβ (shiftIndex m hm j)
      (shift_involution m hm j hj2) (fun ν => constant k (δ^ν.val))
    intro ν
    rw [← constant_mul, ← mul_pow, ← pow_two, hδ, one_pow, constant_one]
  have la := linear_act (k := k) (M := M) (s := s) (d := m) m fA
    (GeometricScalarLiftR0141.scalarMap_over k M rot scal inv ha ζ) eA'
  have lb := linear_act (k := k) (M := M) (s := s) (d := m) m fB
    (GeometricShiftLiftR0141.shiftMap_structure k M rot scal inv ha) eB'
  have ls := linear_act (k := k) (M := M) (s := s) (d := m) m fS
    (GeometricInversionLiftR0141.inversionMap_structure k M rot scal inv ha) eS
  have aγ : Eigen k M s m m ζ fA eA γ := by
    intro ν
    apply (scaled_iff k M s m _ _ _).mpr
    change act k M s m fA eA
      (sc k M s m (constant k (δ^ν.val)) (β (shiftIndex m hm j ν))) = _
    rw [act_scaled_back k M s m fA eA eA' ε hε hAA, la.scale,
      (scaled_iff k M s m _ _ _).mp (hAβ (shiftIndex m hm j ν))]
    change sc k M s m (constant k ε)
      (sc k M s m (constant k (δ^ν.val))
        (sc k M s m (phase k ζ (shiftIndex m hm j ν).val) (β (shiftIndex m hm j ν)))) =
      sc k M s m (phase k ζ ν.val)
        (sc k M s m (constant k (δ^ν.val)) (β (shiftIndex m hm j ν)))
    rw [sc_mul, sc_mul, sc_mul]
    congr 1
    rw [mul_assoc, mul_left_comm, phase_shift_sign k m hm ζ hζ j ν ε hj hε, mul_comm]
  have bγ : Cyclic k M s m m hm fB eB γ := by
    intro ν
    change act k M s m fB eB
      (sc k M s m (constant k (δ^ν.val)) (β (shiftIndex m hm j ν))) = _
    rw [act_scaled_back k M s m fB eB eB' δ hδ hBB, lb.scale,
      hBβ (shiftIndex m hm j ν), sc_mul]
    change sc k M s m (constant k δ * constant k (δ^ν.val))
      (β (next m hm (shiftIndex m hm j ν))) =
      sc k M s m (constant k (δ^(next m hm ν).val))
        (β (shiftIndex m hm j (next m hm ν)))
    rw [shift_next, sign_next k m hm he δ hδ ν, constant_mul, mul_comm (constant k δ)]
  have sγ : Reverses k M s m m hm fS eS γ := by
    obtain ⟨c, hc, _⟩ := geometric_intertwiner_rigidity k m hm he T M hM s hs
      rot scal inv ha ζ hζ eA eB hA hB γ hγ aγ bγ
    have hcommon (ν : Fin m) := (scaled_iff k M s m _ _ _).mp (hc.2 ν)
    intro ν
    rw [hcommon ν, ls.scale, hS ν, hcommon (negIndex m hm ν)]
  obtain ⟨hframe, hvalues⟩ := geometric_basis_projective_values k m hm he T M hM s hs
    rot scal inv ha ζ hζ eA eB hA hB γ hγ aγ bγ
  refine ⟨ε, δ, j, hε, hδ, hj, hAA, hBB, hγ, aγ, bγ, sγ, hframe, ?_⟩
  intro frame
  have hz : γ (zeroIndex m hm) = β j := rephase_zero k M s m hm δ j β
  have hv (ν : Fin m) : genericValue k M s hs.1 m frame (γ ν) =
      constant k (δ^ν.val) * genericValue k M s hs.1 m frame (β (shiftIndex m hm j ν)) := by
    apply GeometricBasisProjectiveValuesR0141.value_scaled
    exact (scaled_iff k M s m _ _ _).mpr rfl
  constructor
  · simpa only [hz] using (hvalues frame).1
  · intro ν
    simpa only [hz, hv] using (hvalues frame).2 ν

end ArithmeticThetaSymmetricMarkingR0142
#print axioms ArithmeticThetaSymmetricMarkingR0142.aligned_marking_projective_values
