module

public import GenericLineCoefficients
public import NormalLineFrames
public import TensorPowerRootIntegration

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower

universe u

noncomputable section

set_option maxHeartbeats 3000000

namespace ArithmeticThetaNormalizedSections

/-! The one-chart statement is obtained from the accepted affine-cover gluing
theorem by measuring every cover frame against the prescribed frame. -/

theorem existsUnique_root_from_one_chart (X : Scheme.{u}) [IsIntegral X]
    (H : X.Modules) (hN : NormalAffine X) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) (n : ℕ) (hn : 0 < n)
    (r : X.functionField) (F : Γ(tensorPower X H n, ⊤))
    (hpow : r ^ n = powerCoefficient X H U e n F) :
    ∃! s : Γ(H, ⊤),
      sectionCoefficient X H U e s = r ∧
      tensorPowerSection X H n ⊤ s = F := by
  obtain ⟨C⟩ := exists_normalFrameCover X H hN hH
  letI (i : X) : Nonempty (U ⊓ C.opens i : X.Opens) :=
    overlap_nonempty X U (C.opens i)
  let T : RationalFrame C :=
    { coeff := fun i => by
        letI : Nonempty (U ⊓ C.opens i : X.Opens) := overlap_nonempty X U (C.opens i)
        exact X.germToFunctionField (U ⊓ C.opens i)
          (transition (e.equiv _ inf_le_left) ((C.frame i).equiv _ inf_le_right))
      nonzero := by
        intro i
        letI : Nonempty (U ⊓ C.opens i : X.Opens) := overlap_nonempty X U (C.opens i)
        exact ((transitionUnit (e.equiv _ inf_le_left)
          ((C.frame i).equiv _ inf_le_right)).isUnit.map
          (X.germToFunctionField (U ⊓ C.opens i)).hom).ne_zero
      transition_eq := by
        intro i j
        letI : Nonempty (U ⊓ C.opens i : X.Opens) := overlap_nonempty X U (C.opens i)
        let W : X.Opens := (U ⊓ C.opens i) ⊓ C.opens j
        letI : Nonempty W := overlap_nonempty X (U ⊓ C.opens i) (C.opens j)
        have hc := congrArg (X.germToFunctionField W)
          (transition_cocycle (e.equiv W (inf_le_left.trans inf_le_left))
            ((C.frame i).equiv W (inf_le_left.trans inf_le_right))
            ((C.frame j).equiv W (inf_le_right)))
        rw [map_mul] at hc
        rw [← germ_restrict X (U ⊓ C.opens j) W
            (le_inf ((inf_le_left : W ≤ U ⊓ C.opens i).trans inf_le_left)
              (inf_le_right : W ≤ C.opens j)),
          ← germ_restrict X (C.opens i ⊓ C.opens j) W
            (le_inf ((inf_le_left : W ≤ U ⊓ C.opens i).trans inf_le_right)
              (inf_le_right : W ≤ C.opens j)),
          ← germ_restrict X (U ⊓ C.opens i) W inf_le_left]
        rw [transition_restrict, transition_restrict]
        change _ = X.germToFunctionField W
            (X.presheaf.map (homOfLE
              (le_inf ((inf_le_left : W ≤ U ⊓ C.opens i).trans inf_le_right)
                (inf_le_right : W ≤ C.opens j))).op
              (transition ((C.frame i).equiv (C.opens i ⊓ C.opens j) inf_le_left)
                ((C.frame j).equiv (C.opens i ⊓ C.opens j) inf_le_right))) * _
        rw [transition_restrict]
        exact hc.trans (mul_comm _ _)}
  obtain ⟨s, ⟨hs, hF⟩, huniq⟩ := existsUnique_regular_tensor_root X H X C T n hn r F (by
    intro i
    letI : Nonempty (U ⊓ C.opens i : X.Opens) := overlap_nonempty X U (C.opens i)
    let W := U ⊓ C.opens i
    let : Nonempty W := overlap_nonempty X U (C.opens i)
    let aU : Γ(X, U) :=
      sectionCoordinate X (tensorPower X H n) U
        (tensorPowerFrame X H U e n) F
    let ai : Γ(X, C.opens i) :=
      sectionCoordinate X (tensorPower X H n) (C.opens i)
        (tensorPowerFrame X H (C.opens i) (C.frame i) n) F
    have hU :
        (tensorPowerFrame X H U e n).equiv W
            inf_le_left
            (X.presheaf.map
              (homOfLE (inf_le_left : W ≤ U)).op aU) =
          (tensorPower X H n).presheaf.map
            (homOfLE (le_top : W ≤ ⊤)).op F := by
      rw [← (tensorPowerFrame X H U e n).naturality U W inf_le_left le_rfl]
      simp only [aU, sectionCoordinate, LinearEquiv.apply_symm_apply]
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, homOfLE_comp]
    have hI :
        (tensorPowerFrame X H (C.opens i) (C.frame i) n).equiv W
            (inf_le_right)
            (X.presheaf.map
              (homOfLE (inf_le_right : W ≤ C.opens i)).op ai) =
          (tensorPower X H n).presheaf.map
            (homOfLE (le_top : W ≤ ⊤)).op F := by
      rw [← (tensorPowerFrame X H (C.opens i) (C.frame i) n).naturality
        (C.opens i) W inf_le_right le_rfl]
      simp only [ai, sectionCoordinate, LinearEquiv.apply_symm_apply]
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, homOfLE_comp]
    have hcoord := hU.trans hI.symm
    have htr := transition_apply
      ((tensorPowerFrame X H U e n).equiv W
        inf_le_left)
      ((tensorPowerFrame X H (C.opens i) (C.frame i) n).equiv W inf_le_right)
      (X.presheaf.map
        (homOfLE (inf_le_right : W ≤ C.opens i)).op ai)
    have hpowframe := tensorPowerFrame_transition X H U (C.opens i) e
      (C.frame i) n W inf_le_left inf_le_right
    have htr' :
        transition
          ((tensorPowerFrame X H U e n).equiv W
            inf_le_left)
          ((tensorPowerFrame X H (C.opens i) (C.frame i) n).equiv W inf_le_right) =
          transition (e.equiv W inf_le_left)
            ((C.frame i).equiv W inf_le_right) ^ n := by
      exact congrArg (fun z : Γ(X, W)ˣ => (z : Γ(X, W))) hpowframe
    have hcoord' :
        X.presheaf.map
          (homOfLE (inf_le_left : W ≤ U)).op aU =
          (transition (e.equiv W inf_le_left)
            ((C.frame i).equiv W inf_le_right) ^ n) *
            (X.presheaf.map
              (homOfLE (inf_le_right : W ≤ C.opens i)).op ai) := by
      apply ((tensorPowerFrame X H U e n).equiv W
        inf_le_left).injective
      rw [htr'] at htr
      rw [hcoord, htr]
    have hg := congrArg (X.germToFunctionField W) hcoord'
    rw [map_mul, germ_restrict, germ_restrict] at hg
    have hpow' :
        (r / T.coeff i) ^ n =
          X.germToFunctionField (C.opens i) ai := by
      have hT : T.coeff i = X.germToFunctionField W
          (transition (e.equiv W inf_le_left)
            ((C.frame i).equiv W inf_le_right)) := by
        rfl
      rw [hT]
      dsimp [powerCoefficient] at hpow
      have heq : r ^ n = X.germToFunctionField U aU := hpow
      rw [div_pow, heq, hg]
      have hq : X.germToFunctionField W
          (transition (e.equiv W inf_le_left) ((C.frame i).equiv W inf_le_right)) ≠ 0 := by
        rw [← hT]
        exact T.nonzero i
      field_simp [hq]
      rw [map_pow, mul_comm]
    simpa [ai, coordinate, sectionCoordinate] using hpow')
  have hsU : sectionCoefficient X H U e s = r := by
    let i : X := Classical.choice (show Nonempty X from inferInstance)
    let W : X.Opens := U ⊓ C.opens i
    letI : Nonempty W := overlap_nonempty X U (C.opens i)
    let aU : Γ(X, U) := sectionCoordinate X H U e s
    let ai : Γ(X, C.opens i) := coordinate C s i
    have hU :
        e.equiv W inf_le_left (X.presheaf.map
          (homOfLE (inf_le_left : W ≤ U)).op aU) =
          H.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := by
      rw [← e.naturality U W inf_le_left le_rfl]
      simp only [aU, sectionCoordinate, LinearEquiv.apply_symm_apply]
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, homOfLE_comp]
    have hI :
        (C.frame i).equiv W inf_le_right (X.presheaf.map
          (homOfLE (inf_le_right : W ≤ C.opens i)).op ai) =
          H.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := by
      rw [← (C.frame i).naturality (C.opens i) W inf_le_right le_rfl]
      simp only [ai, coordinate, LinearEquiv.apply_symm_apply]
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, homOfLE_comp]
    have hcoord := hU.trans hI.symm
    have htr := transition_apply (e.equiv W inf_le_left)
      ((C.frame i).equiv W inf_le_right)
      (X.presheaf.map (homOfLE (inf_le_right : W ≤ C.opens i)).op ai)
    have hcoord' :
        X.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op aU =
          transition (e.equiv W inf_le_left) ((C.frame i).equiv W inf_le_right) *
            X.presheaf.map (homOfLE (inf_le_right : W ≤ C.opens i)).op ai := by
      apply (e.equiv W inf_le_left).injective
      rw [hcoord, htr]
    have hg := congrArg (X.germToFunctionField W) hcoord'
    rw [map_mul, germ_restrict, germ_restrict] at hg
    have hT : T.coeff i = X.germToFunctionField W
        (transition (e.equiv W inf_le_left) ((C.frame i).equiv W inf_le_right)) := by
      rfl
    change X.germToFunctionField U aU = r
    rw [hg, hs i, hT]
    have hq : X.germToFunctionField W
        (transition (e.equiv W inf_le_left) ((C.frame i).equiv W inf_le_right)) ≠ 0 := by
      rw [← hT]
      exact T.nonzero i
    field_simp [hq]
  refine ⟨s, ?_, ?_⟩
  · exact ⟨hsU, hF⟩
  · intro t ht
    apply sectionCoefficient_injective X H hH U e
    exact ht.1.trans hsU.symm

end ArithmeticThetaNormalizedSections
