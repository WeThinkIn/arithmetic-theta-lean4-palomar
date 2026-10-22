module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
public import P2M.Util
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom IsQuasicoherent res obj"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem eq_zero_of_forall_res_basicOpen_eq_zero {F : OModulePresheaf π} (hF : OModulePresheaf.IsQuasicoherent F)
    (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1)
    (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 := by
  choose n hn using fun j => (hF U (h j)).2 x (hx j)

  have hspan : Ideal.span (Set.range fun j => (h j) ^ (n j + 1)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    exact (hcov.trans (iSup_mono fun j =>
        (V.basicOpen_pow (h j) (n j).succ_pos).ge)).trans
      (iSup_le fun j => le_iSup_of_le ⟨_, j, rfl⟩ le_rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : Γ(V, U.1)) ∈ Ideal.span _ from hspan ▸ Submodule.mem_top)
  calc x = (1 : Γ(V, U.1)) • x := (one_smul _ x).symm
    _ = (∑ j, c j * (h j) ^ (n j + 1)) • x := by rw [hc]
    _ = ∑ j, c j • ((h j) ^ (n j + 1) • x) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => by
        rw [pow_succ', mul_smul, hn j, smul_zero, smul_zero]

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1)) (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1) (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 :=
  AlgebraicGeometry.OModulePresheaf.G4T.eq_zero_of_forall_res_basicOpen_eq_zero hF U h hcov x hx
